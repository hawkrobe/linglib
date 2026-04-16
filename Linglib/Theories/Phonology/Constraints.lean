import Linglib.Core.Logic.OT
import Linglib.Core.Constraint.Weighted

/-!
# Shared Phonological Constraint Library
@cite{prince-smolensky-1993} @cite{mccarthy-prince-1995}

Reusable constraint constructors for Optimality Theory and Harmonic Grammar.
Every phonological study in linglib defines constraints as `NamedConstraint C`
or `WeightedConstraint C` instances. Many constraint *families* recur across
studies with different candidate types:

- **MAX**: penalizes deletion (segment/feature not in output)
- **DEP**: penalizes epenthesis (segment/feature in output but not input)
- **IDENT**: penalizes featural unfaithfulness
- **\*STRUC**: penalizes structural complexity (markedness)

This module provides generic constructors so that study files can write:

```
def myMax := mkMax "MAX-V" (fun c => c.deleted)
```

rather than manually assembling the `NamedConstraint` record each time. The
constructors enforce the correct `ConstraintFamily` classification.

## Contextual faithfulness

Following @cite{coetzee-pater-2011}, contextual faithfulness constraints
(e.g. MAX-PRE-V, MAX-FINAL) are standard MAX/DEP constraints with an
additional context predicate. `mkMaxCtx` and `mkDepCtx` take a context
guard: the constraint is violated only when the context guard is true.

## Violation counting

All constructors support both binary (0/1) and gradient (Nat) violations.
Binary constraints use a `Bool` predicate; gradient constraints use a
`Nat`-valued evaluation function directly.
-/

namespace Phonology.Constraints

open Core.OT

-- ============================================================================
-- § 1: Faithfulness Constraint Constructors
-- ============================================================================

/-- Build a MAX constraint (penalizes deletion).
    `violated c` returns `true` when candidate `c` exhibits deletion. -/
def mkMax {C : Type} (name : String) (violated : C → Bool) : NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if violated c then 1 else 0 }

/-- Build a contextual MAX constraint.
    Violated only when both deletion occurs AND the context holds.
    Models positional faithfulness (@cite{coetzee-pater-2011} §3.2). -/
def mkMaxCtx {C : Type} (name : String)
    (deleted : C → Bool) (context : C → Bool) : NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if deleted c && context c then 1 else 0 }

/-- Build a DEP constraint (penalizes epenthesis).
    `violated c` returns `true` when candidate `c` exhibits insertion. -/
def mkDep {C : Type} (name : String) (violated : C → Bool) : NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if violated c then 1 else 0 }

/-- Build an IDENT constraint (penalizes featural change).
    `violated c` returns `true` when the feature value has changed. -/
def mkIdent {C : Type} (name : String) (violated : C → Bool) : NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if violated c then 1 else 0 }

-- ============================================================================
-- § 1b: Morpheme-Specific Constraint Constructors (@cite{finley-2009})
-- ============================================================================

/-- Build a LEFT-ANCHOR constraint: the morpheme's tonal specification must
    be in correspondence with the left edge of the host.
    `violated c` returns `true` when the left anchor is not satisfied.

    Following @cite{finley-2009}: morpheme-specific versions of
    @cite{mccarthy-prince-1995}'s ANCHOR constraints. -/
def mkAnchorLeft {C : Type} (name : String) (violated : C → Bool) :
    NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := λ c => if violated c then 1 else 0 }

/-- Build a RIGHT-ANCHOR constraint: the morpheme's tonal specification must
    be in correspondence with the right edge of the host. -/
def mkAnchorRight {C : Type} (name : String) (violated : C → Bool) :
    NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := λ c => if violated c then 1 else 0 }

/-- Build an INTEGRITY constraint: the morpheme's tone must not have
    multiple correspondents in the output.
    Penalizes splitting of a single input tone across multiple output TBUs
    when the one-to-one mapping is violated. -/
def mkIntegrity {C : Type} (name : String) (violated : C → Bool) :
    NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := λ c => if violated c then 1 else 0 }

/-- Anchor-left constraints are faithfulness constraints. -/
theorem mkAnchorLeft_is_faithfulness {C : Type} (name : String) (p : C → Bool) :
    (mkAnchorLeft name p).family = .faithfulness := rfl

/-- Anchor-right constraints are faithfulness constraints. -/
theorem mkAnchorRight_is_faithfulness {C : Type} (name : String) (p : C → Bool) :
    (mkAnchorRight name p).family = .faithfulness := rfl

/-- Integrity constraints are faithfulness constraints. -/
theorem mkIntegrity_is_faithfulness {C : Type} (name : String) (p : C → Bool) :
    (mkIntegrity name p).family = .faithfulness := rfl

-- ============================================================================
-- § 2: Markedness Constraint Constructors (re-exported from Core.OT)
-- ============================================================================

-- `mkMark`, `mkFaith`, `mkMarkGrad`, `mkFaithGrad` are defined in `Core.OT`.
-- Re-export them so `open Phonology.Constraints` includes them.
export Core.OT (mkMark mkFaith mkMarkGrad mkFaithGrad)

-- ============================================================================
-- § 2b: OCP (Obligatory Contour Principle)
-- ============================================================================

/-- Count adjacent identical pairs in a list.
    Used by `mkOCP` to evaluate identity violations on a tier. -/
def adjacentIdentical {α : Type} [BEq α] : List α → Nat
  | [] | [_] => 0
  | a :: b :: rest => (if a == b then 1 else 0) + adjacentIdentical (b :: rest)

/-- Build an OCP constraint: penalizes adjacent identical elements on a tier.
    `project` extracts the relevant tier from a candidate.

    The OCP is parametrically polymorphic over the feature type `α` — it
    operates on identity vs. non-identity of adjacent elements, regardless
    of what kind of features they are. Following @cite{berent-2026}, this
    polymorphism captures the algebraic nature of phonological constraints:
    they generalize to novel feature values by construction. -/
def mkOCP {C α : Type} [BEq α] (name : String) (project : C → List α) :
    NamedConstraint C :=
  mkMarkGrad name (λ c => adjacentIdentical (project c))

-- ============================================================================
-- § 3: Classification Properties
-- ============================================================================

/-- MAX constraints are faithfulness constraints. -/
theorem mkMax_is_faithfulness {C : Type} (name : String) (p : C → Bool) :
    (mkMax name p).family = .faithfulness := rfl

/-- DEP constraints are faithfulness constraints. -/
theorem mkDep_is_faithfulness {C : Type} (name : String) (p : C → Bool) :
    (mkDep name p).family = .faithfulness := rfl

/-- Markedness constraints are markedness constraints. -/
theorem mkMark_is_markedness {C : Type} (name : String) (p : C → Bool) :
    (mkMark name p).family = .markedness := rfl

/-- Contextual MAX constraints are faithfulness constraints. -/
theorem mkMaxCtx_is_faithfulness {C : Type} (name : String)
    (d : C → Bool) (ctx : C → Bool) :
    (mkMaxCtx name d ctx).family = .faithfulness := rfl

/-- OCP constraints are markedness constraints. -/
theorem mkOCP_is_markedness {C α : Type} [BEq α] (name : String)
    (project : C → List α) :
    (mkOCP name project).family = .markedness := rfl

-- ============================================================================
-- § 4: Violation Bounds
-- ============================================================================

/-- Binary constraints have violations bounded by 1. -/
theorem mkMax_bounded {C : Type} (name : String) (p : C → Bool) (c : C) :
    (mkMax name p).eval c ≤ 1 := by
  simp only [mkMax]; split <;> omega

/-- Binary markedness constraints have violations bounded by 1. -/
theorem mkMark_bounded {C : Type} (name : String) (p : C → Bool) (c : C) :
    (mkMark name p).eval c ≤ 1 := by
  simp only [mkMark]; split <;> omega

/-- Contextual MAX constraints have violations bounded by 1. -/
theorem mkMaxCtx_bounded {C : Type} (name : String)
    (d : C → Bool) (ctx : C → Bool) (c : C) :
    (mkMaxCtx name d ctx).eval c ≤ 1 := by
  simp only [mkMaxCtx]; split <;> omega

-- ============================================================================
-- § 5: Weighted Constraint Constructors
-- ============================================================================

open Core.Constraint

/-- Build a weighted MAX constraint with a given weight. -/
def mkMaxW {C : Type} (name : String) (violated : C → Bool) (w : ℚ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkMax name violated, weight := w }

/-- Build a weighted contextual MAX constraint. -/
def mkMaxCtxW {C : Type} (name : String)
    (deleted : C → Bool) (context : C → Bool) (w : ℚ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkMaxCtx name deleted context, weight := w }

/-- Build a weighted DEP constraint. -/
def mkDepW {C : Type} (name : String) (violated : C → Bool) (w : ℚ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkDep name violated, weight := w }

/-- Build a weighted IDENT constraint. -/
def mkIdentW {C : Type} (name : String) (violated : C → Bool) (w : ℚ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkIdent name violated, weight := w }

/-- Build a weighted binary markedness constraint. -/
def mkMarkW {C : Type} (name : String) (violated : C → Bool) (w : ℚ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkMark name violated, weight := w }

/-- Build a weighted gradient markedness constraint. -/
def mkMarkGradW {C : Type} (name : String) (violations : C → Nat) (w : ℚ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkMarkGrad name violations, weight := w }

end Phonology.Constraints
