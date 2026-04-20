import Linglib.Core.Constraint.OT.Basic
import Linglib.Core.Constraint.Weighted
import Linglib.Core.StringHom

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
- **ALIGN**: penalizes edge mismatches between morphological and prosodic
  constituents (@cite{mccarthy-prince-1993} Generalized Alignment, used
  by @cite{faust-2026} as \*Misalignment)

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

open Core.Constraint.OT

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
-- § 2: Markedness Constraint Constructors (re-exported from Core.Constraint.OT)
-- ============================================================================

-- `mkMark`, `mkFaith`, `mkMarkGrad`, `mkFaithGrad` are defined in `Core.Constraint.OT`.
-- Re-export them so `open Phonology.Constraints` includes them.
export Core.Constraint.OT (mkMark mkFaith mkMarkGrad mkFaithGrad)

-- ============================================================================
-- § 2b: Forbidden-Pair Markedness (OCP, sibilant-harmony, …)
-- ============================================================================

/-- Count adjacent pairs `(a, b)` in a list satisfying a binary relation `R`.
    The shared engine behind any "forbidden adjacent pair" markedness
    constraint over a single segmental tier: OCP (`R := (· = ·)`), agreement
    constraints (`R := disagree-on-feature-X`), and the like. Stress-based
    rhythm constraints (\*Lapse, \*Clash) require a syllable-level alphabet,
    not a segment-level one, and so live in their own constructors. -/
def countAdjacent {α : Type} (R : α → α → Prop) [DecidableRel R] :
    List α → Nat
  | [] | [_] => 0
  | a :: b :: rest => (if R a b then 1 else 0) + countAdjacent R (b :: rest)

/-- Build a markedness constraint penalizing tier-adjacent forbidden pairs.
    The candidate's raw symbol list is extracted by `extract`, the tier `T`
    projects it onto the relevant tier alphabet (an erasing string
    homomorphism — see `Core.StringHom`), and each tier-adjacent pair `(a, b)`
    with `R a b` contributes one violation.

    Generic markedness constructor for adjacency-based phonological
    constraints over a single tier. OCP is the case `R := (· = ·)`
    (`mkOCPOnTier` below). The TSL_2 bridge
    `Phonology.Subregular.mkForbidPairsOnTier_zero_iff_in_lang` characterizes
    zero-violation candidates as members of the corresponding tier-based
    strictly 2-local language for any choice of `R`. -/
def mkForbidPairsOnTier {C α β : Type} (name : String) (R : β → β → Prop)
    [DecidableRel R] (T : Core.Tier α β) (extract : C → List α) :
    NamedConstraint C :=
  mkMarkGrad name (fun c => countAdjacent R (Core.Tier.apply T (extract c)))

-- ---- SL_1 helper for forbidden singletons ---------------------------------

/-- Build a markedness constraint penalizing tier elements satisfying `P`.
    The SL_1 sibling of `mkForbidPairsOnTier`: each tier symbol `a` with
    `P a` contributes one violation. \*Coda — viewed as "no segment in
    coda position survives the syllable-coda tier" — is the canonical SL_1
    instance and should use this constructor rather than be shoehorned into
    the forbidden-*pair* schema. The TSL_1 / SL_1 language-side bridge is
    not yet wired; the constructor exists to keep SL_1 phenomena from
    silently masquerading as TSL_2. -/
def mkForbidSingletonOnTier {C α β : Type} (name : String) (P : β → Prop)
    [DecidablePred P] (T : Core.Tier α β) (extract : C → List α) :
    NamedConstraint C :=
  mkMarkGrad name
    (fun c => (Core.Tier.apply T (extract c)).countP (fun x => decide (P x)))

-- ---- OCP as the identity-relation instance --------------------------------

/-- Count adjacent identical pairs in a list. Definitional alias for
    `countAdjacent (· = ·)` — kept under this name because OCP-style
    constraints read more naturally with the linguistic-domain term. -/
def adjacentIdentical {α : Type} [DecidableEq α] : List α → Nat :=
  countAdjacent (· = ·)

/-- Build an OCP constraint: penalizes adjacent identical elements on a tier.
    `project` extracts the relevant tier from a candidate.

    The OCP is parametrically polymorphic over the feature type `α` — it
    operates on identity vs. non-identity of adjacent elements, regardless
    of what kind of features they are. Following @cite{berent-2026}, this
    polymorphism captures the algebraic nature of phonological constraints:
    they generalize to novel feature values by construction. -/
def mkOCP {C α : Type} [DecidableEq α] (name : String) (project : C → List α) :
    NamedConstraint C :=
  mkMarkGrad name (λ c => adjacentIdentical (project c))

/-- Build an OCP constraint from a `Core.Tier` projection. The candidate's
    raw symbol list is extracted by `extract`, and the tier `T` projects
    that string onto the relevant tier alphabet (an erasing string
    homomorphism — see `Core.StringHom`).

    This is the constraint-algebra adapter for the unified `Tier` interface:
    autosegmental tonal-tier OCP, sibilant-harmony OCP, and learned-tier
    OCP (à la @cite{belth-2026}) all factor through this constructor.

    @cite{goldsmith-1976} @cite{berent-2026} -/
def mkOCPOnTier {C α β : Type} [DecidableEq β]
    (name : String) (T : Core.Tier α β) (extract : C → List α) :
    NamedConstraint C :=
  mkOCP name (fun c => Core.Tier.apply T (extract c))

-- ---- AGREE as the inequality-relation instance ----------------------------

/-- Build an AGREE constraint from a `Core.Tier` projection: penalizes
    each tier-adjacent pair `(a, b)` with `a ≠ b`. The non-identity dual of
    `mkOCPOnTier`. AGREE-style markedness in OT phonology is the symmetric
    specialization of `mkForbidPairsOnTier` with `R := (· ≠ ·)`, just as the
    OCP is the `R := (· = ·)` specialization. The two specializations sit in
    the same constraint algebra; their consumers (consonant harmony, vowel
    harmony, dissimilation, anti-OCP) use the same machinery up to the
    choice of `R`. -/
def mkAgreeOnTier {C α β : Type} [DecidableEq β]
    (name : String) (T : Core.Tier α β) (extract : C → List α) :
    NamedConstraint C :=
  mkForbidPairsOnTier name (· ≠ ·) T extract

-- ============================================================================
-- § 2c: Alignment (@cite{mccarthy-prince-1993} Generalized Alignment)
-- ============================================================================

/-- Build a binary ALIGN constraint (markedness): violated when the candidate's
    edge configuration is wrong. The Generalized Alignment schema
    `Align(Cat₁, Edge₁, Cat₂, Edge₂)` (@cite{mccarthy-prince-1993}) is given
    here in its predicate-based form: the user supplies the predicate
    `violated c` that fires when the edge configuration is misaligned.

    Specific alignment instances include left/right edge alignment of
    morphological constituents to prosodic constituents and the
    \*Misalignment principle of @cite{faust-2026} (root nonfinal element
    must not be template-final). -/
def mkAlign {C : Type} (name : String) (violated : C → Bool) : NamedConstraint C :=
  { name := name
    family := .markedness
    eval := fun c => if violated c then 1 else 0 }

/-- Gradient ALIGN: counts edge-mismatch violations (@cite{mccarthy-prince-1993}). -/
def mkAlignGrad {C : Type} (name : String) (violations : C → Nat) :
    NamedConstraint C :=
  { name := name
    family := .markedness
    eval := violations }

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

/-- Forbidden-pair constraints are markedness constraints. -/
theorem mkForbidPairsOnTier_is_markedness {C α β : Type} (name : String)
    (R : β → β → Prop) [DecidableRel R] (T : Core.Tier α β)
    (extract : C → List α) :
    (mkForbidPairsOnTier name R T extract).family = .markedness := rfl

/-- AGREE constraints are markedness constraints. -/
theorem mkAgreeOnTier_is_markedness {C α β : Type} [DecidableEq β]
    (name : String) (T : Core.Tier α β) (extract : C → List α) :
    (mkAgreeOnTier name T extract).family = .markedness := rfl

/-- Forbidden-singleton constraints are markedness constraints. -/
theorem mkForbidSingletonOnTier_is_markedness {C α β : Type} (name : String)
    (P : β → Prop) [DecidablePred P] (T : Core.Tier α β)
    (extract : C → List α) :
    (mkForbidSingletonOnTier name P T extract).family = .markedness := rfl

/-- OCP constraints are markedness constraints. -/
theorem mkOCP_is_markedness {C α : Type} [DecidableEq α] (name : String)
    (project : C → List α) :
    (mkOCP name project).family = .markedness := rfl

/-- Tier-driven OCP constraints are markedness constraints. -/
theorem mkOCPOnTier_is_markedness {C α β : Type} [DecidableEq β] (name : String)
    (T : Core.Tier α β) (extract : C → List α) :
    (mkOCPOnTier name T extract).family = .markedness := rfl

/-- ALIGN constraints are markedness constraints
    (@cite{mccarthy-prince-1993}). -/
theorem mkAlign_is_markedness {C : Type} (name : String) (p : C → Bool) :
    (mkAlign name p).family = .markedness := rfl

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
