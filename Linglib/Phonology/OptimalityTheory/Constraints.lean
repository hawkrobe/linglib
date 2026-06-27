import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Basic
import Linglib.Phonology.Constraints.Weighted
import Linglib.Core.Computability.TierProjection
import Linglib.Core.Computability.Subregular.Language.ForbiddenPairs

/-!
# Shared Phonological Constraint Library
[prince-smolensky-1993] [mccarthy-prince-1995]

Reusable constraint constructors for Optimality Theory and Harmonic Grammar.
Every phonological study in linglib defines constraints as `NamedConstraint C`
or `WeightedConstraint C` instances. Many constraint *families* recur across
studies with different candidate types:

- **MAX**: penalizes deletion (segment/feature not in output)
- **DEP**: penalizes epenthesis (segment/feature in output but not input)
- **IDENT**: penalizes featural unfaithfulness
- **\*STRUC**: penalizes structural complexity (markedness)
- **ALIGN**: penalizes edge mismatches between morphological and prosodic
  constituents ([mccarthy-prince-1993] Generalized Alignment, used
  by [faust-2026] as \*Misalignment)

This module provides generic constructors so that study files can write:

```
def myMax := mkMax "MAX-V" (fun c => c.deleted)
```

rather than manually assembling the `NamedConstraint` record each time. The
constructors tag each constraint with its `Family`; the substantive
faithfulness distinctions (MAX vs DEP vs IDENT) live in `Correspondence`.

## Contextual faithfulness

Following [coetzee-pater-2011], contextual faithfulness constraints
(e.g. MAX-PRE-V, MAX-FINAL) are standard MAX/DEP constraints with an
additional context predicate. `mkMaxCtx` and `mkDepCtx` take a context
guard: the constraint is violated only when the context guard is true.

## Violation counting

All constructors support both binary (0/1) and gradient (Nat) violations.
Binary constraints use a `Bool` predicate; gradient constraints use a
`Nat`-valued evaluation function directly.
-/

namespace OptimalityTheory

open Constraints

-- ============================================================================
-- § 1: Faithfulness Constraint Constructors
-- ============================================================================

/-- Build a MAX constraint (penalizes deletion).

    `P c` holds (as a proposition) when candidate `c` exhibits deletion.
    Decidable for the constraint to be evaluable. -/
def mkMax {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if P c then 1 else 0 }

/-- Build a contextual MAX constraint.
    Violated only when both deletion occurs AND the context holds.
    Models positional faithfulness ([coetzee-pater-2011] §3.2). -/
def mkMaxCtx {C : Type*} (name : String)
    (Deleted : C → Prop) [DecidablePred Deleted]
    (Context : C → Prop) [DecidablePred Context] :
    NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if Deleted c ∧ Context c then 1 else 0 }

/-- Build a DEP constraint (penalizes epenthesis).
    `P c` holds when candidate `c` exhibits insertion. -/
def mkDep {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if P c then 1 else 0 }

/-- Build an IDENT constraint (penalizes featural change).
    `P c` holds when the feature value has changed. -/
def mkIdent {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name := name
    family := .faithfulness
    eval := fun c => if P c then 1 else 0 }


-- ============================================================================
-- § 2: Markedness Constraint Constructors (re-exported from Constraint)
-- ============================================================================

-- `mkMark`, `mkFaith`, `mkMarkGrad`, `mkFaithGrad` are defined in `Constraint`.
-- Re-export them so `open OptimalityTheory` includes them.
export Constraints (mkMark mkFaith mkMarkGrad mkFaithGrad)

-- ============================================================================
-- § 2b: Forbidden-Pair Markedness (OCP, sibilant-harmony, …)
-- ============================================================================

-- `countAdjacent` lives at the substrate layer in
-- `Subregular.ForbiddenPairs` since it is alphabet-generic
-- list combinatorics with nothing OT-specific. Re-exported here so consumers
-- of `OptimalityTheory` see it under the conventional name.
export Subregular (countAdjacent)

/-- Build a markedness constraint penalizing tier-adjacent forbidden pairs.
    The candidate's raw symbol list is extracted by `extract`, the tier `T`
    projects it onto the relevant tier alphabet (an erasing string
    homomorphism — see `Core.Computability.TierProjection`), and each tier-adjacent pair `(a, b)`
    with `R a b` contributes one violation.

    Generic markedness constructor for adjacency-based phonological
    constraints over a single tier. OCP is the case `R := (· = ·)`
    (`mkOCPOnTier` below). The TSL_2 bridge
    `Subregular.mkForbidPairsOnTier_zero_iff_in_lang` characterizes
    zero-violation candidates as members of the corresponding tier-based
    strictly 2-local language for any choice of `R`. -/
def mkForbidPairsOnTier {C α β : Type*} (name : String) (R : β → β → Prop)
    [DecidableRel R] (T : TierProjection α β) (extract : C → List α) :
    NamedConstraint C :=
  mkMarkGrad name (fun c => countAdjacent R (TierProjection.apply T (extract c)))

-- ---- SL_1 helper for forbidden singletons ---------------------------------

/-- Build a markedness constraint penalizing tier elements satisfying `P`.
    The SL_1 sibling of `mkForbidPairsOnTier`: each tier symbol `a` with
    `P a` contributes one violation. \*Coda — viewed as "no segment in
    coda position survives the syllable-coda tier" — is the canonical SL_1
    instance and should use this constructor rather than be shoehorned into
    the forbidden-*pair* schema. The TSL_1 / SL_1 language-side bridge is
    not yet wired; the constructor exists to keep SL_1 phenomena from
    silently masquerading as TSL_2. -/
def mkForbidSingletonOnTier {C α β : Type*} (name : String) (P : β → Prop)
    [DecidablePred P] (T : TierProjection α β) (extract : C → List α) :
    NamedConstraint C :=
  mkMarkGrad name
    (fun c => (TierProjection.apply T (extract c)).countP (fun x => decide (P x)))

-- ---- OCP as the identity-relation instance --------------------------------

/-- Count adjacent identical pairs in a list. Definitional alias for
    `countAdjacent (· = ·)` — kept under this name because OCP-style
    constraints read more naturally with the linguistic-domain term. -/
def adjacentIdentical {α : Type*} [DecidableEq α] : List α → Nat :=
  countAdjacent (· = ·)

/-- Build an OCP constraint ([mccarthy-1986]): penalizes adjacent identical
    elements on a tier. `project` extracts the relevant tier from a candidate.

    The OCP is parametrically polymorphic over the feature type `α` — it
    operates on identity vs. non-identity of adjacent elements, regardless
    of what kind of features they are. Following [berent-2026], this
    polymorphism captures the algebraic nature of phonological constraints:
    they generalize to novel feature values by construction. -/
def mkOCP {C α : Type*} [DecidableEq α] (name : String) (project : C → List α) :
    NamedConstraint C :=
  mkMarkGrad name (λ c => adjacentIdentical (project c))

/-- Build an OCP constraint from a `TierProjection` projection. The candidate's
    raw symbol list is extracted by `extract`, and the tier `T` projects
    that string onto the relevant tier alphabet (an erasing string
    homomorphism — see `Core.Computability.TierProjection`).

    This is the constraint-algebra adapter for the unified `TierProjection` interface:
    autosegmental tonal-tier OCP, sibilant-harmony OCP, and learned-tier
    OCP (à la [belth-2026]) all factor through this constructor.

    Defined as the `R := (· = ·)` specialization of `mkForbidPairsOnTier`,
    mirroring `mkAgreeOnTier`'s `R := (· ≠ ·)` specialization. The two
    sit in the same constraint algebra and the equivalence is `rfl`.

    [goldsmith-1976] [mccarthy-1986] [berent-2026] -/
def mkOCPOnTier {C α β : Type*} [DecidableEq β]
    (name : String) (T : TierProjection α β) (extract : C → List α) :
    NamedConstraint C :=
  mkForbidPairsOnTier name (· = ·) T extract

-- ---- AGREE as the inequality-relation instance ----------------------------

/-- Build an AGREE constraint from a `TierProjection` projection: penalizes
    each tier-adjacent pair `(a, b)` with `a ≠ b`. The non-identity dual of
    `mkOCPOnTier`. AGREE-style markedness in OT phonology is the symmetric
    specialization of `mkForbidPairsOnTier` with `R := (· ≠ ·)`, just as the
    OCP is the `R := (· = ·)` specialization. The two specializations sit in
    the same constraint algebra; their consumers (consonant harmony, vowel
    harmony, dissimilation, anti-OCP) use the same machinery up to the
    choice of `R`. -/
def mkAgreeOnTier {C α β : Type*} [DecidableEq β]
    (name : String) (T : TierProjection α β) (extract : C → List α) :
    NamedConstraint C :=
  mkForbidPairsOnTier name (· ≠ ·) T extract

-- ============================================================================
-- § 2c: Alignment ([mccarthy-prince-1993] Generalized Alignment)
-- ============================================================================

/-- Build a binary ALIGN constraint (markedness): violated when the candidate's
    edge configuration is wrong. The Generalized Alignment schema
    `Align(Cat₁, Edge₁, Cat₂, Edge₂)` ([mccarthy-prince-1993]) is given
    here in its predicate-based form: the user supplies the predicate `P c`
    that holds when the edge configuration is misaligned.

    Specific alignment instances include left/right edge alignment of
    morphological constituents to prosodic constituents and the
    \*Misalignment principle of [faust-2026] (root nonfinal element
    must not be template-final). -/
def mkAlign {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name := name
    family := .markedness
    eval := fun c => if P c then 1 else 0 }

-- ============================================================================
-- § 3: Violation Bounds
-- ============================================================================

/-- Binary constraints have violations bounded by 1. -/
theorem mkMax_bounded {C : Type*} (name : String)
    (P : C → Prop) [DecidablePred P] (c : C) :
    (mkMax name P).eval c ≤ 1 := by
  simp only [mkMax]; split <;> omega

/-- Binary markedness constraints have violations bounded by 1. -/
theorem mkMark_bounded {C : Type*} (name : String)
    (P : C → Prop) [DecidablePred P] (c : C) :
    (mkMark name P).eval c ≤ 1 := by
  simp only [mkMark]; split <;> omega

/-- Contextual MAX constraints have violations bounded by 1. -/
theorem mkMaxCtx_bounded {C : Type*} (name : String)
    (D : C → Prop) [DecidablePred D]
    (Ctx : C → Prop) [DecidablePred Ctx] (c : C) :
    (mkMaxCtx name D Ctx).eval c ≤ 1 := by
  simp only [mkMaxCtx]; split <;> omega

-- ============================================================================
-- § 4: Weighted Constraint Constructors
-- ============================================================================

open Constraints

/-- Build a weighted MAX constraint with a given weight. -/
def mkMaxW {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] (w : ℝ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkMax name P, weight := w }

/-- Build a weighted DEP constraint. -/
def mkDepW {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] (w : ℝ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkDep name P, weight := w }

/-- Build a weighted IDENT constraint. -/
def mkIdentW {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] (w : ℝ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkIdent name P, weight := w }

/-- Build a weighted binary markedness constraint. -/
def mkMarkW {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] (w : ℝ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkMark name P, weight := w }

/-- Build a weighted gradient markedness constraint. -/
def mkMarkGradW {C : Type*} (name : String) (violations : C → Nat) (w : ℝ) :
    WeightedConstraint C :=
  { toNamedConstraint := mkMarkGrad name violations, weight := w }

end OptimalityTheory
