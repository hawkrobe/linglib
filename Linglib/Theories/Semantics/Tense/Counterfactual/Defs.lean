import Linglib.Theories.Semantics.Tense.Basic

/-!
# Counterfactual past — the two-uses-of-past machinery
@cite{iatridou-2000}

The structural commitment that past morphology is **ambiguous between
temporal and counterfactual uses**, with only the temporal use subject
to the Upper Limit Constraint. Originally proposed by
@cite{iatridou-2000} (`The Grammatical Ingredients of
Counterfactuality`); the substrate-side machinery lives here, and
@cite{iatridou-2000}'s paper-anchored derivation theorems live in
`Phenomena/Conditionals/Studies/Iatridou2000.lean`.

## Core Machinery

1. **`PastMorphologyUse`**: 2-case enum distinguishing temporal vs
   counterfactual past morphology.
2. **`CounterfactualDistance`**: world-pair structure for the modal-
   distance interpretation.
3. **`refinedULC`**: dispatch on `PastMorphologyUse` — temporal use
   carries the standard `upperLimitConstraint`, counterfactual use is
   exempt (`True`).

The split between this concept-file and the paper-anchored theorems
parallels `Tense/SOT/Ambiguity.lean` ↔ `Studies/Ogihara1996.lean`.
-/

namespace Semantics.Tense.Counterfactual

open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Counterfactual Distance
-- ════════════════════════════════════════════════════════════════

/-- Two uses of past morphology, following @cite{iatridou-2000}.

    Past morphology is ambiguous between:
    1. Temporal precedence (genuine past tense)
    2. Modal remoteness (counterfactual distance from actuality)

    @cite{iatridou-2000}'s "exclusion feature": past morphology marks
    exclusion from the set of relevant times/worlds. Temporal past
    excludes present times; counterfactual past excludes actual
    worlds. -/
inductive PastMorphologyUse where
  /-- Temporal: precedence on the time line -/
  | temporal
  /-- Counterfactual: distance from actuality -/
  | counterfactual
  deriving DecidableEq, Repr

/-- Counterfactual distance: past morphology marks modal remoteness,
    not temporal precedence. The "reference world" is remote from
    the actual world. -/
structure CounterfactualDistance (World : Type*) where
  /-- The actual world -/
  actual : World
  /-- The counterfactual world -/
  counterfactual : World
  /-- The worlds are distinct (modal distance > 0) -/
  distinct : actual ≠ counterfactual


-- ════════════════════════════════════════════════════════════════
-- § Refined ULC
-- ════════════════════════════════════════════════════════════════

/-- The refined ULC: the upper limit constraint applies only to
    temporal tense, not to counterfactual tense.

    If the past morphology is temporal, ULC holds (R ≤ E_matrix).
    If the past morphology is counterfactual, ULC does not apply. -/
def refinedULC {Time : Type*} [LE Time]
    (use : PastMorphologyUse) (embeddedR matrixE : Time) : Prop :=
  match use with
  | .temporal => upperLimitConstraint embeddedR matrixE
  | .counterfactual => True  -- no temporal constraint

/-- Temporal tense is subject to ULC. -/
theorem temporal_has_ulc {Time : Type*} [LE Time]
    (embeddedR matrixE : Time) (h : embeddedR ≤ matrixE) :
    refinedULC .temporal embeddedR matrixE :=
  h

/-- Counterfactual tense is exempt from ULC. -/
theorem counterfactual_exempt_from_ulc {Time : Type*} [LE Time]
    (embeddedR matrixE : Time) :
    refinedULC .counterfactual embeddedR matrixE :=
  trivial

/-- The two uses of past morphology are genuinely distinct. -/
theorem temporal_ne_counterfactual :
    PastMorphologyUse.temporal ≠ PastMorphologyUse.counterfactual :=
  nofun


end Semantics.Tense.Counterfactual
