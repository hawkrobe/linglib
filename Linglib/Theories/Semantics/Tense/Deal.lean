import Linglib.Theories.Semantics.Tense.Basic

/-!
# Deal (2020): Counterfactual Tense and the Upper Limit Constraint

Deal's theory: past morphology in counterfactuals encodes **modal distance**,
not temporal precedence. This explains why counterfactual "were" does not
locate events in the past ("If I were rich..." is about the present).

## Core Mechanisms

1. **Counterfactual distance**: past morphology marks modal remoteness
   from actuality, not temporal precedence
2. **ULC refinement**: the Upper Limit Constraint holds for temporal tense
   but not for counterfactual tense (which is not truly temporal)

## Key Innovation

Abusch's ULC says embedded R ≤ matrix E. But counterfactuals violate this:
"If I were rich, I would buy a house" — the "were" does not refer to a
time before the attitude event. Deal resolves this by distinguishing
temporal tense (subject to ULC) from counterfactual tense (exempt from ULC).

## References

- Deal, A. R. (2020). Counterfactuals and the Upper Limit Constraint.
  Handout, LSA Summer Institute.
- Iatridou, S. (2000). The grammatical ingredients of counterfactuality.
  *Linguistic Inquiry* 31(2): 231-270.
-/

namespace Semantics.Tense.Deal

open Core.Tense
open Core.Reichenbach
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Counterfactual Distance
-- ════════════════════════════════════════════════════════════════

/-- The two uses of past morphology, following Iatridou (2000).

    Past morphology is ambiguous between:
    1. Temporal precedence (genuine past tense)
    2. Modal remoteness (counterfactual distance from actuality)

    Iatridou's "exclusion feature": past morphology marks exclusion
    from the set of relevant times/worlds. Temporal past excludes
    present times; counterfactual past excludes actual worlds. -/
inductive PastMorphologyUse where
  /-- Temporal: precedence on the time line -/
  | temporal
  /-- Counterfactual: distance from actuality -/
  | counterfactual
  deriving DecidableEq, Repr, BEq

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
-- § ULC Refinement
-- ════════════════════════════════════════════════════════════════

/-- Deal's refined ULC: the upper limit constraint applies only to
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


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Deal derives the counterfactual override: counterfactual morphology
    is not subject to the ULC, because it doesn't encode temporal
    precedence. -/
theorem deal_counterfactual_overrides_ulc {Time : Type*} [LinearOrder Time]
    (embeddedR matrixE : Time) (h_forward : embeddedR > matrixE) :
    -- Despite R > E_matrix (violating temporal ULC), the counterfactual
    -- "ULC" is trivially satisfied
    refinedULC .counterfactual embeddedR matrixE := by
  simp [refinedULC]

/-- Deal refines the ULC: it holds for temporal tense but not for
    counterfactual tense. The temporal and counterfactual uses of
    past morphology have different formal properties. -/
theorem deal_refines_ulc {Time : Type*} [LinearOrder Time]
    (embeddedR matrixE : Time) (h_forward : embeddedR > matrixE) :
    ¬ refinedULC .temporal embeddedR matrixE ∧
    refinedULC .counterfactual embeddedR matrixE := by
  constructor
  · simp [refinedULC, upperLimitConstraint]
    omega
  · simp [refinedULC]

/-- The two uses of past morphology are genuinely distinct:
    temporal tense ≠ counterfactual tense. -/
theorem temporal_ne_counterfactual :
    PastMorphologyUse.temporal ≠ PastMorphologyUse.counterfactual :=
  nofun


-- ════════════════════════════════════════════════════════════════
-- § Theory Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Deal (2020) theory identity card. -/
def Deal : TenseTheory where
  name := "Deal 2020"
  citation := "Deal, A. R. (2020). Counterfactuals and the Upper Limit Constraint."
  hasTemporalDeRe := false
  hasULC := true  -- has ULC but refined (temporal only)
  hasZeroTense := false
  hasSOTDeletion := false
  simultaneousMechanism := "not primary focus (inherits from base tense theory)"


end Semantics.Tense.Deal
