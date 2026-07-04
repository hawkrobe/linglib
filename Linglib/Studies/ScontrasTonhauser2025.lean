import Linglib.Pragmatics.RSA.ScoreChain
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.BToM
import Linglib.Semantics.Attitudes.Factivity
import Linglib.Studies.DegenTonhauser2021
import Linglib.Semantics.Presupposition.Basic

/-!
# [scontras-tonhauser-2025]: projection without lexical presupposition

An RSA model of *know* under negation (SuB 29, pp. 1431–1448): the pragmatic
listener jointly infers the world state and the speaker's private assumptions
(eq. 7), the speaker scores QUD-projected informativity (eq. 6, α = 10, fn.
12), and the literal listener answers the QUD within the assumption set
(eq. 5). Projection of the complement C emerges with no lexically-specified
constraint on the common ground. Domain: 6 utterances × 4 worlds (BEL × C) ×
15 belief states × 2 QUDs; literal semantics from
`Semantics.Attitudes.Factivity` (know = `factivePos`, think =
`nonFactivePos`).

## Main results

* `bel_qud_marginal_eq_prior_high` / `_low`: under the BEL? QUD the world
  C-marginal *equals the prior* for every utterance — S1 depends on the
  world only through its BEL-cell, so projection is invisible there.
* `prediction_2b`: higher prior ⇒ stronger projection (C? QUD), the effect
  [degen-tonhauser-2021] documents across 20 predicates (Exp 1: β = 0.16,
  p < .001).
* `prediction_2c`: BEL? QUD ⇒ stronger projection than C? QUD (Exp 2:
  β = 0.14, p < .001).
* `c_qud_thinkNeg_higher`: under C?, negated *know* is evidence against C.
* `model_predicts_effects`: the model directions match the regressions.

## Implementation notes

α = 10 is a natural power, so the chain is exact ℚ≥0: the speaker is
`RSA.Score.s1` over the QUD-aggregated literal listener with degenerate
cells falling back to `cPos` (one declaration covering both faces), the
listener is `PMF.ofScores`, and every prediction is one kernel-verified
event-mass comparison.

Utterance cost (§3.1: complex = 2 × simple) is omitted: `exp(−αC)` is
transcendental, and the omission reverses prediction (2a)'s world-marginal
direction (the paper derives know > think *with* cost, Figure 7a);
predictions (2b) and (2c) are robust to it. Prior parameters follow §3.1:
P(C) ∈ {2/3, 1/3}, P(BEL | C) = 1/2, uniform over the 15 assumption sets.

## TODO

Model the cost term (log-rational costs keep ℚ exactness) and derive
prediction (2a)'s world-marginal direction. Prove the structural equivalence
with [qing-goodman-lassiter-2016] (fn. 10: "private assumptions" vs "common
ground" is interpretive, not computational) — see the matching TODO in
`QingGoodmanLassiter2016.lean`.
-/

open scoped ENNReal NNReal NNRat

namespace ScontrasTonhauser2025

open BigOperators
open Semantics.Attitudes.Factivity

/-! ### Worlds and utterances -/

/-- World state: (BEL, C) where BEL = Cole believes C, C = complement is true.
    Flat inductive for tactic enumerability. -/
inductive WorldState where
  | w11  -- (BEL=1, C=1): Cole believes C and C is true
  | w10  -- (BEL=1, C=0): Cole believes C but C is false
  | w01  -- (BEL=0, C=1): Cole doesn't believe but C is true
  | w00  -- (BEL=0, C=0): Cole doesn't believe and C is false
  deriving DecidableEq, Repr, Inhabited, Fintype

def WorldState.bel : WorldState → Bool
  | .w11 | .w10 => true
  | .w01 | .w00 => false

def WorldState.c : WorldState → Bool
  | .w11 | .w01 => true
  | .w10 | .w00 => false

instance : HasComplement WorldState where c := WorldState.c
instance : HasBelief WorldState where bel := WorldState.bel

/-- Attitude verb utterances about Cole's mental state, plus bare
    complement assertions. -/
inductive Utterance where
  | knowPos     -- "Cole knows that C"
  | knowNeg     -- "Cole doesn't know that C"
  | thinkPos    -- "Cole thinks that C"
  | thinkNeg    -- "Cole doesn't think that C"
  | cPos        -- "C"
  | cNeg        -- "not C"
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := {.knowPos, .knowNeg, .thinkPos, .thinkNeg, .cPos, .cNeg}
  complete := fun x => by cases x <;> simp

/-! ### Literal truth conditions (from `Factivity`) -/

/-- Literal truth conditions derived from factive/non-factive semantics.

    "know" is factive: `factivePos` = BEL ∧ C
    "think" is non-factive: `nonFactivePos` = BEL
    "C" / "not C" are direct assertions about the complement. -/
def literalMeaning : Utterance → WorldState → Bool
  | .knowPos  => factivePos
  | .knowNeg  => factiveNeg
  | .thinkPos => nonFactivePos
  | .thinkNeg => nonFactiveNeg
  | .cPos     => HasComplement.c
  | .cNeg     => fun w => !HasComplement.c w

/-! ### Speaker belief states (the 15 non-empty subsets of W) -/

/-- Speaker's private assumptions: all 15 non-empty subsets of W.
    Section 3 follows [qing-goodman-lassiter-2016]: A ranges over all
    non-empty subsets of the world space. -/
inductive BeliefState where
  -- Singletons (4)
  | onlyW11 | onlyW10 | onlyW01 | onlyW00
  -- Aligned pairs (4)
  | belTrue | belFalse | cTrue | cFalse
  -- Cross pairs (2)
  | diagonal | antiDiagonal
  -- Triples (4)
  | notW11 | notW10 | notW01 | notW00
  -- Full (1)
  | all
  deriving DecidableEq, Repr, Inhabited

instance : Fintype BeliefState where
  elems := {.onlyW11, .onlyW10, .onlyW01, .onlyW00,
            .belTrue, .belFalse, .cTrue, .cFalse,
            .diagonal, .antiDiagonal,
            .notW11, .notW10, .notW01, .notW00,
            .all}
  complete := fun x => by cases x <;> simp

/-- Membership in belief state. Boolean operations on `WorldState` fields
    reduce cleanly under kernel evaluation. -/
def speakerCredenceBool : BeliefState → WorldState → Bool
  | .all, _ => true
  | .onlyW11, w => w.bel && w.c
  | .onlyW10, w => w.bel && !w.c
  | .onlyW01, w => !w.bel && w.c
  | .onlyW00, w => !w.bel && !w.c
  | .belTrue, w => w.bel
  | .belFalse, w => !w.bel
  | .cTrue, w => w.c
  | .cFalse, w => !w.c
  | .diagonal, w => (w.bel && w.c) || (!w.bel && !w.c)
  | .antiDiagonal, w => (!w.bel && w.c) || (w.bel && !w.c)
  | .notW11, w => !(w.bel && w.c)
  | .notW10, w => !(w.bel && !w.c)
  | .notW01, w => !(!w.bel && w.c)
  | .notW00, w => !(!w.bel && !w.c)

/-- Whether C is true in all worlds of the belief state. -/
def assumesC : BeliefState → Bool
  | .onlyW11 | .onlyW01 | .cTrue => true
  | _ => false

/-! ### Priors -/

/-- World prior parameterized by P(C).
    P(BEL, C) = P(BEL | C) · P(C), with P(BEL | C) = 1/2. -/
def worldPrior (pC : ℚ≥0) : WorldState → ℚ≥0
  | .w11 | .w01 => pC / 2
  | .w10 | .w00 => (1 - pC) / 2

/-- World prior sums to 1 whenever P(C) is a probability. -/
theorem worldPrior_sum {pC : ℚ≥0} (h1 : pC ≤ 1) :
    worldPrior pC .w11 + worldPrior pC .w10 +
    worldPrior pC .w01 + worldPrior pC .w00 = 1 := by
  rw [← NNRat.coe_inj]
  push_cast [worldPrior, NNRat.coe_sub h1]
  ring

/-! ### The score chain -/

/-- Literal listener within the assumption set (eq. 5): prior conditioned
on worlds where `u` is true, empty extensions normalizing to zero rows. -/
def l0Score (pC : ℚ≥0) (bs : BeliefState) (u : Utterance) : WorldState → ℚ≥0 :=
  PMF.normalizeScores fun w =>
    if speakerCredenceBool bs w && literalMeaning u w then worldPrior pC w else 0

/-- QUD aggregation of the literal listener (eq. 5). -/
def qAgg (qud : QUD) (pC : ℚ≥0) (bs : BeliefState) (u : Utterance) :
    WorldState → ℚ≥0
  | .w11 => match qud with
    | .bel => l0Score pC bs u .w11 + l0Score pC bs u .w10
    | .c   => l0Score pC bs u .w11 + l0Score pC bs u .w01
  | .w10 => match qud with
    | .bel => l0Score pC bs u .w11 + l0Score pC bs u .w10
    | .c   => l0Score pC bs u .w10 + l0Score pC bs u .w00
  | .w01 => match qud with
    | .bel => l0Score pC bs u .w01 + l0Score pC bs u .w00
    | .c   => l0Score pC bs u .w11 + l0Score pC bs u .w01
  | .w00 => match qud with
    | .bel => l0Score pC bs u .w01 + l0Score pC bs u .w00
    | .c   => l0Score pC bs u .w10 + l0Score pC bs u .w00

/-- Speaker (eq. 6 at α = 10, zero cost): `RSA.Score.s1` over the
QUD-aggregated literal listener; degenerate cells fall back to `cPos` —
one declaration covering both faces. -/
def s1Post (qud : QUD) (pC : ℚ≥0) (bs : BeliefState) :
    WorldState → Utterance → ℚ≥0 :=
  RSA.Score.s1 (fun u w => qAgg qud pC bs u w) 10 (fun _ => 1) (.pure .cPos)

/-- Listener world score (eq. 7; uniform assumption prior). -/
def worldScore (qud : QUD) (pC : ℚ≥0) (u : Utterance) (w : WorldState) : ℚ≥0 :=
  worldPrior pC w * ∑ bs, s1Post qud pC bs w u

/-- Pragmatic listener over worlds (eq. 7). -/
noncomputable def l1World (qud : QUD) (pC : ℚ≥0) (u : Utterance) :
    PMF WorldState :=
  .ofScores .uniform (worldScore qud pC u)

/-- The listener's C-marginal. -/
noncomputable def l1CEvent (qud : QUD) (pC : ℚ≥0) (u : Utterance) : ℝ≥0∞ :=
  ∑' w, if w.c then l1World qud pC u w else 0

/-! ### Listener predictions -/

/-- The C-marginals on the ℚ≥0 face. -/
private def cMass (qud : QUD) (pC : ℚ≥0) (u : Utterance) : ℚ≥0 :=
  PMF.eventMass (PMF.scoresWith .uniform (worldScore qud pC u)) (·.c)

private theorem l1CEvent_eq (qud : QUD) (pC : ℚ≥0) (u : Utterance)
    {q : ℚ≥0} (h : cMass qud pC u = q) :
    l1CEvent qud pC u = ((q : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_event_eq_ratCast _ _ _ h

private theorem l1CEvent_lt (q₁ q₂ : QUD) (p₁ p₂ : ℚ≥0) (u₁ u₂ : Utterance)
    (h : cMass q₁ p₁ u₁ < cMass q₂ p₂ u₂) :
    l1CEvent q₁ p₁ u₁ < l1CEvent q₂ p₂ u₂ :=
  PMF.ofScores_event_lt_cross _ _ _ _ h

/-- Under the BEL? QUD the C-marginal equals the prior, for every utterance:
S1 depends on the world only through its BEL-cell, so the C-dimension washes
out of the world posterior. Projection is invisible at the world marginal. -/
theorem bel_qud_marginal_eq_prior_high (u : Utterance) :
    l1CEvent .bel (2/3) u = (((2/3 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  l1CEvent_eq _ _ _ ((by revert u; decide +kernel :
    ∀ u, cMass .bel (2/3) u = 2/3) u)

/-- The low-prior analogue of `bel_qud_marginal_eq_prior_high`. -/
theorem bel_qud_marginal_eq_prior_low (u : Utterance) :
    l1CEvent .bel (1/3) u = (((1/3 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  l1CEvent_eq _ _ _ ((by revert u; decide +kernel :
    ∀ u, cMass .bel (1/3) u = 1/3) u)

/-- Under the C? QUD, knowNeg is evidence against C — ¬(BEL∧C) is compatible
with C-false worlds — so thinkNeg preserves P(C) better. -/
theorem c_qud_thinkNeg_higher :
    l1CEvent .c (2/3) .knowNeg < l1CEvent .c (2/3) .thinkNeg :=
  l1CEvent_lt _ _ _ _ _ _ (by decide +kernel)

/-! ### Prediction 2a: utterance effect (know > think)

The paper derives 2a *with* utterance cost (Figure 7a); the cost-free model
does not — under BEL? both marginals sit at the prior, and under C? the
direction reverses (`c_qud_thinkNeg_higher`). Fn. 11's A-marginal measure
(P(A ⊧ C | u)) may capture the effect without cost; see the module TODO. -/

/-- Prediction 2b (prior effect): higher prior increases projection. -/
theorem prediction_2b : l1CEvent .c (1/3) .knowNeg < l1CEvent .c (2/3) .knowNeg :=
  l1CEvent_lt _ _ _ _ _ _ (by decide +kernel)

/-- Prediction 2c (QUD effect): under BEL? the C-marginal stays at the prior
(`bel_qud_marginal_eq_prior_high`), while under C? the literal semantics of
"doesn't know C" lowers it. -/
theorem prediction_2c : l1CEvent .c (2/3) .knowNeg < l1CEvent .bel (2/3) .knowNeg :=
  l1CEvent_lt _ _ _ _ _ _ (by decide +kernel)

/-! ### Structural properties -/

/-- "know" entails C (from `factivePos_entails_c`). -/
theorem know_entails_c : ∀ w, literalMeaning .knowPos w = true → w.c = true :=
  factivePos_entails_c

/-- "think" does NOT entail C. -/
theorem think_not_entails_c :
    ∃ w, literalMeaning .thinkPos w = true ∧ w.c = false :=
  ⟨.w10, rfl, rfl⟩

/-- "know" entails BEL (from `factivePos_entails_bel`). -/
theorem know_entails_bel : ∀ w, literalMeaning .knowPos w = true → w.bel = true :=
  factivePos_entails_bel

/-- Know entails think (factivity is strictly stronger than belief). -/
theorem know_entails_think : ∀ w,
    literalMeaning .knowPos w = true → literalMeaning .thinkPos w = true :=
  factive_entails_nonfactive

/-- knowNeg (= ¬(BEL∧C)) is true at all worlds except w11. -/
theorem knowNeg_semantics :
    literalMeaning .knowNeg .w11 = false ∧
    literalMeaning .knowNeg .w10 = true ∧
    literalMeaning .knowNeg .w01 = true ∧
    literalMeaning .knowNeg .w00 = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- thinkNeg (= ¬BEL) is true only at worlds where Cole doesn't believe. -/
theorem thinkNeg_semantics :
    literalMeaning .thinkNeg .w11 = false ∧
    literalMeaning .thinkNeg .w10 = false ∧
    literalMeaning .thinkNeg .w01 = true ∧
    literalMeaning .thinkNeg .w00 = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- knowNeg is compatible with strictly more worlds than thinkNeg (3 vs 2),
    making it the weaker (less informative) negation. -/
theorem knowNeg_weaker_than_thinkNeg :
    (Finset.univ.filter (fun w : WorldState => literalMeaning .knowNeg w)).card >
    (Finset.univ.filter (fun w : WorldState => literalMeaning .thinkNeg w)).card := by
  decide

/-- The pattern-matched `assumesC` agrees with the generic
    `assumesComplement` from `Factivity`. -/
theorem assumesC_matches_generic : ∀ bs : BeliefState,
    assumesC bs = assumesComplement (speakerCredenceBool bs)
      [.w11, .w10, .w01, .w00] := by
  intro bs; cases bs <;> decide

/-- Exactly 3 of 15 belief states assume C: onlyW11, onlyW01, cTrue. -/
theorem three_of_fifteen_assume_c :
    (Finset.univ.filter (fun bs : BeliefState => assumesC bs)).card = 3 := by
  decide

/-! ### Experimental data -/

/-- Effect size from a linear mixed-effects model. p values are upper bounds
    (paper reports "< .001"). -/
structure UtteranceEffect where
  β : ℚ
  se : ℚ
  t : ℚ
  p : ℚ
  deriving Repr

/-- Exp 1: Utterance effect (know > think). -/
def exp1_utteranceEffect : UtteranceEffect :=
  { β := 0.35, se := 0.03, t := 12.2, p := 0.001 }

/-- Exp 1: Prior effect (higher > lower). -/
def exp1_priorEffect : UtteranceEffect :=
  { β := 0.16, se := 0.03, t := 5.5, p := 0.001 }

/-- Exp 1: QUD effect (NOT significant — manipulation too weak). -/
def exp1_qudEffect : UtteranceEffect :=
  { β := 0.009, se := 0.03, t := 0.3, p := 0.75 }

/-- Exp 2: Utterance effect (know > think). -/
def exp2_utteranceEffect : UtteranceEffect :=
  { β := 0.34, se := 0.04, t := 8.8, p := 0.001 }

/-- Exp 2: QUD effect (significant with stronger manipulation). -/
def exp2_qudEffect : UtteranceEffect :=
  { β := 0.14, se := 0.04, t := 3.6, p := 0.001 }

inductive Hypothesis where
  | utterance  -- (2a) know > think
  | prior      -- (2b) higher > lower prior
  | qud        -- (2c) BEL? > C?
  deriving DecidableEq, Repr

/-- Which experiments support each hypothesis.
    Exp 1: (2a) yes, (2b) yes, (2c) no (QUD not significant).
    Exp 2: (2a) yes, (2b) not tested, (2c) yes. -/
def supported : Hypothesis → Bool × Bool
  | .utterance => (true, true)
  | .prior     => (true, false)
  | .qud       => (false, true)

def directionCorrect : Hypothesis → Bool
  | .utterance => exp1_utteranceEffect.β > 0
  | .prior     => exp1_priorEffect.β > 0
  | .qud       => exp2_qudEffect.β > 0

/-! ### BToM bridge -/

open Core in
/-- Classification of BeliefState in BToM terms. -/
def beliefStateCategory : LatentCategory := .mental

open Core in
/-- Classification of QUD in BToM terms. -/
def qudCategory : LatentCategory := .shared

/-- Characteristic function: does the speaker assume C? -/
def assumesCIndicator : BeliefState → ℚ :=
  fun bs => if assumesC bs then 1 else 0

/-- Belief states that assume C have indicator 1. -/
theorem assumesCIndicator_pos (bs : BeliefState) (h : assumesC bs = true) :
    assumesCIndicator bs = 1 := by
  simp [assumesCIndicator, h]

/-- Belief states that don't assume C have indicator 0. -/
theorem assumesCIndicator_neg (bs : BeliefState) (h : assumesC bs = false) :
    assumesCIndicator bs = 0 := by
  simp [assumesCIndicator, h]

/-- The three C-entailing belief states have indicator 1;
    the remaining twelve have indicator 0. -/
theorem assumesCIndicator_classification :
    assumesCIndicator .onlyW11 = 1 ∧
    assumesCIndicator .onlyW01 = 1 ∧
    assumesCIndicator .cTrue = 1 ∧
    assumesCIndicator .onlyW10 = 0 ∧
    assumesCIndicator .onlyW00 = 0 ∧
    assumesCIndicator .belTrue = 0 ∧
    assumesCIndicator .belFalse = 0 ∧
    assumesCIndicator .cFalse = 0 ∧
    assumesCIndicator .diagonal = 0 ∧
    assumesCIndicator .antiDiagonal = 0 ∧
    assumesCIndicator .notW11 = 0 ∧
    assumesCIndicator .notW10 = 0 ∧
    assumesCIndicator .notW01 = 0 ∧
    assumesCIndicator .notW00 = 0 ∧
    assumesCIndicator .all = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Model–data connection -/

/-- Predictions (2b) and (2c) match experimental effect directions.
    Prediction (2a) requires cost; see the commentary above. -/
theorem model_predicts_effects :
    (l1CEvent .c (2/3) .knowNeg > l1CEvent .c (1/3) .knowNeg) ∧
    (l1CEvent .bel (2/3) .knowNeg > l1CEvent .c (2/3) .knowNeg) ∧
    directionCorrect .prior = true ∧
    directionCorrect .qud = true :=
  ⟨prediction_2b, prediction_2c,
   by simp only [directionCorrect, exp1_priorEffect, decide_eq_true_eq]; norm_num,
   by simp only [directionCorrect, exp2_qudEffect, decide_eq_true_eq]; norm_num⟩

/-! ### Connection to [degen-tonhauser-2021] -/

/-- The prior effect found by S&T 2025 (β = 0.16 > 0) replicates the positive
    prior effect of [degen-tonhauser-2021] (β = 0.14 categorical, β = 0.28
    individual): higher prior probability of the complement content leads to
    stronger projection. [degen-tonhauser-2021] makes this structural — any
    prior-sensitive (monotone) account predicts the modulation
    (`DegenTonhauser2021.sensitive_predicts_modulation`) — and the RSA model's
    `prediction_2b` provides the same explanation here. -/
theorem prior_effect_consistent_with_dt2021 :
    exp1_priorEffect.β > 0 := by norm_num [exp1_priorEffect]

/-! ### Compositional filtering vs BToM -/

/-! Compares the BToM model against compositional filtering ([heim-1983]):
presuppositions project through connectives via local context computation;
the filtering presupposition of "if A then B_p" is "A → p".

The key empirical argument: the BToM model predicts that even non-factive
"think" — which has NO presupposition to filter — exhibits projection
effects, because L1 can still infer what the speaker takes for granted.
Compositional filtering predicts a trivial presupposition for
non-presuppositional items. -/

section FilteringComparison

open Semantics.Presupposition

variable {W : Type*}

/-- The filtering prediction for "if A then know-C":
    the presupposition of the consequent (= C) is filtered by the antecedent.
    Result: conditional presupposes "A → C". -/
def filteringPrediction_know (a c : W → Prop) : PartialProp W :=
  PartialProp.impFilter (PartialProp.ofProp a) (PartialProp.condAssert c (fun _ => True))

/-- The filtering prediction for "if A then think-C":
    "think" has no presupposition, so filtering produces a trivial result. -/
def filteringPrediction_think (a : W → Prop) : PartialProp W :=
  PartialProp.impFilter (PartialProp.ofProp a) PartialProp.top

/-- **Filtering predicts non-trivial presupposition for "know"**:
    The presupposition of "if A then know-C" is ¬A ∨ C (= A → C),
    which is NOT tautological. -/
theorem filtering_know_nontrivial (a c : W → Prop)
    (h : ∃ w, a w ∧ ¬c w) :
    ∃ w, ¬(filteringPrediction_know a c).presup w := by
  obtain ⟨w, ha, hc⟩ := h
  refine ⟨w, ?_⟩
  simp only [filteringPrediction_know, PartialProp.impFilter, PartialProp.ofProp,
    PartialProp.condAssert, not_and]
  intro _
  exact fun h_imp => hc (h_imp ha)

/-- **Filtering predicts TRIVIAL presupposition for "think"**:
    The presupposition of "if A then think-C" is always true,
    regardless of A, because "think" contributes no presupposition. -/
theorem filtering_think_trivial (a : W → Prop) :
    ∀ w, (filteringPrediction_think a).presup w := by
  intro w
  simp only [filteringPrediction_think, PartialProp.impFilter, PartialProp.ofProp, PartialProp.top]
  exact ⟨trivial, fun _ => trivial⟩

/--
BToM predicts projection effects for ANY verb in conditional environments,
because projection arises from pragmatic reasoning about the speaker's
private assumptions, not from lexical presupposition.

The key mechanism: when A and C are related (correlated in the prior),
the listener infers that a speaker who utters "if A, X Vs C" likely takes
C for granted — regardless of whether V is factive.
-/
structure ProjectionPrediction where
  /-- Whether projection is predicted for factive verbs in conditionals. -/
  factive_projects : Bool
  /-- Whether projection is predicted for non-factive verbs in conditionals. -/
  nonFactive_projects : Bool
  /-- Whether relatedness modulates projection strength. -/
  relatedness_modulates : Bool

/-- BToM predictions: both factive and non-factive show conditional
    presupposition, modulated by relatedness. -/
def btomPrediction : ProjectionPrediction where
  factive_projects := true
  nonFactive_projects := true
  relatedness_modulates := true

/-- Filtering predictions: only factive shows conditional presupposition,
    with no role for relatedness (it's purely structural). -/
def filteringPrediction : ProjectionPrediction where
  factive_projects := true
  nonFactive_projects := false    -- Think has no presupposition
  relatedness_modulates := false  -- Filtering is structural, not probabilistic

/--
**Strict subsumption**: BToM predicts everything filtering predicts
(factive conditional presupposition) plus more (non-factive conditional
presupposition, relatedness modulation).
-/
theorem btom_subsumes_filtering :
    -- BToM agrees with filtering on factive projection
    btomPrediction.factive_projects = filteringPrediction.factive_projects ∧
    -- BToM predicts non-factive projection where filtering doesn't
    btomPrediction.nonFactive_projects = true ∧
    filteringPrediction.nonFactive_projects = false ∧
    -- BToM predicts relatedness modulation where filtering doesn't
    btomPrediction.relatedness_modulates = true ∧
    filteringPrediction.relatedness_modulates = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
**The critical divergence**: For non-factive "think" in conditionals,
filtering predicts trivial presupposition (no projection), while BToM
predicts non-trivial projection modulated by relatedness.

This is the [scontras-tonhauser-2025] argument: if projection were
due to compositional filtering alone, non-presuppositional items like
"think" should show no effect. But BToM predicts projection effects
even for "think", because L1 infers the speaker's private assumptions
regardless of the verb's factivity status.
-/
theorem critical_divergence_at_nonfactive :
    filteringPrediction.nonFactive_projects ≠ btomPrediction.nonFactive_projects := by
  decide

/--
**Filtering is a special case**: When relatedness is maximal (A entails C),
BToM's projection prediction converges to the filtering prediction.
Filtering captures the structural component; BToM adds the probabilistic
modulation.
-/
theorem filtering_is_limiting_case (a c : W → Prop)
    (h_entails : ∀ w, a w → c w) :
    ∀ w, (filteringPrediction_know a c).presup w := by
  intro w
  exact ⟨trivial, fun ha => h_entails w ha⟩

end FilteringComparison

end ScontrasTonhauser2025
