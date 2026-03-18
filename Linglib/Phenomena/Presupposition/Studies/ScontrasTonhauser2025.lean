import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Core.Agent.BToM
import Linglib.Theories.Semantics.Attitudes.Factivity
import Linglib.Phenomena.Presupposition.Studies.DegenTonhauser2021
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{scontras-tonhauser-2025}

Projection emerges from RSA over speaker's private assumptions, not lexical
presupposition. L1 jointly infers world state and speaker's belief state.

## The Model (Section 3)

- **L0** (eq. 5): L0(Q(w)|u,A,Q) ∝ Σ_{w'∈A∩⟦u⟧, Q(w')=Q(w)} P(w')
- **S1** (eq. 6): S1(u|w,A,Q) ∝ exp(α(log L0(Q(w)|u,A,Q) − C(u)))
- **L1** (eq. 7): L1(w,A|u,Q) ∝ S1(u|w,A,Q) · P(w) · P(A)

Domain: 6 utterances × 4 worlds × 15 belief states × 2 QUDs. α = 10.

## Section 3 Parameters (fn. 12)

- **Belief states A**: all 15 non-empty subsets of W
  (following @cite{qing-goodman-lassiter-2016})
- **Prior over A**: uniform
- **α = 10**
- **P(C)**: 2/3 (higher) or 1/3 (lower); P(BEL|C) = 1/2

Cost (complex = 2×simple) is omitted: exp(−αC) with α = 10 introduces
irrational numbers incompatible with ℚ arithmetic. Cost omission affects
S1's normalization even for same-cost comparisons, reversing the direction of
prediction (2a); the full model with cost predicts know > think (Figure 7a).
Predictions (2b) and (2c) are robust to cost omission.

## Factive Semantics

Literal truth conditions derive from `Semantics.Attitudes.Factivity`:
know = `factivePos` (BEL ∧ C), think = `nonFactivePos` (BEL).

## Key Structural Insight

Under QUD=BEL?, L1's world-marginal P(C|u) = P(C) for all utterances — a
mathematical identity. S1 scores depend on w only through w.bel, so the
complement dimension washes out in the marginal. Prediction 2b (prior
effect) therefore comes from the C? QUD condition; prediction 2c (QUD
effect) compares the uninformative BEL? marginal against the C? marginal.

## BToM Connection

This is a BToM model: L1 inverts S1's generative model to jointly infer
the speaker's belief state and the world state.

## Experimental Results

Exp 1 confirms (2a) utterance effect (β = 0.35, p < .001) and (2b) prior
effect (β = 0.16, p < .001). The QUD manipulation was not significant
(β = 0.009, p = .75). Exp 2 confirms (2a) utterance effect (β = 0.34,
p < .001) and (2c) QUD effect (β = 0.14, p < .001) with a stronger QUD
manipulation. Exp 2 did not manipulate prior probability.

## Connection to @cite{degen-tonhauser-2021}

The prior effect (prediction 2b) replicates the core finding of
@cite{degen-tonhauser-2021}: higher prior probability of complement content
leads to stronger projection. D&T 2021 demonstrate this across 20 predicates
with β = 0.14 (categorical) / β = 0.28 (individual-level). S&T 2025's RSA
model provides the theoretical explanation: L1's Bayesian inference naturally
incorporates prior beliefs, so higher priors yield higher posteriors.
-/

set_option autoImplicit false

namespace Phenomena.Presupposition.Studies.ScontrasTonhauser2025

open BigOperators
open Real (rpow rpow_nonneg rpow_pos_of_pos)
open Semantics.Attitudes.Factivity

-- ============================================================================
-- §1. World and Utterance Types
-- ============================================================================

/-- World state: (BEL, C) where BEL = Cole believes C, C = complement is true.
    Flat inductive for tactic enumerability. -/
inductive WorldState where
  | w11  -- (BEL=1, C=1): Cole believes C and C is true
  | w10  -- (BEL=1, C=0): Cole believes C but C is false
  | w01  -- (BEL=0, C=1): Cole doesn't believe but C is true
  | w00  -- (BEL=0, C=0): Cole doesn't believe and C is false
  deriving DecidableEq, Repr, BEq, Inhabited, Fintype

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
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Fintype Utterance where
  elems := {.knowPos, .knowNeg, .thinkPos, .thinkNeg, .cPos, .cNeg}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Literal Truth Conditions (derived from Factivity)
-- ============================================================================

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

-- ============================================================================
-- §3. Speaker Belief States — all 15 non-empty subsets of W
-- ============================================================================

/-- Speaker's private assumptions: all 15 non-empty subsets of W.
    Section 3 follows @cite{qing-goodman-lassiter-2016}: A ranges over all
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
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Fintype BeliefState where
  elems := {.onlyW11, .onlyW10, .onlyW01, .onlyW00,
            .belTrue, .belFalse, .cTrue, .cFalse,
            .diagonal, .antiDiagonal,
            .notW11, .notW10, .notW01, .notW00,
            .all}
  complete := fun x => by cases x <;> simp

/-- Membership in belief state. Boolean operations on `WorldState` fields
    reduce cleanly for `rsa_predict`. -/
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

-- ============================================================================
-- §4. QUD Aggregation
-- ============================================================================

/-- QUD aggregation: sums L0 probabilities over the QUD equivalence class of w.
    Named `qudAggregate` to distinguish from `Factivity.qudProject`
    (the equivalence relation, not the aggregation).
    - BEL? QUD: partitions by BEL → sums over same-BEL worlds
    - C? QUD: partitions by C → sums over same-C worlds -/
def qudAggregate (qud : QUD) (f : WorldState → ℝ) (w : WorldState) : ℝ :=
  match qud, w with
  | .bel, .w11 => f .w11 + f .w10
  | .bel, .w10 => f .w11 + f .w10
  | .bel, .w01 => f .w01 + f .w00
  | .bel, .w00 => f .w01 + f .w00
  | .c,   .w11 => f .w11 + f .w01
  | .c,   .w01 => f .w11 + f .w01
  | .c,   .w10 => f .w10 + f .w00
  | .c,   .w00 => f .w10 + f .w00

theorem qudAggregate_nonneg {qud : QUD} {f : WorldState → ℝ} {w : WorldState}
    (hf : ∀ w, 0 ≤ f w) : 0 ≤ qudAggregate qud f w := by
  cases qud <;> cases w <;> simp only [qudAggregate] <;> exact add_nonneg (hf _) (hf _)

-- ============================================================================
-- §5. Priors
-- ============================================================================

/-- World prior parameterized by P(C).
    P(BEL, C) = P(BEL | C) · P(C), with P(BEL | C) = 1/2. -/
def worldPriorQ (pC : ℚ) : WorldState → ℚ
  | .w11 | .w01 => pC / 2
  | .w10 | .w00 => (1 - pC) / 2

theorem worldPriorQ_nonneg (pC : ℚ) (h0 : 0 ≤ pC) (h1 : pC ≤ 1)
    (w : WorldState) : 0 ≤ worldPriorQ pC w := by
  cases w <;> simp [worldPriorQ] <;> linarith

/-- World prior sums to 1 for any P(C). -/
theorem worldPriorQ_sum (pC : ℚ) :
    worldPriorQ pC .w11 + worldPriorQ pC .w10 +
    worldPriorQ pC .w01 + worldPriorQ pC .w00 = 1 := by
  simp [worldPriorQ]; ring

-- ============================================================================
-- §6. RSAConfig
-- ============================================================================

/-- RSA model for Section 3: uniform prior over all 15 belief states,
    QUD-projected rpow scoring, α = 10. -/
noncomputable def cfg (qud : QUD) (pC : ℚ) (hpC : 0 ≤ pC) (hpC1 : pC ≤ 1) :
    RSA.RSAConfig Utterance WorldState where
  Latent := BeliefState
  meaning _ bs u w :=
    if speakerCredenceBool bs w && literalMeaning u w then
      (worldPriorQ pC w : ℝ)
    else 0
  meaning_nonneg _ _ _ w := by
    split
    · exact Rat.cast_nonneg.mpr (worldPriorQ_nonneg pC hpC hpC1 w)
    · exact le_refl 0
  s1Score l0 α _bs w u := rpow (qudAggregate qud (l0 u) w) α
  s1Score_nonneg _ _ _ _ u hl _ :=
    rpow_nonneg (qudAggregate_nonneg (fun w => hl u w)) _
  α := 10
  α_pos := by positivity
  worldPrior w := (worldPriorQ pC w : ℝ)
  worldPrior_nonneg w := Rat.cast_nonneg.mpr (worldPriorQ_nonneg pC hpC hpC1 w)
  latentPrior _w _bs := 1
  latentPrior_nonneg _w _bs := one_pos.le

/-- QUD=BEL?, P(C)=2/3. -/
noncomputable abbrev cfgBelHigh := cfg .bel (2/3) (by norm_num) (by norm_num)

/-- QUD=BEL?, P(C)=1/3. -/
noncomputable abbrev cfgBelLow := cfg .bel (1/3) (by norm_num) (by norm_num)

/-- QUD=C?, P(C)=2/3. -/
noncomputable abbrev cfgCHigh := cfg .c (2/3) (by norm_num) (by norm_num)

/-- QUD=C?, P(C)=1/3. -/
noncomputable abbrev cfgCLow := cfg .c (1/3) (by norm_num) (by norm_num)

-- ============================================================================
-- §7. L1 Predictions
-- ============================================================================

-- ---------- helpers for BEL? QUD identity ----------

private theorem worldState_univ :
    (Finset.univ : Finset WorldState) = {.w11, .w10, .w01, .w00} := by
  ext x; cases x <;> simp

private theorem c_filter :
    Finset.univ.filter (fun w : WorldState => w.c = true) = {.w11, .w01} := by
  native_decide

private theorem meaning_pos_high (u : Utterance) :
    ∃ w₀, 0 < cfgBelHigh.meaning cfgBelHigh.initial .all u w₀ := by
  cases u
  · exact ⟨.w11, by simp only [cfg, speakerCredenceBool, literalMeaning, factivePos,
      HasBelief.bel, WorldState.bel, HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w10, by simp only [cfg, speakerCredenceBool, literalMeaning, factiveNeg,
      HasBelief.bel, WorldState.bel, HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w11, by simp only [cfg, speakerCredenceBool, literalMeaning, nonFactivePos,
      HasBelief.bel, WorldState.bel, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w01, by simp only [cfg, speakerCredenceBool, literalMeaning, nonFactiveNeg,
      HasBelief.bel, WorldState.bel, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w11, by simp only [cfg, speakerCredenceBool, literalMeaning,
      HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w10, by simp only [cfg, speakerCredenceBool, literalMeaning,
      HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩

set_option maxHeartbeats 1600000 in
private theorem high_totalScore_pos (u : Utterance) :
    0 < cfgBelHigh.L1agent.totalScore u := by
  obtain ⟨w₀, hm⟩ := meaning_pos_high u
  have hL0t := lt_of_lt_of_le hm (Finset.single_le_sum
    (fun w' _ => cfgBelHigh.meaning_nonneg cfgBelHigh.initial .all u w') (Finset.mem_univ w₀))
  have hL0t' : 0 < (cfgBelHigh.L0agent .all).totalScore u := hL0t
  have hL0p : 0 < (cfgBelHigh.L0agent .all).policy u w₀ := by
    unfold Core.RationalAction.policy; rw [if_neg (ne_of_gt hL0t')]; exact div_pos hm hL0t'
  have hqud : 0 < qudAggregate .bel ((cfgBelHigh.L0agent .all).policy u) w₀ := by
    cases w₀ <;> simp only [qudAggregate] <;>
      linarith [(cfgBelHigh.L0agent .all).policy_nonneg u .w11,
                (cfgBelHigh.L0agent .all).policy_nonneg u .w10,
                (cfgBelHigh.L0agent .all).policy_nonneg u .w01,
                (cfgBelHigh.L0agent .all).policy_nonneg u .w00]
  have hS1s : 0 < (cfgBelHigh.S1agent .all).score w₀ u := by
    simp only [RSA.RSAConfig.S1agent, RSA.RSAConfig.L0agent, cfgBelHigh, cfg]
    exact rpow_pos_of_pos hqud _
  have hS1t := lt_of_lt_of_le hS1s (Finset.single_le_sum
    (fun u' _ => (cfgBelHigh.S1agent .all).score_nonneg w₀ u') (Finset.mem_univ u))
  have hS1t' : 0 < (cfgBelHigh.S1agent .all).totalScore w₀ := hS1t
  have hS1p : 0 < cfgBelHigh.S1 .all w₀ u := by
    unfold RSA.RSAConfig.S1 Core.RationalAction.policy; rw [if_neg (ne_of_gt hS1t')]
    exact div_pos hS1s hS1t'
  have hwp : (0 : ℝ) < cfgBelHigh.worldPrior w₀ := by
    cases w₀ <;> simp only [cfgBelHigh, cfg, worldPriorQ] <;> push_cast <;> norm_num
  have hls : 0 < ∑ l : BeliefState, cfgBelHigh.latentPrior w₀ l * cfgBelHigh.S1 l w₀ u :=
    calc 0 < cfgBelHigh.latentPrior w₀ (BeliefState.all) * cfgBelHigh.S1 .all w₀ u := by
              rw [show cfgBelHigh.latentPrior w₀ .all = 1 from rfl, one_mul]; exact hS1p
      _ ≤ ∑ l : BeliefState, cfgBelHigh.latentPrior w₀ l * cfgBelHigh.S1 l w₀ u :=
            Finset.single_le_sum
              (fun l _ => mul_nonneg (cfgBelHigh.latentPrior_nonneg w₀ l) (cfgBelHigh.S1_nonneg l w₀ u))
              (Finset.mem_univ (BeliefState.all))
  exact lt_of_lt_of_le (show 0 < cfgBelHigh.L1agent.score u w₀ by
      simp only [RSA.RSAConfig.L1agent]; exact mul_pos hwp hls)
    (Finset.single_le_sum (fun w' _ => cfgBelHigh.L1agent.score_nonneg u w') (Finset.mem_univ w₀))

set_option maxHeartbeats 800000 in
private theorem high_score_w10 (u : Utterance) :
    cfgBelHigh.L1agent.score u .w10 =
    (1/2 : ℝ) * cfgBelHigh.L1agent.score u .w11 := by
  simp only [RSA.RSAConfig.L1agent]
  simp_rw [show ∀ l, cfgBelHigh.S1 l .w10 u = cfgBelHigh.S1 l .w11 u from fun _ => rfl]
  simp_rw [show ∀ l, cfgBelHigh.latentPrior .w10 l = cfgBelHigh.latentPrior .w11 l from fun _ => rfl]
  simp only [cfgBelHigh, cfg, worldPriorQ]; push_cast; ring

set_option maxHeartbeats 800000 in
private theorem high_score_w00 (u : Utterance) :
    cfgBelHigh.L1agent.score u .w00 =
    (1/2 : ℝ) * cfgBelHigh.L1agent.score u .w01 := by
  simp only [RSA.RSAConfig.L1agent]
  simp_rw [show ∀ l, cfgBelHigh.S1 l .w00 u = cfgBelHigh.S1 l .w01 u from fun _ => rfl]
  simp_rw [show ∀ l, cfgBelHigh.latentPrior .w00 l = cfgBelHigh.latentPrior .w01 l from fun _ => rfl]
  simp only [cfgBelHigh, cfg, worldPriorQ]; push_cast; ring

private theorem high_totalScore_expand (u : Utterance) :
    cfgBelHigh.L1agent.totalScore u =
    cfgBelHigh.L1agent.score u .w11 + cfgBelHigh.L1agent.score u .w10 +
    cfgBelHigh.L1agent.score u .w01 + cfgBelHigh.L1agent.score u .w00 := by
  unfold Core.RationalAction.totalScore; rw [worldState_univ]
  simp only [Finset.sum_insert (show WorldState.w11 ∉ ({.w10, .w01, .w00} : Finset WorldState) by decide),
             Finset.sum_insert (show WorldState.w10 ∉ ({.w01, .w00} : Finset WorldState) by decide),
             Finset.sum_insert (show WorldState.w01 ∉ ({.w00} : Finset WorldState) by decide),
             Finset.sum_singleton]; ring

set_option maxHeartbeats 1600000 in
/-- Under BEL? QUD, L1's world-marginal for C equals the prior P(C) for every
    utterance. S1 scores depend on w only through w.bel, so the complement
    dimension washes out in the marginal:

    L1_marginal(C|u, BEL?) = Σ_{w:C(w)} P(w)·f(u,w.bel) / Σ_w P(w)·f(u,w.bel)
                            = (pC/2)·(f₁+f₀) / ((1/2)·(f₁+f₀)) = pC. -/
theorem bel_qud_marginal_eq_prior_high (u : Utterance) :
    cfgBelHigh.L1_marginal u (·.c) = 2/3 := by
  have h := ne_of_gt (high_totalScore_pos u)
  unfold RSA.RSAConfig.L1_marginal RSA.RSAConfig.L1
  simp only [Core.RationalAction.policy, h, ↓reduceIte]
  rw [← Finset.sum_div, c_filter, Finset.sum_pair (by decide : WorldState.w11 ≠ WorldState.w01)]
  rw [high_totalScore_expand, high_score_w10, high_score_w00]
  rw [high_totalScore_expand, high_score_w10, high_score_w00] at h
  rw [div_eq_iff h]; ring

-- ---------- low-prior analogues ----------

private theorem meaning_pos_low (u : Utterance) :
    ∃ w₀, 0 < cfgBelLow.meaning cfgBelLow.initial .all u w₀ := by
  cases u
  · exact ⟨.w11, by simp only [cfg, speakerCredenceBool, literalMeaning, factivePos,
      HasBelief.bel, WorldState.bel, HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w10, by simp only [cfg, speakerCredenceBool, literalMeaning, factiveNeg,
      HasBelief.bel, WorldState.bel, HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w11, by simp only [cfg, speakerCredenceBool, literalMeaning, nonFactivePos,
      HasBelief.bel, WorldState.bel, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w01, by simp only [cfg, speakerCredenceBool, literalMeaning, nonFactiveNeg,
      HasBelief.bel, WorldState.bel, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w11, by simp only [cfg, speakerCredenceBool, literalMeaning,
      HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩
  · exact ⟨.w10, by simp only [cfg, speakerCredenceBool, literalMeaning,
      HasComplement.c, WorldState.c, worldPriorQ]; push_cast; norm_num⟩

set_option maxHeartbeats 1600000 in
private theorem low_totalScore_pos (u : Utterance) :
    0 < cfgBelLow.L1agent.totalScore u := by
  obtain ⟨w₀, hm⟩ := meaning_pos_low u
  have hL0t := lt_of_lt_of_le hm (Finset.single_le_sum
    (fun w' _ => cfgBelLow.meaning_nonneg cfgBelLow.initial .all u w') (Finset.mem_univ w₀))
  have hL0t' : 0 < (cfgBelLow.L0agent .all).totalScore u := hL0t
  have hL0p : 0 < (cfgBelLow.L0agent .all).policy u w₀ := by
    unfold Core.RationalAction.policy; rw [if_neg (ne_of_gt hL0t')]; exact div_pos hm hL0t'
  have hqud : 0 < qudAggregate .bel ((cfgBelLow.L0agent .all).policy u) w₀ := by
    cases w₀ <;> simp only [qudAggregate] <;>
      linarith [(cfgBelLow.L0agent .all).policy_nonneg u .w11,
                (cfgBelLow.L0agent .all).policy_nonneg u .w10,
                (cfgBelLow.L0agent .all).policy_nonneg u .w01,
                (cfgBelLow.L0agent .all).policy_nonneg u .w00]
  have hS1s : 0 < (cfgBelLow.S1agent .all).score w₀ u := by
    simp only [RSA.RSAConfig.S1agent, RSA.RSAConfig.L0agent, cfgBelLow, cfg]
    exact rpow_pos_of_pos hqud _
  have hS1t := lt_of_lt_of_le hS1s (Finset.single_le_sum
    (fun u' _ => (cfgBelLow.S1agent .all).score_nonneg w₀ u') (Finset.mem_univ u))
  have hS1t' : 0 < (cfgBelLow.S1agent .all).totalScore w₀ := hS1t
  have hS1p : 0 < cfgBelLow.S1 .all w₀ u := by
    unfold RSA.RSAConfig.S1 Core.RationalAction.policy; rw [if_neg (ne_of_gt hS1t')]
    exact div_pos hS1s hS1t'
  have hwp : (0 : ℝ) < cfgBelLow.worldPrior w₀ := by
    cases w₀ <;> simp only [cfgBelLow, cfg, worldPriorQ] <;> push_cast <;> norm_num
  have hls : 0 < ∑ l : BeliefState, cfgBelLow.latentPrior w₀ l * cfgBelLow.S1 l w₀ u :=
    calc 0 < cfgBelLow.latentPrior w₀ (BeliefState.all) * cfgBelLow.S1 .all w₀ u := by
              rw [show cfgBelLow.latentPrior w₀ .all = 1 from rfl, one_mul]; exact hS1p
      _ ≤ ∑ l : BeliefState, cfgBelLow.latentPrior w₀ l * cfgBelLow.S1 l w₀ u :=
            Finset.single_le_sum
              (fun l _ => mul_nonneg (cfgBelLow.latentPrior_nonneg w₀ l) (cfgBelLow.S1_nonneg l w₀ u))
              (Finset.mem_univ (BeliefState.all))
  exact lt_of_lt_of_le (show 0 < cfgBelLow.L1agent.score u w₀ by
      simp only [RSA.RSAConfig.L1agent]; exact mul_pos hwp hls)
    (Finset.single_le_sum (fun w' _ => cfgBelLow.L1agent.score_nonneg u w') (Finset.mem_univ w₀))

set_option maxHeartbeats 800000 in
private theorem low_score_w10 (u : Utterance) :
    cfgBelLow.L1agent.score u .w10 =
    (2 : ℝ) * cfgBelLow.L1agent.score u .w11 := by
  simp only [RSA.RSAConfig.L1agent]
  simp_rw [show ∀ l, cfgBelLow.S1 l .w10 u = cfgBelLow.S1 l .w11 u from fun _ => rfl]
  simp_rw [show ∀ l, cfgBelLow.latentPrior .w10 l = cfgBelLow.latentPrior .w11 l from fun _ => rfl]
  simp only [cfgBelLow, cfg, worldPriorQ]; push_cast; ring

set_option maxHeartbeats 800000 in
private theorem low_score_w00 (u : Utterance) :
    cfgBelLow.L1agent.score u .w00 =
    (2 : ℝ) * cfgBelLow.L1agent.score u .w01 := by
  simp only [RSA.RSAConfig.L1agent]
  simp_rw [show ∀ l, cfgBelLow.S1 l .w00 u = cfgBelLow.S1 l .w01 u from fun _ => rfl]
  simp_rw [show ∀ l, cfgBelLow.latentPrior .w00 l = cfgBelLow.latentPrior .w01 l from fun _ => rfl]
  simp only [cfgBelLow, cfg, worldPriorQ]; push_cast; ring

private theorem low_totalScore_expand (u : Utterance) :
    cfgBelLow.L1agent.totalScore u =
    cfgBelLow.L1agent.score u .w11 + cfgBelLow.L1agent.score u .w10 +
    cfgBelLow.L1agent.score u .w01 + cfgBelLow.L1agent.score u .w00 := by
  unfold Core.RationalAction.totalScore; rw [worldState_univ]
  simp only [Finset.sum_insert (show WorldState.w11 ∉ ({.w10, .w01, .w00} : Finset WorldState) by decide),
             Finset.sum_insert (show WorldState.w10 ∉ ({.w01, .w00} : Finset WorldState) by decide),
             Finset.sum_insert (show WorldState.w01 ∉ ({.w00} : Finset WorldState) by decide),
             Finset.sum_singleton]; ring

set_option maxHeartbeats 1600000 in
/-- Same identity for the low-prior configuration: P(C|u, BEL?) = P(C) = 1/3. -/
theorem bel_qud_marginal_eq_prior_low (u : Utterance) :
    cfgBelLow.L1_marginal u (·.c) = 1/3 := by
  have h := ne_of_gt (low_totalScore_pos u)
  unfold RSA.RSAConfig.L1_marginal RSA.RSAConfig.L1
  simp only [Core.RationalAction.policy, h, ↓reduceIte]
  rw [← Finset.sum_div, c_filter, Finset.sum_pair (by decide : WorldState.w11 ≠ WorldState.w01)]
  rw [low_totalScore_expand, low_score_w10, low_score_w00]
  rw [low_totalScore_expand, low_score_w10, low_score_w00] at h
  rw [div_eq_iff h]; ring

set_option maxHeartbeats 1600000 in
/-- Under C? QUD, knowNeg is evidence AGAINST C: ¬(BEL∧C) is literally
    compatible with C-false worlds, so an informative speaker uses knowNeg
    more often when C is false. Thus thinkNeg preserves P(C) better. -/
theorem c_qud_thinkNeg_higher :
    cfgCHigh.L1_marginal .thinkNeg (·.c) >
    cfgCHigh.L1_marginal .knowNeg (·.c) := by
  rsa_predict

/-! ### Prediction 2a: Utterance Effect (know > think)

The paper predicts stronger projection for factive know than non-factive
think (Figure 7a). The full Section 3 model — including utterance cost
(complex = 2×simple) — produces this direction via the world-marginal.
Our cost-free model does not:
- **BEL? QUD**: both utterances yield P(C|u) = P(C) (the identity above)
- **C? QUD**: the direction is reversed (`c_qud_thinkNeg_higher`)

The reversal is due to cost omission, which changes S1's normalization.
With cost, simple utterances (cPos, cNeg) dominate S1's softmax via
exp(−α·C_simple) ≫ exp(−α·C_complex), altering which (world, belief state)
combinations favor knowNeg vs thinkNeg in L1's posterior.

The paper also notes (fn. 11) that projection can be measured via the
A-marginal P(A ⊧ C | u) — the probability that the speaker's inferred
belief state entails C. This measure may capture the utterance effect
even without cost, since the mechanism works through belief state inference
rather than world-marginal. -/

set_option maxHeartbeats 3200000 in
/-- Prediction 2b (prior effect): higher prior increases projection.
    Under C? QUD, L1 assigns higher probability to C with P(C) = 2/3
    than with P(C) = 1/3. -/
theorem prediction_2b :
    cfgCHigh.L1_marginal .knowNeg (·.c) >
    cfgCLow.L1_marginal .knowNeg (·.c) := by
  rsa_predict

set_option maxHeartbeats 3200000 in
/-- Prediction 2c (QUD effect): BEL? QUD increases projection over C? QUD.
    Under BEL? QUD, C is not at-issue and L1_marginal(C) = P(C) = 2/3.
    Under C? QUD, the literal semantics of "doesn't know C" (= ¬(BEL∧C))
    lowers P(C) from the prior, so BEL? > C?. -/
theorem prediction_2c :
    cfgBelHigh.L1_marginal .knowNeg (·.c) >
    cfgCHigh.L1_marginal .knowNeg (·.c) := by
  rsa_predict

-- ============================================================================
-- §8. Structural Properties
-- ============================================================================

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
  native_decide

/-- The pattern-matched `assumesC` agrees with the generic
    `assumesComplement` from `Factivity`. -/
theorem assumesC_matches_generic : ∀ bs : BeliefState,
    assumesC bs = assumesComplement (speakerCredenceBool bs)
      [.w11, .w10, .w01, .w00] := by
  intro bs; cases bs <;> native_decide

/-- Exactly 3 of 15 belief states assume C: onlyW11, onlyW01, cTrue. -/
theorem three_of_fifteen_assume_c :
    (Finset.univ.filter (fun bs : BeliefState => assumesC bs)).card = 3 := by
  native_decide

-- ============================================================================
-- §9. Experimental Data
-- ============================================================================

/-- Effect size from a linear mixed-effects model. p values are upper bounds
    (paper reports "< .001"). -/
structure UtteranceEffect where
  β : Float
  se : Float
  t : Float
  p : Float
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

-- ============================================================================
-- §10. BToM Bridge
-- ============================================================================

open Core.BToM in
/-- Classification of BeliefState in BToM terms. -/
def beliefStateCategory : LatentCategory := .mental

open Core.BToM in
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

-- ============================================================================
-- §11. Model–Data Connection
-- ============================================================================

/-- Predictions (2b) and (2c) match experimental effect directions.
    Prediction (2a) requires cost; see the commentary above. -/
theorem model_predicts_effects :
    (cfgCHigh.L1_marginal .knowNeg (·.c) >
     cfgCLow.L1_marginal .knowNeg (·.c)) ∧
    (cfgBelHigh.L1_marginal .knowNeg (·.c) >
     cfgCHigh.L1_marginal .knowNeg (·.c)) ∧
    directionCorrect .prior = true ∧
    directionCorrect .qud = true :=
  ⟨prediction_2b, prediction_2c,
   by native_decide, by native_decide⟩

-- ============================================================================
-- §12. Connection to @cite{degen-tonhauser-2021}
-- ============================================================================

/-- The prior effect found by S&T 2025 (β = 0.16) replicates the prior effect
    found by @cite{degen-tonhauser-2021} (β = 0.14 categorical, β = 0.28
    individual). Both find that higher prior probability of the complement
    content leads to stronger projection. The RSA model's `prediction_2b`
    provides the theoretical explanation for this empirical finding. -/
theorem prior_effect_consistent_with_dt2021 :
    exp1_priorEffect.β > 0 ∧
    (DegenTonhauser2021.exp1_priorEffect .categorical).β > 0 ∧
    (DegenTonhauser2021.exp1_priorEffect .individualLevel).β > 0 :=
  ⟨by native_decide, by native_decide, by native_decide⟩

end Phenomena.Presupposition.Studies.ScontrasTonhauser2025
