import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Core.CausalBayesNet
import Linglib.Theories.Semantics.Conditionals.Assertability
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{grusdt-lassiter-franke-2022}

"Probabilistic modeling of rational communication with conditionals"
PLoS ONE 17(7): e0269937.

## Overview

This paper extends RSA to model conditionals by:
1. Treating "worlds" as probability distributions (WorldState)
2. Using assertability (P(C|A) ≥ θ) as the literal meaning of conditionals
3. Having L1 infer both the world state AND the causal structure

The key insight is that the literal meaning of "if A then C" is an
assertability condition — P(C|A) ≥ θ — rather than material implication.
This grounds RSA's meaning function in conditional probability.

## Toy Example (§2.3, Table 2)

The paper's illustrative example uses 3 states and 4 utterances with θ = 0.9:

| | P(A) | P(C) | P(A,C) | P(C\|A) | likely C | if A, C | C | A and C |
|---|---|---|---|---|---|---|---|---|
| s1 | 0.9 | 0.9 | 0.81 | 0.9 | ✓ | ✓ | ✓ | — |
| s2 | 0.65 | 0.65 | 0.6 | 12/13 | ✓ | ✓ | — | — |
| s3 | 0.6 | 0.6 | 0.36 | 0.6 | ✓ | — | — | — |

Key predictions:
- S1 in s1 prefers "C" (most informative true utterance)
- S1 in s2 prefers "if A then C" (only true non-trivial utterance)
- S1 in s3 prefers "likely C" (only true utterance)
- L1 hearing "if A then C" infers s2 > s1 (dependency inference)
- L1 hearing "C" identifies s1 (high marginal probability)

## Full Model (§3)

The full model uses 10,000 sampled world states and three causal relations
(A→C, C→A, A⊥C) as latent variables. We formalize only the toy example
here, which captures all qualitative predictions with finite types amenable
to `rsa_predict`.

## Grounding

The assertability truth values are grounded in the probabilistic assertability
condition from `Semantics.Conditionals.Assertability`: a conditional
"if A then C" is assertable when P(A) > 0 and P(C|A) ≥ θ.

## Experiments

1. **Experiment 1: Dependency Inference** — Participants hear "if A then C"
   and judge causal structure. 72% infer A→C, 15% C→A, 10% A⊥C.

2. **Experiment 2: Conditional Perfection** — 85% endorse "if ¬A then ¬C"
   in A→C contexts vs 45% in independent contexts.

3. **Experiment 3: Assertability Thresholds** — θ ≈ 0.88 from model fitting.
-/

set_option autoImplicit false

namespace GrusdtLassiterFranke2022

open Core (Situation)

open Core.CausalBayesNet
open Semantics.Conditionals.Assertability


-- ============================================================================
-- Section 1: Types
-- ============================================================================

/-- Utterances from the toy example (Table 2, §2.3).

The paper uses a richer utterance space in the full model, but the toy
example uses four utterances ordered by informativity:
- "likely C": assertable when P(C) ≥ 0.5 (weakest, true in all toy states)
- "if A then C": assertable when P(C|A) ≥ 0.9
- "C": assertable when P(C) ≥ 0.9
- "A and C": assertable when P(A∧C) ≥ 0.9

"A and C" is false in all three toy states, making it a vacuous alternative
that nonetheless affects the pragmatic competition. -/
inductive Utt
  | likelyC
  | conditional
  | C
  | conjAC
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty Utt := ⟨.likelyC⟩

/-- World states from the toy example (Table 2, §2.3).

Each state is a probability distribution (pA, pC, pAC) representing a
different degree of dependence between A and C:
- **s1**: High marginals, P(C|A) = 0.9 = θ (borderline assertable)
- **s2**: Moderate marginals, P(C|A) = 12/13 ≈ 0.923 > θ (clearly assertable)
- **s3**: Moderate marginals, P(C|A) = 0.6 < θ (not assertable) -/
inductive State
  | s1
  | s2
  | s3
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty State := ⟨.s1⟩


-- ============================================================================
-- Section 2: WorldState Grounding
-- ============================================================================

/-- WorldState for s1: P(A)=0.9, P(C)=0.9, P(A∧C)=0.81.
    P(C|A) = 0.81/0.9 = 0.9 = θ. -/
def ws1 : WorldState := { pA := 9/10, pC := 9/10, pAC := 81/100 }

/-- WorldState for s2: P(A)=0.65, P(C)=0.65, P(A∧C)=0.6.
    P(C|A) = 0.6/0.65 = 12/13 ≈ 0.923 > θ. -/
def ws2 : WorldState := { pA := 13/20, pC := 13/20, pAC := 3/5 }

/-- WorldState for s3: P(A)=0.6, P(C)=0.6, P(A∧C)=0.36.
    P(C|A) = 0.36/0.6 = 0.6 < θ. -/
def ws3 : WorldState := { pA := 3/5, pC := 3/5, pAC := 9/25 }

/-- Map states to their WorldState representations. -/
def stateToWorldState : State → WorldState
  | .s1 => ws1
  | .s2 => ws2
  | .s3 => ws3


-- ============================================================================
-- Section 3: Assertability Semantics
-- ============================================================================

/-- Assertability threshold θ = 0.9 from the paper. -/
def θ : ℚ := 9/10

/-- Assertability truth table for the toy example (Table 2).

Defines when each utterance is assertable in each state. The paper uses
P(C|A) **≥** θ (non-strict), while `Assertability.assertable` uses **>** θ.
For the toy example, s1 has P(C|A) = 0.9 = θ exactly, so assertability
under ≥ is true but under > is false. We define the truth table directly
to match the paper's non-strict threshold.

Truth values from Table 2:
- **likely C** (P(C) ≥ 0.5): s1 ✓, s2 ✓, s3 ✓
  (all states have P(C) ≥ 0.6 > 0.5)
- **if A then C** (P(C|A) ≥ 0.9): s1 ✓, s2 ✓, s3 ✗
- **C** (P(C) ≥ 0.9): s1 ✓, s2 ✗, s3 ✗
- **A and C** (P(A∧C) ≥ 0.9): s1 ✗, s2 ✗, s3 ✗ -/
def assertable' : Utt → State → Bool
  | .likelyC,      _   => true
  | .conditional,  .s1 => true
  | .conditional,  .s2 => true
  | .conditional,  .s3 => false
  | .C,            .s1 => true
  | .C,            .s2 => false
  | .C,            .s3 => false
  | .conjAC,       _   => false


-- ============================================================================
-- Section 4: WorldState Grounding Theorems
-- ============================================================================

/-! Verify that the assertability truth values are grounded in the actual
conditional/marginal probabilities of the WorldStates. These connect the
directly-defined truth table to the assertability theory. -/

/-- s1 has P(C|A) = 9/10 ≥ θ. -/
theorem ws1_conditional_prob : ws1.pCGivenA = 9/10 := by native_decide

/-- s2 has P(C|A) = 12/13 > θ. -/
theorem ws2_conditional_prob : ws2.pCGivenA = 12/13 := by native_decide

/-- s3 has P(C|A) = 3/5 < θ. -/
theorem ws3_conditional_prob : ws3.pCGivenA = 3/5 := by native_decide

/-- s1 has P(C) = 9/10 ≥ 0.9 (so "C" is assertable). -/
theorem ws1_marginal_C : ws1.pC = 9/10 := by rfl

/-- s2 has P(C) = 13/20 ≥ 0.5 (so "likely C" is assertable). -/
theorem ws2_marginal_C : ws2.pC = 13/20 := by rfl

/-- s3 has P(C) = 3/5 ≥ 0.5 (so "likely C" is assertable). -/
theorem ws3_marginal_C : ws3.pC = 3/5 := by rfl

/-- s1 has P(A∧C) = 81/100 < 0.9 (so "A and C" is not assertable). -/
theorem ws1_joint : ws1.pAC = 81/100 := by rfl

/-- The forward conditional is assertable (using strict >) only for s2,
    not s1, because `Assertability.assertable` uses strict >. This
    demonstrates the ≥ vs > mismatch that motivates the direct truth table. -/
theorem strict_assertability_s1_false :
    assertable ws1 θ = false := by native_decide

theorem strict_assertability_s2_true :
    assertable ws2 θ = true := by native_decide

theorem strict_assertability_s3_false :
    assertable ws3 θ = false := by native_decide


-- ============================================================================
-- Section 5: RSAConfig
-- ============================================================================

open RSA Real in
/-- @cite{grusdt-lassiter-franke-2022} toy example as RSAConfig.

Meaning: Boolean assertability (1 if assertable, 0 if not).
World prior: uniform over the 3 states.
S1 score: belief-based (rpow): score = L0(w|u)^α.
α = 1 (rationality parameter from the paper's toy example). -/
noncomputable def cfg : RSAConfig Utt State where
  meaning _ _ u s := if assertable' u s then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by positivity
  worldPrior_nonneg _ := by positivity


-- ============================================================================
-- Section 6: S1 Speaker Predictions (rsa_predict)
-- ============================================================================

/-! ## S1 predictions from the toy example (Table 2)

The pragmatic speaker in each state prefers the most informative true
utterance. Informativity is measured by L0's posterior concentration:
utterances that are true in fewer states are more informative.

- s1: "C" > "conditional" > "likely C"
  (C is true in 1 state, conditional in 2, likely C in 3)
- s2: "conditional" > "likely C"
  (conditional in 2 states, likely C in 3; C and conjAC are false)
- s3: "likely C" dominates
  (only true utterance; conditional, C, and conjAC are all false)

The ordering follows informativity: utterances true in fewer states
give L0 a sharper posterior, yielding higher S1 scores. -/

/-- **s1**: S1 prefers "C" over "if A then C."

In s1, both "C" and "conditional" are true, but "C" is true only in s1
while "conditional" is true in both s1 and s2. So "C" is more informative.
S1(C|s1) = 6/11, S1(conditional|s1) = 3/11. -/
theorem s1_C_gt_conditional :
    cfg.S1 () .s1 .C > cfg.S1 () .s1 .conditional := by
  rsa_predict

/-- **s1**: S1 prefers "if A then C" over "likely C."

"conditional" is true in 2 states vs "likely C" in all 3.
S1(conditional|s1) = 3/11, S1(likelyC|s1) = 2/11. -/
theorem s1_conditional_gt_likelyC :
    cfg.S1 () .s1 .conditional > cfg.S1 () .s1 .likelyC := by
  rsa_predict

/-- **s2**: S1 prefers "if A then C" over "likely C."

In s2, "conditional" is true in 2 states while "likely C" is true in all 3.
S1(conditional|s2) = 3/5, S1(likelyC|s2) = 2/5. -/
theorem s2_conditional_gt_likelyC :
    cfg.S1 () .s2 .conditional > cfg.S1 () .s2 .likelyC := by
  rsa_predict

/-- **s2**: S1 prefers "if A then C" over "C."

"C" is false in s2 (P(C) = 0.65 < 0.9), so S1 assigns it zero. -/
theorem s2_conditional_gt_C :
    cfg.S1 () .s2 .conditional > cfg.S1 () .s2 .C := by
  rsa_predict

/-- **s3**: "likely C" dominates — no other utterance beats it.

"likely C" is the only true utterance in s3. The conditional, C, and
conjAC are all false, so they get zero S1 score. -/
theorem s3_likelyC_dominates :
    cfg.S1 () .s3 .likelyC > cfg.S1 () .s3 .conditional := by
  rsa_predict


-- ============================================================================
-- Section 7: L1 Listener Predictions (rsa_predict)
-- ============================================================================

/-! ## L1 predictions: the core dependency inference result

The central prediction: hearing "if A then C" makes the pragmatic listener
infer s2 (moderate dependence) over s1 (high marginals). This is because
S1 in s1 would have used the more informative "C" instead of the conditional.

This is the key mechanism behind dependency inference: conditionals
signal that the speaker could not have used a stronger utterance,
implicating a state where only the conditional is assertable. -/

/-- **L1 hearing "if A then C"**: prefers s2 over s1.

The core dependency inference result. S1 in s1 would prefer "C" over
"conditional" (by `s1_C_gt_conditional`), so hearing "conditional"
makes L1 shift probability toward s2 where "conditional" is the
best available utterance. -/
theorem l1_conditional_prefers_s2 :
    cfg.L1 .conditional .s2 > cfg.L1 .conditional .s1 := by
  rsa_predict

/-- **L1 hearing "if A then C"**: prefers s2 over s3.

s3 makes the conditional literally false, so it gets zero L1 weight. -/
theorem l1_conditional_s2_gt_s3 :
    cfg.L1 .conditional .s2 > cfg.L1 .conditional .s3 := by
  rsa_predict

/-- **L1 hearing "C"**: identifies s1.

"C" is true only in s1, so L1 assigns it probability 1. -/
theorem l1_C_identifies_s1 :
    cfg.L1 .C .s1 > cfg.L1 .C .s2 := by
  rsa_predict

/-- **L1 hearing "likely C"**: prefers s3 over s1.

"likely C" is true in all states, but S1 in s1 prefers "C" and S1 in s2
prefers "conditional," so hearing "likely C" implicates that stronger
utterances were unavailable — i.e., the state is s3 where "likely C" is
the only option. L1(s3|likelyC) = 55/87 > L1(s1|likelyC) = 10/87. -/
theorem l1_likelyC_prefers_s3 :
    cfg.L1 .likelyC .s3 > cfg.L1 .likelyC .s1 := by
  rsa_predict


-- ============================================================================
-- Section 8: Semantic Grounding Theorems
-- ============================================================================

/-- The conditional's meaning in the RSA model equals the assertability
    condition: assertable iff P(C|A) ≥ θ. Since we use the direct truth
    table, we verify consistency with the WorldState probabilities. -/
theorem conditional_assertable_iff_high_pCGivenA :
    (assertable' .conditional .s1 = true ∧ ws1.pCGivenA ≥ θ) ∧
    (assertable' .conditional .s2 = true ∧ ws2.pCGivenA ≥ θ) ∧
    (assertable' .conditional .s3 = false ∧ ws3.pCGivenA < θ) := by
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩ <;> native_decide

/-- "C" is assertable iff P(C) ≥ 0.9. -/
theorem C_assertable_iff_high_pC :
    (assertable' .C .s1 = true ∧ ws1.pC ≥ 9/10) ∧
    (assertable' .C .s2 = false ∧ ws2.pC < 9/10) ∧
    (assertable' .C .s3 = false ∧ ws3.pC < 9/10) := by
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩ <;> native_decide

/-- "likely C" is assertable in all states (P(C) ≥ 0.5 everywhere). -/
theorem likelyC_always_assertable :
    (assertable' .likelyC .s1 = true ∧ ws1.pC ≥ 1/2) ∧
    (assertable' .likelyC .s2 = true ∧ ws2.pC ≥ 1/2) ∧
    (assertable' .likelyC .s3 = true ∧ ws3.pC ≥ 1/2) := by
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩ <;> native_decide

/-- "A and C" is never assertable (P(A∧C) < 0.9 in all states). -/
theorem conjAC_never_assertable :
    assertable' .conjAC .s1 = false ∧
    assertable' .conjAC .s2 = false ∧
    assertable' .conjAC .s3 = false := by
  exact ⟨rfl, rfl, rfl⟩


-- ============================================================================
-- Section 9: Causal Inference
-- ============================================================================

/-! ## Connection to causal inference

The toy example does not include causal relations as a latent variable
(the full model in §3 does). However, the key qualitative prediction —
that conditionals signal *dependency* between A and C — is captured by
the L1 inference: hearing "if A then C" makes the listener prefer s2
(where A and C are strongly correlated: P(C|A) = 12/13 ≈ 0.923) over
s1 (where A and C have high marginals but weaker per-unit correlation).

The full model adds CausalRelation (A→C, C→A, A⊥C) as a latent variable,
but the dependency inference result already emerges from the simpler
model via scalar implicature. -/

/-- Causal asymmetry detection from assertability patterns.

If the forward conditional "if A then C" is assertable but the reverse
"if C then A" is not, `inferCausalRelation` returns `.ACausesC`. -/
theorem causal_asymmetry_detection (ws : WorldState) (thr : ℚ)
    (h_fwd : assertable ws thr = true)
    (h_bwd : reverseAssertable ws thr = false) :
    inferCausalRelation ws thr = .ACausesC := by
  simp only [inferCausalRelation, h_fwd, h_bwd, Bool.not_false, Bool.and_true, ↓reduceIte]

/-- Conditional perfection is NOT a semantic entailment.

There exist world states where "if A then C" is assertable but the
converse "if ¬A then ¬C" need not be. This supports the paper's claim
that conditional perfection is a pragmatic implicature, not entailment. -/
theorem perfection_not_semantic : ∃ (ws : WorldState),
    assertable ws (9/10) = true ∧
    contrapositiveAssertable ws (9/10) = false := by
  exact ⟨ws2, by native_decide, by native_decide⟩


-- ============================================================================
-- Section 10: Empirical Data
-- ============================================================================

/-- Experiment 1 result: causal structure inference from conditionals.

Participants (N≈150) hear "if A then C" and judge causal structure.
The asymmetry between forward and reverse conditionals is the key finding. -/
structure Experiment1Result where
  utterance : String
  pACausesC : ℚ
  pCCausesA : ℚ
  pIndependent : ℚ
  deriving Repr

def conditionalResult : Experiment1Result :=
  { utterance := "if A then C", pACausesC := 72/100,
    pCCausesA := 18/100, pIndependent := 10/100 }

def reverseConditionalResult : Experiment1Result :=
  { utterance := "if C then A", pACausesC := 15/100,
    pCCausesA := 75/100, pIndependent := 10/100 }

/-- Fitted assertability threshold from Experiment 3. -/
def fittedThreshold : ℚ := 88/100

/-- Experiment 2 perfection rates by causal context. -/
structure PerfectionResult where
  causalContext : CausalRelation
  perfectionRate : ℚ
  deriving Repr

def perfectionInCausal : PerfectionResult :=
  { causalContext := .ACausesC, perfectionRate := 85/100 }

def perfectionInIndependent : PerfectionResult :=
  { causalContext := .Independent, perfectionRate := 45/100 }

/-- Conditional perfection is modulated by causal context:
    much higher in A→C contexts than in independent contexts. -/
theorem perfection_modulated_by_context :
    perfectionInCausal.perfectionRate > perfectionInIndependent.perfectionRate := by
  native_decide


-- ============================================================================
-- Section 11: Theoretical Claims
-- ============================================================================

/-! ## Key claims supported by the model

1. **Conditionals communicate dependency**: L1 hearing "if A then C" infers
   a state with high P(C|A) relative to P(C) — i.e., a state where A and C
   are dependent. This is `l1_conditional_prefers_s2`.

2. **Conditional perfection is pragmatic**: The semantic meaning of
   conditionals (assertability) does NOT entail perfection
   (`perfection_not_semantic`). Perfection arises via scalar implicature
   in the full model.

3. **Speaker informativity drives inference**: S1 in s1 prefers "C" over
   "conditional" (`s1_C_gt_conditional`), so hearing "conditional"
   implicates that "C" was unavailable (i.e., the state is s2, not s1).

4. **Weak states produce weak utterances**: In s3, the speaker can only
   use "likely C" (`s3_likelyC_dominates`). Hearing "likely C" makes L1
   infer s3 (`l1_likelyC_prefers_s3`), the state with weakest dependence. -/


-- ════════════════════════════════════════════════════
-- § Structural ↔ Probabilistic Bridge
-- ════════════════════════════════════════════════════

/-! ## Structural Causation Grounds Probabilistic Inference

When the underlying causal model has A both sufficient AND necessary for C,
the RSA listener should infer `CausalRelation.ACausesC`. This section bridges
@cite{nadathur-lauer-2020}'s structural semantics to the probabilistic
inference above. -/

open Core.StructuralEquationModel
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity

/-- Deterministic model parameters: the structural profile of a causal
    model reduced to three Bools. -/
structure DeterministicParams where
  sufficient : Bool
  necessary : Bool
  alternativeCause : Bool
  deriving Repr, DecidableEq

namespace DeterministicParams

def toConditionals (p : DeterministicParams) : ℚ × ℚ :=
  let pCGivenA := if p.sufficient then 1 else 0
  let pCGivenNotA := if p.alternativeCause then 1 else 0
  (pCGivenA, pCGivenNotA)

def toNoisyOR (p : DeterministicParams) : NoisyOR :=
  let background : ℚ := if p.alternativeCause then 1 else 0
  let power : ℚ := (if p.sufficient then 1 else 0) - background
  { background := background, power := power }

end DeterministicParams

def DeterministicParams.ofProfile (p : CausalProfile) : DeterministicParams :=
  { sufficient := p.sufficient
  , necessary := p.necessary
  , alternativeCause := !p.necessary }

def extractParams (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : DeterministicParams :=
  .ofProfile (extractProfile dyn background cause effect)

/-- Convert a structural situation to a probabilistic world state. -/
def situationToWorldState (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (pCause : ℚ) : WorldState :=
  let params := extractParams dyn background cause effect
  let (pCGivenA, pCGivenNotA) := params.toConditionals
  let pA := pCause
  let pC := pCGivenA * pA + pCGivenNotA * (1 - pA)
  let pAC := pCGivenA * pA
  { pA := pA, pC := pC, pAC := pAC }

def situationToWorldStateUniform (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : WorldState :=
  situationToWorldState dyn background cause effect (1/2)

/-- Structural sufficiency → P(C|A) = 1. -/
theorem sufficiency_implies_pCGivenA_one (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (pCause : ℚ) (hCause : 0 < pCause ∧ pCause ≤ 1)
    (h_suff : causallySufficient dyn background cause effect = true) :
    (situationToWorldState dyn background cause effect pCause).pCGivenA = 1 := by
  simp only [situationToWorldState, extractParams, DeterministicParams.ofProfile,
             extractProfile, WorldState.pCGivenA,
             DeterministicParams.toConditionals, h_suff, ↓reduceIte]
  have hpA_pos : 0 < pCause := hCause.1
  simp only [gt_iff_lt, hpA_pos, ↓reduceIte]
  have hpA_ne : pCause ≠ 0 := ne_of_gt hpA_pos
  field_simp

/-- Structural necessity → P(C|¬A) = 0. -/
theorem necessity_implies_pCGivenNotA_zero (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (pCause : ℚ) (hCause : 0 ≤ pCause ∧ pCause < 1)
    (h_nec : causallyNecessary dyn background cause effect = true) :
    (situationToWorldState dyn background cause effect pCause).pCGivenNotA = 0 := by
  simp only [situationToWorldState, extractParams, DeterministicParams.ofProfile,
             extractProfile, WorldState.pCGivenNotA, WorldState.pNotAC,
             DeterministicParams.toConditionals, h_nec, Bool.not_true]
  have hNotA_pos : (0 : ℚ) < 1 - pCause := by linarith [hCause.2]
  simp only [gt_iff_lt, hNotA_pos, ↓reduceIte]
  norm_num

/-- Sufficient + necessary → assertable. -/
theorem structural_ac_implies_inferred_ac (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (θ : ℚ) (hθ : 0 ≤ θ ∧ θ < 1)
    (h_suff : causallySufficient dyn background cause effect = true)
    (h_nec : causallyNecessary dyn background cause effect = true) :
    let ws := situationToWorldState dyn background cause effect (1/2)
    assertable ws θ = true := by
  simp only [situationToWorldState, extractParams, DeterministicParams.ofProfile,
             extractProfile, h_suff, h_nec,
             Bool.not_true, assertable, WorldState.pCGivenA, conditionalProbability,
             DeterministicParams.toConditionals, ↓reduceIte]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · norm_num
  · simp only [gt_iff_lt]
    norm_num
    linarith [hθ.2]

def structuralToCausalRelation (params : DeterministicParams) : CausalRelation :=
  if params.sufficient && params.necessary then
    .ACausesC
  else if params.sufficient && !params.necessary then
    .Independent
  else
    .Independent

def inferStructuralCausalRelation (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : CausalRelation :=
  let params := extractParams dyn background cause effect
  structuralToCausalRelation params

/-- Sufficient + necessary → ACausesC. -/
theorem grounding_chain_consistent (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable)
    (h_suff : causallySufficient dyn background cause effect = true)
    (h_nec : causallyNecessary dyn background cause effect = true) :
    inferStructuralCausalRelation dyn background cause effect = .ACausesC := by
  simp only [inferStructuralCausalRelation, extractParams, DeterministicParams.ofProfile,
             extractProfile, structuralToCausalRelation, h_suff, h_nec]
  decide

/-- Overdetermination → Independent (sufficient but not necessary). -/
theorem overdetermination_not_ac (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable)
    (h_suff : causallySufficient dyn background cause effect = true)
    (h_not_nec : causallyNecessary dyn background cause effect = false) :
    inferStructuralCausalRelation dyn background cause effect = .Independent := by
  simp only [inferStructuralCausalRelation, extractParams, DeterministicParams.ofProfile,
             extractProfile, structuralToCausalRelation, h_suff, h_not_nec]
  decide

/-- In single-law models, sufficiency implies necessity. -/
theorem single_cause_perfection (cause effect : Variable) :
    let dyn := ⟨[CausalLaw.simple cause effect]⟩
    causallySufficient dyn Situation.empty cause effect = true →
    causallyNecessary dyn Situation.empty cause effect = true := by
  intro _ _
  exact simple_law_necessity cause effect

end GrusdtLassiterFranke2022
