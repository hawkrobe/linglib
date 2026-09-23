module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Analysis.SpecialFunctions.Softmax

/-!
# The decision-theoretic listener

This file defines the listener of Rational Speech Act models who acts. After an utterance the
listener's belief is a kernel from utterances to states; a decision problem is a reward for
each action at each state ([van-rooy-2003]); the listener's expected reward of an action is
the reward averaged over the belief, and the listener chooses an action by the softmax of
expected reward at a rationality, the score speaker of `Linglib.Pragmatics.RSA.Basic` applied
to actions. The decision-theoretic utility of an utterance for the speaker is the true reward
of the action the listener's policy chooses, the relevance of [sumers-etal-2024] and the
utility of [harding-gerstenberg-icard-2025]; the action-oriented speakers of
[qing-franke-2015] are the case in which the reward is the payoff of a signaling game.

## Main definitions

* `RSA.expectedReward` — the listener's expected reward of an action after an utterance.
* `RSA.policy` — the listener's policy, the softmax of expected reward at a rationality.
* `RSA.actionUtility` — the expected true reward of the listener's choice, the speaker's
  decision-theoretic utility of an utterance at a state.

## Main results

* `RSA.policy_real_lt_iff` — the listener prefers the action with the higher expected reward.
* `RSA.policy_real_singleton` — the policy's share of an action is the real softmax.
* `RSA.policy_real_of_pair`, `RSA.actionUtility_of_pair` — with two actions the share is the
  logistic function of the scaled difference in expected reward, and the utility is the rewards
  weighted by the shares.

## References

* [sumers-etal-2024]
* [harding-gerstenberg-icard-2025]
* [van-rooy-2003]
* [qing-franke-2015]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section ActionUtility

variable {W U A : Type*} [MeasurableSpace U] [Fintype A] [MeasurableSpace A]

/-- The decision-theoretic utility of an utterance at a state: the true reward of the action
the listener's policy chooses, in expectation. -/
noncomputable def actionUtility (π : Kernel U A) (R : A → W → ℝ) (u : U) (w : W) : ℝ :=
  ∑ a, (π u).real {a} * R a w

variable [DiscreteMeasurableSpace A] (R : A → W → ℝ) (π : Kernel U A) {u : U} {a a' : A} {w : W}

/-- With two actions, utility is the reward of the first weighted by its share and of the second
by the rest. -/
theorem actionUtility_of_pair [IsMarkovKernel π] (haa' : a ≠ a') (hall : ∀ c, c = a ∨ c = a') :
    actionUtility π R u w = (π u).real {a} * R a w + (1 - (π u).real {a}) * R a' w := by
  rw [actionUtility, Fintype.sum_eq_add a a' haa' (λ c hc => absurd (hall c) (not_or.mpr hc)),
    ← measureReal_singleton_add_singleton_of_pair (π u) haa' (λ c _ => hall c)]
  ring

end ActionUtility

section Policy

variable {W U A : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSpace U]

/-- The listener's expected reward of an action after an utterance: the reward averaged over
the belief. -/
noncomputable def expectedReward (L : Kernel U W) (R : A → W → ℝ) (u : U) (a : A) : ℝ :=
  ∑ w, (L u).real {w} * R a w

variable [Fintype U] [DiscreteMeasurableSpace U] [Fintype A] [MeasurableSpace A]
  [DiscreteMeasurableSpace A]

/-- The score of an action for the listener: rationality times expected reward. -/
noncomputable def policyScore (β : ℝ) (L : Kernel U W) (R : A → W → ℝ) (u : U) (a : A) :
    EReal :=
  ((β * expectedReward L R u a : ℝ) : EReal)

/-- The listener's policy: the softmax of expected reward at rationality `β`. -/
noncomputable def policy (β : ℝ) (L : Kernel U W) (R : A → W → ℝ) : Kernel U A :=
  speakerOfScore (policyScore β L R)

variable (β : ℝ) (L : Kernel U W) (R : A → W → ℝ)

instance : IsFiniteKernel (policy β L R) := inferInstanceAs (IsFiniteKernel (speakerOfScore _))

instance [Nonempty A] : IsMarkovKernel (policy β L R) :=
  isMarkovKernel_speakerOfScore (λ _ => ⟨Classical.arbitrary A, EReal.coe_ne_bot _⟩)
    (λ _ _ => EReal.coe_ne_top _)

variable {β} {u : U} {a a' : A} {w : W}

/-- Row preference of the policy is comparison of expected reward. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (policy β L R u).real {a} < (policy β L R u).real {a'} ↔
      expectedReward L R u a < expectedReward L R u a' := by
  rw [policy, speakerOfScore_real_singleton_lt_iff (score := policyScore β L R) (w := u)
    (λ _ => EReal.coe_ne_top _) ⟨a, EReal.coe_ne_bot _⟩, policyScore, policyScore,
    EReal.coe_lt_coe_iff]
  exact mul_lt_mul_iff_right₀ hβ

/-- The policy's share of an action is the real softmax of the scaled expected rewards. -/
theorem policy_real_singleton :
    (policy β L R u).real {a} = Real.softmax (λ a => β * expectedReward L R u a) a := by
  rw [policy, speakerOfScore,
    Kernel.ofWeights_real_singleton (λ u a => EReal.exp (policyScore β L R u a)) u
      (λ b => by rw [ne_eq, EReal.exp_eq_top_iff, policyScore]; exact EReal.coe_ne_top _),
    Real.softmax_def]
  simp only [policyScore, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- With two actions, the policy's share of one is the logistic function of the scaled
difference in expected reward. -/
theorem policy_real_of_pair (haa' : a ≠ a') (hall : ∀ c, c = a ∨ c = a') :
    (policy β L R u).real {a} =
      Real.sigmoid (β * (expectedReward L R u a - expectedReward L R u a')) := by
  rw [policy, speakerOfScore_real_singleton_of_pair (score := policyScore β L R) (w := u) haa'
    (EReal.coe_ne_bot _) (EReal.coe_ne_bot _) (λ _ => EReal.coe_ne_top _) (λ c _ => hall c),
    policyScore, policyScore, EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

/-- Two utterances after which the listener's expected rewards agree up to a constant shift
leave the policy, and so the utility at every state, the same; the listeners may differ. -/
theorem actionUtility_policy_eq_of_expectedReward_eq_add {L' : Kernel U W} {u' : U} {c : ℝ}
    (h : ∀ a, expectedReward L R u a = expectedReward L' R u' a + c) :
    actionUtility (policy β L R) R u w = actionUtility (policy β L' R) R u' w := by
  simp only [actionUtility, policy_real_singleton, h, mul_add]
  rw [Real.softmax_add_const]

end Policy

end RSA
