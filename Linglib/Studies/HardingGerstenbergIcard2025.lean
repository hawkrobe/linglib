import Linglib.Pragmatics.RSA.Uniform
import Linglib.Core.Probability.Kernel.Posterior
import Linglib.Semantics.Causation.SEM.Bool
import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Semantics.Causation.CCSelection
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Harding, Gerstenberg, and Icard (2025): A Communication-First Account of Explanation

This file formalizes the model of [harding-gerstenberg-icard-2025], on which an answer to "why
FACT?" is a message in a Rational Speech Act game ([frank-goodman-2012]) whose literal meaning
is actual causation and whose speaker is useful rather than informative, after
[sumers-etal-2023]. The literal listener conditions a prior over causal situations on the
message (2), the substrate's `RSA.uniformListener`; the listener acts in a decision problem by
the softmax of expected reward (3), `policy`, the substrate's `RSA.speakerOfScore`; the speaker
maximizes the reward of the listener's action less the message's cost (4), (6), `speaker`; the
pragmatic listener is the posterior of the speaker at the prior (7); and the goodness of an
explanation is the gain in expected reward over acting on the prior alone (8), `goodness`.
When the listener's interests are unknown the decision problem is the manipulation game
(Definition 2), whose reward for a variable is the probability over contexts that intervening
on it changes FACT, `manipulationReward`. In the roof example (Example 2) citing the thatched
roof and citing the drought are equally informative but not equally useful, since only the
former bears on replacing a roof (Table 1), so at any rationality the listener replaces the roof
more readily after the former, `RoofReplacement.policy_replace_lt`. In the late-meeting example
(Example 3) citing the tardiness is worth giving although the listener already knows it: the
speaker cites the birthday exactly in the conjunctive world, so the pragmatic listener infers
from her not doing so that tardiness alone is the cause, and the goodness of the message is
positive, `LateMeeting.goodness_pos`. In the milk example (Example 4) citing both culprits is
worth more than citing one, but a sufficient cost difference makes the speaker prefer the
shorter message, `MilkTheft.speaker_prefers_short`. The interpretation sets are the paper's,
and for the late meeting the positive memberships are derived from actual causation in the
worlds' structural causal models.

## Implementation notes

The agents are kept at finite rationality, where the paper takes the limit, and each claim is
stated for the rationalities it needs. Actual causation is the witness form of the
Halpern–Pearl definition, `actualCause`, which the paper leaves open to any extant account; the
negative memberships are not derived. Priors are uniform, as in the examples.

## TODO

* Table 4, the manipulation-game rewards of Example 2, from the four structural models and a
  product prior over the contexts; the roof and milk interpretation sets from actual causation.

## References

* [harding-gerstenberg-icard-2025]
* [halpern-pearl-2005]
* [sumers-etal-2023]
* [frank-goodman-2012]
-/

namespace HardingGerstenbergIcard2025

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### The communication game, section 3 -/

section Framework

variable {W M A : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
  [Fintype M] [MeasurableSpace M] [DiscreteMeasurableSpace M]
  [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]

/-- The expected reward of an action under the listener's belief given the message, the sum
of (3). -/
noncomputable def expectedReward (L : Kernel M W) (R : A → W → ℝ) (m : M) (a : A) : ℝ :=
  ∑ w, (L m).real {w} * R a w

/-- The score of an action for the listener: rationality times expected reward. -/
noncomputable def policyScore (β : ℝ) (L : Kernel M W) (R : A → W → ℝ) (m : M) (a : A) :
    EReal :=
  ((β * expectedReward L R m a : ℝ) : EReal)

/-- (3): the listener's policy, the softmax of expected reward at rationality `β`. -/
noncomputable def policy (β : ℝ) (L : Kernel M W) (R : A → W → ℝ) : Kernel M A :=
  speakerOfScore (policyScore β L R)

/-- (4): the speaker's utility of a message at a world, the expected reward of the action the
listener's policy chooses. -/
noncomputable def utility (π : Kernel M A) (R : A → W → ℝ) (m : M) (w : W) : ℝ :=
  ∑ a, (π m).real {a} * R a w

/-- The score of a message for the speaker: rationality times utility, less cost. -/
noncomputable def speakerScore (β : ℝ) (cost : M → ℝ) (π : Kernel M A) (R : A → W → ℝ)
    (w : W) (m : M) : EReal :=
  ((β * utility π R m w - cost m : ℝ) : EReal)

/-- (6): the speaker, the softmax of utility less cost at rationality `β`. -/
noncomputable def speaker (β : ℝ) (cost : M → ℝ) (π : Kernel M A) (R : A → W → ℝ) :
    Kernel W M :=
  speakerOfScore (speakerScore β cost π R)

/-- (8): the goodness of a message at a world, the listener's expected reward after the
message less what acting on the prior alone would have earned. -/
noncomputable def goodness (πL πPrior : Kernel M A) (R : A → W → ℝ) (m : M) (w : W) : ℝ :=
  utility πL R m w - utility πPrior R m w

variable (β : ℝ) (L : Kernel M W) (R : A → W → ℝ) (cost : M → ℝ) (π : Kernel M A)

instance : IsFiniteKernel (policy β L R) := inferInstanceAs (IsFiniteKernel (speakerOfScore _))

instance : IsFiniteKernel (speaker β cost π R) :=
  inferInstanceAs (IsFiniteKernel (speakerOfScore _))

instance [Nonempty A] : IsMarkovKernel (policy β L R) :=
  isMarkovKernel_speakerOfScore (λ _ => ⟨Classical.arbitrary A, EReal.coe_ne_bot _⟩)
    (λ _ _ => EReal.coe_ne_top _)

instance [Nonempty M] : IsMarkovKernel (speaker β cost π R) :=
  isMarkovKernel_speakerOfScore (λ _ => ⟨Classical.arbitrary M, EReal.coe_ne_bot _⟩)
    (λ _ _ => EReal.coe_ne_top _)

variable {β} {m m' : M} {a a' : A} {w : W}

/-- Row preference of the policy is comparison of expected reward. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (policy β L R m).real {a} < (policy β L R m).real {a'} ↔
      expectedReward L R m a < expectedReward L R m a' := by
  rw [policy, speakerOfScore_real_singleton_lt_iff (score := policyScore β L R) (w := m)
    (λ _ => EReal.coe_ne_top _) ⟨a, EReal.coe_ne_bot _⟩, policyScore, policyScore,
    EReal.coe_lt_coe_iff]
  exact mul_lt_mul_iff_right₀ hβ

/-- With two actions, the policy's share of one is the logistic function of the scaled
difference in expected reward. -/
theorem policy_real_of_pair (haa' : a ≠ a') (hall : ∀ c, c = a ∨ c = a') :
    (policy β L R m).real {a} =
      Real.sigmoid (β * (expectedReward L R m a - expectedReward L R m a')) := by
  rw [policy, speakerOfScore_real_singleton_of_pair (score := policyScore β L R) (w := m) haa'
    (EReal.coe_ne_bot _) (EReal.coe_ne_bot _) (λ _ => EReal.coe_ne_top _) (λ c _ => hall c),
    policyScore, policyScore, EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

/-- With two actions, utility is the reward of the first weighted by its share and of the second
by the rest. -/
theorem utility_of_pair [IsMarkovKernel π] (haa' : a ≠ a') (hall : ∀ c, c = a ∨ c = a') :
    utility π R m w = (π m).real {a} * R a w + (1 - (π m).real {a}) * R a' w := by
  rw [utility, Fintype.sum_eq_add a a' haa' (λ c hc => absurd (hall c) (not_or.mpr hc)),
    ← measureReal_singleton_add_singleton_of_pair (π m) haa' (λ c _ => hall c)]
  ring

/-- Row preference of the speaker is comparison of utility less cost. -/
theorem speaker_real_lt_iff (hβ : 0 < β) :
    (speaker β cost π R w).real {m} < (speaker β cost π R w).real {m'} ↔
      β * utility π R m w - cost m < β * utility π R m' w - cost m' := by
  rw [speaker, speakerOfScore_real_singleton_lt_iff (score := speakerScore β cost π R) (w := w)
    (λ _ => EReal.coe_ne_top _) ⟨m, EReal.coe_ne_bot _⟩, speakerScore, speakerScore,
    EReal.coe_lt_coe_iff]

/-- With two messages, the speaker's share of one is the logistic function of the scaled
difference in utility less the difference in cost. -/
theorem speaker_real_of_pair (hmm' : m ≠ m') (hall : ∀ c, c = m ∨ c = m') :
    (speaker β cost π R w).real {m} =
      Real.sigmoid (β * (utility π R m w - utility π R m' w) - (cost m - cost m')) := by
  rw [speaker, speakerOfScore_real_singleton_of_pair (score := speakerScore β cost π R) (w := w)
    hmm' (EReal.coe_ne_bot _) (EReal.coe_ne_bot _) (λ _ => EReal.coe_ne_top _) (λ c _ => hall c),
    speakerScore, speakerScore, EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

end Framework

/-! ### The manipulation game, Definition 2 -/

section ManipulationGame

open Causation Causation.SEM

variable {V Ctx : Type*} [Fintype V] [DecidableEq V] [Fintype Ctx]

/-- The reward of intervening on `X` in a model (Definition 2): the probability over contexts
that some intervention on `X` changes FACT. -/
noncomputable def manipulationReward (P : Ctx → ℝ) (ctx : Ctx → Valuation (λ _ : V => Bool))
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M] (X fact : V) : ℝ :=
  ∑ u, P u * (haveI := Classical.dec (BoolSEM.manipulates M (ctx u) X fact)
    if BoolSEM.manipulates M (ctx u) X fact then 1 else 0)

end ManipulationGame

/-! ### Actual causation, the literal meaning of "because" -/

open Causation Causation.Mechanism Causation.SEM

/-- Actual causation in witness form: the cause and the effect hold at the actual world, and
at some witness valuation the cause is but-for the effect
(`CCSelection.completesForEffect`), [halpern-pearl-2005]'s definition without the contingency
clause the paper leaves to any extant account. -/
def actualCause {V : Type*} [Fintype V] [DecidableEq V] (M : BoolSEM V)
    [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M] (u : Valuation (λ _ : V => Bool))
    (cause effect : V) : Prop :=
  u.hasValue cause true ∧ (M.developDet u).hasValue effect true ∧
    ∃ s' : Valuation (λ _ : V => Bool), CCSelection.completesForEffect M s' cause true false effect true

/-! ### Example 3: the late meeting -/

namespace LateMeeting

/-- The endogenous variables: Bob's tardiness, his forgetting the birthday, Charlie's
crossness. -/
inductive V | T | B | C
  deriving DecidableEq, Fintype, Repr

def vars : List V := [.T, .B, .C]

def graphT : CausalGraph V := ⟨λ | .T => ∅ | .B => ∅ | .C => {.T}⟩

def graphConj : CausalGraph V := ⟨λ | .T => ∅ | .B => ∅ | .C => {.T, .B}⟩

/-- The model in which tardiness alone causes crossness. -/
noncomputable def semT : BoolSEM V :=
  { graph := graphT
    mech := λ v => match v with
      | .T => const (G := graphT) false
      | .B => const (G := graphT) false
      | .C => deterministic (λ ρ => ρ ⟨.T, by simp [graphT]⟩) }

/-- The conjunctive model, in which both are needed. -/
noncomputable def semConj : BoolSEM V :=
  { graph := graphConj
    mech := λ v => match v with
      | .T => const (G := graphConj) false
      | .B => const (G := graphConj) false
      | .C => deterministic (λ ρ => ρ ⟨.T, by simp [graphConj]⟩ && ρ ⟨.B, by simp [graphConj]⟩) }

noncomputable instance : SEM.IsDeterministic semT where
  mech_det v := match v with
    | .T | .B => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .C => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

noncomputable instance : SEM.IsDeterministic semConj where
  mech_det v := match v with
    | .T | .B => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .C => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

instance : CausalGraph.IsDAG semT.graph :=
  CausalGraph.IsDAG.of_depth _ (λ | .T => 0 | .B => 0 | .C => 1) <| by
    intro u v h; cases v <;> simp_all [graphT, semT]

instance : CausalGraph.IsDAG semConj.graph :=
  CausalGraph.IsDAG.of_depth _ (λ | .T => 0 | .B => 0 | .C => 1) <| by
    intro u v h; cases v <;> simp_all [graphConj, semConj]
    rcases h with rfl | rfl <;> decide

/-- The context Bob knows: he was late and forgot the birthday. -/
def context : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .T true |>.extend .B true

/-- "Because T" is true in both worlds and "because B" in the conjunctive world: the
interpretation sets of Example 3, derived from actual causation. -/
theorem actualCause_T_semT : actualCause semT context .T .C := by
  refine ⟨by decide, ?_, context, ?_⟩
  · exact SEM.developDet_hasValue_of_developDetOn_hasValue (vs := vars) (n := 1) (by decide)
  · exact CCSelection.completesForEffect_of_developDetOn vars 1 (by decide) (by decide)

theorem actualCause_T_semConj : actualCause semConj context .T .C := by
  refine ⟨by decide, ?_, context, ?_⟩
  · exact SEM.developDet_hasValue_of_developDetOn_hasValue (vs := vars) (n := 1) (by decide)
  · exact CCSelection.completesForEffect_of_developDetOn vars 1 (by decide) (by decide)

theorem actualCause_B_semConj : actualCause semConj context .B .C := by
  refine ⟨by decide, ?_, context, ?_⟩
  · exact SEM.developDet_hasValue_of_developDetOn_hasValue (vs := vars) (n := 1) (by decide)
  · exact CCSelection.completesForEffect_of_developDetOn vars 1 (by decide) (by decide)

/-- In the tardiness-only world the birthday is not but-for crossness at the actual context:
crossness reads tardiness alone. -/
theorem not_completesForEffect_B_semT :
    ¬ CCSelection.completesForEffect semT context .B true false .C true :=
  λ ⟨_, hb⟩ => hb (SEM.developDet_hasValue_of_developDetOn_hasValue (vs := vars) (n := 1)
    (by decide))

/-- The worlds: `0` the tardiness-only model, `1` the conjunctive model. -/
abbrev World := Fin 2

/-- The messages: `0` "because T", `1` "because B". -/
abbrev Msg := Fin 2

/-- The actions of Table 3: `0` apologize for the tardiness alone, `1` for both. -/
abbrev Act := Fin 2

/-- The interpretation sets (Example 3). -/
def sem : Msg → Finset World := ![{0, 1}, {1}]

/-- Table 3: apologizing for what is the cause earns 1, otherwise −1. -/
def reward : Act → World → ℝ := λ a w => if a = w then 1 else -1

/-- The literal listener at the uniform prior (2). -/
noncomputable abbrev L0 : Kernel Msg World := uniformListener sem

/-- The prior as a listener who has heard nothing. -/
noncomputable abbrev prior : Kernel Msg World := uniformListener λ _ => Finset.univ

/-- The uniform prior over the worlds. -/
noncomputable abbrev μ : Measure World := uniformOn Set.univ

theorem prior_apply (m : Msg) : prior m = μ := by
  rw [uniformListener_apply, Finset.coe_univ]

theorem expectedReward_L0 (a : Act) :
    expectedReward L0 reward 0 a = 0 ∧
      expectedReward L0 reward 1 a = if a = 1 then 1 else -1 := by
  fin_cases a <;> simp [expectedReward, Fin.sum_univ_two, uniformListener_apply_singleton,
    measureReal_def, sem, reward] <;> norm_num

theorem expectedReward_prior (m : Msg) (a : Act) : expectedReward prior reward m a = 0 := by
  fin_cases a <;> simp [expectedReward, Fin.sum_univ_two, uniformListener_apply_singleton,
    measureReal_def, reward] <;> norm_num

variable {βL βS : ℝ}

/-- After "because B" the listener apologizes for both with a share above one half, and after
"because T" with exactly one half. -/
theorem policy_L0_both :
    (policy βL L0 reward 1).real {1} = Real.sigmoid (2 * βL) ∧
      (policy βL L0 reward 0).real {1} = 1 / 2 := by
  constructor
  · rw [policy_real_of_pair L0 reward (m := 1) (a := 1) (a' := 0) (by decide) (by decide),
      (expectedReward_L0 1).2, (expectedReward_L0 0).2]
    norm_num
    ring
  · rw [policy_real_of_pair L0 reward (m := 0) (a := 1) (a' := 0) (by decide) (by decide),
      (expectedReward_L0 1).1, (expectedReward_L0 0).1]
    simp [Real.sigmoid_zero]

theorem policy_prior_half (m : Msg) : (policy βL prior reward m).real {1} = 1 / 2 := by
  rw [policy_real_of_pair prior reward (m := m) (a := 1) (a' := 0) (by decide) (by decide),
    expectedReward_prior, expectedReward_prior]
  simp [Real.sigmoid_zero]

/-- The speaker's utilities (4): "because T" is worth nothing in either world, "because B" less
than nothing in the tardiness-only world and more in the conjunctive one. -/
theorem utility_L0 :
    utility (policy βL L0 reward) reward 0 0 = 0 ∧ utility (policy βL L0 reward) reward 0 1 = 0 ∧
      utility (policy βL L0 reward) reward 1 0 = 1 - 2 * Real.sigmoid (2 * βL) ∧
      utility (policy βL L0 reward) reward 1 1 = 2 * Real.sigmoid (2 * βL) - 1 := by
  have h := policy_L0_both (βL := βL)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [utility_of_pair reward (policy βL L0 reward) (a := 1) (a' := 0) (by decide) (by decide)]
  · rw [h.2]; simp [reward]; norm_num
  · rw [h.2]; simp [reward]; norm_num
  · rw [h.1]; simp [reward]; ring
  · rw [h.1]; simp [reward]; ring

theorem half_lt_sigmoid (hβ : 0 < βL) : 1 / 2 < Real.sigmoid (2 * βL) := by
  have := Real.sigmoid_lt (show (0 : ℝ) < 2 * βL by linarith)
  rwa [Real.sigmoid_zero, inv_eq_one_div] at this

/-- The speaker cites the birthday exactly in the conjunctive world (equal costs). -/
theorem speaker_cites_B_iff (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    (speaker βS (λ _ => c) (policy βL L0 reward) reward 0).real {1} <
        (speaker βS (λ _ => c) (policy βL L0 reward) reward 0).real {0} ∧
      (speaker βS (λ _ => c) (policy βL L0 reward) reward 1).real {0} <
        (speaker βS (λ _ => c) (policy βL L0 reward) reward 1).real {1} := by
  obtain ⟨h00, h01, h10, h11⟩ := utility_L0 (βL := βL)
  have hs := half_lt_sigmoid hβL
  constructor
  · rw [speaker_real_lt_iff reward (λ _ => c) (policy βL L0 reward) (w := 0) (m := 1) (m' := 0)
      hβS, h00, h10]
    nlinarith
  · rw [speaker_real_lt_iff reward (λ _ => c) (policy βL L0 reward) (w := 1) (m := 0) (m' := 1)
      hβS, h01, h11]
    nlinarith

theorem μ_singleton (w : World) : μ {w} ≠ 0 ∧ μ.real {w} = 1 / 2 := by
  rw [← prior_apply 0, uniformListener_apply_singleton, measureReal_def,
    uniformListener_apply_singleton]
  simp

/-- The speaker of Example 3 at equal costs `c`. -/
noncomputable def S (βL βS c : ℝ) : Kernel World Msg :=
  speaker βS (λ _ => c) (policy βL L0 reward) reward

instance (βL βS c : ℝ) : IsFiniteKernel (S βL βS c) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

instance (βL βS c : ℝ) : IsMarkovKernel (S βL βS c) :=
  inferInstanceAs (IsMarkovKernel (speaker _ _ _ _))

theorem S_apply_ne_zero (βL βS c : ℝ) (w : World) (m : Msg) : S βL βS c w {m} ≠ 0 :=
  speakerOfScore_apply_singleton_ne_zero
    (score := speakerScore βS (λ _ => c) (policy βL L0 reward) reward) (EReal.coe_ne_bot _)
    (λ _ => EReal.coe_ne_top _)

theorem comp_S_ne_zero (βL βS c : ℝ) : (S βL βS c ∘ₘ μ) {0} ≠ 0 := by
  rw [Measure.comp_apply_singleton]
  intro h
  exact mul_ne_zero (μ_singleton 0).1 (S_apply_ne_zero βL βS c 0 0)
    (Finset.sum_eq_zero_iff.mp h 0 (Finset.mem_univ _))

/-- "Because T" is likelier from the tardiness-only world than from the conjunctive one. -/
theorem S_real_lt (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    (S βL βS c 1).real {0} < (S βL βS c 0).real {0} := by
  obtain ⟨h00, h01, h10, h11⟩ := utility_L0 (βL := βL)
  have hs := half_lt_sigmoid hβL
  unfold S
  rw [speaker_real_of_pair reward (λ _ => c) (policy βL L0 reward) (w := 1) (m := 0) (m' := 1)
    (by decide) (by decide), speaker_real_of_pair reward (λ _ => c) (policy βL L0 reward)
    (w := 0) (m := 0) (m' := 1) (by decide) (by decide), h00, h01, h10, h11]
  exact Real.sigmoid_lt (by nlinarith)

/-- The pragmatic listener (7). -/
noncomputable def PL (βL βS c : ℝ) : Kernel Msg World := (S βL βS c)†μ

instance (βL βS c : ℝ) : IsMarkovKernel (PL βL βS c) :=
  inferInstanceAs (IsMarkovKernel ((S βL βS c)†μ))

/-- The pragmatic listener hearing "because T" raises the tardiness-only world above its prior:
the speaker would have cited the birthday in the conjunctive world. -/
theorem pragmatic_T (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    μ.real {0} < (PL βL βS c 0).real {0} := by
  rw [PL, real_lt_posterior_real_singleton_iff_of_pair (S βL βS c) μ (ω := 0) (ω' := 1)
    (by decide) (λ w _ => by fin_cases w <;> simp) (comp_S_ne_zero βL βS c) (μ_singleton 0).1
    (μ_singleton 1).1]
  exact S_real_lt hβL hβS c

/-- Goodness (8): citing the tardiness is worth giving, although Bob already knew it. -/
theorem goodness_pos (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    0 < goodness (policy βL (PL βL βS c) reward) (policy βL prior reward) reward 0 0 := by
  have hpost : μ.real {0} < (PL βL βS c 0).real {0} := pragmatic_T hβL hβS c
  have hsum : (PL βL βS c 0).real {0} + (PL βL βS c 0).real {1} = 1 :=
    measureReal_singleton_add_singleton_of_pair (PL βL βS c 0) (ω := 0) (ω' := 1) (by decide)
      (λ w _ => by fin_cases w <;> simp)
  have hE : expectedReward (PL βL βS c) reward 0 0 - expectedReward (PL βL βS c) reward 0 1 =
      2 * ((PL βL βS c 0).real {0} - (PL βL βS c 0).real {1}) := by
    simp [expectedReward, Fin.sum_univ_two, reward]
    ring
  have hpos : 0 < βL * (expectedReward (PL βL βS c) reward 0 0 -
      expectedReward (PL βL βS c) reward 0 1) := by
    rw [hE]
    have := (μ_singleton 0).2
    nlinarith
  rw [goodness, utility_of_pair reward (policy βL (PL βL βS c) reward) (a := 0) (a' := 1)
    (by decide) (by decide), utility_of_pair reward (policy βL prior reward) (a := 0) (a' := 1)
    (by decide) (by decide), policy_real_of_pair (PL βL βS c) reward (m := 0) (a := 0) (a' := 1)
    (by decide) (by decide), policy_real_of_pair prior reward (m := 0) (a := 0) (a' := 1)
    (by decide) (by decide), expectedReward_prior, expectedReward_prior]
  have hσ := Real.sigmoid_lt hpos
  rw [Real.sigmoid_zero] at hσ
  simp only [reward, Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, mul_one, mul_neg, sub_zero,
    mul_zero, Real.sigmoid_zero]
  norm_num at hσ ⊢
  linarith

end LateMeeting

/-! ### Example 2: the roof replacement -/

namespace RoofReplacement

/-- The worlds: `0` the roof-only model, `1` the drought-only model, `2` conjunctive, `3`
disjunctive, all at the context where the roof is thatched and there was a drought. -/
abbrev World := Fin 4

/-- The messages: `0` "because R", `1` "because D". -/
abbrev Msg := Fin 2

/-- The actions of Table 1: `0` replace the roof, `1` do not. -/
abbrev Act := Fin 2

/-- The interpretation sets of Example 2. -/
def sem : Msg → Finset World := ![{0, 2, 3}, {1, 2, 3}]

/-- Table 1: replacing earns 0 everywhere; not replacing earns 1 in the drought-only world and
−1 elsewhere. -/
def reward : Act → World → ℝ := λ a w => if a = 0 then 0 else if w = 1 then 1 else -1

noncomputable abbrev L0 : Kernel Msg World := uniformListener sem

/-- Equally informative: the conjunctive world is as likely after either message. -/
theorem L0_conj_eq : (L0 0).real {2} = (L0 1).real {2} := by
  simp [uniformListener_apply_singleton, measureReal_def, sem]

theorem expectedReward_L0 :
    expectedReward L0 reward 0 0 = 0 ∧ expectedReward L0 reward 0 1 = -1 ∧
      expectedReward L0 reward 1 0 = 0 ∧ expectedReward L0 reward 1 1 = -1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [expectedReward, Fin.sum_univ_four, uniformListener_apply_singleton, measureReal_def, sem,
      reward] <;> norm_num

/-- Not equally useful: at any rationality the listener replaces the roof more readily after
"because R" than after "because D". -/
theorem policy_replace_lt {βL : ℝ} (hβ : 0 < βL) :
    (policy βL L0 reward 1).real {0} < (policy βL L0 reward 0).real {0} := by
  obtain ⟨h00, h01, h10, h11⟩ := expectedReward_L0
  rw [policy_real_of_pair L0 reward (m := 1) (a := 0) (a' := 1) (by decide) (by decide),
    policy_real_of_pair L0 reward (m := 0) (a := 0) (a' := 1) (by decide) (by decide), h00, h01,
    h10, h11]
  exact Real.sigmoid_lt (by nlinarith)

end RoofReplacement

/-! ### Example 4: the milk theft -/

namespace MilkTheft

/-- The worlds: the contexts in which Charlie alone (`0`), Dana alone (`1`), or both (`2`) drank
the milk, in the disjunctive model. -/
abbrev World := Fin 3

/-- The messages: `0` "because C", `1` "because D", `2` "because C and D". -/
abbrev Msg := Fin 3

/-- The actions of Table 5: confront Charlie (`0`), Dana (`1`), or both (`2`). -/
abbrev Act := Fin 3

/-- The interpretation sets of Example 4. -/
def sem : Msg → Finset World := ![{0, 2}, {1, 2}, {2}]

/-- Table 5. -/
def reward : Act → World → ℝ :=
  ![![1, -1, 0], ![-1, 1, 0], ![0, 0, 1]]

noncomputable abbrev L0 : Kernel Msg World := uniformListener sem

theorem expectedReward_L0_conj (a : Act) :
    expectedReward L0 reward 2 a = if a = 2 then 1 else 0 := by
  fin_cases a <;> simp [expectedReward, Fin.sum_univ_three, uniformListener_apply_singleton,
    measureReal_def, sem, reward]

theorem expectedReward_L0_C :
    expectedReward L0 reward 0 0 = 1 / 2 ∧ expectedReward L0 reward 0 1 = -1 / 2 ∧
      expectedReward L0 reward 0 2 = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [expectedReward, Fin.sum_univ_three, uniformListener_apply_singleton, measureReal_def,
      sem, reward] <;> norm_num

/-- After "because C and D" confronting both is the strictly preferred action; after
"because C" it is tied with confronting Charlie. -/
theorem policy_L0 {βL : ℝ} (hβ : 0 < βL) :
    (policy βL L0 reward 2).real {0} < (policy βL L0 reward 2).real {2} ∧
      ¬ (policy βL L0 reward 0).real {0} < (policy βL L0 reward 0).real {2} := by
  constructor
  · rw [policy_real_lt_iff L0 reward (m := 2) hβ, expectedReward_L0_conj, expectedReward_L0_conj]
    simp
  · rw [policy_real_lt_iff L0 reward (m := 0) hβ, expectedReward_L0_C.1, expectedReward_L0_C.2.2]
    simp

/-- With a sufficient cost difference the speaker prefers the shorter message although it is
less useful: the redundancy trade-off of section 4.4.1. -/
theorem speaker_prefers_short {βL βS : ℝ} (hβS : 0 < βS) (cost : Msg → ℝ)
    (h : βS * (utility (policy βL L0 reward) reward 2 2 - utility (policy βL L0 reward) reward 0 2)
      < cost 2 - cost 0) :
    (speaker βS cost (policy βL L0 reward) reward 2).real {2} <
      (speaker βS cost (policy βL L0 reward) reward 2).real {0} := by
  rw [speaker_real_lt_iff reward cost (policy βL L0 reward) (w := 2) (m := 2) (m' := 0) hβS]
  linarith

end MilkTheft

end HardingGerstenbergIcard2025
