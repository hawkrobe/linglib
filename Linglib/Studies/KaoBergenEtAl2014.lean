import Linglib.Pragmatics.RSA.QUD

/-!
# Kao, Bergen and Goodman (2014): Formalizing the Pragmatics of Metaphor Understanding

This file formalizes the metaphor model of [kao-etal-2014-metaphor] on the RSA kernel pipeline.
A meaning pairs a category, the animal named or a person, with a vector of three features; the
literal listener conditions the prior on the category named, and a speaker whose goal is to
communicate one feature is informative about the listener's mass on that feature's value
(eqs. 1 and 2), so that "John is a shark" can convey scariness to a listener who does not
believe John a shark. The pragmatic listener marginalizes the goal: it is the family listener of
the goal-indexed projected listeners over the product of the meaning prior and the goal prior.

Two structural theorems carry the paper's qualitative claims. A goal projects the category
away, so the speaker's choice depends on the features alone and the listener's posterior odds
between the animal and the person at a feature vector are the prior odds (`category_odds`): the
interpretation of the animal's name as a person (`nonliteral`) is driven by a category prior
that the paper fits at one in a hundred. And the speaker's odds for naming the animal rather
than the person are the power of the odds of the feature's value under the animal against the
person (`speaker_odds`), so the animal is named more readily than the person at a value the
animal makes likelier (`names_animal_iff`): the mechanism by which the metaphor elevates the
animal's typical features.

## Implementation notes

Priors are arguments: the category prior and the feature priors of Experiment 1b enter as one
probability measure on meanings, the goal prior as a probability measure on goals, uniform under
a vague question and weighted toward the asked feature under a specific one. The model's
numerical fits, the person probability of 0.994 and the correlations of Fig. 2, rest on the
elicited priors of thirty-two animals, not printed in the paper, and are not stated.

## References

* [kao-etal-2014-metaphor]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace KaoBergenEtAl2014

/-- The categories: the animal named, and a person. -/
inductive Cat
  | animal | person
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Cat := ⊤
instance : DiscreteMeasurableSpace Cat := ⟨λ _ => trivial⟩
instance : Nonempty Cat := ⟨.person⟩

/-- The three features of the paper's example, each present or absent. -/
abbrev Features := Bool × Bool × Bool

/-- A meaning: the category and the feature vector. -/
abbrev Meaning := Cat × Features

/-- A goal names the feature to communicate, `g_i(f) = f_i`. -/
inductive Goal
  | f₁ | f₂ | f₃
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Goal := ⊤
instance : DiscreteMeasurableSpace Goal := ⟨λ _ => trivial⟩
instance : Nonempty Goal := ⟨.f₁⟩

/-- The value of the goal's feature. -/
def Goal.feature : Goal → Features → Bool
  | .f₁, (a, _, _) => a
  | .f₂, (_, b, _) => b
  | .f₃, (_, _, c) => c

/-- The projection of a goal (eq. 1) reads the goal's feature and ignores the category. -/
def project (g : Goal) (m : Meaning) : Bool := g.feature m.2

/-- The meaning of an utterance: the category named is the category. -/
def sem (u : Cat) : Set Meaning := {m | m.1 = u}

/-- The literal listener: the prior conditioned on the category named. -/
noncomputable def L0 (μ : Measure Meaning) : Kernel Cat Meaning :=
  literalListener μ λ u => (sem u).indicator 1

theorem L0_apply (μ : Measure Meaning) (u : Cat) : L0 μ u = μ[|sem u] := by
  rw [L0, literalListener_indicator, Kernel.ofFunOfCountable_apply]

theorem L0_apply_le_one (μ : Measure Meaning) (u : Cat) (s : Set Meaning) : L0 μ u s ≤ 1 :=
  literalListener_apply_le_one μ _ u s

theorem L0_apply_singleton_ne_zero_iff (μ : Measure Meaning) [IsFiniteMeasure μ] (u : Cat)
    (m : Meaning) : L0 μ u {m} ≠ 0 ↔ m.1 = u ∧ μ {m} ≠ 0 := by
  by_cases h : m ∈ sem u
  · rw [L0, literalListener_indicator_apply_singleton μ sem h]
    exact ⟨λ h' => ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      λ h' => mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [L0, literalListener_indicator_apply_singleton_of_notMem μ sem h]
    exact iff_of_false (λ h' => h' rfl) (λ h' => h h'.1)

/-- The probability that the goal's feature has value `b` in a member of category `u`. -/
noncomputable def featureProb (μ : Measure Meaning) (u : Cat) (g : Goal) (b : Bool) : ℝ≥0∞ :=
  μ[|sem u] {m | g.feature m.2 = b}

/-- The projected listener at a meaning is the feature probability of its goal's value under
the category named. -/
theorem projListener_eq (μ : Measure Meaning) (g : Goal) (u : Cat) (m : Meaning) :
    projListener project (L0 μ) g u {m} = featureProb μ u g (g.feature m.2) := by
  rw [projListener_apply_singleton, L0_apply]
  rfl

/-- The goal-indexed speaker (eq. 2): the best response to the projected literal listener of
the goal at rationality `α`, with no utterance cost. -/
noncomputable def S1 (μ : Measure Meaning) (α : ℝ) : Kernel (Meaning × Goal) Cat :=
  familySpeaker (projListener project (L0 μ)) α 1

/-- The pragmatic listener over meaning and goal, whose first marginal is the meaning listener:
the family listener over the product of the meaning prior and the goal prior. -/
noncomputable def L1 (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
    [IsProbabilityMeasure ν] (α : ℝ) : Kernel Cat (Meaning × Goal) :=
  familyListener (projListener project (L0 μ)) α 1 (μ.prod ν)

section Speaker

variable (μ : Measure Meaning) (α : ℝ) (g : Goal) (m : Meaning)

/-- The speaker's odds for naming the animal rather than the person are the `α`-th power of the
odds of the goal's feature value under the animal against the person. -/
theorem speaker_odds :
    S1 μ α (m, g) {.animal} * featureProb μ .person g (g.feature m.2) ^ α
      = S1 μ α (m, g) {.person} * featureProb μ .animal g (g.feature m.2) ^ α := by
  simp only [S1, familySpeaker_apply, speaker_apply_singleton, projListener_eq, Pi.one_apply,
    mul_one, ENNReal.div_eq_inv_mul]
  ring

/-- The speaker names the animal rather than the person exactly when the goal's feature value
is likelier under the animal than under the person. -/
theorem names_animal_iff (hα : 0 < α)
    (h0 : featureProb μ .animal g (g.feature m.2) ≠ 0 ∨
      featureProb μ .person g (g.feature m.2) ≠ 0) :
    (S1 μ α (m, g)).real {.person} < (S1 μ α (m, g)).real {.animal}
      ↔ featureProb μ .person g (g.feature m.2) < featureProb μ .animal g (g.feature m.2) := by
  have hle : ∀ u, projListener project (L0 μ) g u {m} ≤ 1 :=
    λ u => projListener_apply_singleton_le_one _ _ _ _ _ (L0_apply_le_one μ)
  have h0' : ∃ u, projListener project (L0 μ) g u {m} ^ α * (1 : Cat → ℝ≥0∞) u ≠ 0 := by
    rcases h0 with h | h
    · refine ⟨.animal, ?_⟩
      rw [projListener_eq, Pi.one_apply, mul_one]
      exact weight_rpow_ne_zero hα.le h
    · refine ⟨.person, ?_⟩
      rw [projListener_eq, Pi.one_apply, mul_one]
      exact weight_rpow_ne_zero hα.le h
  rw [S1, familySpeaker_apply]
  dsimp only
  rw [speaker_real_singleton_lt_iff (cost := 1) hα.le (λ _ => ENNReal.one_ne_top) hle h0',
    projListener_eq, projListener_eq, Pi.one_apply, Pi.one_apply, mul_one, mul_one,
    ENNReal.rpow_lt_rpow_iff hα]

end Speaker

section Listener

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
  [IsProbabilityMeasure ν] (α : ℝ)

/-- A goal's speaker produces an utterance at a meaning exactly when some meaning of positive
prior sharing the goal's feature value bears the category named. -/
theorem S1_apply_singleton_ne_zero_iff (hα : 0 < α) (g : Goal) (m : Meaning) (u : Cat) :
    S1 μ α (m, g) {u} ≠ 0 ↔ ∃ m', g.feature m'.2 = g.feature m.2 ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [S1, familySpeaker_apply]
  constructor
  · intro h
    have hL : projListener project (L0 μ) g u {m} ≠ 0 := λ h' =>
      h (speaker_apply_singleton_eq_zero hα h')
    rw [projListener_apply_singleton_ne_zero_iff] at hL
    obtain ⟨m', hm', h0⟩ := hL
    exact ⟨m', hm', (L0_apply_singleton_ne_zero_iff μ u m').mp h0⟩
  · rintro ⟨m', hm', hu, hμ⟩
    exact speaker_apply_singleton_ne_zero hα.le (λ _ => one_ne_zero) (λ _ => ENNReal.one_ne_top)
      (λ u' => projListener_apply_singleton_le_one _ _ _ _ _ (L0_apply_le_one μ))
      ((projListener_apply_singleton_ne_zero_iff _ _ _ _ _).mpr
        ⟨m', hm', (L0_apply_singleton_ne_zero_iff μ u m').mpr ⟨hu, hμ⟩⟩)

/-- An utterance naming a category of positive prior has a positive marginal. -/
theorem comp_S1_ne_zero (hα : 0 < α) {u : Cat} (h : ∃ m : Meaning, m.1 = u ∧ μ {m} ≠ 0) :
    (S1 μ α ∘ₘ μ.prod ν) {u} ≠ 0 := by
  obtain ⟨m, hm, hμ⟩ := h
  obtain ⟨g, -, hg⟩ : ∃ g ∈ (Finset.univ : Finset Goal), ν {g} ≠ 0 := by
    refine Finset.exists_ne_zero_of_sum_ne_zero ?_
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    exact one_ne_zero
  refine comp_familySpeaker_ne_zero (w := m) (l := g) ?_ ?_
  · rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    exact mul_ne_zero hμ hg
  · exact (S1_apply_singleton_ne_zero_iff μ α hα g m u).mpr ⟨m, rfl, hm, hμ⟩

/-- The meaning listener's support: a meaning is a possible interpretation of an utterance
exactly when it has positive prior and some goal of positive prior has a feature value it
shares with a meaning of positive prior bearing the category named. -/
theorem listener_ne_zero_iff (hα : 0 < α) {u : Cat} (hu : (S1 μ α ∘ₘ μ.prod ν) {u} ≠ 0)
    (m : Meaning) :
    (L1 μ ν α u).fst {m} ≠ 0 ↔ μ {m} ≠ 0 ∧
      ∃ g, ν {g} ≠ 0 ∧ ∃ m', g.feature m'.2 = g.feature m.2 ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [L1, familyListener_fst_apply_singleton_ne_zero_iff _ _ _ hu]
  simp only [← S1_apply_singleton_ne_zero_iff μ α hα, S1, ← Set.singleton_prod_singleton,
    Measure.prod_prod, mul_ne_zero_iff]
  exact ⟨λ ⟨g, ⟨hm, hg⟩, hs⟩ => ⟨hm, g, hg, hs⟩, λ ⟨hm, g, hg, hs⟩ => ⟨g, ⟨hm, hg⟩, hs⟩⟩

/-- Nonliteral interpretation: a person with the goal's feature value is a possible meaning of
the animal's name whenever some animal of positive prior shares the value. -/
theorem nonliteral (hα : 0 < α) {g : Goal} (hν : ν {g} ≠ 0) {f f' : Features}
    (hp : μ {(.person, f)} ≠ 0) (ha : μ {(.animal, f')} ≠ 0)
    (hf : g.feature f' = g.feature f) : (L1 μ ν α .animal).fst {(.person, f)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα (comp_S1_ne_zero μ ν α hα ⟨_, rfl, ha⟩)]
  exact ⟨hp, g, hν, (.animal, f'), hf, rfl, ha⟩

/-- Category inference is prior-driven: since a goal projects the category away, the speaker
behaves alike at the animal and at the person with the same features, and the listener's
posterior odds between the two categories at a feature vector are their prior odds. -/
theorem category_odds {u : Cat} (hu : (S1 μ α ∘ₘ μ.prod ν) {u} ≠ 0) (c c' : Cat)
    (f : Features) :
    (L1 μ ν α u).fst {(c, f)} * μ {(c', f)} = (L1 μ ν α u).fst {(c', f)} * μ {(c, f)} := by
  have hS : ∀ c g, S1 μ α ((c, f), g) = S1 μ α ((.person, f), g) := λ c g =>
    Kernel.ofWeights_apply_eq_of_mul one_ne_zero ENNReal.one_ne_top λ u => by
      simp only [projListener_eq, Pi.one_apply, mul_one]
  have key : ∀ c, (L1 μ ν α u).fst {(c, f)}
      = μ {(c, f)} * ∑ g, ν {g} * (S1 μ α ((.person, f), g) {u} / (S1 μ α ∘ₘ μ.prod ν) {u}) :=
    λ c => by
      rw [L1, Measure.fst_apply_singleton, Finset.mul_sum]
      refine Finset.sum_congr rfl λ g _ => ?_
      rw [familyListener_apply_singleton _ _ _ hu, ← Set.singleton_prod_singleton,
        Measure.prod_prod, ← familySpeaker_apply, ← S1, hS c g, mul_div_assoc, mul_assoc]
  rw [key c, key c']
  ring

end Listener

end KaoBergenEtAl2014
