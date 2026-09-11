import Linglib.Pragmatics.RSA.QUD

/-!
# Kao and Goodman (2015): Let's Talk (Ironically) About the Weather

This file formalizes the irony model of [kao-goodman-2015] on the RSA kernel pipeline. The
model is the question-under-discussion RSA of [kao-etal-2014-hyperbole] over a meaning space of
a weather state and the speaker's affect toward it, the question being the state or a dimension
of affect (eq. 1); the paper's contribution is the affect space. With valence alone, "The
weather is terrible" can be hyperbolic, merely bad weather, but not ironic, since a negative
utterance carries no true information about positive affect; with the arousal dimension the
paper finds in its elicited emotion ratings alongside valence, the utterance can convey high
arousal, which terrible and amazing weather share, and the listener can read it as amazing
weather.

Both claims are support theorems. Under the arousal question, "terrible" can mean amazing
weather with positive valence and high arousal whenever the prior admits high arousal at
terrible weather (`irony`); under questions of state and valence only, a positive-valence
reading of "terrible" needs positive valence to be possible at terrible weather itself
(`valence_flip_needs_arousal`). The hyperbolic reading is available under the valence question
(`hyperbole`).

## Implementation notes

Priors are arguments: the state prior of a weather context and the affect prior of
Experiment 1, the probabilities of positive valence and high arousal at each state read off the
first two principal components of the emotion ratings, enter as one probability measure on
meanings, and the question prior as a probability measure on questions. The model's fits to
Experiment 2 are not stated.

## References

* [kao-goodman-2015]
* [kao-etal-2014-hyperbole]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace KaoGoodman2015

/-- The weather states, which are also the utterances. -/
inductive Weather
  | terrible | bad | neutral | good | amazing
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Weather := ⊤
instance : DiscreteMeasurableSpace Weather := ⟨λ _ => trivial⟩
instance : Nonempty Weather := ⟨.neutral⟩

/-- The speaker's affect: positive valence, and high arousal. -/
abbrev Affect := Bool × Bool

/-- A meaning: the weather state and the speaker's affect toward it. -/
abbrev Meaning := Weather × Affect

/-- The question under discussion: the state, or a dimension of affect. -/
inductive QUD
  | state | valence | arousal
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace QUD := ⊤
instance : DiscreteMeasurableSpace QUD := ⟨λ _ => trivial⟩
instance : Nonempty QUD := ⟨.state⟩

/-- The projection of a question (eq. 1): the state, the valence, or the arousal. -/
def project : QUD → Meaning → Weather ⊕ Bool
  | .state, m => .inl m.1
  | .valence, m => .inr m.2.1
  | .arousal, m => .inr m.2.2

/-- The meaning of an utterance: the state named is the state. -/
def sem (u : Weather) : Set Meaning := {m | m.1 = u}

/-- The literal listener: the prior conditioned on the state named. -/
noncomputable def L0 (μ : Measure Meaning) : Kernel Weather Meaning :=
  literalListener μ λ u => (sem u).indicator 1

theorem L0_apply_le_one (μ : Measure Meaning) (u : Weather) (s : Set Meaning) :
    L0 μ u s ≤ 1 :=
  literalListener_apply_le_one μ _ u s

theorem L0_apply_singleton_ne_zero_iff (μ : Measure Meaning) [IsFiniteMeasure μ] (u : Weather)
    (m : Meaning) : L0 μ u {m} ≠ 0 ↔ m.1 = u ∧ μ {m} ≠ 0 := by
  by_cases h : m ∈ sem u
  · rw [L0, literalListener_indicator_apply_singleton μ sem h]
    exact ⟨λ h' => ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      λ h' => mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [L0, literalListener_indicator_apply_singleton_of_notMem μ sem h]
    exact iff_of_false (λ h' => h' rfl) (λ h' => h h'.1)

/-- The question-indexed speaker: the best response to the projected literal listener of the
question at rationality `α`, with no utterance cost. -/
noncomputable def S1 (μ : Measure Meaning) (α : ℝ) : Kernel (Meaning × QUD) Weather :=
  familySpeaker (projListener project (L0 μ)) α 1

/-- The pragmatic listener over meaning and question, whose first marginal is the meaning
listener: the family listener over the product of the meaning prior and the question prior. -/
noncomputable def L1 (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure QUD)
    [IsProbabilityMeasure ν] (α : ℝ) : Kernel Weather (Meaning × QUD) :=
  familyListener (projListener project (L0 μ)) α 1 (μ.prod ν)

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure QUD)
  [IsProbabilityMeasure ν] (α : ℝ)

/-- A question's speaker produces an utterance at a meaning exactly when the meaning's cell
holds a meaning of positive prior at which the utterance is literally true. -/
theorem S1_apply_singleton_ne_zero_iff (hα : 0 < α) (q : QUD) (m : Meaning) (u : Weather) :
    S1 μ α (m, q) {u} ≠ 0 ↔ ∃ m', project q m' = project q m ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [S1, familySpeaker_apply]
  constructor
  · intro h
    have hL : projListener project (L0 μ) q u {m} ≠ 0 := λ h' =>
      h (speaker_apply_singleton_eq_zero hα h')
    rw [projListener_apply_singleton_ne_zero_iff] at hL
    obtain ⟨m', hm', h0⟩ := hL
    exact ⟨m', hm', (L0_apply_singleton_ne_zero_iff μ u m').mp h0⟩
  · rintro ⟨m', hm', hu, hμ⟩
    exact speaker_apply_singleton_ne_zero hα.le (λ _ => one_ne_zero) (λ _ => ENNReal.one_ne_top)
      (λ u' => projListener_apply_singleton_le_one _ _ _ _ _ (L0_apply_le_one μ))
      ((projListener_apply_singleton_ne_zero_iff _ _ _ _ _).mpr
        ⟨m', hm', (L0_apply_singleton_ne_zero_iff μ u m').mpr ⟨hu, hμ⟩⟩)

/-- An utterance naming a state of positive prior has a positive marginal. -/
theorem comp_S1_ne_zero (hα : 0 < α) {u : Weather} (h : ∃ m : Meaning, m.1 = u ∧ μ {m} ≠ 0) :
    (S1 μ α ∘ₘ μ.prod ν) {u} ≠ 0 := by
  obtain ⟨m, hm, hμ⟩ := h
  obtain ⟨q, -, hq⟩ : ∃ q ∈ (Finset.univ : Finset QUD), ν {q} ≠ 0 := by
    refine Finset.exists_ne_zero_of_sum_ne_zero ?_
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    exact one_ne_zero
  refine comp_familySpeaker_ne_zero (w := m) (l := q) ?_ ?_
  · rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    exact mul_ne_zero hμ hq
  · exact (S1_apply_singleton_ne_zero_iff μ α hα q m u).mpr ⟨m, rfl, hm, hμ⟩

/-- The meaning listener's support: a meaning is a possible interpretation of an utterance
exactly when it has positive prior and some question of positive prior projects it into the
cell of a meaning of positive prior at which the utterance is literally true. -/
theorem listener_ne_zero_iff (hα : 0 < α) {u : Weather} (hu : (S1 μ α ∘ₘ μ.prod ν) {u} ≠ 0)
    (m : Meaning) :
    (L1 μ ν α u).fst {m} ≠ 0 ↔ μ {m} ≠ 0 ∧
      ∃ q, ν {q} ≠ 0 ∧ ∃ m', project q m' = project q m ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [L1, familyListener_fst_apply_singleton_ne_zero_iff _ _ _ hu]
  simp only [← S1_apply_singleton_ne_zero_iff μ α hα, S1, ← Set.singleton_prod_singleton,
    Measure.prod_prod, mul_ne_zero_iff]
  exact ⟨λ ⟨q, ⟨hm, hq⟩, hs⟩ => ⟨hm, q, hq, hs⟩, λ ⟨hm, q, hq, hs⟩ => ⟨q, ⟨hm, hq⟩, hs⟩⟩

/-- Hyperbole: under the valence question, "terrible" can mean bad weather with negative
valence, through the negative valence of terrible weather. -/
theorem hyperbole (hα : 0 < α) (hν : ν {.valence} ≠ 0) {a a' : Bool}
    (hbad : μ {(.bad, false, a)} ≠ 0) (hterrible : μ {(.terrible, false, a')} ≠ 0) :
    (L1 μ ν α .terrible).fst {(.bad, false, a)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα (comp_S1_ne_zero μ ν α hα ⟨_, rfl, hterrible⟩)]
  exact ⟨hbad, .valence, hν, (.terrible, false, a'), rfl, rfl, hterrible⟩

/-- Irony: under the arousal question, "terrible" can mean amazing weather with positive
valence and high arousal, through the high arousal of terrible weather. -/
theorem irony (hα : 0 < α) (hν : ν {.arousal} ≠ 0) {v : Bool}
    (hamazing : μ {(.amazing, true, true)} ≠ 0) (hterrible : μ {(.terrible, v, true)} ≠ 0) :
    (L1 μ ν α .terrible).fst {(.amazing, true, true)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα (comp_S1_ne_zero μ ν α hα ⟨_, rfl, hterrible⟩)]
  exact ⟨hamazing, .arousal, hν, (.terrible, v, true), rfl, rfl, hterrible⟩

/-- Without the arousal question, a positive-valence reading of "terrible" needs positive
valence to be possible at terrible weather itself: a negative utterance carries no true
information about positive affect. -/
theorem valence_flip_needs_arousal (hα : 0 < α) (hν : ∀ q, ν {q} ≠ 0 → q ≠ .arousal)
    (hu : (S1 μ α ∘ₘ μ.prod ν) {.terrible} ≠ 0) {s : Weather} {a : Bool}
    (h : (L1 μ ν α .terrible).fst {(s, true, a)} ≠ 0) :
    ∃ a', μ {(.terrible, true, a')} ≠ 0 := by
  obtain ⟨hm, q, hq, ⟨s', v', a'⟩, hm', hs', hμ⟩ := (listener_ne_zero_iff μ ν α hα hu _).mp h
  simp only at hs'
  subst hs'
  rcases q with _ | _ | _
  · obtain rfl : Weather.terrible = s := Sum.inl.inj hm'
    exact ⟨a, hm⟩
  · obtain rfl : v' = true := Sum.inr.inj hm'
    exact ⟨a', hμ⟩
  · exact absurd rfl (hν _ hq)

end KaoGoodman2015
