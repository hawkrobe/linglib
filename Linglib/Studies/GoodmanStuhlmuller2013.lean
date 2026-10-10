module

public import Linglib.Core.Probability.Distributions.Hypergeometric
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Core.Probability.UniformOn
public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Quantification.NumberTree

/-!
# Goodman and Stuhlmüller (2013): Knowledge and Implicature: Modeling Language Understanding as Social Cognition

Goodman and Stuhlmüller model scalar implicature under a speaker with incomplete knowledge. The
state is how many of `N` objects have a property, and the speaker's access is how many of them
she looks at. She observes how many of those have the property, a hypergeometric draw, believes
her posterior over states (`belief`), and softmax-optimizes the expected log-probability the
literal listener gives the state under that belief (`obsSpeaker`). The listener, who knows her
access but not her observation, marginalizes the observation (`speaker`) and applies Bayes' rule
(`listener`).

## Main statements

* `obsSpeaker_real_singleton`: the speaker says only what holds at every state her observation
  leaves possible, and weights such an utterance by the inverse size of its extension to the
  power of the rationality.
* `listener_full_lt`: with complete access the speaker knows the state, and of two states at
  which an utterance is true the listener favours the one at which fewer alternatives are true.
  For three objects, *some* implicates *not all* (`some_full`) and a numeral its exact reading
  (`two_full`, `one_full`).
* `speaker_of_isUpperSet`: when every meaning is upward closed, as the lower-bounded numerals
  are, the speaker who has seen `k` objects with the property speaks as one who knows there are
  exactly `k`.
* `some_partial`, `one_minimal`, `two_partial`, `one_partial_three`, `one_partial_two`: with
  access to one or two of three objects the *some* implicature is canceled, *one* after one
  object and *two* after two carry none, and *one* after two objects keeps the implicature
  against three but not against two.

## Implementation notes

* The speaker is `RSA.speaker` at her posterior belief and no cost. The literal listener is
  uniform on an utterance's extension, so only the support of the belief matters.
* The model takes any number of objects, and the alternatives and predictions are for three. An
  utterance's extension is a row of the tree of numbers, the numerals on their lower-bounded
  meaning.
* The alternatives are the paper's, *none*, *some*, *all* and *one*, *two*, *three*, without a
  silent option, so a speaker whose observation supports none of them says nothing.
* The prior is uniform, the regime of the paper's expository predictions; its fitted binomial
  prior and its rationality only reshape the plotted magnitudes. Experiment results and the
  quantitative fit are not formalized.

## References

* [goodman-stuhlmuller-2013]
* [frank-goodman-2012]
* [horn-1972]
-/

@[expose] public section

namespace GoodmanStuhlmuller2013

open MeasureTheory ProbabilityTheory Quantifier
open scoped ENNReal

variable {N : ℕ}

/-! ### Observation and belief -/

section Belief

variable {n : ℕ} {k : Fin (N + 1)}

/-- The states an observation leaves possible are those at which the speaker could see `k`
objects with the property among the `n` she looks at. -/
def compatible (n : ℕ) (k : Fin (N + 1)) : Finset (Fin (N + 1)) :=
  Finset.univ.filter fun s ↦ hypergeometricCount N s n k ≠ 0

@[simp] theorem mem_compatible {s : Fin (N + 1)} :
    s ∈ compatible n k ↔ hypergeometricCount N s n k ≠ 0 := by
  simp [compatible]

/-- The speaker's belief after an observation is her posterior over states under the uniform
prior. -/
noncomputable def belief (N n : ℕ) : Kernel (Fin (N + 1)) (Fin (N + 1)) :=
  (hypergeometric N n)†(uniformOn Set.univ)

instance : IsMarkovKernel (belief N n) :=
  inferInstanceAs (IsMarkovKernel ((hypergeometric N n)†(uniformOn Set.univ)))

/-- After a possible observation the speaker entertains exactly the states compatible with it. -/
theorem belief_apply_singleton_ne_zero_iff (hk : (compatible n k).Nonempty) (s : Fin (N + 1)) :
    belief N n k {s} ≠ 0 ↔ s ∈ compatible n k := by
  obtain ⟨s₀, hs₀⟩ := hk
  rw [belief, posterior_apply_singleton_ne_zero_iff _ _ (comp_apply_singleton_ne_zero _ _
    (uniformOn_univ_singleton_ne_zero s₀) ((hypergeometric_apply_singleton_ne_zero_iff s₀ k).2
      (mem_compatible.1 hs₀))), hypergeometric_apply_singleton_ne_zero_iff, mem_compatible]
  exact and_iff_right (uniformOn_univ_singleton_ne_zero s)

/-- With complete access the speaker's belief is the point mass at her observation. -/
theorem belief_full (k : Fin (N + 1)) : belief N N k = Measure.dirac k :=
  posterior_hypergeometric_self k _ (uniformOn_univ_singleton_ne_zero k)

end Belief

/-! ### The speaker and the listener -/

section Model

variable {U : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
  (sem : U → Finset (Fin (N + 1))) (α : ℝ) (n : ℕ)

/-- The speaker of equations (2) and (3) believes her posterior over states and addresses the
literal listener `Plex` of section 1, who is uniform on an utterance's extension. -/
noncomputable def obsSpeaker : Kernel (Fin (N + 1)) U :=
  RSA.speaker α 0 (RSA.uniformListener sem) (belief N n)

instance : IsFiniteKernel (obsSpeaker sem α n) :=
  inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))

/-- The speaker the listener models (equation 4) marginalizes the observation the listener cannot
see over the observation kernel. -/
noncomputable def speaker : Kernel (Fin (N + 1)) U :=
  obsSpeaker sem α n ∘ₖ hypergeometric N n

instance : IsFiniteKernel (speaker sem α n) :=
  inferInstanceAs (IsFiniteKernel (obsSpeaker sem α n ∘ₖ hypergeometric N n))

/-- The listener (equation 1) is the speaker's Bayesian inverse under a uniform prior. -/
noncomputable def listener : Kernel U (Fin (N + 1)) :=
  RSA.pragmaticListener (speaker sem α n) (uniformOn Set.univ)

variable {sem α n} {k : Fin (N + 1)} {u : U}

/-- After a possible observation the speaker says only what holds at every state it leaves
possible, and weights such an utterance by the inverse size of its extension to the power `α`. -/
theorem obsSpeaker_real_singleton (hα : 0 < α) (hk : (compatible n k).Nonempty) (u : U) :
    (obsSpeaker sem α n k).real {u} =
      (if compatible n k ⊆ sem u then ((sem u).card : ℝ)⁻¹ ^ α else 0) /
        ∑ u', if compatible n k ⊆ sem u' then ((sem u').card : ℝ)⁻¹ ^ α else 0 :=
  RSA.speaker_uniformListener_real_singleton sem hα (belief_apply_singleton_ne_zero_iff hk) u

/-- When the utterances true at every state an observation leaves possible are those true at one
state, the speaker speaks as if she knew that state. -/
theorem obsSpeaker_apply_eq_uniformSpeaker (hα : 0 < α) (hk : (compatible n k).Nonempty)
    {s : Fin (N + 1)} (h : ∀ u, compatible n k ⊆ sem u ↔ s ∈ sem u) :
    obsSpeaker sem α n k = RSA.uniformSpeaker sem α s :=
  RSA.speaker_uniformListener_apply_eq_uniformSpeaker sem hα
    (belief_apply_singleton_ne_zero_iff hk) h

/-- When every meaning is upward closed, the speaker who has seen `k` objects with the property
speaks as one who knows there are exactly `k`, her observation being her lower bound. -/
theorem obsSpeaker_apply_of_isUpperSet (hα : 0 < α)
    (hsem : ∀ u, IsUpperSet (sem u : Set (Fin (N + 1)))) (hk : (k : ℕ) ≤ n) (hn : n ≤ N) :
    obsSpeaker sem α n k = RSA.uniformSpeaker sem α k :=
  have hmem : k ∈ compatible n k :=
    mem_compatible.2 (hypergeometricCount_ne_zero_iff.2 ⟨hk, le_rfl, by omega⟩)
  obsSpeaker_apply_eq_uniformSpeaker hα ⟨k, hmem⟩ fun u ↦
    ⟨fun h ↦ h hmem, fun h s hs ↦ hsem u
      (Fin.le_def.2 (hypergeometricCount_ne_zero_iff.1 (mem_compatible.1 hs)).2.1) h⟩

theorem speaker_apply_singleton (s : Fin (N + 1)) (u : U) :
    speaker sem α n s {u} = ∑ k, hypergeometric N n s {k} * obsSpeaker sem α n k {u} :=
  Kernel.comp_apply_singleton _ _ s u

theorem speaker_real_singleton_le_one (s : Fin (N + 1)) (u : U) :
    (speaker sem α n s).real {u} ≤ 1 := by
  have h : speaker sem α n s {u} ≤ 1 :=
    calc speaker sem α n s {u}
      _ = ∑ k, hypergeometric N n s {k} * obsSpeaker sem α n k {u} := speaker_apply_singleton s u
      _ ≤ ∑ k, hypergeometric N n s {k} := Finset.sum_le_sum fun k _ ↦ mul_le_of_le_one_right'
          ((measure_mono (Set.subset_univ _)).trans (RSA.speaker_apply_univ_le_one _ _ _ _ k))
      _ = hypergeometric N n s Set.univ := by rw [← Finset.coe_univ, sum_measure_singleton]
      _ ≤ 1 := Kernel.ofWeights_apply_univ_le_one _ s
  rw [measureReal_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top h

/-- With complete access the speaker knows the state. -/
theorem speaker_full : speaker sem α N = RSA.uniformSpeaker sem α := by
  rw [speaker, hypergeometric_self, Kernel.comp_id, obsSpeaker,
    show ⇑(belief N N) = Measure.dirac from funext belief_full]

/-- When every object has the property, the speaker sees it of each object she looks at. -/
theorem speaker_last (hn : n ≤ N) :
    speaker sem α n (Fin.last N) = obsSpeaker sem α n ⟨n, Nat.lt_succ_of_le hn⟩ := by
  rw [speaker, Kernel.comp_apply, hypergeometric_last hn, Measure.dirac_bind (Kernel.measurable _)]

/-- When every meaning is upward closed, as the lower-bounded numerals are, the speaker the
listener models draws her observation and speaks as one who knows it to be the state. -/
theorem speaker_of_isUpperSet (hα : 0 < α) (hsem : ∀ u, IsUpperSet (sem u : Set (Fin (N + 1))))
    (hn : n ≤ N) : speaker sem α n = RSA.uniformSpeaker sem α ∘ₖ hypergeometric N n :=
  Kernel.ext fun s ↦ Measure.ext_of_singleton fun u ↦ by
    rw [speaker_apply_singleton, Kernel.comp_apply_singleton]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases h0 : hypergeometric N n s {k} = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [obsSpeaker_apply_of_isUpperSet hα hsem (hypergeometricCount_ne_zero_iff.1
        ((hypergeometric_apply_singleton_ne_zero_iff s k).1 h0)).1 hn]

/-- With complete access, of two states at which an utterance is true the listener favours the
one at which fewer alternatives are true, since the speaker's choice is spread over them. -/
theorem listener_full_lt (hα : 0 < α) {s s' : Fin (N + 1)} (hu : s ∈ sem u)
    (h : RSA.trueChoices sem s ⊂ RSA.trueChoices sem s') :
    (listener sem α N u).real {s'} < (listener sem α N u).real {s} := by
  rw [listener, RSA.pragmaticListener_uniformOn_real_lt_iff (t₀ := s)
    (by rw [speaker_full]; exact RSA.uniformSpeaker_apply_singleton_ne_zero sem hα.le hu),
    speaker_full]
  exact RSA.uniformSpeaker_real_singleton_lt_of_trueChoices_ssubset sem hα hu h

end Model

/-! ### The alternatives of section 1.1, for three objects -/

/-- The quantifier alternatives *none*, *some*, *all*. -/
inductive QUtt where
  | none_
  | some_
  | all
  deriving DecidableEq, Fintype

instance : MeasurableSpace QUtt := ⊤
instance : DiscreteMeasurableSpace QUtt := ⟨fun _ ↦ trivial⟩

/-- The states at which a quantifier holds of the three objects, the row of its tree of
numbers. -/
def QUtt.extension : QUtt → Finset (Fin 4)
  | .none_ => NumberTree.no.row 3
  | .some_ => NumberTree.some.row 3
  | .all => NumberTree.all.row 3

/-- The numeral alternatives *one*, *two*, *three*. -/
inductive NumUtt where
  | one
  | two
  | three
  deriving DecidableEq, Fintype

instance : MeasurableSpace NumUtt := ⊤
instance : DiscreteMeasurableSpace NumUtt := ⟨fun _ ↦ trivial⟩

/-- The number a numeral names. -/
def NumUtt.value : NumUtt → ℕ
  | .one => 1
  | .two => 2
  | .three => 3

/-- The states at which a numeral holds of the three objects on the lower-bounded meaning of
[horn-1972], its number or more. -/
def NumUtt.extension (u : NumUtt) : Finset (Fin 4) :=
  (NumberTree.cardinal (Degree.Comparison.ge.interval u.value)).row 3

theorem NumUtt.mem_extension {u : NumUtt} {s : Fin 4} : s ∈ u.extension ↔ u.value ≤ s := by
  simp [NumUtt.extension]

theorem NumUtt.isUpperSet_extension (u : NumUtt) : IsUpperSet (u.extension : Set (Fin 4)) :=
  fun _ _ hab ha ↦ NumUtt.mem_extension.2 ((NumUtt.mem_extension.1 ha).trans (Fin.le_def.1 hab))

/-! ### The predictions of section 1.1, for every rationality -/

section Findings

variable {α : ℝ}

/-- The fully informed speaker at two objects says *one* or *two*. -/
private theorem informed_two_add_le :
    (RSA.uniformSpeaker NumUtt.extension α 2).real {.one} +
      (RSA.uniformSpeaker NumUtt.extension α 2).real {.two} ≤ 1 := by
  simpa using RSA.sum_uniformSpeaker_real_singleton_le_one NumUtt.extension α 2 {.one, .two}

variable (hα : 0 < α)
include hα

/-- With complete access *some* is read as *some but not all*; the state with two objects is more
probable than the state with three, where the speaker could have said *all*. -/
theorem some_full :
    (listener QUtt.extension α 3 .some_).real {3} <
      (listener QUtt.extension α 3 .some_).real {2} :=
  listener_full_lt hα (by decide) (by decide)

/-- With access to one or two objects the implicature is canceled; the state with two objects is
no more probable than the state with three, since a speaker who has seen only objects with the
property can say nothing stronger than *some*. -/
theorem some_partial {n : ℕ} (hn : n = 1 ∨ n = 2) :
    (listener QUtt.extension α n .some_).real {2} ≤
      (listener QUtt.extension α n .some_).real {3} := by
  have h3 : speaker QUtt.extension α n 3 {.some_} = 1 := by
    rw [show (3 : Fin 4) = Fin.last 3 from rfl, speaker_last (by omega)]
    rcases hn with rfl | rfl
    · rw [obsSpeaker_apply_eq_uniformSpeaker hα (by decide) (s := 1) (by decide)]
      exact RSA.uniformSpeaker_apply_singleton_eq_one _ hα (by decide) (by decide)
    · rw [obsSpeaker_apply_eq_uniformSpeaker hα (by decide) (s := 2) (by decide)]
      exact RSA.uniformSpeaker_apply_singleton_eq_one _ hα (by decide) (by decide)
  rw [listener, RSA.pragmaticListener_uniformOn_real_le_iff (t₀ := 3) (h3 ▸ one_ne_zero),
    measureReal_def (speaker QUtt.extension α n 3), h3, ENNReal.toReal_one]
  exact speaker_real_singleton_le_one _ _

/-- With complete access *two* is read as *exactly two*; the state with two objects is more
probable than the state with three, where the speaker could have said *three*. -/
theorem two_full :
    (listener NumUtt.extension α 3 .two).real {3} <
      (listener NumUtt.extension α 3 .two).real {2} :=
  listener_full_lt hα (by decide) (by decide)

/-- With complete access *one* is read as *exactly one*; the state with one object is more
probable than a state with more. -/
theorem one_full {s : Fin 4} (hs : 1 < s) :
    (listener NumUtt.extension α 3 .one).real {s} <
      (listener NumUtt.extension α 3 .one).real {1} :=
  listener_full_lt hα (by decide) (by revert s; decide)

/-- With partial access the numeral speaker draws her observation and speaks as one who knows
it to be the state. -/
private theorem numeral_speaker_real {n : ℕ} (hn : n ≤ 3) (s : Fin 4) (u : NumUtt) :
    (speaker NumUtt.extension α n s).real {u} = ∑ k, (hypergeometric 3 n s).real {k} *
      (RSA.uniformSpeaker NumUtt.extension α k).real {u} := by
  rw [speaker_of_isUpperSet hα NumUtt.isUpperSet_extension hn, Kernel.comp_real_singleton]

/-- When all three objects have the property, the speaker may use any numeral up to the number
she looks at. -/
private theorem numeral_speaker_three_ne_zero {n : ℕ} (hn : n ≤ 3) {u : NumUtt}
    (hu : u.value ≤ n) : speaker NumUtt.extension α n 3 {u} ≠ 0 := by
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, speaker_last hn,
    obsSpeaker_apply_of_isUpperSet (n := n) hα NumUtt.isUpperSet_extension le_rfl hn]
  exact RSA.uniformSpeaker_apply_singleton_ne_zero _ hα.le (NumUtt.mem_extension.2 hu)

/-- The fully informed speaker at no objects has no numeral to use. -/
private theorem informed_zero (u : NumUtt) :
    (RSA.uniformSpeaker NumUtt.extension α 0).real {u} = 0 :=
  RSA.uniformSpeaker_real_singleton_eq_zero _ hα (by cases u <;> decide)

/-- The fully informed speaker at one object says *one*. -/
private theorem informed_one_one : (RSA.uniformSpeaker NumUtt.extension α 1).real {.one} = 1 := by
  rw [measureReal_def, RSA.uniformSpeaker_apply_singleton_eq_one _ hα (by decide) (by decide),
    ENNReal.toReal_one]

private theorem informed_one_two : (RSA.uniformSpeaker NumUtt.extension α 1).real {.two} = 0 :=
  RSA.uniformSpeaker_real_singleton_eq_zero _ hα (by decide)

/-- The fully informed speaker at two objects prefers *two* to *one*, the more informative
numeral. -/
private theorem informed_two_lt :
    (RSA.uniformSpeaker NumUtt.extension α 2).real {.one} <
      (RSA.uniformSpeaker NumUtt.extension α 2).real {.two} :=
  RSA.uniformSpeaker_real_singleton_lt_of_card_lt _ hα (by decide) (by decide) (by decide)

/-- After one object *one* carries no implicature; a state with more objects with the property is
at least as probable, since the speaker says *one* exactly when the object she looks at has the
property. -/
theorem one_minimal {s s' : Fin 4} (h : s ≤ s') :
    (listener NumUtt.extension α 1 .one).real {s} ≤
      (listener NumUtt.extension α 1 .one).real {s'} := by
  have key (s : Fin 4) : (speaker NumUtt.extension α 1 s).real {.one} = ((s : ℕ) : ℝ) / 3 := by
    simp [numeral_speaker_real hα, Fin.sum_univ_four, hypergeometric_real_singleton,
      hypergeometricCount, informed_zero hα, informed_one_one hα]
  rw [listener, RSA.pragmaticListener_uniformOn_real_le_iff
    (numeral_speaker_three_ne_zero hα (by norm_num) (by decide)), key, key]
  gcongr
  exact_mod_cast h

/-- After two objects *two* carries no implicature; the state with two objects is no more
probable than the state with three, since the speaker says *two* only when both objects she
looks at have the property. -/
theorem two_partial :
    (listener NumUtt.extension α 2 .two).real {2} ≤
      (listener NumUtt.extension α 2 .two).real {3} := by
  rw [listener, RSA.pragmaticListener_uniformOn_real_le_iff
    (numeral_speaker_three_ne_zero hα (by norm_num) (by decide))]
  simp [numeral_speaker_real hα, Fin.sum_univ_four, hypergeometric_real_singleton,
    hypergeometricCount, informed_zero hα, informed_one_two hα]
  linarith [measureReal_nonneg (μ := RSA.uniformSpeaker NumUtt.extension α 2) (s := {.two})]

/-- After two objects *one* keeps its implicature against three; the state with one object is
more probable than the state with three, where the speaker saw two objects with the property and
would rather have said *two*. -/
theorem one_partial_three :
    (listener NumUtt.extension α 2 .one).real {3} <
      (listener NumUtt.extension α 2 .one).real {1} := by
  rw [listener, RSA.pragmaticListener_uniformOn_real_lt_iff
    (numeral_speaker_three_ne_zero hα (by norm_num) (by decide))]
  simp [numeral_speaker_real hα, Fin.sum_univ_four, hypergeometric_real_singleton,
    hypergeometricCount, informed_zero hα, informed_one_one hα]
  linarith [informed_two_lt hα, informed_two_add_le (α := α)]

/-- After two objects *one* loses its implicature against two; the state with one object is no
more probable than the state with two, where the speaker may have seen only one object with the
property. -/
theorem one_partial_two :
    (listener NumUtt.extension α 2 .one).real {1} ≤
      (listener NumUtt.extension α 2 .one).real {2} := by
  rw [listener, RSA.pragmaticListener_uniformOn_real_le_iff
    (numeral_speaker_three_ne_zero hα (by norm_num) (by decide))]
  simp [numeral_speaker_real hα, Fin.sum_univ_four, hypergeometric_real_singleton,
    hypergeometricCount, informed_zero hα, informed_one_one hα]

end Findings

end GoodmanStuhlmuller2013
