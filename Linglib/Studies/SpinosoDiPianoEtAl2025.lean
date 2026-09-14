import Linglib.Studies.KaoGoodman2015

/-!
# Spinoso-Di Piano, Austin, Piantanida and Cheung (2025): (RSA)²

This file formalizes the rhetorical-strategy-aware Rational Speech Act framework of
[spinoso-di-piano-etal-2025] on the RSA kernel pipeline. The framework replaces the Boolean
meaning of the literal listener by a rhetorical function, one graded meaning per rhetorical
strategy such as literalness, irony or hyperbole. A strategy-indexed literal listener, speaker
and pragmatic listener run the standard pipeline, and the listener averages the strategies
under a strategy posterior given the utterance (`listener`). Standard RSA assigns no mass to a
meaning outside the literal extension of the utterance (`L1_indicator_apply_singleton_of_notMem`,
the paper's Appendix A.2); a strategy's listener puts positive mass on a meaning exactly when
the prior does and the strategy's rhetorical function admits the meaning at the utterance
(`L1_apply_singleton_ne_zero_iff`), and the pragmatic listener does so through any strategy of
positive posterior weight (`listener_apply_singleton_ne_zero_iff`).

The speaker with an utterance prior is the Frank–Goodman speaker with the utility log of the
literal listener's mass less a cost, at the utterance prior `exp (−α · cost)`
(`S1_eq_speakerOfScore`, Appendix A.1). Against question-under-discussion RSA, the affect-aware
model of [kao-goodman-2015] and [kao-etal-2014-hyperbole], every QUD-RSA literal listener, the
projected listener normalized over meanings, is an (RSA)² literal listener whose rhetorical
function is the projected mass over the prior (`L0_rhetoricalOfQUD`, Lemma 1), and the model
of [kao-goodman-2015] is such an instance (`kaoGoodman2015_L0`). The QUD-RSA literal listeners
of a finite meaning space form a finite set while (RSA)² realizes every distribution, so some
(RSA)² literal listener is no QUD-RSA literal listener (`exists_not_mem_qudListeners`,
Lemma 2). On the running example, *the weather is amazing* in a blizzard with the literal and
ironic strategies over the weather scale of [kao-goodman-2015], the literal strategy leaves
terrible weather with no mass, the ironic strategy gives it positive mass, and the pragmatic
listener reads the utterance as terrible weather exactly when the strategy posterior admits
irony (`literal_amazing_terrible`, `irony_amazing_terrible`, `listener_amazing_terrible_iff`).

## Implementation notes

The context of the paper's conditional probabilities indexes the prior, the utterance prior,
the rhetorical functions and the strategy posterior; every statement holds at a fixed context,
so the context is not represented. The paper's Definition 1 normalizes the projected literal
listener over meanings, so Lemma 1 is stated for the normalized `RSA.projListener`; the speaker
of [kao-goodman-2015] reads the unnormalized cell mass, which the definition does not cover.
The fitted rhetorical functions and strategy posteriors of the paper's experiments, the
comparison with affect-aware RSA on the number and weather data, and the language-model
listeners of its Section 5 are not formalized.

## References

* [spinoso-di-piano-etal-2025]
* [kao-goodman-2015]
* [kao-etal-2014-hyperbole]
* [frank-goodman-2012]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace SpinosoDiPianoEtAl2025

universe v

variable {M U R : Type*} [Fintype M] [MeasurableSpace M] [DiscreteMeasurableSpace M]
  [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

/-! ### The framework -/

section Framework

/-- The strategy-indexed literal listener (eq. 4): the prior reweighted by the rhetorical
function of the strategy. -/
noncomputable def L0 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (r : R) : Kernel U M :=
  literalListener μ (f r)

/-- The strategy-indexed speaker (eq. 5): the best response to the strategy's literal listener,
with the utterance prior as the cost factor. -/
noncomputable def S1 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (π : U → ℝ≥0∞) (r : R) :
    Kernel M U :=
  speaker α π (L0 μ f r)

instance (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (π : U → ℝ≥0∞) (r : R) :
    IsFiniteKernel (S1 μ f α π r) :=
  inferInstanceAs (IsFiniteKernel (speaker α π (L0 μ f r)))

/-- The strategy-indexed pragmatic listener (eq. 6). -/
noncomputable def L1 [Nonempty M] (μ : Measure M) [IsFiniteMeasure μ] (f : R → U → M → ℝ≥0∞)
    (α : ℝ) (π : U → ℝ≥0∞) (r : R) : Kernel U M :=
  pragmaticListener α π (L0 μ f r) μ

/-- The pragmatic listener (eq. 7): the strategy-indexed listeners averaged under the strategy
posterior given the utterance. -/
noncomputable def listener [Nonempty M] [MeasurableSpace R] (μ : Measure M) [IsFiniteMeasure μ]
    (f : R → U → M → ℝ≥0∞) (α : ℝ) (π : U → ℝ≥0∞) (ρ : Kernel U R) : Kernel U M :=
  Kernel.ofFunOfCountable λ u => (ρ u).bind λ r => L1 μ f α π r u

variable (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (π : U → ℝ≥0∞)

theorem L0_apply_singleton (r : R) (u : U) (m : M) :
    L0 μ f r u {m} = f r u m * μ {m} / ∑ m', f r u m' * μ {m'} :=
  literalListener_apply_singleton μ (f r) u m

/-- The speaker with an utterance prior is the Frank–Goodman speaker (Appendix A.1): the
softmax at rationality `α` of the utility log of the literal listener's mass less a cost is
the speaker whose utterance prior is `exp (−α · cost)`. -/
theorem S1_eq_speakerOfScore (κ : U → ℝ) (r : R) :
    S1 μ f α (λ u => ENNReal.ofReal (Real.exp (-(α * κ u)))) r =
      speakerOfScore λ m u => ENNReal.log (L0 μ f r u {m}) * α - ↑(α * κ u) := by
  rw [S1, speaker_eq_speakerOfScore]
  congr 1
  funext m u
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, EReal.coe_neg, sub_eq_add_neg]

variable [IsFiniteMeasure μ]

/-- A meaning has positive literal mass under a strategy exactly when the prior and the
strategy's rhetorical function do. -/
theorem L0_apply_singleton_ne_zero_iff {r : R} {u : U} (hf : ∀ m, f r u m ≠ ∞) (m : M) :
    L0 μ f r u {m} ≠ 0 ↔ f r u m ≠ 0 ∧ μ {m} ≠ 0 := by
  rw [L0_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, not_or, not_or]
  exact ⟨λ h => h.1, λ h => ⟨h, ENNReal.sum_ne_top.mpr λ m' _ =>
    ENNReal.mul_ne_top (hf m') (measure_ne_top _ _)⟩⟩

/-- A strategy's speaker produces an utterance at a meaning exactly when the meaning has
positive prior and the strategy's rhetorical function admits it at the utterance. -/
theorem S1_apply_singleton_ne_zero_iff (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0) (hπ : ∀ u, π u ≠ ∞)
    {r : R} (hf : ∀ u m, f r u m ≠ ∞) (m : M) (u : U) :
    S1 μ f α π r m {u} ≠ 0 ↔ f r u m ≠ 0 ∧ μ {m} ≠ 0 := by
  rw [← L0_apply_singleton_ne_zero_iff μ f (hf u)]
  exact ⟨λ h h' => h (speaker_apply_singleton_eq_zero hα h'),
    speaker_apply_singleton_ne_zero hα.le hπ0 hπ λ u' => literalListener_apply_le_one μ (f r) u' _⟩

/-- An utterance some meaning of positive prior admits under a strategy has a positive
marginal. -/
theorem comp_S1_ne_zero (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0) (hπ : ∀ u, π u ≠ ∞) {r : R}
    (hf : ∀ u m, f r u m ≠ ∞) {u : U} (hu : ∃ m, f r u m ≠ 0 ∧ μ {m} ≠ 0) :
    (S1 μ f α π r ∘ₘ μ) {u} ≠ 0 := by
  obtain ⟨m, hm, hμ⟩ := hu
  exact comp_apply_singleton_ne_zero _ _ hμ
    ((S1_apply_singleton_ne_zero_iff μ f α π hα hπ0 hπ hf m u).mpr ⟨hm, hμ⟩)

variable [Nonempty M]

/-- A strategy's pragmatic listener puts positive mass on a meaning exactly when the prior does
and the strategy's rhetorical function admits the meaning at the utterance: the framework
escapes the literal extension. -/
theorem L1_apply_singleton_ne_zero_iff (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0) (hπ : ∀ u, π u ≠ ∞)
    {r : R} (hf : ∀ u m, f r u m ≠ ∞) {u : U} (hu : ∃ m, f r u m ≠ 0 ∧ μ {m} ≠ 0) (m : M) :
    L1 μ f α π r u {m} ≠ 0 ↔ f r u m ≠ 0 ∧ μ {m} ≠ 0 := by
  have h := posterior_apply_singleton_ne_zero_iff (S1 μ f α π r) μ
    (comp_S1_ne_zero μ f α π hα hπ0 hπ hf hu) m
  rw [S1_apply_singleton_ne_zero_iff μ f α π hα hπ0 hπ hf] at h
  exact h.trans ⟨λ h => h.2, λ h => ⟨h.2, h⟩⟩

/-- Standard RSA gives no mass to non-literal meanings (Appendix A.2): under a strategy whose
rhetorical function is a Boolean meaning, a meaning outside the extension of the utterance
has no listener mass once some meaning in the extension has prior mass. -/
theorem L1_indicator_apply_singleton_of_notMem (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0)
    (hπ : ∀ u, π u ≠ ∞) (sem : U → Set M) {r : R} (hr : f r = λ u => (sem u).indicator 1)
    {u : U} {m : M} (hm : m ∉ sem u) {m' : M} (hm' : m' ∈ sem u) (hμ : μ {m'} ≠ 0) :
    L1 μ f α π r u {m} = 0 := by
  rw [L1, L0, hr]
  exact pragmaticListener_literalListener_indicator_apply_singleton_of_notMem α π μ hα hπ0 hπ
    sem hm hm' hμ

variable [Fintype R] [MeasurableSpace R] [DiscreteMeasurableSpace R]

theorem listener_apply_singleton (ρ : Kernel U R) (u : U) (m : M) :
    listener μ f α π ρ u {m} = ∑ r, L1 μ f α π r u {m} * ρ u {r} := by
  rw [listener, Kernel.ofFunOfCountable_apply,
    Measure.bind_apply (.singleton m) Measurable.of_discrete.aemeasurable, lintegral_fintype]

/-- The pragmatic listener puts positive mass on a meaning exactly when some strategy of
positive posterior weight does. -/
theorem listener_apply_singleton_ne_zero_iff (ρ : Kernel U R) (u : U) (m : M) :
    listener μ f α π ρ u {m} ≠ 0 ↔ ∃ r, ρ u {r} ≠ 0 ∧ L1 μ f α π r u {m} ≠ 0 := by
  simp only [listener_apply_singleton, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ,
    true_implies, mul_eq_zero, not_forall, not_or]
  exact exists_congr λ r => and_comm

/-- The pragmatic listener interprets an utterance as a meaning of positive prior exactly when
some strategy of positive posterior weight admits the meaning at the utterance. -/
theorem listener_apply_singleton_ne_zero_iff' (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0)
    (hπ : ∀ u, π u ≠ ∞) (hf : ∀ r u m, f r u m ≠ ∞) (ρ : Kernel U R) {u : U}
    (hu : ∀ r, ∃ m, f r u m ≠ 0 ∧ μ {m} ≠ 0) (m : M) :
    listener μ f α π ρ u {m} ≠ 0 ↔ μ {m} ≠ 0 ∧ ∃ r, ρ u {r} ≠ 0 ∧ f r u m ≠ 0 := by
  rw [listener_apply_singleton_ne_zero_iff]
  simp only [L1_apply_singleton_ne_zero_iff μ f α π hα hπ0 hπ (hf _) (hu _)]
  exact ⟨λ ⟨r, hr, hfr, hm⟩ => ⟨hm, r, hr, hfr⟩, λ ⟨hm, r, hr, hfr⟩ => ⟨r, hr, hfr, hm⟩⟩

end Framework

/-! ### Question-under-discussion RSA as a special case -/

section QUD

variable {G X : Type*} (μ : Measure M) [IsFiniteMeasure μ]

/-- The rhetorical function of a question (eq. 19): the projected literal mass of the meaning's
cell over the prior, scaled by a constant that keeps it in the unit interval. -/
noncomputable def rhetoricalOfQUD (project : G → M → X) (L : Kernel U M) (k : ℝ≥0∞) (g : G)
    (u : U) (m : M) : ℝ≥0∞ :=
  projListener project L g u {m} / (k * μ {m})

/-- Lemma 1: the QUD-RSA literal listener of a question, the projected listener normalized
over meanings, is the (RSA)² literal listener of the question's rhetorical function, at a
prior of positive mass everywhere. -/
theorem L0_rhetoricalOfQUD (hμ : ∀ m, μ {m} ≠ 0) (project : G → M → X) (L : Kernel U M)
    {k : ℝ≥0∞} (hk0 : k ≠ 0) (hk : k ≠ ∞) (g : G) (u : U) :
    L0 μ (rhetoricalOfQUD μ project L k) g u = (projListener project L g u)[|Set.univ] := by
  have h : rhetoricalOfQUD μ project L k g =
      λ u m => k⁻¹ * (projListener project L g u {m} / μ {m}) := by
    funext u m
    rw [rhetoricalOfQUD, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hk0) (Or.inl hk),
      mul_assoc, ← ENNReal.div_eq_inv_mul (a := projListener project L g u {m})]
  rw [L0, h, literalListener_const_mul μ _ (ENNReal.inv_ne_zero.mpr hk)
    (ENNReal.inv_ne_top.mpr hk0), literalListener_div μ hμ (projListener project L g)]

/-- The affect-aware model of [kao-goodman-2015] is an instance: its projected literal
listener under each question, normalized over meanings, is an (RSA)² literal listener. -/
theorem kaoGoodman2015_L0 (μ : Measure KaoGoodman2015.Meaning) [IsFiniteMeasure μ]
    (hμ : ∀ m, μ {m} ≠ 0) {k : ℝ≥0∞} (hk0 : k ≠ 0) (hk : k ≠ ∞) (q : KaoGoodman2015.QUD)
    (u : KaoGoodman2015.Weather) :
    L0 μ (rhetoricalOfQUD μ KaoGoodman2015.project (KaoGoodman2015.L0 μ) k) q u =
      (projListener KaoGoodman2015.project (KaoGoodman2015.L0 μ) q u)[|Set.univ] :=
  L0_rhetoricalOfQUD μ hμ _ _ hk0 hk q u

/-- The QUD-RSA literal listeners of a literal listener (eq. 13): the projected listeners
normalized over meanings, over every question and utterance. -/
def qudListeners (L : Kernel U M) : Set (Measure M) :=
  {ν | ∃ (X : Type v) (q : M → X) (u : U), ν = (projListener id L q u)[|Set.univ]}

omit [DiscreteMeasurableSpace M] in
/-- A QUD-RSA literal listener depends on the question only through the cells it induces, so
the QUD-RSA literal listeners of a finite meaning space are finitely many. -/
theorem qudListeners_finite [MeasurableSingletonClass M] (L : Kernel U M) :
    (qudListeners.{v} L).Finite :=
  (Set.finite_range λ p : U × (M → Set M) =>
      (∑ m, L p.1 (p.2 m) • Measure.dirac m)[|Set.univ]).subset <| by
    rintro ν ⟨X, q, u, rfl⟩
    exact ⟨(u, λ m => q ⁻¹' {q m}), rfl⟩

/-- Every probability vector over meanings is an (RSA)² literal listener at a prior of positive
mass everywhere: the rhetorical function is the vector over the prior. -/
theorem L0_div_apply_singleton (hμ : ∀ m, μ {m} ≠ 0) (p : M → ℝ≥0∞) (hp : ∑ m, p m = 1) (r : R)
    (u : U) (m : M) : L0 μ (λ _ _ m => p m / μ {m}) r u {m} = p m := by
  rw [L0_apply_singleton]
  simp_rw [ENNReal.div_mul_cancel (hμ _) (measure_ne_top μ _)]
  rw [hp, div_one]

/-- Lemma 2: over a meaning space with two meanings, at a prior of positive mass everywhere,
some (RSA)² literal listener is no QUD-RSA literal listener of any question at any utterance,
since the latter are finitely many and the former realize every distribution. -/
theorem exists_not_mem_qudListeners [Nontrivial M] (hμ : ∀ m, μ {m} ≠ 0) (L : Kernel U M) :
    ∃ f : R → U → M → ℝ≥0∞, ∀ r u, L0 μ f r u ∉ qudListeners.{v} L := by
  obtain ⟨m₁, m₂, hne⟩ := exists_pair_ne M
  set ν : ℝ≥0∞ → Measure M := λ t => t • Measure.dirac m₁ + (1 - t) • Measure.dirac m₂ with hν
  have hval : ∀ t ∈ Set.Ioo (0 : ℝ≥0∞) 1, (ν t)[|Set.univ] {m₁} = t := λ t ht => by
    have huniv : ν t Set.univ = 1 := by
      simp [hν, add_tsub_cancel_of_le ht.2.le]
    rw [cond_apply MeasurableSet.univ, huniv, inv_one, one_mul, Set.univ_inter]
    simp [hν, Set.indicator, hne.symm]
  have hinj : Set.InjOn (λ t => (ν t)[|Set.univ]) (Set.Ioo 0 1) := λ a ha b hb h => by
    have h' : (ν a)[|Set.univ] = (ν b)[|Set.univ] := h
    rw [← hval a ha, ← hval b hb, h']
  have hinf : (Set.image (λ t => (ν t)[|Set.univ]) (Set.Ioo 0 1)).Infinite :=
    (Set.Ioo_infinite zero_lt_one).image hinj
  obtain ⟨_, ⟨t, -, rfl⟩, hnot⟩ := (hinf.sdiff (qudListeners_finite L)).nonempty
  refine ⟨λ _ _ m => ν t {m} / μ {m}, λ r u => ?_⟩
  rwa [L0, literalListener_div μ hμ (λ _ => ν t)]

end QUD

/-! ### The running example -/

section Weather

open KaoGoodman2015 (Weather)

/-- The rhetorical strategies of the weather experiment. -/
inductive Strategy
  | literal | irony
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Strategy := ⊤
instance : DiscreteMeasurableSpace Strategy := ⟨λ _ => trivial⟩

/-- The antonym on the weather scale. -/
def opposite : Weather → Weather
  | .terrible => .amazing
  | .bad => .good
  | .neutral => .neutral
  | .good => .bad
  | .amazing => .terrible

/-- The rhetorical functions of the running example: the literal strategy names the state, the
ironic strategy its antonym. -/
noncomputable def weatherF : Strategy → Weather → Weather → ℝ≥0∞
  | .literal, u => ({u} : Set Weather).indicator 1
  | .irony, u => ({opposite u} : Set Weather).indicator 1

theorem weatherF_ne_top (r : Strategy) (u m : Weather) : weatherF r u m ≠ ∞ := by
  cases r <;> simp only [weatherF, Set.indicator_apply] <;> split_ifs <;> simp

variable (μ : Measure Weather) [IsFiniteMeasure μ] (α : ℝ) (π : Weather → ℝ≥0∞)

/-- Under the literal strategy, *the weather is amazing* leaves terrible weather with no
mass, the standard RSA prediction. -/
theorem literal_amazing_terrible (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0) (hπ : ∀ u, π u ≠ ∞)
    (hμ : μ {.amazing} ≠ 0) : L1 μ weatherF α π .literal .amazing {.terrible} = 0 :=
  L1_indicator_apply_singleton_of_notMem μ weatherF α π hα hπ0 hπ (λ u => {u}) rfl
    (Set.mem_singleton_iff.not.mpr (by decide)) (Set.mem_singleton _) hμ

/-- Under the ironic strategy, *the weather is amazing* gives terrible weather positive mass
whenever the prior does. -/
theorem irony_amazing_terrible (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0) (hπ : ∀ u, π u ≠ ∞)
    (hμ : μ {.terrible} ≠ 0) : L1 μ weatherF α π .irony .amazing {.terrible} ≠ 0 :=
  (L1_apply_singleton_ne_zero_iff μ weatherF α π hα hπ0 hπ (weatherF_ne_top .irony)
    ⟨.terrible, by simp [weatherF, opposite], hμ⟩ _).mpr ⟨by simp [weatherF, opposite], hμ⟩

/-- The pragmatic listener reads *the weather is amazing* as terrible weather exactly when the
strategy posterior gives irony positive weight, at a prior positive at terrible and amazing
weather. -/
theorem listener_amazing_terrible_iff (hα : 0 < α) (hπ0 : ∀ u, π u ≠ 0) (hπ : ∀ u, π u ≠ ∞)
    (ρ : Kernel Weather Strategy) (hμt : μ {.terrible} ≠ 0) (hμa : μ {.amazing} ≠ 0) :
    listener μ weatherF α π ρ .amazing {.terrible} ≠ 0 ↔ ρ .amazing {.irony} ≠ 0 := by
  rw [listener_apply_singleton_ne_zero_iff' μ weatherF α π hα hπ0 hπ weatherF_ne_top ρ
    (λ r => by
      cases r
      · exact ⟨.amazing, by simp [weatherF], hμa⟩
      · exact ⟨.terrible, by simp [weatherF, opposite], hμt⟩)]
  constructor
  · rintro ⟨-, _ | _, hr, hf⟩
    · exact absurd hf (by simp [weatherF])
    · exact hr
  · exact λ h => ⟨hμt, .irony, h, by simp [weatherF, opposite]⟩

end Weather

end SpinosoDiPianoEtAl2025
