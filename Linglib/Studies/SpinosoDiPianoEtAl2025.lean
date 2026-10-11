module

public import Linglib.Studies.KaoGoodman2015

/-!
# Spinoso-Di Piano, Austin, Piantanida and Cheung (2025): (RSA)²: A Rhetorical-Strategy-Aware Rational Speech Act Framework for Figurative Language Understanding

The framework replaces the Boolean meaning of the literal listener by a rhetorical function, one
graded meaning per rhetorical strategy such as literalness, irony or hyperbole. A strategy-indexed
literal listener, speaker and pragmatic listener run the standard pipeline (`L0`, `S1`, `L1`),
and the listener averages the strategies under a strategy posterior given the utterance
(`listener`).

## Main results

* `L1_indicator_apply_singleton_of_notMem`, `L1_apply_singleton_ne_zero_iff`: standard RSA gives
  no mass to a meaning outside the literal extension of the utterance, while a strategy's listener
  gives a meaning mass exactly when the prior does and the strategy's rhetorical function admits
  it.
* `L0_rhetoricalOfQUD`: every literal listener of question-under-discussion RSA is the literal
  listener of a rhetorical function, at a prior that is positive everywhere.
* `exists_not_mem_qudListeners`: over two or more meanings some literal listener of the framework
  is no literal listener of question-under-discussion RSA.
* `listener_amazing_terrible_iff`: in a blizzard, *the weather is amazing* is read as terrible
  weather exactly when the strategy posterior admits irony.

## Implementation notes

* The context of the paper's conditional probabilities indexes the prior, the utterance prior,
  the rhetorical functions and the strategy posterior. Every statement holds at a fixed context,
  so the context is not represented.
* The paper's first definition states the literal listener of question-under-discussion RSA as a
  distribution over meanings (`qudListener`). Kao and colleagues state it as a distribution over
  answers, the pushforward of the literal listener along the question. The two give a meaning's
  cell proportional mass, with a constant that depends on the utterance, so the speakers built on
  them differ.

## TODO

* The fitted rhetorical functions and strategy posteriors of the paper's experiments, the
  comparison with affect-aware RSA on the number and weather data, and the language-model
  listeners of its fifth section are not formalized.

## References

* [spinoso-di-piano-etal-2025]
* [kao-goodman-2015]
* [kao-etal-2014-hyperbole]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace SpinosoDiPianoEtAl2025

universe v

variable {M U R : Type*} [Fintype M] [MeasurableSpace M]
  [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

/-! ### The framework -/

section Framework

variable [DiscreteMeasurableSpace M]

/-- The strategy-indexed literal listener (eq. 4) reweights the prior by the rhetorical
function of the strategy. -/
noncomputable def L0 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (r : R) : Kernel U M :=
  Kernel.ofDensity μ (f r)

instance (μ : Measure M) (f : R → U → M → ℝ≥0∞) (r : R) : IsFiniteKernel (L0 μ f r) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

/-- The strategy-indexed speaker (eq. 5) is the best response to the strategy's literal
listener, less the utterance cost. -/
noncomputable def S1 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ) (r : R) :
    Kernel M U :=
  speaker α κ (L0 μ f r) Measure.dirac

instance (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ) (r : R) :
    IsFiniteKernel (S1 μ f α κ r) :=
  inferInstanceAs (IsFiniteKernel (speaker α κ (L0 μ f r) Measure.dirac))

/-- The strategy-indexed pragmatic listener (eq. 6). -/
noncomputable def L1 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ) (r : R) :
    Kernel U M :=
  RSA.listener μ (S1 μ f α κ r)

/-- The pragmatic listener (eq. 7) averages the strategy-indexed listeners under the strategy
posterior given the utterance. -/
noncomputable def listener [MeasurableSpace R] (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ)
    (κ : U → ℝ) (ρ : Kernel U R) : Kernel U M :=
  Kernel.ofFunOfCountable fun u ↦ (ρ u).bind fun r ↦ L1 μ f α κ r u

variable (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ)

theorem L0_apply_singleton (r : R) (u : U) (m : M) :
    L0 μ f r u {m} = f r u m * μ {m} / ∑ m', f r u m' * μ {m'} :=
  Kernel.ofDensity_apply_singleton μ (f r) u m

/-- The Frank–Goodman speaker is the speaker with an utterance prior (Appendix A.1). At
rationality `α ≠ 0` and the cost `−log π / α`, its weights are the literal listener's mass to
the power `α` times the utterance prior `π`. -/
theorem S1_eq_ofWeights_prior (hα : α ≠ 0) {π : U → ℝ≥0∞} (hπ0 : ∀ u, π u ≠ 0)
    (hπ : ∀ u, π u ≠ ∞) (r : R) :
    S1 μ f α (fun u ↦ -Real.log (π u).toReal / α) r =
      Kernel.ofWeights fun m u ↦ L0 μ f r u {m} ^ α * π u := by
  rw [S1, speaker_dirac_eq_ofWeights]
  congr 1
  funext m u
  rw [mul_div_cancel₀ _ hα, neg_neg, Real.exp_log (ENNReal.toReal_pos (hπ0 u) (hπ u)),
    ENNReal.ofReal_toReal (hπ u)]

/-- Standard RSA gives no mass to non-literal meanings (Appendix A.2). Under a strategy whose
rhetorical function is a Boolean meaning, a meaning outside the extension of the utterance has
no listener mass. -/
theorem L1_indicator_apply_singleton_of_notMem (hα : 0 < α) (sem : U → Set M) {r : R}
    (hr : f r = fun u ↦ (sem u).indicator 1) {u : U} {m : M} (hm : m ∉ sem u) :
    L1 μ f α κ r u {m} = 0 := by
  simp only [L1, S1, L0, hr, ← listener_truthful_eq_ofDensity]
  exact listener_speaker_listener_truthful_apply_singleton_of_notMem hα κ μ sem hm

section

variable [Fintype R] [MeasurableSpace R] [DiscreteMeasurableSpace R]

theorem listener_apply_singleton (ρ : Kernel U R) (u : U) (m : M) :
    listener μ f α κ ρ u {m} = ∑ r, L1 μ f α κ r u {m} * ρ u {r} := by
  rw [listener, Kernel.ofFunOfCountable_apply,
    Measure.bind_apply (.singleton m) Measurable.of_discrete.aemeasurable, lintegral_fintype]

/-- The pragmatic listener puts positive mass on a meaning exactly when some strategy of
positive posterior weight does. -/
theorem listener_apply_singleton_ne_zero_iff (ρ : Kernel U R) (u : U) (m : M) :
    listener μ f α κ ρ u {m} ≠ 0 ↔ ∃ r, ρ u {r} ≠ 0 ∧ L1 μ f α κ r u {m} ≠ 0 := by
  simp only [listener_apply_singleton, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ,
    true_implies, mul_eq_zero, not_forall, not_or]
  exact exists_congr fun r ↦ and_comm

end

variable [IsFiniteMeasure μ]

/-- A meaning has positive literal mass under a strategy exactly when the prior and the
strategy's rhetorical function do. -/
theorem L0_apply_singleton_ne_zero_iff {r : R} {u : U} (hf : ∀ m, f r u m ≠ ∞) (m : M) :
    L0 μ f r u {m} ≠ 0 ↔ f r u m ≠ 0 ∧ μ {m} ≠ 0 := by
  rw [L0_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, not_or, not_or]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, ENNReal.sum_ne_top.mpr fun m' _ ↦
    ENNReal.mul_ne_top (hf m') (measure_ne_top _ _)⟩⟩

/-- A strategy's speaker produces an utterance at a meaning exactly when the meaning has
positive prior and the strategy's rhetorical function admits it at the utterance. -/
theorem S1_apply_singleton_ne_zero_iff (hα : 0 < α) {r : R} (hf : ∀ u m, f r u m ≠ ∞) (m : M)
    (u : U) :
    S1 μ f α κ r m {u} ≠ 0 ↔ f r u m ≠ 0 ∧ μ {m} ≠ 0 := by
  rw [← L0_apply_singleton_ne_zero_iff μ f (hf u)]
  exact ⟨fun h h' ↦ h (speaker_dirac_apply_singleton_eq_zero hα h'),
    speaker_dirac_apply_singleton_ne_zero hα.le⟩

/-- A strategy's pragmatic listener puts positive mass on a meaning exactly when the prior does
and the strategy's rhetorical function admits the meaning at the utterance, so the framework
escapes the literal extension. -/
theorem L1_apply_singleton_ne_zero_iff (hα : 0 < α) {r : R} (hf : ∀ u m, f r u m ≠ ∞) (u : U)
    (m : M) : L1 μ f α κ r u {m} ≠ 0 ↔ f r u m ≠ 0 ∧ μ {m} ≠ 0 := by
  rw [L1, RSA.listener_apply_singleton_ne_zero_iff, S1_apply_singleton_ne_zero_iff μ f α κ hα hf]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.2, h⟩⟩

variable [Fintype R] [MeasurableSpace R] [DiscreteMeasurableSpace R]

/-- The pragmatic listener interprets an utterance as a meaning of positive prior exactly when
some strategy of positive posterior weight admits the meaning at the utterance. -/
theorem listener_apply_singleton_ne_zero_iff' (hα : 0 < α) (hf : ∀ r u m, f r u m ≠ ∞)
    (ρ : Kernel U R) (u : U) (m : M) :
    listener μ f α κ ρ u {m} ≠ 0 ↔ μ {m} ≠ 0 ∧ ∃ r, ρ u {r} ≠ 0 ∧ f r u m ≠ 0 := by
  rw [listener_apply_singleton_ne_zero_iff]
  simp only [L1_apply_singleton_ne_zero_iff μ f α κ hα (hf _)]
  exact ⟨fun ⟨r, hr, hfr, hm⟩ ↦ ⟨hm, r, hr, hfr⟩, fun ⟨hm, r, hr, hfr⟩ ↦ ⟨r, hr, hfr, hm⟩⟩

end Framework

/-! ### Question-under-discussion RSA as a special case -/

section QUD

/-- The literal listener of question-under-discussion RSA (eq. 13) gives a meaning mass
proportional to the literal listener's mass on the meanings with the same answer. -/
noncomputable def qudListener {X : Type*} (L : Kernel U M) (q : M → X) : Kernel U M :=
  Kernel.ofDensity Measure.count fun u m ↦ L u (q ⁻¹' {q m})

section

variable [DiscreteMeasurableSpace M] {G X : Type*} (μ : Measure M) [IsFiniteMeasure μ]

/-- The rhetorical function of a question (eq. 19) is the literal mass of the meaning's cell
over the prior, scaled by a constant that keeps it in the unit interval. -/
noncomputable def rhetoricalOfQUD (project : G → M → X) (L : Kernel U M) (k : ℝ≥0∞) (g : G)
    (u : U) (m : M) : ℝ≥0∞ :=
  L u (project g ⁻¹' {project g m}) / (k * μ {m})

/-- The literal listener of question-under-discussion RSA under a question is the literal
listener of the question's rhetorical function, at a prior of positive mass everywhere
(Lemma 1). -/
theorem L0_rhetoricalOfQUD (hμ : ∀ m, μ {m} ≠ 0) (project : G → M → X) (L : Kernel U M)
    {k : ℝ≥0∞} (hk0 : k ≠ 0) (hk : k ≠ ∞) (g : G) :
    L0 μ (rhetoricalOfQUD μ project L k) g = qudListener L (project g) := by
  have h : rhetoricalOfQUD μ project L k g =
      fun u m ↦ k⁻¹ * (L u (project g ⁻¹' {project g m}) / μ {m}) := by
    funext u m
    rw [rhetoricalOfQUD, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hk0) (Or.inl hk),
      mul_assoc, ← ENNReal.div_eq_inv_mul (a := L u (project g ⁻¹' {project g m}))]
  rw [L0, h, Kernel.ofDensity_const_mul μ _ (ENNReal.inv_ne_zero.mpr hk)
    (ENNReal.inv_ne_top.mpr hk0)]
  ext u : 1
  refine Measure.ext_of_singleton fun m ↦ ?_
  rw [qudListener, Kernel.ofDensity_apply_singleton, Kernel.ofDensity_apply_singleton]
  simp only [ENNReal.div_mul_cancel (hμ _) (measure_ne_top μ _), Measure.count_singleton, mul_one]

/-- The literal listener and the questions of [kao-goodman-2015] give literal listeners of
question-under-discussion RSA that are literal listeners of rhetorical functions. -/
theorem kaoGoodman2015_L0 (μ : Measure KaoGoodman2015.Meaning) [IsFiniteMeasure μ]
    (hμ : ∀ m, μ {m} ≠ 0) {k : ℝ≥0∞} (hk0 : k ≠ 0) (hk : k ≠ ∞) (q : KaoGoodman2015.QUD) :
    L0 μ (rhetoricalOfQUD μ KaoGoodman2015.project (KaoGoodman2015.L0 μ) k) q =
      qudListener (KaoGoodman2015.L0 μ) (KaoGoodman2015.project q) :=
  L0_rhetoricalOfQUD μ hμ _ _ hk0 hk q

end

/-- The literal listeners of question-under-discussion RSA over a literal listener, at every
question and utterance. -/
def qudListeners (L : Kernel U M) : Set (Measure M) :=
  {ν | ∃ (X : Type v) (q : M → X) (u : U), ν = qudListener L q u}

/-- A literal listener of question-under-discussion RSA depends on the question only through
the cells it induces, so over a finite meaning space there are finitely many. -/
theorem qudListeners_finite (L : Kernel U M) : (qudListeners.{v} L).Finite :=
  (Set.finite_range fun p : U × (M → Set M) ↦
      (Measure.count.withDensity fun m ↦ L p.1 (p.2 m))[|Set.univ]).subset <| by
    rintro ν ⟨X, q, u, rfl⟩
    exact ⟨(u, fun m ↦ q ⁻¹' {q m}), rfl⟩

variable [DiscreteMeasurableSpace M] (μ : Measure M) [IsFiniteMeasure μ]

/-- Every probability vector over meanings is a literal listener of the framework at a prior of
positive mass everywhere, whose rhetorical function is the vector over the prior. -/
theorem L0_div_apply_singleton (hμ : ∀ m, μ {m} ≠ 0) (p : M → ℝ≥0∞) (hp : ∑ m, p m = 1) (r : R)
    (u : U) (m : M) : L0 μ (fun _ _ m ↦ p m / μ {m}) r u {m} = p m := by
  rw [L0_apply_singleton]
  simp_rw [ENNReal.div_mul_cancel (hμ _) (measure_ne_top μ _)]
  rw [hp, div_one]

/-- Over a meaning space with two meanings, at a prior of positive mass everywhere, some literal
listener of the framework is no literal listener of question-under-discussion RSA at any question
and utterance, since the latter are finitely many and the former realize every distribution
(Lemma 2). -/
theorem exists_not_mem_qudListeners [Nontrivial M] (hμ : ∀ m, μ {m} ≠ 0) (L : Kernel U M) :
    ∃ f : R → U → M → ℝ≥0∞, ∀ r u, L0 μ f r u ∉ qudListeners.{v} L := by
  obtain ⟨m₁, m₂, hne⟩ := exists_pair_ne M
  set ν : ℝ≥0∞ → Measure M := fun t ↦ t • Measure.dirac m₁ + (1 - t) • Measure.dirac m₂ with hν
  have hval : ∀ t ∈ Set.Ioo (0 : ℝ≥0∞) 1, (ν t)[|Set.univ] {m₁} = t := fun t ht ↦ by
    have huniv : ν t Set.univ = 1 := by
      simp [hν, add_tsub_cancel_of_le ht.2.le]
    rw [cond_apply MeasurableSet.univ, huniv, inv_one, one_mul, Set.univ_inter]
    simp [hν, Set.indicator, hne.symm]
  have hinj : Set.InjOn (fun t ↦ (ν t)[|Set.univ]) (Set.Ioo 0 1) := fun a ha b hb h ↦ by
    have h' : (ν a)[|Set.univ] = (ν b)[|Set.univ] := h
    rw [← hval a ha, ← hval b hb, h']
  have hinf : (Set.image (fun t ↦ (ν t)[|Set.univ]) (Set.Ioo 0 1)).Infinite :=
    (Set.Ioo_infinite zero_lt_one).image hinj
  obtain ⟨_, ⟨t, -, rfl⟩, hnot⟩ := (hinf.sdiff (qudListeners_finite L)).nonempty
  refine ⟨fun _ _ m ↦ ν t {m} / μ {m}, fun r u ↦ ?_⟩
  rwa [L0, Kernel.ofDensity_div μ hμ (fun _ ↦ ν t)]

end QUD

/-! ### The running example -/

section Weather

open KaoGoodman2015 (Weather)

/-- The rhetorical strategies of the weather experiment. -/
inductive Strategy
  | literal | irony
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Strategy := ⊤
instance : DiscreteMeasurableSpace Strategy := ⟨fun _ ↦ trivial⟩

/-- The antonym on the weather scale. -/
def opposite : Weather → Weather
  | .terrible => .amazing
  | .bad => .good
  | .neutral => .neutral
  | .good => .bad
  | .amazing => .terrible

/-- In the running example the literal strategy names the state and the ironic strategy its
antonym. -/
noncomputable def weatherF : Strategy → Weather → Weather → ℝ≥0∞
  | .literal, u => ({u} : Set Weather).indicator 1
  | .irony, u => ({opposite u} : Set Weather).indicator 1

theorem weatherF_ne_top (r : Strategy) (u m : Weather) : weatherF r u m ≠ ∞ := by
  cases r <;> simp only [weatherF, Set.indicator_apply] <;> split_ifs <;> simp

variable (μ : Measure Weather) (α : ℝ) (κ : Weather → ℝ)

/-- Under the literal strategy, *the weather is amazing* leaves terrible weather with no
mass, the standard RSA prediction. -/
theorem literal_amazing_terrible (hα : 0 < α) :
    L1 μ weatherF α κ .literal .amazing {.terrible} = 0 :=
  L1_indicator_apply_singleton_of_notMem μ weatherF α κ hα (fun u ↦ {u}) rfl
    (Set.mem_singleton_iff.not.mpr (by decide))

variable [IsFiniteMeasure μ]

/-- Under the ironic strategy, *the weather is amazing* gives terrible weather positive mass
whenever the prior does. -/
theorem irony_amazing_terrible (hα : 0 < α) (hμ : μ {.terrible} ≠ 0) :
    L1 μ weatherF α κ .irony .amazing {.terrible} ≠ 0 :=
  (L1_apply_singleton_ne_zero_iff μ weatherF α κ hα (weatherF_ne_top .irony) _ _).mpr
    ⟨by simp [weatherF, opposite], hμ⟩

/-- The pragmatic listener reads *the weather is amazing* as terrible weather exactly when the
strategy posterior gives irony positive weight, at a prior positive at terrible and amazing
weather. -/
theorem listener_amazing_terrible_iff (hα : 0 < α) (ρ : Kernel Weather Strategy)
    (hμt : μ {.terrible} ≠ 0) :
    listener μ weatherF α κ ρ .amazing {.terrible} ≠ 0 ↔ ρ .amazing {.irony} ≠ 0 := by
  rw [listener_apply_singleton_ne_zero_iff' μ weatherF α κ hα weatherF_ne_top ρ]
  constructor
  · rintro ⟨-, _ | _, hr, hf⟩
    · exact absurd hf (by simp [weatherF])
    · exact hr
  · exact fun h ↦ ⟨hμt, .irony, h, by simp [weatherF, opposite]⟩

end Weather

end SpinosoDiPianoEtAl2025
