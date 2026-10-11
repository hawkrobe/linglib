module

public import Linglib.Pragmatics.RSA.Basic

/-!
# Sikos, Venhuizen, Drenhaus and Crocker (2021): Reevaluating Pragmatic Reasoning in Language Games

Sikos and colleagues compare the rational speech act model of Frank and Goodman with a baseline
in one-shot reference games. RSA's listener inverts, against a salience prior, a speaker who
chooses among the words true of the referent in proportion to their informativity, the
reciprocal of the size of each word's extension. The baseline keeps the Bayesian inversion but
replaces that speaker by literal meaning alone, a uniform choice among the words true of the
referent. A display is a model `d` whose three positions each have a colour and a shape, and the
extension `d.sem u` of a word is the set of positions with the colour or the shape it names.

## Main statements

* `baselineListener_eq_listener_truthful`: when every object has the same number of true words,
  one colour and one shape in the paper's displays, the baseline is RSA's literal listener at
  the salience prior.
* `rsaListener_apply_singleton_of_eq_singleton`, `rsaListener_apply_singleton_of_notMem` and
  their baseline twins: the two models agree wherever a word is true of a single object or false
  of an object, the predictions of one hundred and of zero percent.
* `solvable_rsa_prefers`, `solvable_baseline_indifferent`, `reducible_rsa_prefers`: in the
  pragmatically solvable and reducible displays RSA prefers the pragmatic referent to the
  competitor, where the baseline is at chance.
* `rsaListener_real_lt_iff`: listener preference compares prior mass times speaker likelihood,
  so a salient competitor wins exactly when its prior advantage exceeds the likelihood ratio.

## Implementation notes

* Fit statistics stay in prose. Across three experiments the baseline fit listener choices at
  least as well as RSA overall; RSA fit better only for a color word in pragmatically solvable
  contexts (Experiments 2 and 3), and in the pragmatically reducible contexts listeners chose the
  salient competitor, which RSA predicts only because the prior reverses its speaker's
  preference. The theory predicts where the models can differ, not which fits better.
* The contexts are indexed by position, the objects by their color and shape, so that the two
  identical pragmatic referents of a reducible context are distinct positions.

## References

* [sikos-etal-2021]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace SikosEtAl2021

section General

variable {W U : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W] [Fintype U]
  [MeasurableSpace U] [DiscreteMeasurableSpace U] (sem : U → Set W)

/-- The literal listener with the uniform prior, RSA's `L0`. -/
noncomputable def L0 : Kernel U W := listener Measure.count (truthful sem)

instance : IsFiniteKernel (L0 sem) := inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

theorem L0_apply_singleton_of_notMem {w : W} {u : U} (h : w ∉ sem u) : L0 sem u {w} = 0 :=
  listener_truthful_apply_singleton_of_notMem Measure.count sem h

variable [Fintype W]

/-- The informative speaker (3) is the best response to `L0` at rationality one and constant
cost, choosing among the words true of the referent in proportion to their informativity. -/
noncomputable def rsaSpeaker : Kernel W U := speaker 1 0 (L0 sem) Measure.dirac

instance : IsFiniteKernel (rsaSpeaker sem) := inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

/-- The baseline speaker (4) uses literal meaning alone, choosing uniformly among the words true
of the referent. -/
noncomputable def baselineSpeaker : Kernel W U :=
  Kernel.ofWeights fun w u ↦ (sem u).indicator 1 w

instance : IsFiniteKernel (baselineSpeaker sem) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

theorem L0_apply_singleton {w : W} {u : U} (h : w ∈ sem u) :
    L0 sem u {w} = (Measure.count (sem u))⁻¹ := by
  rw [L0, listener_truthful_apply_singleton Measure.count sem h, Measure.count_singleton,
    mul_one]

theorem L0_ne_zero {w : W} {u : U} (h : w ∈ sem u) : L0 sem u {w} ≠ 0 := by
  rw [L0_apply_singleton sem h]
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

/-- A word false of a referent is never produced for it. -/
theorem rsaSpeaker_apply_singleton_of_notMem {w : W} {u : U} (h : w ∉ sem u) :
    rsaSpeaker sem w {u} = 0 :=
  speaker_dirac_apply_singleton_eq_zero one_pos (L0_apply_singleton_of_notMem sem h)

theorem rsaSpeaker_apply_singleton_ne_zero {w : W} {u : U} (h : w ∈ sem u) :
    rsaSpeaker sem w {u} ≠ 0 :=
  speaker_dirac_apply_singleton_ne_zero zero_le_one (L0_ne_zero sem h)

theorem baselineSpeaker_apply_singleton_of_notMem {w : W} {u : U} (h : w ∉ sem u) :
    baselineSpeaker sem w {u} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by simp [Set.indicator_of_notMem h])

theorem baselineSpeaker_apply_singleton_ne_zero {w : W} {u : U} (h : w ∈ sem u) :
    baselineSpeaker sem w {u} ≠ 0 :=
  Kernel.ofWeights_apply_singleton_ne_zero (by simp [Set.indicator_of_mem h]) fun u' ↦ by
    by_cases h' : w ∈ sem u' <;> simp [h']

/-! ### The listeners -/

section Listener

variable [StandardBorelSpace W] [Nonempty W] (μ : Measure W) [IsFiniteMeasure μ]

/-- RSA's listener (1) inverts the informative speaker against the salience prior. -/
noncomputable def rsaListener : Kernel U W := (rsaSpeaker sem)†μ

/-- The baseline literal listener model (4) inverts the baseline speaker against the salience
prior. -/
noncomputable def baselineListener : Kernel U W := (baselineSpeaker sem)†μ

/-- In a trivial condition the word is true of one object of positive prior mass, and RSA is
certain of it, a prediction of one hundred percent. -/
theorem rsaListener_apply_singleton_of_eq_singleton {u : U} {w₀ : W} (h : sem u = {w₀})
    (hμ : μ {w₀} ≠ 0) : rsaListener sem μ u {w₀} = 1 :=
  posterior_apply_singleton_eq_one _ μ
    (fun w hw ↦ rsaSpeaker_apply_singleton_of_notMem sem (by rw [h]; exact hw))
    (rsaSpeaker_apply_singleton_ne_zero sem (by rw [h]; exact Set.mem_singleton w₀)) hμ

/-- In a trivial condition the baseline is certain of the same object. -/
theorem baselineListener_apply_singleton_of_eq_singleton {u : U} {w₀ : W} (h : sem u = {w₀})
    (hμ : μ {w₀} ≠ 0) : baselineListener sem μ u {w₀} = 1 :=
  posterior_apply_singleton_eq_one _ μ
    (fun w hw ↦ baselineSpeaker_apply_singleton_of_notMem sem (by rw [h]; exact hw))
    (baselineSpeaker_apply_singleton_ne_zero sem (by rw [h]; exact Set.mem_singleton w₀)) hμ

/-- An object the word is false of gets no mass under RSA, a prediction of zero percent. -/
theorem rsaListener_apply_singleton_of_notMem {u : U} {w w' : W} (hw : w ∉ sem u)
    (hw' : w' ∈ sem u) (hμ' : μ {w'} ≠ 0) : rsaListener sem μ u {w} = 0 :=
  posterior_apply_singleton_eq_zero _ μ
    (comp_apply_singleton_ne_zero _ _ hμ' (rsaSpeaker_apply_singleton_ne_zero sem hw'))
    (rsaSpeaker_apply_singleton_of_notMem sem hw)

/-- An excluded object gets no mass under the baseline either. -/
theorem baselineListener_apply_singleton_of_notMem {u : U} {w w' : W} (hw : w ∉ sem u)
    (hw' : w' ∈ sem u) (hμ' : μ {w'} ≠ 0) : baselineListener sem μ u {w} = 0 :=
  posterior_apply_singleton_eq_zero _ μ
    (comp_apply_singleton_ne_zero _ _ hμ' (baselineSpeaker_apply_singleton_ne_zero sem hw'))
    (baselineSpeaker_apply_singleton_of_notMem sem hw)

/-- Listener preference between two objects compares prior mass times speaker likelihood, so a
salient competitor wins against the informative speaker's preferred referent exactly when its
prior advantage exceeds the likelihood ratio. -/
theorem rsaListener_real_lt_iff {u : U} {w₀ : W} (hw₀ : w₀ ∈ sem u) (hμ₀ : μ {w₀} ≠ 0)
    (w₁ w₂ : W) :
    (rsaListener sem μ u).real {w₁} < (rsaListener sem μ u).real {w₂} ↔
      μ.real {w₁} * (rsaSpeaker sem w₁).real {u} < μ.real {w₂} * (rsaSpeaker sem w₂).real {u} := by
  have hx := comp_apply_singleton_ne_zero _ _ hμ₀ (rsaSpeaker_apply_singleton_ne_zero sem hw₀)
  simpa [rsaListener] using posterior_real_finset_lt_iff (rsaSpeaker sem) μ hx {w₁} {w₂}

end Listener

/-! ### The words true of an object -/

variable [∀ u, DecidablePred (· ∈ sem u)]

/-- The words true of an object, the paper's `W(r)`. -/
def applicable (w : W) : Finset U := Finset.univ.filter fun u ↦ w ∈ sem u

/-- The baseline speaker's probability of a true word is the reciprocal of the number of words
true of the referent. -/
theorem baselineSpeaker_apply_singleton {w : W} {u : U} (h : w ∈ sem u) :
    baselineSpeaker sem w {u} = ((applicable sem w).card : ℝ≥0∞)⁻¹ := by
  rw [baselineSpeaker, Kernel.ofWeights_apply_singleton, Set.indicator_of_mem h, Pi.one_apply,
    applicable]
  simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole, one_div]

/-- The real value of the literal listener with the uniform prior. -/
theorem L0_toReal (u : U) (w : W) :
    (L0 sem u {w}).toReal = if w ∈ sem u then 1 / ((sem u).toFinset.card : ℝ) else 0 := by
  have hcount : Measure.count (sem u) = ((sem u).toFinset.card : ℝ≥0∞) := by
    rw [← Measure.count_apply_finset, Set.coe_toFinset]
  split_ifs with h
  · rw [L0_apply_singleton sem h, hcount, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  · rw [L0_apply_singleton_of_notMem sem h, ENNReal.toReal_zero]

/-- When every object has the same number of true words, one color and one shape in the paper's
displays, the baseline listener is RSA's literal listener with the salience prior, that is, `L0`
itself informed by the prior. -/
theorem baselineListener_eq_listener_truthful [StandardBorelSpace W] [Nonempty W]
    (μ : Measure W) [IsFiniteMeasure μ] {k : ℕ} (hk : k ≠ 0)
    (hcard : ∀ w, (applicable sem w).card = k) {u : U} (hμ : μ (sem u) ≠ 0) (w : W) :
    baselineListener sem μ u {w} = listener μ (truthful sem) u {w} := by
  have hrow (w' : W) :
      baselineSpeaker sem w' {u} = (sem u).indicator (fun _ ↦ (k : ℝ≥0∞)⁻¹) w' := by
    by_cases h : w' ∈ sem u
    · rw [baselineSpeaker_apply_singleton sem h, hcard, Set.indicator_of_mem h]
    · rw [baselineSpeaker_apply_singleton_of_notMem sem h, Set.indicator_of_notMem h]
  have hk' : (k : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hk'' : (k : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hk)
  have hcomp : (baselineSpeaker sem ∘ₘ μ) {u} = μ (sem u) * (k : ℝ≥0∞)⁻¹ := by
    rw [Measure.comp_apply_singleton]
    simp_rw [hrow, Set.indicator_apply, mul_ite, mul_zero]
    rw [← Finset.sum_filter, ← Finset.sum_mul, sum_measure_singleton]
    congr 2
    ext x
    simp
  have hx : (baselineSpeaker sem ∘ₘ μ) {u} ≠ 0 := by rw [hcomp]; exact mul_ne_zero hμ hk'
  by_cases h : w ∈ sem u
  · rw [baselineListener, posterior_apply_singleton _ _ hx, hcomp, hrow w, Set.indicator_of_mem h,
      listener_truthful_apply_singleton μ sem h, ENNReal.mul_div_mul_right _ _ hk' hk'',
      div_eq_mul_inv, mul_comm]
  · rw [baselineListener, posterior_apply_singleton _ _ hx, hrow w, Set.indicator_of_notMem h,
      listener_truthful_apply_singleton_of_notMem μ sem h]
    simp

end General

/-! ### The pragmatic conditions of Experiment 1 -/

section Contexts

/-- The colors of the examples. -/
inductive Color
  | blue | green
  deriving DecidableEq, Fintype, Repr

/-- The shapes of the examples. -/
inductive Shape
  | boot | mitt
  deriving DecidableEq, Fintype, Repr

/-- A word is a color word or a shape word. -/
inductive Word
  | color (c : Color) | shape (s : Shape)
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- A display is a model with three positions, each with a color and a shape. -/
structure Display where
  color : Fin 3 → Color
  shape : Fin 3 → Shape

/-- The lexical entries. In a display a color word is true of the positions with that color, and
a shape word of the positions with that shape. -/
def Display.sem (d : Display) : Word → Set (Fin 3)
  | .color c => {i | d.color i = c}
  | .shape s => {i | d.shape i = s}

instance (d : Display) : ∀ u : Word, DecidablePred (· ∈ d.sem u)
  | .color c, i => inferInstanceAs (Decidable (d.color i = c))
  | .shape s, i => inferInstanceAs (Decidable (d.shape i = s))

theorem sum_word (f : Word → ℝ) :
    ∑ u, f u = f (.color .blue) + f (.color .green) + f (.shape .boot) + f (.shape .mitt) := by
  rw [show (Finset.univ : Finset Word) =
      {.color .blue, .color .green, .shape .boot, .shape .mitt} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  ring

/-- Every object has exactly two applicable words, its color and its shape. -/
theorem card_applicable (d : Display) (i : Fin 3) : (applicable d.sem i).card = 2 := by
  rw [show applicable d.sem i = {Word.color (d.color i), Word.shape (d.shape i)} from ?_,
    Finset.card_pair (by simp)]
  ext u
  rcases u with c | s <;> simp [applicable, Display.sem, eq_comm]

variable (d : Display)

/-- The speaker's real probability of a word at a position, in terms of the literal listener. -/
theorem rsaSpeaker_real (i : Fin 3) (u : Word) :
    (rsaSpeaker d.sem i).real {u} =
      (L0 d.sem u {i}).toReal / ∑ u', (L0 d.sem u' {i}).toReal := by
  rw [rsaSpeaker, speaker_dirac_zero_real_singleton zero_le_one]
  simp only [ENNReal.rpow_one]

/-- In the pragmatically solvable display of Tables 5 and 9 the blue boot is the pragmatic
referent, the blue mitt the color competitor, and the green boot the shape competitor. -/
def solvable : Display := ⟨![.blue, .blue, .green], ![.boot, .mitt, .boot]⟩

/-- With a uniform prior, RSA prefers the pragmatic referent to the color competitor on hearing
the color word, since for the blue mitt the speaker had the more informative *mitt*. -/
theorem solvable_rsa_prefers :
    (rsaListener solvable.sem Measure.count (.color .blue)).real {1} <
      (rsaListener solvable.sem Measure.count (.color .blue)).real {0} := by
  have hb : (solvable.sem (.color .blue)).toFinset.card = 2 := by decide
  have hg : (solvable.sem (.color .green)).toFinset.card = 1 := by decide
  have hbo : (solvable.sem (.shape .boot)).toFinset.card = 2 := by decide
  have hmi : (solvable.sem (.shape .mitt)).toFinset.card = 1 := by decide
  rw [rsaListener_real_lt_iff _ _ (w₀ := 0) (by decide)
      (by simp),
    rsaSpeaker_real, rsaSpeaker_real]
  simp only [sum_word, L0_toReal, hb, hg, hbo, hmi, measureReal_def,
    Measure.count_singleton]
  rw [ite_eq_left (by decide : (1 : Fin 3) ∈ solvable.sem (.color .blue)),
    ite_eq_right (by decide : (1 : Fin 3) ∉ solvable.sem (.color .green)),
    ite_eq_right (by decide : (1 : Fin 3) ∉ solvable.sem (.shape .boot)),
    ite_eq_left (by decide : (1 : Fin 3) ∈ solvable.sem (.shape .mitt)),
    ite_eq_left (by decide : (0 : Fin 3) ∈ solvable.sem (.color .blue)),
    ite_eq_right (by decide : (0 : Fin 3) ∉ solvable.sem (.color .green)),
    ite_eq_left (by decide : (0 : Fin 3) ∈ solvable.sem (.shape .boot)),
    ite_eq_right (by decide : (0 : Fin 3) ∉ solvable.sem (.shape .mitt))]
  norm_num

/-- The baseline is at chance between the two blue objects. -/
theorem solvable_baseline_indifferent :
    baselineListener solvable.sem Measure.count (.color .blue) {0} =
      baselineListener solvable.sem Measure.count (.color .blue) {1} := by
  have h0 : (0 : Fin 3) ∈ solvable.sem (.color .blue) := by decide
  have h1 : (1 : Fin 3) ∈ solvable.sem (.color .blue) := by decide
  refine posterior_apply_singleton_congr _ _
    (comp_apply_singleton_ne_zero _ _ (w := 0) (by simp)
      (baselineSpeaker_apply_singleton_ne_zero _ h0)) ?_ (by simp)
  simp only [baselineSpeaker_apply_singleton _ h0, baselineSpeaker_apply_singleton _ h1,
    card_applicable]

/-- The pragmatically reducible display of Tables 4 and 8 has two blue boots, the pragmatic
referents, and a blue mitt, the competitor with the unique feature. -/
def reducible : Display := ⟨![.blue, .blue, .blue], ![.boot, .boot, .mitt]⟩

/-- With a uniform prior, RSA prefers each pragmatic referent to the competitor on hearing the
color word, which applies to all three, so pragmatic reasoning reduces the ambiguity without
resolving it. -/
theorem reducible_rsa_prefers :
    (rsaListener reducible.sem Measure.count (.color .blue)).real {2} <
      (rsaListener reducible.sem Measure.count (.color .blue)).real {0} := by
  have hb : (reducible.sem (.color .blue)).toFinset.card = 3 := by decide
  have hg : (reducible.sem (.color .green)).toFinset.card = 0 := by decide
  have hbo : (reducible.sem (.shape .boot)).toFinset.card = 2 := by decide
  have hmi : (reducible.sem (.shape .mitt)).toFinset.card = 1 := by decide
  rw [rsaListener_real_lt_iff _ _ (w₀ := 0) (by decide)
      (by simp),
    rsaSpeaker_real, rsaSpeaker_real]
  simp only [sum_word, L0_toReal, hb, hg, hbo, hmi, measureReal_def,
    Measure.count_singleton]
  rw [ite_eq_left (by decide : (2 : Fin 3) ∈ reducible.sem (.color .blue)),
    ite_eq_right (by decide : (2 : Fin 3) ∉ reducible.sem (.color .green)),
    ite_eq_right (by decide : (2 : Fin 3) ∉ reducible.sem (.shape .boot)),
    ite_eq_left (by decide : (2 : Fin 3) ∈ reducible.sem (.shape .mitt)),
    ite_eq_left (by decide : (0 : Fin 3) ∈ reducible.sem (.color .blue)),
    ite_eq_right (by decide : (0 : Fin 3) ∉ reducible.sem (.color .green)),
    ite_eq_left (by decide : (0 : Fin 3) ∈ reducible.sem (.shape .boot)),
    ite_eq_right (by decide : (0 : Fin 3) ∉ reducible.sem (.shape .mitt))]
  norm_num

end Contexts

end SikosEtAl2021
