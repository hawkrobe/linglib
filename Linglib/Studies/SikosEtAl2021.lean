import Linglib.Pragmatics.RSA.Basic

/-!
# Sikos, Venhuizen, Drenhaus and Crocker (2021): Reevaluating Pragmatic Reasoning in Language Games

This file formalizes the paper's baseline model and its relation to the rational speech act model
of [frank-goodman-2012] in one-shot reference games. RSA's listener (1) is the Bayesian inverse,
against a salience prior, of a speaker (3) who chooses among the words that apply to the referent
in proportion to their informativity, the reciprocal of the number of objects each applies to;
that speaker is the best response at rationality one to the literal listener with a uniform
prior (`L0`, `rsaSpeaker`, `rsaListener`). The baseline literal listener model (4) keeps the
Bayesian structure but replaces the speaker by literal meaning alone, a uniform choice among the
applicable words (`baselineSpeaker`, `baselineListener`). Since every object of the paper's
displays has one color and one shape, the baseline is RSA's literal listener with the salience
prior (`baselineListener_eq_literalListener`), and the two models agree wherever a word applies
to a single object or fails to apply, the predictions of one hundred and of zero percent that
dominate the original materials (`rsaListener_apply_singleton_of_eq_singleton`,
`baselineListener_apply_singleton_of_eq_singleton`, `rsaListener_apply_singleton_of_notMem`,
`baselineListener_apply_singleton_of_notMem`). The models differ only in the pragmatic
conditions: in a pragmatically solvable context the informative speaker makes RSA prefer the
pragmatic referent to the color competitor where the baseline is at chance
(`solvable_rsa_prefers`, `solvable_baseline_indifferent`), and in a pragmatically reducible
context it makes RSA prefer the two pragmatic referents to the competitor
(`reducible_rsa_prefers`). Listener preference is the comparison of prior mass times speaker
likelihood (`rsaListener_real_lt_iff`), so a salient competitor overrides the informative
speaker exactly when its prior advantage exceeds the likelihood ratio, the way the prior
reverses RSA's pragmatic component in the reducible conditions (§7.2).

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

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace SikosEtAl2021

section General

variable {W U : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
  [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U] (sem : U → Set W)

/-- The uniform prior over the objects of the display. -/
noncomputable def uniform : Measure W := priorOfWeights λ _ => 1

instance : IsFiniteMeasure (uniform (W := W)) :=
  inferInstanceAs (IsFiniteMeasure (priorOfWeights _))

/-- The literal listener with the uniform prior, RSA's `L0`. -/
noncomputable def L0 : Kernel U W := literalListener uniform λ u => (sem u).indicator 1

/-- The informative speaker (3): the best response to `L0` at rationality one and constant
cost, choosing among the applicable words in proportion to their informativity. -/
noncomputable def rsaSpeaker : Kernel W U := speaker 1 1 (L0 sem)

instance : IsFiniteKernel (rsaSpeaker sem) := inferInstanceAs (IsFiniteKernel (speaker _ _ _))

/-- The baseline speaker (4): literal meaning alone, a uniform choice among the words that
apply to the referent. -/
noncomputable def baselineSpeaker : Kernel W U :=
  Kernel.ofWeights λ w u => (sem u).indicator 1 w

instance : IsFiniteKernel (baselineSpeaker sem) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

theorem L0_apply_singleton {w : W} {u : U} (h : w ∈ sem u) :
    L0 sem u {w} = (uniform (sem u))⁻¹ := by
  rw [L0, literalListener_indicator_apply_singleton uniform sem h, uniform,
    priorOfWeights_singleton, Nat.cast_one, mul_one]

theorem L0_apply_singleton_of_notMem {w : W} {u : U} (h : w ∉ sem u) : L0 sem u {w} = 0 :=
  literalListener_indicator_apply_singleton_of_notMem uniform sem h

theorem L0_le_one (u : U) (w : W) : L0 sem u {w} ≤ 1 := by
  by_cases h : w ∈ sem u
  · exact literalListener_indicator_apply_singleton_le_one uniform sem (measure_ne_top _ _) h
  · rw [L0_apply_singleton_of_notMem sem h]; exact zero_le_one

theorem L0_ne_zero {w : W} {u : U} (h : w ∈ sem u) : L0 sem u {w} ≠ 0 := by
  rw [L0_apply_singleton sem h]
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

/-- A word that does not apply to a referent is never produced for it. -/
theorem rsaSpeaker_apply_singleton_of_notMem {w : W} {u : U} (h : w ∉ sem u) :
    rsaSpeaker sem w {u} = 0 :=
  speaker_apply_singleton_eq_zero one_pos (L0_apply_singleton_of_notMem sem h)

theorem rsaSpeaker_apply_singleton_ne_zero {w : W} {u : U} (h : w ∈ sem u) :
    rsaSpeaker sem w {u} ≠ 0 :=
  speaker_apply_singleton_ne_zero zero_le_one (λ _ => one_ne_zero) (λ _ => ENNReal.one_ne_top)
    (L0_le_one sem · w) (L0_ne_zero sem h)

theorem baselineSpeaker_apply_singleton_of_notMem {w : W} {u : U} (h : w ∉ sem u) :
    baselineSpeaker sem w {u} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by simp [Set.indicator_of_notMem h])

variable [∀ u, DecidablePred (· ∈ sem u)]

/-- The words applying to an object, the paper's `W(r)`. -/
def applicable (w : W) : Finset U := Finset.univ.filter λ u => w ∈ sem u

/-- The baseline speaker's probability of an applicable word is the reciprocal of the number of
words applying to the referent. -/
theorem baselineSpeaker_apply_singleton {w : W} {u : U} (h : w ∈ sem u) :
    baselineSpeaker sem w {u} = ((applicable sem w).card : ℝ≥0∞)⁻¹ := by
  rw [baselineSpeaker, Kernel.ofWeights_apply_singleton, Set.indicator_of_mem h, Pi.one_apply,
    applicable]
  simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole, one_div]

theorem baselineSpeaker_apply_singleton_ne_zero {w : W} {u : U} (h : w ∈ sem u) :
    baselineSpeaker sem w {u} ≠ 0 := by
  rw [baselineSpeaker_apply_singleton sem h]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

omit [∀ u, DecidablePred (· ∈ sem u)] in
/-- The uniform prior counts the objects of a set. -/
theorem uniform_apply (s : Set W) [DecidablePred (· ∈ s)] :
    uniform s = ((Finset.univ.filter (· ∈ s)).card : ℝ≥0∞) := by
  rw [uniform, priorOfWeights, Measure.finsetSum_apply]
  simp only [Nat.cast_one, one_smul, Measure.dirac_apply' _ (MeasurableSet.of_discrete),
    Set.indicator_apply, Pi.one_apply, Finset.sum_boole]

/-- The real value of the literal listener with the uniform prior. -/
theorem L0_toReal (u : U) (w : W) :
    (L0 sem u {w}).toReal =
      if w ∈ sem u then 1 / ((Finset.univ.filter (· ∈ sem u)).card : ℝ) else 0 := by
  split_ifs with h
  · rw [L0_apply_singleton sem h, uniform_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      one_div]
  · rw [L0_apply_singleton_of_notMem sem h, ENNReal.toReal_zero]

/-! ### The listeners -/

omit [Fintype W] [DiscreteMeasurableSpace W] in
/-- A kernel whose column at `x` vanishes at a state gives that state no posterior mass, once
some state has positive prior mass and positive column. -/
theorem posterior_apply_singleton_eq_zero [StandardBorelSpace W] [Nonempty W] {κ : Kernel W U}
    [IsFiniteKernel κ] (μ : Measure W) [IsFiniteMeasure μ] {u : U} {w w' : W}
    (hκ : κ w {u} = 0) (hμ' : μ {w'} ≠ 0) (hκ' : κ w' {u} ≠ 0) : (κ†μ) u {w} = 0 := by
  rw [posterior_apply_singleton _ _ (comp_apply_singleton_ne_zero _ _ hμ' hκ'), hκ]
  simp

omit [DiscreteMeasurableSpace W] in
/-- A kernel whose column at `x` is supported on a single state of positive prior mass inverts
to certainty about that state. -/
theorem posterior_apply_singleton_eq_one [StandardBorelSpace W] [Nonempty W] {κ : Kernel W U}
    [IsFiniteKernel κ] (μ : Measure W) [IsFiniteMeasure μ] {u : U} {w₀ : W}
    (hsupp : ∀ w ≠ w₀, κ w {u} = 0) (hκ : κ w₀ {u} ≠ 0) (hμ : μ {w₀} ≠ 0) :
    (κ†μ) u {w₀} = 1 := by
  have hcomp : (κ ∘ₘ μ) {u} = μ {w₀} * κ w₀ {u} := by
    rw [Measure.comp_apply_singleton]
    exact Finset.sum_eq_single w₀ (λ w _ hw => by rw [hsupp w hw, mul_zero])
      (λ h => absurd (Finset.mem_univ _) h)
  rw [posterior_apply_singleton _ _ (by rw [hcomp]; exact mul_ne_zero hμ hκ), hcomp]
  exact ENNReal.div_self (mul_ne_zero hμ hκ)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))

variable [StandardBorelSpace W] [Nonempty W] (μ : Measure W) [IsFiniteMeasure μ]

/-- RSA's listener (1): the inverse of the informative speaker against the salience prior. -/
noncomputable def rsaListener : Kernel U W := pragmaticListener 1 1 (L0 sem) μ

/-- The baseline literal listener model (4): the inverse of the baseline speaker against the
salience prior. -/
noncomputable def baselineListener : Kernel U W := (baselineSpeaker sem)†μ

omit [∀ u, DecidablePred (· ∈ sem u)] in
/-- A trivial condition: the word applies to one object of positive prior mass, and RSA is
certain of it, a prediction of one hundred percent. -/
theorem rsaListener_apply_singleton_of_eq_singleton {u : U} {w₀ : W} (h : sem u = {w₀})
    (hμ : μ {w₀} ≠ 0) : rsaListener sem μ u {w₀} = 1 :=
  posterior_apply_singleton_eq_one μ
    (λ w hw => rsaSpeaker_apply_singleton_of_notMem sem (by rw [h]; exact hw))
    (rsaSpeaker_apply_singleton_ne_zero sem (by rw [h]; exact Set.mem_singleton w₀)) hμ

/-- In a trivial condition the baseline is certain of the same object. -/
theorem baselineListener_apply_singleton_of_eq_singleton {u : U} {w₀ : W} (h : sem u = {w₀})
    (hμ : μ {w₀} ≠ 0) : baselineListener sem μ u {w₀} = 1 :=
  posterior_apply_singleton_eq_one μ
    (λ w hw => baselineSpeaker_apply_singleton_of_notMem sem (by rw [h]; exact hw))
    (baselineSpeaker_apply_singleton_ne_zero sem (by rw [h]; exact Set.mem_singleton w₀)) hμ

omit [∀ u, DecidablePred (· ∈ sem u)] in
/-- An excluded object: a word that does not apply gives it no mass under RSA, a prediction of
zero percent. -/
theorem rsaListener_apply_singleton_of_notMem {u : U} {w w' : W} (hw : w ∉ sem u)
    (hw' : w' ∈ sem u) (hμ' : μ {w'} ≠ 0) : rsaListener sem μ u {w} = 0 :=
  posterior_apply_singleton_eq_zero μ (rsaSpeaker_apply_singleton_of_notMem sem hw) hμ'
    (rsaSpeaker_apply_singleton_ne_zero sem hw')

/-- An excluded object gets no mass under the baseline either. -/
theorem baselineListener_apply_singleton_of_notMem {u : U} {w w' : W} (hw : w ∉ sem u)
    (hw' : w' ∈ sem u) (hμ' : μ {w'} ≠ 0) : baselineListener sem μ u {w} = 0 :=
  posterior_apply_singleton_eq_zero μ (baselineSpeaker_apply_singleton_of_notMem sem hw) hμ'
    (baselineSpeaker_apply_singleton_ne_zero sem hw')

/-- When every object has the same number of applicable words, one color and one shape in the
paper's displays, the baseline listener is RSA's literal listener with the salience prior: the
baseline is `L0` itself, informed by the prior. -/
theorem baselineListener_eq_literalListener {k : ℕ} (hk : k ≠ 0)
    (hcard : ∀ w, (applicable sem w).card = k) {u : U} (hμ : μ (sem u) ≠ 0) (w : W) :
    baselineListener sem μ u {w} = literalListener μ (λ u => (sem u).indicator 1) u {w} := by
  have hrow : ∀ w', baselineSpeaker sem w' {u} = (sem u).indicator (λ _ => (k : ℝ≥0∞)⁻¹) w' := by
    intro w'
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
      literalListener_indicator_apply_singleton μ sem h, ENNReal.mul_div_mul_right _ _ hk' hk'',
      div_eq_mul_inv, mul_comm]
  · rw [baselineListener, posterior_apply_singleton _ _ hx, hrow w, Set.indicator_of_notMem h,
      literalListener_indicator_apply_singleton_of_notMem μ sem h]
    simp

omit [∀ u, DecidablePred (· ∈ sem u)] in
/-- Listener preference between two objects is the comparison of prior mass times speaker
likelihood: a salient competitor wins against the informative speaker's preferred referent
exactly when its prior advantage exceeds the likelihood ratio. -/
theorem rsaListener_real_lt_iff {u : U} {w₀ : W} (hw₀ : w₀ ∈ sem u) (hμ₀ : μ {w₀} ≠ 0)
    (w₁ w₂ : W) :
    (rsaListener sem μ u).real {w₁} < (rsaListener sem μ u).real {w₂} ↔
      μ.real {w₁} * (rsaSpeaker sem w₁).real {u} < μ.real {w₂} * (rsaSpeaker sem w₂).real {u} := by
  have hx := comp_apply_singleton_ne_zero _ _ hμ₀ (rsaSpeaker_apply_singleton_ne_zero sem hw₀)
  show (((rsaSpeaker sem)†μ) u).real {w₁} < (((rsaSpeaker sem)†μ) u).real {w₂} ↔ _
  simpa using posterior_real_finset_lt_iff (rsaSpeaker sem) μ hx {w₁} {w₂}

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
instance : DiscreteMeasurableSpace Word := ⟨λ _ => trivial⟩

/-- A display: three positions, each with a color and a shape. -/
structure Display where
  color : Fin 3 → Color
  shape : Fin 3 → Shape

/-- The positions of a display a word applies to. -/
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
  rw [rsaSpeaker,
    speaker_real_singleton (cost := 1) zero_le_one (λ _ => ENNReal.one_ne_top) (L0_le_one _ · i)]
  simp only [ENNReal.rpow_one, Pi.one_apply, ENNReal.toReal_one, mul_one]

/-- The pragmatically solvable display of Tables 5 and 9: the blue boot is the pragmatic
referent, the blue mitt the color competitor, the green boot the shape competitor. -/
def solvable : Display := ⟨![.blue, .blue, .green], ![.boot, .mitt, .boot]⟩

/-- With a uniform prior, RSA prefers the pragmatic referent to the color competitor on hearing
the color word: for the blue mitt the speaker had the more informative *mitt*. -/
theorem solvable_rsa_prefers :
    (rsaListener solvable.sem uniform (.color .blue)).real {1} <
      (rsaListener solvable.sem uniform (.color .blue)).real {0} := by
  have hb : (Finset.univ.filter (· ∈ solvable.sem (.color .blue))).card = 2 := by decide
  have hg : (Finset.univ.filter (· ∈ solvable.sem (.color .green))).card = 1 := by decide
  have hbo : (Finset.univ.filter (· ∈ solvable.sem (.shape .boot))).card = 2 := by decide
  have hmi : (Finset.univ.filter (· ∈ solvable.sem (.shape .mitt))).card = 1 := by decide
  rw [rsaListener_real_lt_iff _ _ (w₀ := 0) (by decide)
      (by rw [uniform, priorOfWeights_singleton]; simp),
    rsaSpeaker_real, rsaSpeaker_real]
  simp only [sum_word, L0_toReal, hb, hg, hbo, hmi, uniform, measureReal_def,
    priorOfWeights_singleton, Nat.cast_one]
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
    baselineListener solvable.sem uniform (.color .blue) {0} =
      baselineListener solvable.sem uniform (.color .blue) {1} := by
  have h0 : (0 : Fin 3) ∈ solvable.sem (.color .blue) := by decide
  have h1 : (1 : Fin 3) ∈ solvable.sem (.color .blue) := by decide
  refine posterior_apply_singleton_congr _ _
    (comp_apply_singleton_ne_zero _ _ (w := 0) (by rw [uniform, priorOfWeights_singleton]; simp)
      (baselineSpeaker_apply_singleton_ne_zero _ h0)) ?_ (by simp [uniform])
  simp only [baselineSpeaker_apply_singleton _ h0, baselineSpeaker_apply_singleton _ h1,
    card_applicable]

/-- The pragmatically reducible display of Tables 4 and 8: two blue boots, the pragmatic
referents, and a blue mitt, the competitor with the unique feature. -/
def reducible : Display := ⟨![.blue, .blue, .blue], ![.boot, .boot, .mitt]⟩

/-- With a uniform prior, RSA prefers each pragmatic referent to the competitor on hearing the
color word, which applies to all three: pragmatic reasoning reduces the ambiguity without
resolving it. -/
theorem reducible_rsa_prefers :
    (rsaListener reducible.sem uniform (.color .blue)).real {2} <
      (rsaListener reducible.sem uniform (.color .blue)).real {0} := by
  have hb : (Finset.univ.filter (· ∈ reducible.sem (.color .blue))).card = 3 := by decide
  have hg : (Finset.univ.filter (· ∈ reducible.sem (.color .green))).card = 0 := by decide
  have hbo : (Finset.univ.filter (· ∈ reducible.sem (.shape .boot))).card = 2 := by decide
  have hmi : (Finset.univ.filter (· ∈ reducible.sem (.shape .mitt))).card = 1 := by decide
  rw [rsaListener_real_lt_iff _ _ (w₀ := 0) (by decide)
      (by rw [uniform, priorOfWeights_singleton]; simp),
    rsaSpeaker_real, rsaSpeaker_real]
  simp only [sum_word, L0_toReal, hb, hg, hbo, hmi, uniform, measureReal_def,
    priorOfWeights_singleton, Nat.cast_one]
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
