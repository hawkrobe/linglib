import Linglib.Core.LinearAlgebra.Matrix.Symmetric
import Linglib.Processing.Lexical.Discriminative.Coding
import Linglib.Processing.Lexical.Discriminative.Training
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Gahl and Baayen 2024: homophone duration without a stored lexicon

The paper reanalyses the Switchboard durations of the 409 English homophones of [gahl-2008]
(*time* ~ *thyme*) from a discriminative lexicon (`LinearDiscriminativeLexicon`, [baayen-2019]):
linear maps between triphone and embedding vectors, with no stored words and so no word to bear
a frequency. Frequency is treated as composite. *Practice* is frequency-informed learning of the
production map `G` (`IsFILTrainedOn`, [heitmeier-chuang-axen-baayen-2024]); *contextual
independence* is the diagonal `d` of a word-to-word map `W` with `UW = U` over an
utterance-by-word matrix `U`, transformed to `Cind` by (9); *semantic support for form* is the
support a word's own triphones receive from its meaning, the diagonal of `T = ĈCᵀ` (A5),
`semSupWord` at a word's meaning and form. In Gaussian location-scale GAMs the predictors
grounded in the model beat the localist ones (Table 5), homophone twins differ in duration, and
semantically similar twins are closer in duration. The GAM fits are outside the Processing
scope, and the paper derives nothing formal from its Pearson-correlation homophone similarity
(§3.4), so neither is stated here.

What is stated is the paper's own toy lexicon *time, lime, thyme* (§2.3), worked through the
substrate's training theory. The endstate map (4) and the frequency-informed map for token
frequencies 100, 10, 1 (A3) are certified `IsELTrainedOn` and `IsFILTrainedOn` by the
coordinate normal equations; the support matrix of (A6) and both columns of Table 1 come out
exactly, the frequency-informed column being `√frequency` times the support the learned map
alone gives, as it is the fitted value of the `√Q`-scaled regression; the homophones get
distinct predicted forms from identical triphones (Fig. A2); and the word-to-word map of (6) is,
exactly, the orthogonal projector onto the row space of `U`, whose diagonal therefore lies in
`[0, 1]` and dominates its rows and columns as the paper observes.

## Main results

* `endstate_isELTrainedOn`, `frequencyInformed_isFILTrainedOn`: the paper's mappings are the
  substrate's ERM solutions.
* `supportMatrix_endstate`, `semanticSupport_endstate`, `semanticSupportFIL_eq`: (A6) and
  Table 1 exactly; practice reverses the order of *time* and *thyme*
  (`semanticSupport_endstate_time_lt_thyme`, `semanticSupportFIL_thyme_lt_time`).
* `time_sub_thyme_notMem_ker`: the homophones leave the neutralization locus.
* `U_mul_W`, `isSymm_W`, `isIdempotentElem_W`, `le_diag_W`, `diag_W_mem_Icc`: the toy `W`
  and its diagonal; `strictAntiOn_cind`: the transform (9) reverses its order.

## References

* [S. Gahl and R. H. Baayen, *Time and thyme again: Connecting English spoken word duration to
  models of the mental lexicon* (2024)][gahl-baayen-2024]
* [S. Gahl, *Time and thyme are not homophones: The effect of lemma frequency on word durations
  in spontaneous speech* (2008)][gahl-2008]
* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan and J. P. Blevins, *The discriminative
  lexicon* (2019)][baayen-2019]
* [M. Heitmeier, Y.-Y. Chuang, S. D. Axen and R. H. Baayen, *Frequency effects in linear
  discriminative learning* (2024)][heitmeier-chuang-axen-baayen-2024]
-/

namespace GahlBaayen2024

open Processing.Lexical.Discriminative Matrix

noncomputable section

/-! ### The toy lexicon -/

/-- The phones of the toy lexicon, `i` standing for the paper's `ɪ`; the diphthong is written as
the two phones `a ɪ` (§2.3). -/
inductive Phone
  | t | l | a | i | m
  deriving DecidableEq

/-- The toy words as phone strings, *time*, *lime*, *thyme*; the homophones share a string. -/
def word : Fin 3 → List Phone := ![[.t, .a, .i, .m], [.l, .a, .i, .m], [.t, .a, .i, .m]]

/-- The six triphones of (2) in the paper's column order `#ta taɪ aɪm ɪm# #la laɪ`. -/
def triphone : Fin 6 → Augmented Phone :=
  ![[none, some .t, some .a], [some .t, some .a, some .i], [some .a, some .i, some .m],
    [some .i, some .m, none], [none, some .l, some .a], [some .l, some .a, some .i]]

/-- The rows of the form matrix `C` of (2): each word's triphone indicator, the DLM's cue coding
at width 3 (`cueVector`). -/
def toyForms (i : Fin 3) : FormVec 6 := cueVector 3 triphone (word i)

/-- The form matrix as the paper prints it. -/
theorem toyForms_eq :
    toyForms = ![![1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [toyForms, cueVector, multiHot, Matrix.cons_val_two]

/-- The toy lexicon of §2.3: the semantic matrix `S` of (1), rows *time*, *lime*, *thyme* over
two arbitrary semantic dimensions (`0.1 0.3; 0.6 0.2; 1.1 0.6`), and the triphone matrix `C`
of (2). *time* and *thyme* share a form row. -/
def toy : TrainingExperience 3 6 2 where
  meanings := ![![1 / 10, 3 / 10], ![6 / 10, 2 / 10], ![11 / 10, 6 / 10]]
  forms := toyForms

/-- *time*, the first row of the toy lexicon. -/
abbrev time : Fin 3 := 0

/-- *lime*, the second row of the toy lexicon. -/
abbrev lime : Fin 3 := 1

/-- *thyme*, the third row of the toy lexicon. -/
abbrev thyme : Fin 3 := 2

/-- The token frequencies 100, 10, 1 of *time*, *lime*, *thyme* (A3). -/
def freq : FrequencyVector 3 := ![100, 10, 1]

/-! ### Endstate and frequency-informed learning

The paper fits only the production side of the model, so the comprehension maps below are left
zero. Mapping matrices act on row vectors, `ĉ = sG` (10), so a production map is `toLin' Gᵀ`. -/

/-- The endstate mapping `G` of (4), exactly: `(SᵀS)⁻¹SᵀC` of (A2), with
`1181 = 10⁴ · det(SᵀS)`; the paper prints it to two decimals. -/
def endstateG : Matrix (Fin 2) (Fin 6) ℝ :=
  (1181 : ℝ)⁻¹ • !![-1410, -1410, -90, -90, 1320, 1320; 4500, 4500, 2800, 2800, -1700, -1700]

/-- The DLM at the endstate of learning. -/
def endstate : LinearDiscriminativeLexicon ℝ (FormVec 6) (MeaningVec 2) where
  comprehension := 0
  production := Matrix.toLin' endstateGᵀ

/-- The frequency-informed mapping, exactly: the solution of the `√Q`-scaled normal equations
(A4) for the frequencies `freq`, with `16543 = 500 · det(SᵀQS)`. -/
def frequencyInformedG : Matrix (Fin 2) (Fin 6) ℝ :=
  (16543 : ℝ)⁻¹ • !![-20190, -20190, 4230, 4230, 24420, 24420;
    61920, 61920, 53150, 53150, -8770, -8770]

/-- The DLM after frequency-informed learning. -/
def frequencyInformed : LinearDiscriminativeLexicon ℝ (FormVec 6) (MeaningVec 2) where
  comprehension := 0
  production := Matrix.toLin' frequencyInformedGᵀ

/-- The endstate mapping is the substrate's uniform-weight ERM solution: the coordinate normal
equations (A2) hold. -/
theorem endstate_isELTrainedOn : endstate.IsELTrainedOn toy := by
  refine isERMSolution_iff_forall_coord.mpr fun j k => ?_
  fin_cases j <;> fin_cases k <;>
    norm_num [toy, toyForms_eq, endstate, endstateG, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The frequency-informed mapping is the substrate's ERM solution under `freq`: the
`√Q`-scaled normal equations (A4) hold. -/
theorem frequencyInformed_isFILTrainedOn : frequencyInformed.IsFILTrainedOn toy freq := by
  refine isERMSolution_iff_forall_coord.mpr fun j k => ?_
  fin_cases j <;> fin_cases k <;>
    norm_num [toy, toyForms_eq, freq, frequencyInformed, frequencyInformedG, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-! ### Semantic support for form -/

/-- The support matrix `T = ĈCᵀ` of (A5): the support each word's form (column) receives from
each word's meaning (row). -/
def supportMatrix {m n d : ℕ} (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i k => semSupWord D (data.meanings i) (data.forms k)

/-- *Semantic support for form*: the diagonal of `T`, a word's support for its own form. -/
def semanticSupport {m n d : ℕ} (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) : Fin m → ℝ :=
  (supportMatrix D data).diag

/-- (A6): the endstate support matrix, which the paper prints as
`3.455 0.767 3.455; 0.948 1.622 0.948; 4.623 3.409 4.623`. Its columns for *time* and *thyme*
coincide, as their triphones do. -/
theorem supportMatrix_endstate :
    supportMatrix endstate toy =
      (1181 : ℝ)⁻¹ • !![4080, 906, 4080; 1120, 1916, 1120; 5460, 4026, 5460] := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [supportMatrix, semSupWord, toy, toyForms_eq, endstate, endstateG, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Table 1, endstate column: `3.455, 1.622, 4.623`. -/
theorem semanticSupport_endstate :
    semanticSupport endstate toy = (1181 : ℝ)⁻¹ • ![4080, 1916, 5460] := by
  ext i
  fin_cases i <;> simp [semanticSupport, supportMatrix_endstate, Matrix.cons_val_two]

/-- At the endstate, *thyme*'s meaning supports its form more strongly than *time*'s does
(A6). -/
theorem semanticSupport_endstate_time_lt_thyme :
    semanticSupport endstate toy time < semanticSupport endstate toy thyme := by
  rw [semanticSupport_endstate]; norm_num [time, thyme, Matrix.cons_val_two]

/-- Semantic support for form under frequency-informed learning as the paper computes it for
the toy lexicon (Table 1, (A7)): the predicted forms are the fitted values `√Q S G` of the
`√Q`-scaled regression, paired with the words' own unscaled triphone vectors. -/
def semanticSupportFIL (i : Fin 3) : ℝ :=
  semSupWord frequencyInformed ((toy.sqrtScale freq).meanings i) (toy.forms i)

/-- The `√frequency` factor made explicit: the paper's frequency-informed support is
`√(freq i)` times the support the learned map alone gives. -/
theorem semanticSupportFIL_eq_sqrt_mul (i : Fin 3) :
    semanticSupportFIL i = Real.sqrt (freq i) * semanticSupport frequencyInformed toy i := by
  simp [semanticSupportFIL, semanticSupport, supportMatrix, TrainingExperience.sqrtScale]

/-- The learned frequency-informed map alone still supports *thyme* most:
`3.981, 3.151, 6.225`. -/
theorem semanticSupport_frequencyInformed :
    semanticSupport frequencyInformed toy = (16543 : ℝ)⁻¹ • ![65850, 52132, 102972] := by
  ext i
  fin_cases i <;>
    norm_num [semanticSupport, supportMatrix, semSupWord, toy, toyForms_eq, frequencyInformed,
      frequencyInformedG, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Table 1, frequency-informed column: `39.805, 9.965, 6.225`. -/
theorem semanticSupportFIL_eq :
    semanticSupportFIL = ![658500 / 16543, Real.sqrt 10 * (52132 / 16543), 102972 / 16543] := by
  have h100 : Real.sqrt 100 = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ext i
  rw [semanticSupportFIL_eq_sqrt_mul, semanticSupport_frequencyInformed]
  fin_cases i <;> norm_num [freq, h100, Matrix.cons_val_two]

/-- Under practice *time* overtakes *thyme* ((A7): 39.805 against 6.225), reversing the
endstate order. -/
theorem semanticSupportFIL_thyme_lt_time :
    semanticSupportFIL thyme < semanticSupportFIL time := by
  rw [semanticSupportFIL_eq]; norm_num [time, thyme, Matrix.cons_val_two]

/-- Identical triphones, distinct predicted forms: *time* and *thyme* share a form row, but
their meaning difference lies outside the production kernel, the neutralization locus
(`LinearMap.sub_mem_ker_iff`), so their triphones receive different support
((A3), Fig. A2; §6.2). -/
theorem time_sub_thyme_notMem_ker :
    toy.meanings time - toy.meanings thyme ∉ LinearMap.ker endstate.production := fun h => by
  have := congrFun (LinearMap.sub_mem_ker_iff.mp h) 0
  norm_num [toy, toyForms_eq, endstate, endstateG, time, thyme, Matrix.cons_val_two,
    Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at this

/-! ### Contextual independence

The paper's second component of frequency is estimated at the utterance level: a word-to-word
map `W` with `UW = U` (A8) predicts every word of an utterance from all the words in it, and
the diagonal of `W` is the share of a word's prediction strength that it owes to itself
((7), (8)). For the toy utterances of (5) the paper solves the equation by regression; the
printed `W` of (6) is the minimum-norm solution `U⁺U = Uᵀ(UUᵀ)⁻¹U`, the orthogonal projector
onto the row space of `U`, reproduced here exactly. (A5.2) folds the measure back into the
model by scaling a word's semantic vector, which scales its semantic support for form by the
same factor (`semSupWord_smul_left`). -/

/-- The utterance-by-word matrix `U` of (5): rows *my time is short*, *my good time*,
*my fragrant thyme*, *my lime is bad*, *my lime is good*; columns *my, time, is, short, good,
fragrant, thyme, lime, bad*. -/
def U : Matrix (Fin 5) (Fin 9) ℚ :=
  !![1, 1, 1, 1, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 1, 1, 0, 0;
     1, 0, 1, 0, 0, 0, 0, 1, 1;
     1, 0, 1, 0, 1, 0, 0, 1, 0]

/-- The word-to-word map `W` of (6), exactly; the paper prints it to two decimals. -/
def W : Matrix (Fin 9) (Fin 9) ℚ := (71 : ℚ)⁻¹ •
  !![41, 18, 10, 2, 12, 15, 15, 8, 12;
     18, 46, -6, 13, 7, -9, -9, -19, 7;
     10, -6, 44, 23, -4, -5, -5, 21, -4;
     2, 13, 23, 33, -15, -1, -1, -10, -15;
     12, 7, -4, -15, 52, -6, -6, 11, -19;
     15, -9, -5, -1, -6, 28, 28, -4, -6;
     15, -9, -5, -1, -6, 28, 28, -4, -6;
     8, -19, 21, -10, 11, -4, -4, 31, 11;
     12, 7, -4, -15, -19, -6, -6, 11, 52]

/-- `W` solves the paper's equation `UW = U` (A8), exactly where the paper reports agreement
"up to fifteen decimal digits". -/
theorem U_mul_W : U * W = U := by decide +kernel

/-- `W` is symmetric. -/
theorem isSymm_W : W.IsSymm := by decide +kernel

/-- `W` is idempotent: with symmetry, an orthogonal projector. -/
theorem isIdempotentElem_W : IsIdempotentElem W := by
  unfold IsIdempotentElem; decide +kernel

/-- The diagonal of `W` dominates its rows, as the paper observes of (6). -/
theorem le_diag_W : ∀ i j, W i j ≤ W i i := by decide +kernel

/-- The diagonal of `W` lies in `[0, 1]`, the "proportions" of §3.2, because `W` is an
orthogonal projector. -/
theorem diag_W_mem_Icc (i : Fin 9) : W i i ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨Matrix.diag_nonneg_of_isSymm_of_isIdempotentElem isSymm_W isIdempotentElem_W i,
    Matrix.diag_le_one_of_isSymm_of_isIdempotentElem isSymm_W isIdempotentElem_W i⟩

/-- The contextual-independence measure of (9): `Cind = (log(1/d))^{1/4}`, a log against the
right skew of the diagonal values and a power to finish it. -/
def cind (d : ℝ) : ℝ := Real.log (1 / d) ^ (1 / 4 : ℝ)

/-- `Cind` reverses the order of the diagonal values on `(0, 1)`: the more a word predicts
itself, the lower its `Cind` — the sign of its correlation with frequency in Fig. 2. -/
theorem strictAntiOn_cind : StrictAntiOn cind (Set.Ioo 0 1) := fun a ha b hb hab => by
  unfold cind
  refine Real.rpow_lt_rpow (Real.log_nonneg ?_)
    (Real.log_lt_log (one_div_pos.mpr hb.1) (one_div_lt_one_div_of_lt ha.1 hab)) (by norm_num)
  rw [le_div_iff₀ hb.1]; linarith [hb.2]

end

end GahlBaayen2024
