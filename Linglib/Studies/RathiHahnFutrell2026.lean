import Linglib.Morphology.Paradigm.Complexity
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Rathi, Hahn, and Futrell (2026): Toward an information-theoretic model of morphological fusion based on an efficient tradeoff of memory and surprisal

This file formalizes the paper's measure of fusion and its simulations. Informational fusion,
`LearnerModel.fusion`, is the surprisal of a form under a learner that has never seen a form
for its feature set, so it measures how far the form resists analysis into processes attested
for subsets of its features. The efficient tradeoff hypothesis of [hahn-degen-futrell-2021] is
then turned from a theory of morpheme order into one of feature packaging: fusion is favored
where it lowers surprisal for the memory it costs, and the paper's toy languages say exactly
when. With two features whose agreeing values carry weight `q`, the second character of the
agglutinative language carries `log 2` nats out of context and that of the fusional language
`binEntropy (2q)`, the gain being the features' mutual information, `fus_local_gain`, and
positive exactly when the features are dependent. With three features, fusing the two
independent ones leaves local surprisal unchanged but raises the surprisal of the third
character given the second by the mutual information the fused character hides,
`fuseLow_memory_burden`, while fusing the dependent pair costs nothing. Giving up category
clustering adds `binEntropy (2q)` to the surprisal of the first slot, which doubles it at the
paper's uniform weights, `nonclustered_cellEntropy_zero`.

The corpus studies of polyexponence, suppletion and pairwise fusion rest on optimal orderings
and a neural learner computed outside Lean; they belong to the paper and its data release.

## Implementation notes

The cells of a `ParadigmSystem` stand for the string positions of a toy language and its
classes for the meanings, so the paper's quantities are the substrate's `cellEntropy`,
`conditionalCellEntropy` and `mutualCellInfo`, in nats. Each family is parametrized by the
weight `q` of the agreeing feature values; the paper's tables are `q = 3/8`, `q = 3/16` and
`q = 1/4`. The Appendix's arguments for arbitrary unambiguous languages are instantiated on
these families rather than stated over `Core.InformationTheory`, which lacks the invariance of
entropy under an injective recoding.

## References

* [N. Rathi, M. Hahn, R. Futrell, *Toward an information-theoretic model of morphological
  fusion based on an efficient tradeoff of memory and surprisal* (2026)][rathi-hahn-futrell-2026]
* [N. Rathi, M. Hahn, R. Futrell, *An information-theoretic characterization of morphological
  fusion* (2021)][rathi-hahn-futrell-2021]
* [M. Hahn, J. Degen, R. Futrell, *Modeling word and morpheme order in natural language as an
  efficient trade-off of memory and surprisal* (2021)][hahn-degen-futrell-2021]
* [F. Ackerman, R. Malouf, *Morphological organization: the low conditional entropy
  conjecture* (2013)][ackerman-malouf-2013]
* [S. Wu, R. Cotterell, T. O'Connor, *Morphological irregularity correlates with frequency*
  (2019)][wu-cotterell-2019]
* [J. Mansfield, S. Stoll, B. Bickel, *Category clustering: a probabilistic bias in the
  morphology of verbal agreement marking* (2020)][mansfield-stoll-bickel-2020]
* [T. M. Cover, J. A. Thomas, *Elements of information theory* (2006)][cover-thomas-2006]
-/

namespace RathiHahnFutrell2026

open Morphology Real

variable {n : ℕ} {Form : Type*}

/-! ### Informational fusion -/

/-- A language with every form for the feature sets in `S` removed: the data set from which a
learner guesses those forms. -/
def holdOut (L : ParadigmSystem n Form) (S : Finset (Fin n)) : ParadigmSystem n (Option Form) :=
  ⟨L.entries.map λ e => (λ c => if c ∈ S then none else some (e.1 c), e.2)⟩

/-- A learner model: the probability it assigns to a form at a feature set for a lexeme whose
other forms it is shown, after training on a data set. -/
structure LearnerModel (n : ℕ) (Form : Type*) where
  predict : ParadigmSystem n (Option Form) → Paradigm n (Option Form) → Fin n → Form → ℝ

/-- The probability the learner assigns to the form for `σ` in the paradigm `p` of the language
`L`, trained on `L` with the feature sets in `S` held out. -/
def LearnerModel.prob (M : LearnerModel n Form) (L : ParadigmSystem n Form) (p : Paradigm n Form)
    (S : Finset (Fin n)) (σ : Fin n) : ℝ :=
  M.predict (holdOut L S) (λ c => if c ∈ S then none else some (p c)) σ (p σ)

/-- Informational fusion: the surprisal of the form for `σ` under a learner that has seen no
form for the feature sets in `S`, among them `σ`. Holding out `σ` alone is the paper's
informational fusion; holding out every feature set containing a pair of features is its
pairwise fusion. -/
noncomputable def LearnerModel.fusion (M : LearnerModel n Form) (L : ParadigmSystem n Form)
    (p : Paradigm n Form) (S : Finset (Fin n)) (σ : Fin n) : ℝ :=
  -log (M.prob L p S σ)

/-- A form's informational fusion under a learner assigning it a probability is nonnegative. -/
theorem LearnerModel.fusion_nonneg {M : LearnerModel n Form} {L : ParadigmSystem n Form}
    {p : Paradigm n Form} {S : Finset (Fin n)} {σ : Fin n} (h₀ : 0 ≤ M.prob L p S σ)
    (h₁ : M.prob L p S σ ≤ 1) : 0 ≤ M.fusion L p S σ :=
  neg_nonneg.2 (log_nonpos h₀ h₁)

/-! ### The toy languages -/

/-- The entropy of the law with weights `q`, `1/2 − q`, `1/2 − q`, `q` exceeds `log 2` by the
binary entropy of `2q`. -/
private theorem two_negMulLog (q : ℝ) :
    2 * negMulLog q + 2 * negMulLog (1 / 2 - q) - log 2 = binEntropy (2 * q) := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, show (1 : ℝ) - 2 * q = 2 * (1 / 2 - q) by ring,
    negMulLog_mul, negMulLog_mul]
  simp only [negMulLog]
  ring

private theorem negMulLog_half : negMulLog (1 / 2 : ℝ) = log 2 / 2 := by
  simp [negMulLog, log_inv]; ring

private theorem negMulLog_quarter : negMulLog (1 / 4 : ℝ) = log 2 / 2 := by
  rw [show (1 / 4 : ℝ) = (2⁻¹) ^ 2 by norm_num, negMulLog, log_pow, log_inv]; ring

/-- A rational differs from a rational exactly when their real casts do. -/
private theorem cast_ne_iff {q r : ℚ} {x : ℝ} (h : (r : ℝ) = x) : (q : ℝ) ≠ x ↔ q ≠ r := by
  rw [← h, ne_eq, ne_eq, Rat.cast_inj]

/-- Two binary features whose agreeing values weigh `q` each and whose disagreeing values
`1/2 − q`, expressed agglutinatively: the first character by the first feature and the second
by the second. The paper's Table 4 is `q = 3/8`; its Table 6 language with category clustering
is `q = 1/4`. -/
def agg (q : ℚ) : ParadigmSystem 2 Char :=
  ⟨[(!['A', 'C'], q), (!['A', 'D'], 1 / 2 - q), (!['B', 'C'], 1 / 2 - q), (!['B', 'D'], q)]⟩

/-- The fusional language of Table 4: the second character expresses the exclusive or of the
two features. -/
def fus (q : ℚ) : ParadigmSystem 2 Char :=
  ⟨[(!['A', 'C'], q), (!['A', 'D'], 1 / 2 - q), (!['B', 'D'], 1 / 2 - q), (!['B', 'C'], q)]⟩

/-- The language of Table 6 without category clustering: the character for the first feature
precedes the one for the second when the first feature is active and follows it otherwise. -/
def nonclustered (q : ℚ) : ParadigmSystem 2 Char :=
  ⟨[(!['A', 'C'], q), (!['D', 'A'], 1 / 2 - q), (!['C', 'B'], 1 / 2 - q), (!['B', 'D'], q)]⟩

/-- Three binary features, the second and third agreeing with weight `q` and disagreeing with
`1/4 − q` independently of the first, expressed agglutinatively. The paper's Table 5 is
`q = 3/16`. -/
def agg₃ (q : ℚ) : ParadigmSystem 3 Char :=
  ⟨[(!['A', 'B', 'C'], q), (!['A', 'B', 'E'], 1 / 4 - q), (!['A', 'F', 'C'], 1 / 4 - q),
    (!['A', 'F', 'E'], q), (!['G', 'B', 'C'], q), (!['G', 'B', 'E'], 1 / 4 - q),
    (!['G', 'F', 'C'], 1 / 4 - q), (!['G', 'F', 'E'], q)]⟩

/-- The language of Table 5 fusing the two independent features: the second character
expresses the exclusive or of the first two. -/
def fuseLow (q : ℚ) : ParadigmSystem 3 Char :=
  ⟨[(!['A', 'B', 'C'], q), (!['A', 'B', 'E'], 1 / 4 - q), (!['A', 'F', 'C'], 1 / 4 - q),
    (!['A', 'F', 'E'], q), (!['G', 'F', 'C'], q), (!['G', 'F', 'E'], 1 / 4 - q),
    (!['G', 'B', 'C'], 1 / 4 - q), (!['G', 'B', 'E'], q)]⟩

/-- The language of Table 5 fusing the two dependent features: the third character expresses
the exclusive or of the last two. -/
def fuseHigh (q : ℚ) : ParadigmSystem 3 Char :=
  ⟨[(!['A', 'B', 'C'], q), (!['A', 'B', 'E'], 1 / 4 - q), (!['A', 'F', 'E'], 1 / 4 - q),
    (!['A', 'F', 'C'], q), (!['G', 'B', 'C'], q), (!['G', 'B', 'E'], 1 / 4 - q),
    (!['G', 'F', 'E'], 1 / 4 - q), (!['G', 'F', 'C'], q)]⟩

/-! ### Fusing dependent features lowers local surprisal -/

/-- Out of context, each character of the agglutinative language carries `log 2` nats. -/
theorem agg_cellEntropy (q : ℚ) (c : Fin 2) : (agg q).cellEntropy c = log 2 := by
  fin_cases c <;>
    simp [ParadigmSystem.cellEntropy, ParadigmSystem.realizations, ParadigmSystem.cellWeight,
      ParadigmSystem.total, agg] <;>
    ring_nf <;> rw [negMulLog_half] <;> ring

/-- The second feature given the first has entropy `binEntropy (2q)`. -/
theorem agg_conditionalCellEntropy (q : ℚ) :
    (agg q).conditionalCellEntropy 1 0 = binEntropy (2 * q) := by
  rw [ParadigmSystem.conditionalCellEntropy, agg_cellEntropy, ← two_negMulLog]
  congr 1
  simp [ParadigmSystem.jointCellEntropy, ParadigmSystem.jointRealizations,
    ParadigmSystem.jointWeight, ParadigmSystem.total, agg]
  ring_nf

/-- The mutual information of the two features is `log 2 − binEntropy (2q)`, zero exactly
when `q = 1/4`. -/
theorem agg_mutualCellInfo (q : ℚ) : (agg q).mutualCellInfo 1 0 = log 2 - binEntropy (2 * q) := by
  rw [ParadigmSystem.mutualCellInfo, agg_cellEntropy, agg_conditionalCellEntropy]

/-- Out of context, the fused second character carries `binEntropy (2q)` nats. -/
theorem fus_cellEntropy (q : ℚ) : (fus q).cellEntropy 1 = binEntropy (2 * q) := by
  simp [ParadigmSystem.cellEntropy, ParadigmSystem.realizations, ParadigmSystem.cellWeight,
    ParadigmSystem.total, fus]
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring_nf

/-- Fusion lowers the local surprisal of the second character by the mutual information of the
two features. -/
theorem fus_local_gain (q : ℚ) :
    (agg q).cellEntropy 1 - (fus q).cellEntropy 1 = (agg q).mutualCellInfo 1 0 := by
  rw [agg_cellEntropy, fus_cellEntropy, agg_mutualCellInfo]

/-- Fusion lowers local surprisal exactly when the features are dependent. -/
theorem fus_cellEntropy_lt_iff (q : ℚ) :
    (fus q).cellEntropy 1 < (agg q).cellEntropy 1 ↔ q ≠ 1 / 4 := by
  rw [fus_cellEntropy, agg_cellEntropy, binEntropy_lt_log_two, inv_eq_one_div,
    ← cast_ne_iff (q := q) (r := 1 / 4) (x := 1 / 4) (by norm_num)]
  constructor <;> intro h h' <;> apply h <;> linarith

/-! ### Fusing independent features raises long-range surprisal -/

/-- Out of context, each character of the three-feature agglutinative language carries `log 2`
nats. -/
theorem agg₃_cellEntropy (q : ℚ) (c : Fin 3) : (agg₃ q).cellEntropy c = log 2 := by
  fin_cases c <;>
    simp [ParadigmSystem.cellEntropy, ParadigmSystem.realizations, ParadigmSystem.cellWeight,
      ParadigmSystem.total, agg₃] <;>
    ring_nf <;> rw [negMulLog_half] <;> ring

/-- Fusing the independent features leaves local surprisal unchanged. -/
theorem fuseLow_cellEntropy (q : ℚ) (c : Fin 3) : (fuseLow q).cellEntropy c = log 2 := by
  fin_cases c <;>
    simp [ParadigmSystem.cellEntropy, ParadigmSystem.realizations, ParadigmSystem.cellWeight,
      ParadigmSystem.total, fuseLow] <;>
    ring_nf <;> rw [negMulLog_half] <;> ring

/-- The third feature given the second has entropy `binEntropy (4q)`. -/
theorem agg₃_conditionalCellEntropy (q : ℚ) :
    (agg₃ q).conditionalCellEntropy 2 1 = binEntropy (4 * q) := by
  rw [ParadigmSystem.conditionalCellEntropy, agg₃_cellEntropy,
    show (4 : ℝ) * q = 2 * (2 * q) by ring, ← two_negMulLog]
  congr 1
  simp [ParadigmSystem.jointCellEntropy, ParadigmSystem.jointRealizations,
    ParadigmSystem.jointWeight, ParadigmSystem.total, agg₃]
  ring_nf

/-- Fusing the dependent features costs nothing: the third character given the second keeps
the entropy of the third feature given the second. -/
theorem fuseHigh_conditionalCellEntropy (q : ℚ) :
    (fuseHigh q).conditionalCellEntropy 2 1 = binEntropy (4 * q) := by
  rw [ParadigmSystem.conditionalCellEntropy, ← agg₃_conditionalCellEntropy,
    ParadigmSystem.conditionalCellEntropy, agg₃_cellEntropy]
  simp [ParadigmSystem.jointCellEntropy, ParadigmSystem.jointRealizations,
    ParadigmSystem.jointWeight, ParadigmSystem.cellEntropy, ParadigmSystem.realizations,
    ParadigmSystem.cellWeight, ParadigmSystem.total, fuseHigh, agg₃]
  ring_nf
  rw [negMulLog_half]
  ring

/-- Fusing the independent features hides the second feature from the third character, whose
surprisal given the second character rises to `log 2`. -/
theorem fuseLow_conditionalCellEntropy (q : ℚ) :
    (fuseLow q).conditionalCellEntropy 2 1 = log 2 := by
  rw [ParadigmSystem.conditionalCellEntropy, fuseLow_cellEntropy]
  simp [ParadigmSystem.jointCellEntropy, ParadigmSystem.jointRealizations,
    ParadigmSystem.jointWeight, ParadigmSystem.total, fuseLow]
  ring_nf
  rw [negMulLog_quarter]
  ring

/-- The memory burden of fusing independent features is the mutual information of the
dependent features the fused character no longer exposes. -/
theorem fuseLow_memory_burden (q : ℚ) :
    (fuseLow q).conditionalCellEntropy 2 1 - (agg₃ q).conditionalCellEntropy 2 1 =
      (agg₃ q).mutualCellInfo 2 1 := by
  rw [ParadigmSystem.mutualCellInfo, fuseLow_conditionalCellEntropy, agg₃_cellEntropy]

/-- Fusing the independent features raises long-range surprisal exactly when the second and
third features are dependent. -/
theorem agg₃_conditionalCellEntropy_lt_iff (q : ℚ) :
    (agg₃ q).conditionalCellEntropy 2 1 < (fuseLow q).conditionalCellEntropy 2 1 ↔
      q ≠ 1 / 8 := by
  rw [fuseLow_conditionalCellEntropy, agg₃_conditionalCellEntropy, binEntropy_lt_log_two,
    inv_eq_one_div, ← cast_ne_iff (q := q) (r := 1 / 8) (x := 1 / 8) (by norm_num)]
  constructor <;> intro h h' <;> apply h <;> linarith

/-! ### Category clustering lowers local surprisal -/

/-- Without category clustering the first slot has four realizations, and its surprisal
exceeds the clustered language's by the binary entropy of `2q`. -/
theorem nonclustered_cellEntropy_zero (q : ℚ) :
    (nonclustered q).cellEntropy 0 = log 2 + binEntropy (2 * q) := by
  rw [← two_negMulLog]
  simp [ParadigmSystem.cellEntropy, ParadigmSystem.realizations, ParadigmSystem.cellWeight,
    ParadigmSystem.total, nonclustered]
  ring_nf

/-- At the paper's uniform weights the surprisal of the first slot doubles. -/
theorem nonclustered_cellEntropy_zero_quarter :
    (nonclustered (1 / 4)).cellEntropy 0 = 2 * (agg (1 / 4)).cellEntropy 0 := by
  rw [nonclustered_cellEntropy_zero, agg_cellEntropy]
  norm_num
  rw [one_div, binEntropy_two_inv]
  ring

/-- Category clustering lowers the surprisal of the first slot whenever both feature values
occur. -/
theorem agg_cellEntropy_lt_nonclustered {q : ℚ} (h₀ : 0 < q) (h₁ : q < 1 / 2) :
    (agg q).cellEntropy 0 < (nonclustered q).cellEntropy 0 := by
  rw [nonclustered_cellEntropy_zero, agg_cellEntropy]
  have : (0 : ℝ) < q := by exact_mod_cast h₀
  have : (q : ℝ) < 1 / 2 := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]; exact_mod_cast h₁
  linarith [binEntropy_pos (by linarith : (0 : ℝ) < 2 * q) (by linarith : (2 * q : ℝ) < 1)]

end RathiHahnFutrell2026
