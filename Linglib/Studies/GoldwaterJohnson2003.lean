module

public import Linglib.Phonology.HarmonicGrammar.Expressivity
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.Probability.Moments.MGFAnalytic
public import Mathlib.MeasureTheory.Measure.Tilted
public import Linglib.Data.Examples.GoldwaterJohnson2003

/-!
# Goldwater and Johnson (2003): Learning OT Constraint Rankings Using a Maximum Entropy Model

This file formalizes [goldwater-johnson-2003]'s maximum entropy model of constraint-based
phonology. The probability of an output given an input is the softmax of its harmony, the negated
weighted sum of its constraint violations (eq. (1)), so the model is `softmax` over `harmonyScore`,
the log-linear form of Harmonic Grammar ([smolensky-legendre-2006]); learning maximizes the log
pseudo-likelihood of the training pairs (eq. (2)) less a Gaussian penalty on the weights (eq. (3)).
Holding the other weights fixed, the log probability of an observation is concave in any one weight
(`concaveOn_log_gjProb_update`), footnote 4's guarantee of a single global maximum, and replicating
the corpus r times while dividing the prior's variance by r rescales the objective by r, so only nσ²
matters for the weights learned (`regularizedObjective_replicate`). The Wolof tongue-root
grammar's learned weights of Table 1 are exponentially separated (`wolof_separated`), the spacing
that recovers strict domination in the limit ([johnson-2002]). For [boersma-hayes-2001]'s Finnish
genitive plurals, a model choosing between two candidates sees their violations only through the
difference vector (`gjProb_pair`), so Table 2's *naapuri* and *ministeri* classes, distinct in
violations but not in differences, are one class for the learner (`rows_collapse`).

## Implementation notes

The four Finnish rows carry Table 2's violation vectors as digit strings, one digit per constraint
in [boersma-hayes-2001]'s order; Anttila's full grammar is in `Studies/Anttila1997.lean`. The Wolof
weights are the learned values of Table 1; the error rates and Table 4 stay in the paper, as does
the comparison with [boersma-1997]'s Gradual Learning Algorithm.

## References

* [goldwater-johnson-2003]
* [boersma-hayes-2001]
* [boersma-1997]
* [berger-della-pietra-della-pietra-1996]
* [johnson-2002]
* [smolensky-legendre-2006]
-/

@[expose] public section

namespace GoldwaterJohnson2003

open OptimalityTheory HarmonicGrammar Finset Real Data.Examples

variable {I O : Type*} [Fintype O] {n : ℕ}

/-- Eq. (1): the conditional probability of an output is the softmax of its harmony over the
candidate set. -/
noncomputable def gjProb (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ) (i : I)
    (o : O) : ℝ :=
  softmax (λ o' => harmonyScore con w (i, o')) o

/-- Eq. (2), logged: the log pseudo-likelihood of the training pairs. -/
noncomputable def logPseudoLikelihood (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (data : List (I × O)) : ℝ :=
  (data.map λ p => log (gjProb con w p.1 p.2)).sum

/-- Eq. (3) with the paper's common prior, mean zero and deviation σ for every weight. -/
noncomputable def regularizedObjective (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (data : List (I × O)) (σ : ℝ) : ℝ :=
  logPseudoLikelihood con w data - ∑ j, w j ^ 2 / (2 * σ ^ 2)

/-- Replicating the corpus r times while dividing the prior's variance by r multiplies the
objective by r: the weights learned depend on nσ² alone. -/
theorem regularizedObjective_replicate (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (data : List (I × O)) {r : ℕ} (hr : 0 < r) {σ σ' : ℝ} (hσ : 0 < σ)
    (h : (r : ℝ) * σ' ^ 2 = σ ^ 2) :
    regularizedObjective con w (List.replicate r data).flatten σ' =
      r * regularizedObjective con w data σ := by
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hσ' : σ' ^ 2 = σ ^ 2 / r := by rw [← h]; field_simp
  unfold regularizedObjective logPseudoLikelihood
  simp only [List.map_flatten, List.map_replicate, List.sum_flatten, List.sum_replicate,
    nsmul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl λ j _ => ?_
  rw [hσ']
  field_simp

/-- The same weights maximize the objective before and after replication. -/
theorem regularizedObjective_replicate_le_iff (con : ConstraintSet (I × O) (Fin n))
    (w w' : Fin n → ℝ) (data : List (I × O)) {r : ℕ} (hr : 0 < r) {σ σ' : ℝ} (hσ : 0 < σ)
    (h : (r : ℝ) * σ' ^ 2 = σ ^ 2) :
    regularizedObjective con w' (List.replicate r data).flatten σ' ≤
        regularizedObjective con w (List.replicate r data).flatten σ' ↔
      regularizedObjective con w' data σ ≤ regularizedObjective con w data σ := by
  rw [regularizedObjective_replicate con w data hr hσ h,
    regularizedObjective_replicate con w' data hr hσ h]
  exact mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hr)

/-- With the other weights held fixed, the probability of an observation is the softmax of an
affine function of weight j: the negated violations of constraint j as the score, the other
constraints' harmony as the offset. -/
theorem gjProb_update (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ) (j : Fin n) (i : I)
    (o : O) (t : ℝ) :
    gjProb con (Function.update w j t) i o =
      softmax (t • (λ o' => -((con j (i, o') : ℕ) : ℝ)) +
        λ o' => -∑ k ∈ ({j}ᶜ : Finset (Fin n)), w k * (con k (i, o') : ℝ)) o := by
  unfold gjProb
  congr 1
  funext o'
  simp only [harmonyScore_eq_neg_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_add_sum_compl j, Function.update_self,
    Finset.sum_congr rfl (g := λ k => w k * (con k (i, o') : ℝ)) λ k hk => by
      rw [Function.update_of_ne (Finset.notMem_singleton.mp (Finset.mem_compl.mp hk))]]
  ring

open MeasureTheory ProbabilityTheory in
/-- Footnote 4: with the other weights held fixed, the log probability of an observation is
concave in weight j, since the harmony is then affine in that weight and the log-partition
function convex. The log-partition function is, up to a constant, the cumulant generating
function of the negated violations under the counting measure tilted by the other constraints'
harmony, which is convex by `ProbabilityTheory.convexOn_cgf`. -/
theorem concaveOn_log_gjProb_update (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (j : Fin n)
    (i : I) (o : O) : ConcaveOn ℝ Set.univ λ t => log (gjProb con (Function.update w j t) i o) := by
  have : Nonempty O := ⟨o⟩
  simp_rw [gjProb_update]
  suffices ∀ s r : O → ℝ, ConcaveOn ℝ Set.univ fun t : ℝ ↦ log (softmax (t • s + r) o) from
    this _ _
  intro s r
  let _ : MeasurableSpace O := ⊤
  have hZ : 0 < ∑ x, exp (r x) := sum_exp_pos r
  have hcgf (t : ℝ) : log (∑ x, exp (t * s x + r x)) =
      cgf s (Measure.count.tilted r) t + log (∑ x, exp (r x)) := by
    have hmgf : mgf s (Measure.count.tilted r) t =
        (∑ x, exp (t * s x + r x)) / ∑ x, exp (r x) := by
      simp only [mgf, integral_tilted, integral_count, smul_eq_mul, Finset.sum_div, exp_add]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    rw [cgf, hmgf, log_div (sum_exp_pos _).ne' hZ.ne', sub_add_cancel]
  have hconv : ConvexOn ℝ Set.univ (cgf s (Measure.count.tilted r)) := by
    convert convexOn_cgf (X := s) (μ := Measure.count.tilted r)
    exact (Set.eq_univ_of_forall fun t ↦ Integrable.of_finite).symm
  simp only [log_softmax, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcgf]
  exact (((LinearMap.mulRight ℝ (s o)).concaveOn convex_univ).add
    (concaveOn_const (r o) convex_univ)).sub (hconv.add_const _)

/-- The log pseudo-likelihood of a corpus is concave in each weight, as a sum of concave terms. -/
theorem concaveOn_logPseudoLikelihood_update (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (j : Fin n) (data : List (I × O)) :
    ConcaveOn ℝ Set.univ λ t => logPseudoLikelihood con (Function.update w j t) data := by
  induction data with
  | nil => simpa [logPseudoLikelihood] using concaveOn_const (0 : ℝ) convex_univ
  | cons p data ih =>
    simp only [logPseudoLikelihood, List.map_cons, List.sum_cons] at ih ⊢
    exact (concaveOn_log_gjProb_update con w j p.1 p.2).add ih

/-! ### Two candidates: learning from differences (section 3.2) -/

/-- Two candidates as a constraint set over one input: the winner at 0, the loser at 1. -/
def pairConstraintSet (win lose : Fin n → ℕ) : ConstraintSet (Unit × Fin 2) (Fin n) :=
  λ j c => if c.2 = 0 then win j else lose j

/-- A two-candidate model sees the violations only through their difference: the winner's
probability is the sigmoid of the weighted difference vector. -/
theorem gjProb_pair (w : Fin n → ℝ) (win lose : Fin n → ℕ) :
    gjProb (pairConstraintSet win lose) w () 0 = sigmoid (∑ j, w j * ((lose j : ℝ) - win j)) := by
  unfold gjProb
  rw [softmax_fin_two]
  congr 1
  simp only [harmonyScore_eq_neg_sum, pairConstraintSet, Fin.isValue, ite_true, ite_false,
    one_ne_zero, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Two candidate pairs with the same difference vector get the same winner probability under
every weighting. -/
theorem gjProb_pair_eq_of_diff_eq (w : Fin n → ℝ) {win lose win' lose' : Fin n → ℕ}
    (h : (λ j => (lose j : ℤ) - win j) = λ j => (lose' j : ℤ) - win' j) :
    gjProb (pairConstraintSet win lose) w () 0 = gjProb (pairConstraintSet win' lose') w () 0 := by
  rw [gjProb_pair, gjProb_pair]
  congr 1
  refine Finset.sum_congr rfl λ j _ => ?_
  have hj := congrFun h j
  have : ((lose j : ℝ) - win j) = (((lose j : ℤ) - win j : ℤ) : ℝ) := by push_cast; ring
  rw [this, hj]
  push_cast
  ring

/-! ### Table 1: the Wolof tongue-root grammar -/

/-- The weights learned for Boersma's five Wolof constraints (Table 1, nσ² ≈ 1,200,000): *RTRHI,
PARSE[RTR], GESTURE[CONTOUR], PARSE[ATR], *ATRLO. -/
noncomputable def wolofWeights : Fin 5 → ℝ
  | 0 => 3389 / 100
  | 1 => 17
  | 2 => 10
  | 3 => 353 / 100
  | 4 => 41 / 100

/-- The learned weights are exponentially separated: each exceeds the sum of all lower ones, the
spacing under which Harmonic Grammar reproduces the strict domination of the ranking the Gradual
Learning Algorithm finds ([johnson-2002], `lex_imp_lower_violations`). -/
theorem wolof_separated : ExponentiallySeparated wolofWeights 1 := by
  refine ⟨λ i => by fin_cases i <;> norm_num [wolofWeights], λ k => ?_⟩
  fin_cases k <;>
    simp +decide only [wolofWeights, Finset.sum_filter, Fin.sum_univ_five] <;>
    norm_num

/-! ### Tables 2 and 3: Finnish genitive plurals -/

/-- The digits of a feature string as violation counts, one per constraint. -/
def digits (s : String) : List ℕ := s.toList.map λ c => c.toNat - '0'.toNat

/-- A violation vector over [boersma-hayes-2001]'s eleven constraints. -/
def vec (l : List ℕ) : Fin 11 → ℕ := λ j => l.getD j 0

/-- A stem class: the violation vectors of the winning and the losing genitive plural. -/
structure Row where
  winner : Fin 11 → ℕ
  loser : Fin 11 → ℕ
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let w ← ex.feature? "winnerViolations"
  let l ← ex.feature? "loserViolations"
  pure ⟨vec (digits w), vec (digits l)⟩

/-- Table 3's learning signal: the loser's violations minus the winner's. -/
def Row.diff (r : Row) : Fin 11 → ℤ := λ j => (r.loser j : ℤ) - r.winner j

/-- The four stem classes of Table 2. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = Examples.all.length := by decide

/-- Table 3: two of Table 2's classes differ in their violation vectors but not in their
differences, so a learner that sees only differences treats them as one class. -/
theorem rows_collapse : ∃ r₁ ∈ rows, ∃ r₂ ∈ rows, r₁.winner ≠ r₂.winner ∧ r₁.diff = r₂.diff := by
  decide

/-- The two classes receive the same winner probability under every weighting. -/
theorem rows_collapse_prob :
    ∃ r₁ ∈ rows, ∃ r₂ ∈ rows, r₁ ≠ r₂ ∧
      ∀ w, gjProb (pairConstraintSet r₁.winner r₁.loser) w () 0 =
        gjProb (pairConstraintSet r₂.winner r₂.loser) w () 0 := by
  obtain ⟨r₁, h₁, r₂, h₂, hne, hd⟩ := rows_collapse
  exact ⟨r₁, h₁, r₂, h₂, λ h => hne (congrArg Row.winner h), λ w => gjProb_pair_eq_of_diff_eq w hd⟩

end GoldwaterJohnson2003
