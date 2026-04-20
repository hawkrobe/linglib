import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite Probability Mass Functions

`FinitePMF W` bundles a rational-valued mass function with non-negativity and
normalization proofs, eliminating the need to thread `hNN`/`hNorm` hypotheses
through probabilistic theorems.

## Relationship to Other Distribution Types

| Type | Number system | Normalized? | Usage |
|------|--------------|-------------|-------|
| `FinitePMF W` | ℚ | Yes (bundled) | Probabilistic answerhood, questions, Bayesian semantics |
| `RSAConfigData` | ℚ | No | RSA unnormalized weights |
| `RSAConfig` | ℝ | No | RSA mathematical proofs |
| `W → ℝ` | ℝ | Hypothesized | Entropy / information theory |

`FinitePMF` is the canonical type for probabilistic semantics where exact
normalized distributions are needed. RSA priors are deliberately unnormalized
and should NOT use `FinitePMF`.
-/

set_option autoImplicit false

namespace Core

/-- A normalized, non-negative probability distribution over a finite type,
using exact rational arithmetic. -/
structure FinitePMF (W : Type*) [Fintype W] where
  /-- Probability mass function -/
  mass : W → ℚ
  /-- All masses are non-negative -/
  mass_nonneg : ∀ w, 0 ≤ mass w
  /-- Masses sum to 1 -/
  mass_sum_one : ∑ w : W, mass w = 1

namespace FinitePMF

variable {W : Type*} [Fintype W]

instance : CoeFun (FinitePMF W) (fun _ => W → ℚ) where
  coe d := d.mass

/-- Coercion to bare function type, for passing to modules that take `W → ℚ`
(e.g., DTS's `condProb`, `bayesFactor`). -/
instance : Coe (FinitePMF W) (W → ℚ) where
  coe d := d.mass

@[simp] lemma coe_def (d : FinitePMF W) (w : W) : d w = d.mass w := rfl

/-- Uniform distribution over a nonempty finite type. -/
def uniform [Nonempty W] : FinitePMF W where
  mass := fun _ => 1 / (Fintype.card W : ℚ)
  mass_nonneg := fun _ => by
    have hn : (0 : ℚ) < (Fintype.card W : ℚ) := by exact_mod_cast Fintype.card_pos
    linarith [div_pos (show (0:ℚ) < 1 from by norm_num) hn]
  mass_sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
    have h : (Fintype.card W : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    exact div_self h

/-- Probability mass of worlds satisfying a predicate.

`probOf pmf φ = ∑ w, if φ w then pmf w else 0`

Unlike `prob` (which goes through `expect`), this computes the sum
directly — matching the form used by `ProbabilisticAnswerhood.probOfProp`
and `DTS.probSum`. -/
def probOf (pmf : FinitePMF W) (φ : W → Bool) : ℚ :=
  ∑ w : W, if φ w then pmf.mass w else 0

/-- Conditional probability P(target | condition).

Returns P(condition ∧ target) / P(condition) when P(condition) > 0,
otherwise 0. This is the single canonical conditional probability
used by `ProbabilisticAnswerhood.conditionalProb`. -/
def condProb (pmf : FinitePMF W) (condition target : W → Bool) : ℚ :=
  let pCond := pmf.probOf condition
  if pCond > 0 then
    pmf.probOf (fun w => condition w && target w) / pCond
  else 0

/-- `probOf` is nonneg. -/
theorem probOf_nonneg (pmf : FinitePMF W) (φ : W → Bool) :
    0 ≤ pmf.probOf φ := by
  unfold probOf
  exact Finset.sum_nonneg fun w _ => by
    split_ifs <;> [exact pmf.mass_nonneg w; linarith]

/-- `condProb` unfolds when conditioning event has positive probability. -/
theorem condProb_of_pos (pmf : FinitePMF W) (cond target : W → Bool)
    (h : pmf.probOf cond > 0) :
    pmf.condProb cond target =
      pmf.probOf (fun w => cond w && target w) / pmf.probOf cond := by
  simp [condProb, h]

/-- `condProb` is zero when conditioning event has zero probability. -/
theorem condProb_of_zero (pmf : FinitePMF W) (cond target : W → Bool)
    (h : pmf.probOf cond = 0) :
    pmf.condProb cond target = 0 := by
  simp [condProb, h]

/-- `condProb` unfolds when conditioning event has nonzero probability. -/
theorem condProb_of_ne_zero (pmf : FinitePMF W) (cond target : W → Bool)
    (hne : pmf.probOf cond ≠ 0) :
    pmf.condProb cond target =
      pmf.probOf (fun w => cond w && target w) / pmf.probOf cond := by
  exact condProb_of_pos pmf cond target (lt_of_le_of_ne (pmf.probOf_nonneg cond) (Ne.symm hne))

/-- P(φ) + P(¬φ) = 1. -/
theorem probOf_complement_add (pmf : FinitePMF W) (φ : W → Bool) :
    pmf.probOf φ + pmf.probOf (fun w => !φ w) = 1 := by
  have h : pmf.probOf φ + pmf.probOf (fun w => !φ w) = ∑ w : W, pmf w := by
    unfold probOf; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _
    by_cases hf : φ w = true <;> simp [hf]
  rw [h]; exact pmf.mass_sum_one

/-- P(φ ∧ ψ) ≤ P(ψ). -/
theorem probOf_and_le (pmf : FinitePMF W) (φ ψ : W → Bool) :
    pmf.probOf (fun w => φ w && ψ w) ≤ pmf.probOf ψ := by
  unfold probOf; apply Finset.sum_le_sum; intro w _
  by_cases hφ : φ w = true <;> by_cases hψ : ψ w = true <;> simp [hφ, hψ]; exact pmf.mass_nonneg w

/-- Partition: P(φ) = P(φ ∧ ψ) + P(φ ∧ ¬ψ). -/
theorem probOf_partition (pmf : FinitePMF W) (φ ψ : W → Bool) :
    pmf.probOf φ =
    pmf.probOf (fun w => φ w && ψ w) + pmf.probOf (fun w => φ w && !ψ w) := by
  unfold probOf; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w _
  by_cases hφ : φ w = true <;> by_cases hψ : ψ w = true <;> simp [hφ, hψ]

/-- P(target | cond) + P(¬target | cond) = 1 when P(cond) > 0. -/
theorem condProb_complement_sum (pmf : FinitePMF W) (cond target : W → Bool)
    (h : pmf.probOf cond > 0) :
    pmf.condProb cond target + pmf.condProb cond (fun w => !target w) = 1 := by
  rw [condProb_of_pos pmf cond target h,
      condProb_of_pos pmf cond _ h, ← add_div,
      show pmf.probOf (fun w => cond w && target w) +
           pmf.probOf (fun w => cond w && !target w) = pmf.probOf cond from
        (pmf.probOf_partition cond target).symm]
  exact div_self (ne_of_gt h)

/-- If P(target | cond) > P(target) then P(cond) > 0. -/
theorem probOf_pos_of_condProb_gt (pmf : FinitePMF W) (cond target : W → Bool)
    (h : pmf.condProb cond target > pmf.probOf target) :
    pmf.probOf cond > 0 := by
  by_contra hle; push_neg at hle
  have hZero := le_antisymm hle (pmf.probOf_nonneg cond)
  rw [condProb_of_zero pmf cond target hZero] at h
  linarith [pmf.probOf_nonneg target]

/-- If P(target | cond) > P(target) then P(target) > 0. -/
theorem probOf_target_pos_of_condProb_gt (pmf : FinitePMF W) (cond target : W → Bool)
    (h : pmf.condProb cond target > pmf.probOf target) :
    pmf.probOf target > 0 := by
  have hPc := pmf.probOf_pos_of_condProb_gt cond target h
  by_contra hle; push_neg at hle
  have hf_eq := le_antisymm hle (pmf.probOf_nonneg target)
  have hAnd_eq : pmf.probOf (fun w => cond w && target w) = 0 :=
    le_antisymm (by linarith [pmf.probOf_and_le cond target])
               (pmf.probOf_nonneg _)
  have : pmf.condProb cond target = 0 := by
    rw [condProb_of_pos pmf cond target hPc, hAnd_eq]; simp
  linarith

/-! ## Set-based API (mathlib-aligned)

The `probOf`/`condProb` functions above take `W → Bool` predicates for
historical reasons (compatibility with earlier Bool/List question
infrastructure). The mathlib-aligned API takes `Set W` with a
`DecidablePred (· ∈ s)` typeclass instance, mirroring `MeasureTheory.Measure`.

The two APIs are equated by `probOfSet_eq_probOf_setOf` and friends.
New code should prefer the Set form. -/

/-- Probability mass of worlds in a set, mathlib-aligned form.

`probOfSet pmf s = ∑ w, if w ∈ s then pmf.mass w else 0`

The Set-based sibling of `probOf`. Requires `[DecidablePred (· ∈ s)]` so
the indicator is computable. Used by the mathlib-pure question infrastructure
(`Core.Issue` consumers). -/
def probOfSet (pmf : FinitePMF W) (s : Set W) [DecidablePred (· ∈ s)] : ℚ :=
  ∑ w : W, if w ∈ s then pmf.mass w else 0

/-- Conditional probability P(target | condition), mathlib-aligned form.

The Set-based sibling of `condProb`. -/
def condProbSet (pmf : FinitePMF W) (cond target : Set W)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ target)] : ℚ :=
  let pCond := pmf.probOfSet cond
  if pCond > 0 then
    pmf.probOfSet (cond ∩ target) / pCond
  else 0

/-- `probOfSet` is nonneg. -/
theorem probOfSet_nonneg (pmf : FinitePMF W) (s : Set W) [DecidablePred (· ∈ s)] :
    0 ≤ pmf.probOfSet s := by
  unfold probOfSet
  exact Finset.sum_nonneg fun w _ => by
    split_ifs <;> [exact pmf.mass_nonneg w; linarith]

/-- `probOfSet` agrees with `probOf` after coercing the Bool predicate to its
characteristic set. -/
theorem probOfSet_eq_probOf (pmf : FinitePMF W) (φ : W → Bool) :
    pmf.probOfSet {w | φ w} = pmf.probOf φ := by
  unfold probOfSet probOf
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : φ w
  · simp [h, Set.mem_setOf_eq]
  · simp [h, Set.mem_setOf_eq]

/-- `condProbSet` unfolds when conditioning event has positive probability. -/
theorem condProbSet_of_pos (pmf : FinitePMF W) (cond target : Set W)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ target)]
    (h : pmf.probOfSet cond > 0) :
    pmf.condProbSet cond target =
      pmf.probOfSet (cond ∩ target) / pmf.probOfSet cond := by
  simp [condProbSet, h]

/-- `condProbSet` is zero when conditioning event has zero probability. -/
theorem condProbSet_of_zero (pmf : FinitePMF W) (cond target : Set W)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ target)]
    (h : pmf.probOfSet cond = 0) :
    pmf.condProbSet cond target = 0 := by
  simp [condProbSet, h]

/-- P(s) + P(sᶜ) = 1. -/
theorem probOfSet_compl_add (pmf : FinitePMF W) (s : Set W)
    [DecidablePred (· ∈ s)] :
    pmf.probOfSet s + pmf.probOfSet sᶜ = 1 := by
  have h : pmf.probOfSet s + pmf.probOfSet sᶜ = ∑ w : W, pmf w := by
    unfold probOfSet; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _
    by_cases hs : w ∈ s
    · simp [hs]
    · simp [hs]
  rw [h]; exact pmf.mass_sum_one

/-- P(s ∩ t) ≤ P(t). -/
theorem probOfSet_inter_le (pmf : FinitePMF W) (s t : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    pmf.probOfSet (s ∩ t) ≤ pmf.probOfSet t := by
  unfold probOfSet; apply Finset.sum_le_sum; intro w _
  by_cases hs : w ∈ s <;> by_cases ht : w ∈ t
  all_goals simp [hs, ht, Set.mem_inter_iff]
  exact pmf.mass_nonneg w

/-- Partition: P(s) = P(s ∩ t) + P(s ∩ tᶜ). -/
theorem probOfSet_partition (pmf : FinitePMF W) (s t : Set W)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    pmf.probOfSet s =
    pmf.probOfSet (s ∩ t) + pmf.probOfSet (s ∩ tᶜ) := by
  unfold probOfSet; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w _
  by_cases hs : w ∈ s <;> by_cases ht : w ∈ t
  all_goals simp [hs, ht, Set.mem_inter_iff, Set.mem_compl_iff]

/-- P(target | cond) + P(targetᶜ | cond) = 1 when P(cond) > 0. -/
theorem condProbSet_compl_sum (pmf : FinitePMF W) (cond target : Set W)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ target)]
    (h : pmf.probOfSet cond > 0) :
    pmf.condProbSet cond target + pmf.condProbSet cond targetᶜ = 1 := by
  rw [condProbSet_of_pos pmf cond target h,
      condProbSet_of_pos pmf cond _ h, ← add_div,
      show pmf.probOfSet (cond ∩ target) + pmf.probOfSet (cond ∩ targetᶜ)
           = pmf.probOfSet cond from
        (pmf.probOfSet_partition cond target).symm]
  exact div_self (ne_of_gt h)

/-- If P(target | cond) > P(target) then P(cond) > 0. -/
theorem probOfSet_pos_of_condProbSet_gt (pmf : FinitePMF W) (cond target : Set W)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ target)]
    (h : pmf.condProbSet cond target > pmf.probOfSet target) :
    pmf.probOfSet cond > 0 := by
  by_contra hle; push_neg at hle
  have hZero := le_antisymm hle (pmf.probOfSet_nonneg cond)
  rw [condProbSet_of_zero pmf cond target hZero] at h
  linarith [pmf.probOfSet_nonneg target]

/-- If P(target | cond) > P(target) then P(target) > 0. -/
theorem probOfSet_target_pos_of_condProbSet_gt (pmf : FinitePMF W)
    (cond target : Set W)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ target)]
    (h : pmf.condProbSet cond target > pmf.probOfSet target) :
    pmf.probOfSet target > 0 := by
  have hPc := pmf.probOfSet_pos_of_condProbSet_gt cond target h
  by_contra hle; push_neg at hle
  have ht_eq := le_antisymm hle (pmf.probOfSet_nonneg target)
  have hAnd_eq : pmf.probOfSet (cond ∩ target) = 0 :=
    le_antisymm (by
      have := pmf.probOfSet_inter_le cond target
      linarith)
      (pmf.probOfSet_nonneg _)
  have : pmf.condProbSet cond target = 0 := by
    rw [condProbSet_of_pos pmf cond target hPc, hAnd_eq]; simp
  linarith

variable [DecidableEq W]

/-- Point mass at a single value -/
def pure (w₀ : W) : FinitePMF W where
  mass := λ w => if w = w₀ then 1 else 0
  mass_nonneg := λ w => by split_ifs <;> decide
  mass_sum_one := by
    rw [Finset.sum_eq_single w₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact (h (Finset.mem_univ _)).elim

/-- Expected value of a function under this distribution -/
def expect (pmf : FinitePMF W) (f : W → ℚ) : ℚ :=
  Finset.sum Finset.univ λ w => pmf.mass w * f w

/-- Expected value of an indicator (probability of event) -/
def prob (pmf : FinitePMF W) (event : W → Bool) : ℚ :=
  pmf.expect λ w => if event w then 1 else 0

/-- Expected value of pure distribution is the value at that point -/
theorem expect_pure (w₀ : W) (f : W → ℚ) :
    (pure w₀).expect f = f w₀ := by
  simp only [expect, pure]
  rw [Finset.sum_eq_single w₀]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact (h (Finset.mem_univ _)).elim

end FinitePMF

end Core
