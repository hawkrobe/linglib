import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Linglib.Core.Probability.ENNRealArith

/-!
# Finite-fintype convenience naming for `Mathlib.PMF`

`PMF α` (mathlib) is the canonical probability monad in this library, but
its measure-theoretic API names (`toOuterMeasure`, `cond`) read awkwardly
in linguistic content. This file is a paper-thin naming layer:

* `probOfSet p s := p.toOuterMeasure s`
* `condProbSet p cond target := p.toOuterMeasure (cond ∩ target) / p.toOuterMeasure cond`

Both are `abbrev`s — definitionally equal to the mathlib forms — so any
mathlib lemma about `toOuterMeasure` (e.g. `toOuterMeasure_apply_fintype`)
applies directly and no `MeasurableSpace` instance is required.

The conditional ratio is unguarded: ENNReal's `0 / 0 = 0` and
`x ≤ p.toOuterMeasure cond` (monotonicity) jointly imply
`condProbSet p cond target = 0` whenever `p.toOuterMeasure cond = 0`,
which matches `ProbabilityTheory.cond`'s convention.

A handful of lemmas (positivity, monotonicity, partition, complement,
finite normalization) are provided for the patterns that recur in
`Semantics/Questions/Probabilistic.lean` and the corresponding
`Studies/` files. ENNReal arithmetic at consumer sites
goes through `ennreal_arith` (see `Linglib.Core.Probability.ENNRealArith`).
-/

set_option autoImplicit false

namespace PMF

variable {α : Type*} [Fintype α]

open scoped ENNReal
open BigOperators

/-- Probability mass of a set under a finite-fintype PMF, named to match
linguistic content. Definitionally `p.toOuterMeasure s`, so every mathlib
lemma about `toOuterMeasure` applies. -/
noncomputable abbrev probOfSet (p : PMF α) (s : Set α) : ℝ≥0∞ := p.toOuterMeasure s

/-- Conditional probability `P(target | cond)` as a direct ratio.
ENNReal's `0/0 = 0` convention plus `x ≤ p.toOuterMeasure cond`
(monotonicity) handle the degenerate case automatically — no `if` guard
needed. Matches `ProbabilityTheory.cond_apply`'s convention. -/
noncomputable abbrev condProbSet (p : PMF α) (cond target : Set α) : ℝ≥0∞ :=
  p.toOuterMeasure (cond ∩ target) / p.toOuterMeasure cond

/-- `probOfSet` reduces to the indicator-sum form on a finite type. This
is just `PMF.toOuterMeasure_apply_fintype` rephrased with `if-then-else`
in place of `Set.indicator`. -/
theorem probOfSet_apply (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    p.probOfSet s = ∑ a, if a ∈ s then p a else 0 := by
  rw [probOfSet, PMF.toOuterMeasure_apply_fintype]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : a ∈ s
  · simp [h, Set.indicator]
  · simp [h, Set.indicator]

@[simp] theorem probOfSet_empty (p : PMF α) :
    p.probOfSet (∅ : Set α) = 0 := by
  rw [probOfSet, PMF.toOuterMeasure_apply_fintype]
  simp [Set.indicator]

@[simp] theorem probOfSet_univ (p : PMF α) :
    p.probOfSet (Set.univ : Set α) = 1 := by
  rw [probOfSet, PMF.toOuterMeasure_apply_fintype]
  simp only [Set.indicator_univ]
  exact (PMF.tsum_coe p ▸ tsum_eq_sum (fun a (h : a ∉ Finset.univ) =>
    absurd (Finset.mem_univ a) h)).symm

omit [Fintype α] in
theorem probOfSet_mono (p : PMF α) {s t : Set α} (h : s ⊆ t) :
    p.probOfSet s ≤ p.probOfSet t :=
  (p.toOuterMeasure).mono h

omit [Fintype α] in
theorem probOfSet_inter_le_right (p : PMF α) (s t : Set α) :
    p.probOfSet (s ∩ t) ≤ p.probOfSet t :=
  probOfSet_mono p Set.inter_subset_right

omit [Fintype α] in
theorem probOfSet_inter_le_left (p : PMF α) (s t : Set α) :
    p.probOfSet (s ∩ t) ≤ p.probOfSet s :=
  probOfSet_mono p Set.inter_subset_left

/-- `probOfSet` is bounded by `1`. -/
theorem probOfSet_le_one (p : PMF α) (s : Set α) : p.probOfSet s ≤ 1 := by
  calc p.probOfSet s
      ≤ p.probOfSet (Set.univ : Set α) := probOfSet_mono p (Set.subset_univ _)
    _ = 1 := probOfSet_univ p

/-- `probOfSet` is finite. -/
theorem probOfSet_ne_top (p : PMF α) (s : Set α) : p.probOfSet s ≠ ⊤ :=
  (lt_of_le_of_lt (probOfSet_le_one p s) ENNReal.one_lt_top).ne

/-- Partition: `P(s) = P(s ∩ t) + P(s ∩ tᶜ)`. -/
theorem probOfSet_partition (p : PMF α) (s t : Set α)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    p.probOfSet s = p.probOfSet (s ∩ t) + p.probOfSet (s ∩ tᶜ) := by
  rw [probOfSet_apply, probOfSet_apply, probOfSet_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t
  all_goals simp [hs, ht, Set.mem_inter_iff, Set.mem_compl_iff]

/-- `P(s) + P(sᶜ) = 1`. -/
theorem probOfSet_compl_add (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    p.probOfSet s + p.probOfSet sᶜ = 1 := by
  rw [probOfSet_apply, probOfSet_apply, ← Finset.sum_add_distrib]
  rw [show (∑ a, ((if a ∈ s then p a else 0) + if a ∈ sᶜ then p a else 0))
        = ∑ a, p a from
        Finset.sum_congr rfl (fun a _ => by
          by_cases h : a ∈ s
          · simp [h, Set.mem_compl_iff]
          · simp [h, Set.mem_compl_iff])]
  exact (PMF.tsum_coe p ▸ tsum_eq_sum (fun a (h : a ∉ Finset.univ) =>
    absurd (Finset.mem_univ a) h)).symm

omit [Fintype α] in
/-- `condProbSet` is by definition the ratio. Provided as a named lemma
so consumers can `rw [condProbSet_eq_div]` rather than `unfold` an
`abbrev`. -/
theorem condProbSet_eq_div (p : PMF α) (cond target : Set α) :
    p.condProbSet cond target =
      p.probOfSet (cond ∩ target) / p.probOfSet cond := rfl

omit [Fintype α] in
/-- When `P(cond) = 0`, the conditional probability is `0`. -/
theorem condProbSet_of_zero (p : PMF α) (cond target : Set α)
    (h : p.probOfSet cond = 0) :
    p.condProbSet cond target = 0 := by
  have hInter : p.probOfSet (cond ∩ target) = 0 :=
    le_antisymm (h ▸ probOfSet_inter_le_left p cond target) zero_le
  show p.toOuterMeasure (cond ∩ target) / p.toOuterMeasure cond = 0
  rw [show p.toOuterMeasure (cond ∩ target) = 0 from hInter,
      show p.toOuterMeasure cond = 0 from h, ENNReal.zero_div]

/-- `P(target | cond) + P(targetᶜ | cond) = 1` when `P(cond) > 0`. -/
theorem condProbSet_compl_sum (p : PMF α) (cond target : Set α)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ target)]
    (h : p.probOfSet cond > 0) :
    p.condProbSet cond target + p.condProbSet cond targetᶜ = 1 := by
  unfold condProbSet
  rw [ENNReal.div_add_div_same,
      show p.probOfSet (cond ∩ target) + p.probOfSet (cond ∩ targetᶜ)
           = p.probOfSet cond from (probOfSet_partition p cond target).symm]
  exact ENNReal.div_self h.ne' (probOfSet_ne_top p cond)

/-- Conditioning on the trivial evidence `Set.univ` leaves probabilities
unchanged: `P(target | univ) = P(target)`. -/
theorem condProbSet_univ (p : PMF α) (target : Set α) :
    p.condProbSet Set.univ target = p.probOfSet target := by
  rw [condProbSet_eq_div, Set.univ_inter, probOfSet_univ, div_one]

omit [Fintype α] in
/-- If `P(target | cond) > P(target)` then `P(cond) > 0`. -/
theorem probOfSet_pos_of_condProbSet_gt (p : PMF α) (cond target : Set α)
    (h : p.condProbSet cond target > p.probOfSet target) :
    p.probOfSet cond > 0 := by
  by_contra hle
  push Not at hle
  have hZero : p.probOfSet cond = 0 := le_antisymm hle zero_le
  rw [condProbSet_of_zero p cond target hZero] at h
  exact absurd h (not_lt.mpr zero_le)

/-- The "impact" of evidence `R` on proposition `A`: `P(A | R) / P(A)`.
The Bayes-factor face of conditional probability; equals `1` when `R`
provides no information about `A`, exceeds `1` when `R` raises `A`'s
probability, falls below `1` when `R` lowers it. Used in probabilistic
answerhood (Thomas 2026 Def. 62b) and structurally identical to RSA's
posterior-ratio update. -/
noncomputable def impactRatio (p : PMF α) (R A : Set α) : ℝ≥0∞ :=
  p.condProbSet R A / p.probOfSet A

/-- When `A ⊆ R ⊆ R'` and `P(R) < P(R')` strictly, conditioning on the
larger set `R'` strictly decreases `P(A | ·)` (for `A` of positive prior).

Proof: `condProbSet R A = P(A∩R)/P(R) = P(A)/P(R)` since `A ⊆ R`, and
similarly `condProbSet R' A = P(A)/P(R')`. The conclusion is then ENNReal
strict-antitone-in-denominator, `ENNReal.div_lt_div_left`. -/
theorem condProbSet_strict_anti_of_probOfSet_lt
    (p : PMF α) (A R R' : Set α)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ R)] [DecidablePred (· ∈ R')]
    (hAR : A ⊆ R) (hAR' : A ⊆ R')
    (hPosA : p.probOfSet A > 0)
    (hLt : p.probOfSet R < p.probOfSet R') :
    p.condProbSet R A > p.condProbSet R' A := by
  rw [condProbSet_eq_div, condProbSet_eq_div,
      Set.inter_eq_right.mpr hAR, Set.inter_eq_right.mpr hAR']
  exact ENNReal.div_lt_div_left hPosA.ne' (probOfSet_ne_top p A) hLt

/-! ### Conditional expectation given a set

`E[f ∣ A] = (∑_{a ∈ A} p(a) · f(a)) / P(A)`. Mathlib's heavy
`MeasureTheory.condExp` takes a sub-σ-algebra and produces a random
variable; the lightweight finite-PMF "expected value given a set" is
just a number. Equivalent (via `PMF.integral_eq_sum` and
`MeasureTheory.Measure.cond`) to `∫ f d(p.toMeasure.cond A)`; we keep
the direct `∑/∑` form for `decide`-checkability. -/

/-- Conditional expectation `E[f ∣ A]`. `Set.indicator` keeps the
signature decidability-free; ENNReal's `0/0 = 0` handles `P(A) = 0`. -/
noncomputable def condExpect (p : PMF α) (A : Set α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ a, A.indicator (fun a => p a * f a) a) / p.probOfSet A

/-- `condExpect` as an explicit ratio. -/
theorem condExpect_eq_div (p : PMF α) (A : Set α) (f : α → ℝ≥0∞) :
    p.condExpect A f = (∑ a, A.indicator (fun a => p a * f a) a) / p.probOfSet A := rfl

/-- When the value function is the indicator of `B`, `condExpect`
reduces to `condProbSet`. -/
theorem condExpect_indicator (p : PMF α) (A B : Set α) :
    p.condExpect A (B.indicator (fun _ => 1)) = p.condProbSet A B := by
  classical
  unfold condExpect condProbSet
  congr 1
  rw [PMF.toOuterMeasure_apply_fintype]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;>
    simp [hA, hB, Set.indicator, Set.mem_inter_iff]

/-- Linearity of `condExpect` in `f`. Not `@[simp]`: pointwise addition
is the simp normal form, so this lemma is for forward reasoning. -/
theorem condExpect_add (p : PMF α) (A : Set α) (f g : α → ℝ≥0∞) :
    p.condExpect A (f + g) = p.condExpect A f + p.condExpect A g := by
  classical
  unfold condExpect
  rw [ENNReal.div_add_div_same]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hA : a ∈ A
  · simp [hA, Set.indicator, Pi.add_apply, mul_add]
  · simp [hA, Set.indicator]

@[simp]
theorem condExpect_zero (p : PMF α) (A : Set α) : p.condExpect A 0 = 0 := by
  unfold condExpect
  simp [Set.indicator]

end PMF
