/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Exchangeable
public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Linglib.Core.Probability.PolyaUrn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The Pólya urn and the Dirichlet–multinomial distribution

`polyaUrn θ n` is the law of the first `n` draws from the Pólya urn with weights `θ`: the
sequence drawn from the prediction rule `polyaUrnPredictive` of [pitman-2006] Exercise 2.2.2,
built with `seqLaw`. Each sequence has probability `polyaUrnProb θ (countVec s)`
(`polyaUrn_real_singleton`), which depends only on the counts, so the sequence is exchangeable
(`exchangeable_polyaUrn`). The *Dirichlet–multinomial distribution* `dirichletMultinomial θ n` is
the law of the count vector; a count vector `x` with `∑ i, x i = n` has probability
`Nat.multinomial univ x * polyaUrnProb θ x`, since `card_countVec_eq_multinomial` counts the
sequences with counts `x`.

## Main definitions

* `ProbabilityTheory.polyaUrnRule θ n`: the prediction rule as a kernel.
* `ProbabilityTheory.polyaUrn θ n`: the law of the first `n` draws.
* `ProbabilityTheory.dirichletMultinomial θ n`: the law of their count vector.

## Main results

* `ProbabilityTheory.isProbabilityMeasure_polyaUrn`.
* `ProbabilityTheory.polyaUrn_real_singleton`: the probability of a sequence.
* `ProbabilityTheory.exchangeable_polyaUrn`: the drawn sequence is exchangeable.
* `ProbabilityTheory.card_countVec_eq_multinomial`: sequences with given counts number the
  multinomial coefficient.
* `ProbabilityTheory.dirichletMultinomial_real_singleton`: the probability of a count vector.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal Nat

namespace ProbabilityTheory

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Length-`(N + 1)` sequences with count vector `x` ending in `c` are the `snoc`s of the
length-`N` sequences with one fewer `c`. -/
private theorem filter_countVec_eq_image_snoc {N : ℕ} (x : α → ℕ) (c : α) (hc : 0 < x c) :
    (Finset.univ.filter fun seq : Fin (N + 1) → α => countVec seq = x ∧ seq (Fin.last N) = c) =
      (Finset.univ.filter fun seq : Fin N → α =>
        countVec seq = Function.update x c (x c - 1)).image (Fin.snoc · c) := by
  ext seq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hx, hlast⟩
    have hseq : Fin.snoc (Fin.init seq) c = seq := by rw [← hlast]; exact Fin.snoc_init_self seq
    refine ⟨Fin.init seq, funext fun d => ?_, hseq⟩
    have h : Function.update (countVec (Fin.init seq)) c (countVec (Fin.init seq) c + 1) = x := by
      rw [← countVec_snoc, hseq, hx]
    replace h := congrFun h d
    obtain rfl | hd := eq_or_ne d c
    · rw [Function.update_self] at h ⊢; omega
    · rwa [Function.update_of_ne hd] at h ⊢
  · rintro ⟨seq', hseq', rfl⟩
    refine ⟨?_, Fin.snoc_last _ _⟩
    rw [countVec_snoc, hseq', Function.update_self, Function.update_idem, Nat.sub_add_cancel hc,
      Function.update_eq_self]

private theorem card_countVec_mul_prod_factorial :
    ∀ (N : ℕ) (x : α → ℕ), ∑ i, x i = N →
      (Finset.univ.filter fun seq : Fin N → α => countVec seq = x).card * ∏ i, (x i)! = N !
  | 0, x, hx => by
    obtain rfl : x = 0 :=
      funext fun i => Finset.sum_eq_zero_iff.mp hx i (Finset.mem_univ _)
    simp
  | N + 1, x, hx => by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun seq => seq (Fin.last N))
      (t := Finset.univ) fun _ _ => Finset.mem_univ _, Finset.sum_mul]
    have key : ∀ c, ((Finset.univ.filter fun seq : Fin (N + 1) → α => countVec seq = x).filter
        fun seq => seq (Fin.last N) = c).card * ∏ i, (x i)! = x c * N ! := by
      intro c
      rw [Finset.filter_filter]
      obtain hc | hc := Nat.eq_zero_or_pos (x c)
      · rw [hc, zero_mul, Finset.card_eq_zero.mpr, zero_mul]
        refine Finset.filter_eq_empty_iff.mpr fun seq _ ⟨hcv, hlast⟩ => ?_
        have : 0 < countVec seq c :=
          Finset.card_pos.mpr ⟨Fin.last N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlast⟩⟩
        rw [hcv] at this
        omega
      · have hsum : ∑ i, Function.update x c (x c - 1) i = N := by
          rw [Finset.sum_update_of_mem (Finset.mem_univ c), Finset.sdiff_singleton_eq_erase]
          have := Finset.add_sum_erase Finset.univ x (Finset.mem_univ c)
          omega
        have hprod : ∏ i, (x i)! = x c * ∏ i, (Function.update x c (x c - 1) i)! := by
          simp_rw [Function.apply_update (fun _ n => n !) x c (x c - 1)]
          rw [Finset.prod_update_of_mem (Finset.mem_univ c), ← mul_assoc,
            Nat.mul_factorial_pred hc.ne', Finset.sdiff_singleton_eq_erase,
            ← Finset.mul_prod_erase Finset.univ (fun i => (x i)!) (Finset.mem_univ c)]
        rw [filter_countVec_eq_image_snoc x c hc,
          Finset.card_image_of_injective _ fun a b h => by simpa using congrArg Fin.init h,
          hprod, mul_left_comm, card_countVec_mul_prod_factorial N _ hsum]
    rw [Finset.sum_congr rfl fun c _ => key c, ← Finset.sum_mul, hx, Nat.factorial_succ]

/-- The number of length-`N` draw sequences with count vector `x` is the multinomial
coefficient `N! / ∏ (x i)!`. -/
theorem card_countVec_eq_multinomial {N : ℕ} {x : α → ℕ} (hx : ∑ i, x i = N) :
    (Finset.univ.filter fun seq : Fin N → α => countVec seq = x).card =
      Nat.multinomial Finset.univ x :=
  Nat.eq_of_mul_eq_mul_right (Finset.prod_pos fun _ _ => Nat.factorial_pos _)
    ((card_countVec_mul_prod_factorial N x hx).trans
      (by rw [mul_comm, Nat.multinomial_spec, hx]))

/-- No length-`N` sequence has a count vector of total other than `N`. -/
theorem card_countVec_eq_zero {N : ℕ} {x : α → ℕ} (hx : ∑ i, x i ≠ N) :
    (Finset.univ.filter fun seq : Fin N → α => countVec seq = x).card = 0 :=
  Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun seq _ h =>
    hx (h ▸ sum_countVec seq)

variable [MeasurableSpace α] [MeasurableSingletonClass α] (θ : α → ℝ)

/-- The Pólya urn prediction rule as a kernel: after the draws `s`, colour `c` is drawn with
probability `polyaUrnPredictive θ (countVec s) c`. -/
noncomputable def polyaUrnRule (n : ℕ) : Kernel (Fin n → α) α :=
  Kernel.ofFunOfCountable fun s ↦
    ∑ c, ENNReal.ofReal (polyaUrnPredictive θ (countVec s) c) • Measure.dirac c

/-- The *Pólya urn*: the law of the first `n` draws from the urn with weights `θ`. -/
noncomputable def polyaUrn (n : ℕ) : Measure (Fin n → α) :=
  seqLaw (polyaUrnRule θ) n

/-- The *Dirichlet–multinomial distribution*: the law of the count vector of `n` draws from the
urn with weights `θ`. -/
noncomputable def dirichletMultinomial (n : ℕ) : Measure (α → ℕ) :=
  (polyaUrn θ n).map countVec

theorem polyaUrnRule_apply_singleton {n : ℕ} (s : Fin n → α) (c : α) :
    polyaUrnRule θ n s {c} = ENNReal.ofReal (polyaUrnPredictive θ (countVec s) c) := by
  simp only [polyaUrnRule, Kernel.ofFunOfCountable, Kernel.coe_mk, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single c (fun d _ hd ↦ by
    simp [Measure.dirac_apply' _ (measurableSet_singleton c), Ne.symm hd]) (by simp)]
  simp

variable {θ} [Nonempty α] (hθ : ∀ i, 0 < θ i)
include hθ

theorem isMarkovKernel_polyaUrnRule (n : ℕ) : IsMarkovKernel (polyaUrnRule θ n) := by
  refine ⟨fun s ↦ ⟨?_⟩⟩
  simp only [polyaUrnRule, Kernel.ofFunOfCountable, Kernel.coe_mk, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun c _ ↦
      polyaUrnPredictive_nonneg (fun i ↦ (hθ i).le) _ c, sum_polyaUrnPredictive hθ,
    ENNReal.ofReal_one]

theorem isProbabilityMeasure_polyaUrn (n : ℕ) : IsProbabilityMeasure (polyaUrn θ n) :=
  have := isMarkovKernel_polyaUrnRule hθ
  isProbabilityMeasure_seqLaw n

/-- The probability that the urn draws the sequence `s` is `polyaUrnProb θ (countVec s)`. -/
theorem polyaUrn_singleton : ∀ {n : ℕ} (s : Fin n → α),
    polyaUrn θ n {s} = ENNReal.ofReal (polyaUrnProb θ (countVec s))
  | 0, s => by simp [polyaUrn, Subsingleton.elim s default]
  | n + 1, s => by
    have := isMarkovKernel_polyaUrnRule hθ
    rw [polyaUrn, ← Fin.snoc_init_self s, seqLaw_succ_singleton_snoc, ← polyaUrn,
      polyaUrn_singleton, polyaUrnRule_apply_singleton,
      ← ENNReal.ofReal_mul (polyaUrnProb_pos hθ _).le, polyaUrnProb_countVec_snoc]

theorem polyaUrn_real_singleton {n : ℕ} (s : Fin n → α) :
    (polyaUrn θ n).real {s} = polyaUrnProb θ (countVec s) := by
  rw [measureReal_def, polyaUrn_singleton hθ, ENNReal.toReal_ofReal (polyaUrnProb_pos hθ _).le]

/-- The sequence drawn from a Pólya urn is exchangeable ([pitman-2006] Exercise 2.2.2). -/
theorem exchangeable_polyaUrn (n : ℕ) : Exchangeable (polyaUrn θ n) :=
  exchangeable_of_measure_singleton fun s σ ↦ by
    rw [polyaUrn_singleton hθ, polyaUrn_singleton hθ, countVec_comp_perm]

theorem isProbabilityMeasure_dirichletMultinomial (n : ℕ) :
    IsProbabilityMeasure (dirichletMultinomial θ n) :=
  have := isProbabilityMeasure_polyaUrn hθ n
  (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 inferInstance

theorem dirichletMultinomial_singleton (n : ℕ) (x : α → ℕ) :
    dirichletMultinomial θ n {x} =
      #{s : Fin n → α | countVec s = x} * ENNReal.ofReal (polyaUrnProb θ x) := by
  rw [dirichletMultinomial,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x),
    show countVec ⁻¹' {x} = ↑({s : Fin n → α | countVec s = x} : Finset _) by ext; simp,
    ← sum_measure_singleton, Finset.sum_congr rfl fun s hs ↦ by
      rw [polyaUrn_singleton hθ, (Finset.mem_filter.mp hs).2],
    Finset.sum_const, nsmul_eq_mul]

/-- The Dirichlet–multinomial probability of a count vector of total `n`: the multinomial
coefficient times the probability of any one sequence with those counts. -/
theorem dirichletMultinomial_real_singleton {n : ℕ} {x : α → ℕ} (hx : ∑ i, x i = n) :
    (dirichletMultinomial θ n).real {x} = Nat.multinomial univ x * polyaUrnProb θ x := by
  rw [measureReal_def, dirichletMultinomial_singleton hθ, card_countVec_eq_multinomial hx,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (polyaUrnProb_pos hθ _).le]

theorem dirichletMultinomial_singleton_of_sum_ne {n : ℕ} {x : α → ℕ} (hx : ∑ i, x i ≠ n) :
    dirichletMultinomial θ n {x} = 0 := by
  rw [dirichletMultinomial_singleton hθ, card_countVec_eq_zero hx, Nat.cast_zero, zero_mul]

end ProbabilityTheory
