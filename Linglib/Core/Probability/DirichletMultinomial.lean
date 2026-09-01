/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Probability.PolyaUrn
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real

/-!
# Pólya-urn laws: the sequence law and the Dirichlet–multinomial distribution

[odonnell-2015]

For a Pólya urn `u : PolyaUrn α`, `u.seqLaw N` is the law of `N` labelled draws — the
exchangeable sequence law with mass `u.seqProb (countVec seq)` at each `seq : Fin N → α` — and
`u.dirichletMultinomial N` is the law of the count vector, its pushforward along `countVec`. A
count vector `x` with `∑ i, x i = N` has mass `Nat.multinomial univ x * seqProb x`, since
`card_countVec_eq_multinomial` counts the sequences with count vector `x` as `N! / ∏ (x i)!`.

## Main definitions

* `PolyaUrn.seqLaw` — the sequence law, a probability measure on `Fin N → α`.
* `PolyaUrn.dirichletMultinomial` — the count law, a probability measure on `α → ℕ`.

## Main results

* `PolyaUrn.card_countVec_eq_multinomial` — sequences with a given count vector number the
  multinomial coefficient.
* `PolyaUrn.dirichletMultinomial_real_singleton` — the closed-form mass of a count vector.

Split from `PolyaUrn.lean` so that consumers of `seqProb` alone (the fragment grammars in
`Morphology/FragmentGrammars/`) do not import measure theory.
-/

open MeasureTheory
open scoped Nat

namespace ProbabilityTheory.PolyaUrn

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
    obtain rfl : x = fun _ => 0 :=
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
    hx (h ▸ sum_counts_eq_length seq)

section Laws

variable [MeasurableSpace α] [MeasurableSingletonClass α] (u : PolyaUrn α)

/-- The law of `N` labelled draws from the urn: the exchangeable sequence law, with mass
`seqProb (countVec seq)` at each sequence. -/
noncomputable def seqLaw (N : ℕ) : Measure (Fin N → α) :=
  Measure.sum fun seq => ENNReal.ofReal (u.seqProb (countVec seq)) • Measure.dirac seq

@[simp] theorem seqLaw_singleton (N : ℕ) (seq : Fin N → α) :
    u.seqLaw N {seq} = ENNReal.ofReal (u.seqProb (countVec seq)) :=
  Measure.sum_smul_dirac_singleton

/-- The Dirichlet–multinomial distribution: the law of the count vector of `N` draws from the
urn, the pushforward of the sequence law along `countVec`. -/
noncomputable def dirichletMultinomial (N : ℕ) : Measure (α → ℕ) := (u.seqLaw N).map countVec

theorem dirichletMultinomial_singleton (N : ℕ) (x : α → ℕ) :
    u.dirichletMultinomial N {x} =
      (Finset.univ.filter fun seq : Fin N → α => countVec seq = x).card *
        ENNReal.ofReal (u.seqProb x) := by
  rw [dirichletMultinomial,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x),
    show countVec ⁻¹' {x} = ↑(Finset.univ.filter fun seq : Fin N → α => countVec seq = x) by
      ext; simp,
    ← sum_measure_singleton, Finset.sum_congr rfl fun seq hseq => by
      rw [seqLaw_singleton, (Finset.mem_filter.mp hseq).2],
    Finset.sum_const, nsmul_eq_mul]

theorem dirichletMultinomial_singleton_of_sum_eq {N : ℕ} {x : α → ℕ} (hx : ∑ i, x i = N) :
    u.dirichletMultinomial N {x} =
      Nat.multinomial Finset.univ x * ENNReal.ofReal (u.seqProb x) := by
  rw [dirichletMultinomial_singleton, card_countVec_eq_multinomial hx]

theorem dirichletMultinomial_singleton_of_sum_ne {N : ℕ} {x : α → ℕ} (hx : ∑ i, x i ≠ N) :
    u.dirichletMultinomial N {x} = 0 := by
  rw [dirichletMultinomial_singleton, card_countVec_eq_zero hx, Nat.cast_zero, zero_mul]

end Laws

section Probability

variable [Nonempty α] (u : PolyaUrn α)

theorem hasSum_one_seqLaw (N : ℕ) :
    HasSum (fun seq : Fin N → α => u.seqProb (countVec seq)) 1 :=
  u.sum_seqProb_eq_one N ▸ hasSum_fintype _

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem seqLaw_real_singleton (N : ℕ) (seq : Fin N → α) :
    (u.seqLaw N).real {seq} = u.seqProb (countVec seq) := by
  rw [measureReal_def, seqLaw_singleton, ENNReal.toReal_ofReal (u.seqProb_pos _).le]

instance (N : ℕ) : IsProbabilityMeasure (u.seqLaw N) :=
  (u.hasSum_one_seqLaw N).isProbabilityMeasure_sum_dirac fun _ => (u.seqProb_pos _).le

instance (N : ℕ) : IsProbabilityMeasure (u.dirichletMultinomial N) :=
  Measure.isProbabilityMeasure_map .of_discrete

/-- The closed-form Dirichlet–multinomial mass: the multinomial coefficient times the
per-sequence likelihood `Γ(Σπ) / Γ(Σπ + N) · ∏ Γ(π_i + x_i) / Γ(π_i)`. -/
theorem dirichletMultinomial_real_singleton {N : ℕ} {x : α → ℕ} (hx : ∑ i, x i = N) :
    (u.dirichletMultinomial N).real {x} = Nat.multinomial Finset.univ x * u.seqProb x := by
  rw [measureReal_def, dirichletMultinomial_singleton_of_sum_eq u hx, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (u.seqProb_pos _).le]

theorem dirichletMultinomial_real_singleton_pos {N : ℕ} {x : α → ℕ} (hx : ∑ i, x i = N) :
    0 < (u.dirichletMultinomial N).real {x} := by
  rw [dirichletMultinomial_real_singleton u hx]
  exact mul_pos (Nat.cast_pos.mpr (Nat.multinomial_pos _ _)) (u.seqProb_pos x)

end Probability

end ProbabilityTheory.PolyaUrn
