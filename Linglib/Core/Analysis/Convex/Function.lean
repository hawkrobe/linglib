/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Analysis.Convex.Function

/-!
# Finite suprema of convex functions

`[UPSTREAM]` candidates for `Mathlib.Analysis.Convex.Function`: the finite
(`Finset.sup'`) generalization of `ConvexOn.sup`, and its concave dual. The
support function of a finite family of affine functionals — the "max of
affine is convex" fact underlying decision values, Bayes risk, and Blackwell
comparison — is the instance over a `Finset` of linear maps.
-/

open Finset

variable {𝕜 E β ι : Type*}

section LinearOrderedAddCommMonoid

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E}

/-- The pointwise supremum of a nonempty finite family of convex functions is
convex: the `Finset.sup'` generalization of `ConvexOn.sup`. -/
theorem convexOn_finset_sup' {t : Finset ι} (ht : t.Nonempty) {f : ι → E → β}
    (hf : ∀ i ∈ t, ConvexOn 𝕜 s (f i)) :
    ConvexOn 𝕜 s (fun x => t.sup' ht (f · x)) := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton i =>
    have h := hf i (mem_singleton_self i)
    simpa only [sup'_singleton] using h
  | cons i t hi ht ih =>
    have heq : (fun x => (cons i t hi).sup' (cons_nonempty hi) (f · x))
        = f i ⊔ fun x => t.sup' ht (f · x) :=
      funext (λ x => sup'_cons ht (f · x))
    rw [heq]
    exact (hf i (mem_cons_self i t)).sup
      (ih (λ j hj => hf j (mem_cons_of_mem hj)))

/-- The pointwise infimum of a nonempty finite family of concave functions is
concave: the `Finset.inf'` generalization of `ConcaveOn.inf`. -/
theorem concaveOn_finset_inf' {t : Finset ι} (ht : t.Nonempty) {f : ι → E → β}
    (hf : ∀ i ∈ t, ConcaveOn 𝕜 s (f i)) :
    ConcaveOn 𝕜 s (fun x => t.inf' ht (f · x)) :=
  convexOn_finset_sup' (β := βᵒᵈ) ht hf

end LinearOrderedAddCommMonoid
