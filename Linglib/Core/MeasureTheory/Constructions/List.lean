/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measures on lists

Lists carry the discrete σ-algebra, so every function out of a list type is measurable and, over
a countable type, every measure on lists is s-finite. `Measure.listProd` is the law of a list of
independent draws, one from each measure in a list of measures: the `List`-indexed product
measure, built from the binary product.

## Main definitions

* `MeasureTheory.Measure.listProd`: the product of a list of measures.

## Main results

* `MeasureTheory.Measure.listProd_cons_singleton_cons`: the product measure of a singleton list is
  the product of the singleton measures.
* `MeasureTheory.Measure.ωScottContinuous_listProd`: the product is ω-Scott-continuous in each
  factor.

## Implementation notes

The discrete σ-algebra is the only reasonable choice on lists over a countable discrete type,
which is the case of interest for derivation trees and branching processes; it is registered
globally here as the library's convention.
-/

open MeasureTheory OmegaCompletePartialOrder
open scoped ENNReal

instance {α : Type*} : MeasurableSpace (List α) := ⊤

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- The law of a list of independent draws, one from each measure in the list. -/
noncomputable def listProd : List (Measure α) → Measure (List α)
  | [] => dirac []
  | μ :: μs => (μ.prod (listProd μs)).map (Function.uncurry List.cons)

@[simp] theorem listProd_nil : listProd ([] : List (Measure α)) = dirac [] := rfl

theorem listProd_cons (μ : Measure α) (μs : List (Measure α)) :
    listProd (μ :: μs) = (μ.prod (listProd μs)).map (Function.uncurry List.cons) := rfl

@[simp] theorem listProd_nil_singleton_cons (x : α) (xs : List α) :
    listProd ([] : List (Measure α)) {x :: xs} = 0 := by
  rw [listProd_nil, dirac_apply' _ .of_discrete]
  simp

variable [Countable α] [MeasurableSingletonClass α]

theorem isProbabilityMeasure_listProd {μs : List (Measure α)}
    (h : ∀ μ ∈ μs, IsProbabilityMeasure μ) : IsProbabilityMeasure (listProd μs) := by
  induction μs with
  | nil => rw [listProd_nil]; infer_instance
  | cons μ μs ih =>
    have := ih fun ν hν => h ν (List.mem_cons_of_mem _ hν)
    have := h μ (List.mem_cons_self ..)
    rw [listProd_cons]
    exact isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

theorem listProd_univ_le_one {μs : List (Measure α)} (h : ∀ μ ∈ μs, μ Set.univ ≤ 1) :
    listProd μs Set.univ ≤ 1 := by
  induction μs with
  | nil => simp
  | cons μ μs ih =>
    rw [listProd_cons, map_apply .of_discrete .univ, Set.preimage_univ, ← Set.univ_prod_univ,
      prod_prod]
    exact mul_le_one' (h μ (List.mem_cons_self ..)) (ih fun ν hν => h ν (List.mem_cons_of_mem _ hν))

@[simp] theorem listProd_cons_singleton_nil (μ : Measure α) (μs : List (Measure α)) :
    listProd (μ :: μs) {[]} = 0 := by
  rw [listProd_cons, map_apply .of_discrete .of_discrete]
  convert measure_empty (μ := μ.prod (listProd μs))
  ext ⟨_, _⟩
  simp

@[simp] theorem listProd_cons_singleton_cons (μ : Measure α) (μs : List (Measure α)) (x : α)
    (xs : List α) : listProd (μ :: μs) {x :: xs} = μ {x} * listProd μs {xs} := by
  rw [listProd_cons, map_apply .of_discrete .of_discrete, ← prod_prod]
  congr 1
  ext ⟨_, _⟩
  simp

variable {γ : Type*} [OmegaCompletePartialOrder γ]

theorem ωScottContinuous_listProd {ι : Type*} {F : ι → γ → Measure α} {l : List ι}
    (hF : ∀ i ∈ l, ωScottContinuous (F i)) :
    ωScottContinuous fun x => listProd (l.map fun i => F i x) := by
  induction l with
  | nil => exact ωScottContinuous.const
  | cons i l ih =>
    simp only [List.map_cons, listProd_cons]
    exact ωScottContinuous_map (ωScottContinuous_prod (hF i (List.mem_cons_self ..))
      (ih fun j hj => hF j (List.mem_cons_of_mem _ hj))) .of_discrete

end MeasureTheory.Measure
