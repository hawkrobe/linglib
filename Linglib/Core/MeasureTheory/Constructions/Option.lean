/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# The measurable space on `Option`

`Option α` carries the image of the σ-algebra of `α` under `some`: a set is measurable when its
preimage under `some` is. The point `none` is an atom, `some` is a measurable embedding, and the
space is discrete when `α` is.

## Main results

* `measurableEmbedding_some`: `some` is a measurable embedding.
* `Option.measurableSet_iff`: measurability is measurability of the preimage under `some`.
-/

@[expose] public section

open MeasureTheory

namespace Option

variable {α : Type*}

private theorem preimage_some_singleton_none : some ⁻¹' ({none} : Set (Option α)) = ∅ := by
  ext; simp

private theorem preimage_some_singleton_some (a : α) :
    some ⁻¹' ({some a} : Set (Option α)) = {a} := by
  ext; simp

variable [m : MeasurableSpace α]

instance instMeasurableSpace : MeasurableSpace (Option α) := m.map some

theorem measurableSet_iff {s : Set (Option α)} : MeasurableSet s ↔ MeasurableSet (some ⁻¹' s) :=
  Iff.rfl

@[measurability]
theorem measurableSet_singleton_none : MeasurableSet ({none} : Set (Option α)) := by
  rw [measurableSet_iff, preimage_some_singleton_none]
  exact .empty

@[fun_prop]
theorem measurable_some : Measurable (some : α → Option α) := fun _ hs ↦ hs

instance [MeasurableSingletonClass α] : MeasurableSingletonClass (Option α) :=
  ⟨fun o ↦ by
    cases o with
    | none => exact measurableSet_singleton_none
    | some a => rw [measurableSet_iff, preimage_some_singleton_some]; exact .singleton a⟩

instance [DiscreteMeasurableSpace α] : DiscreteMeasurableSpace (Option α) :=
  ⟨fun _ ↦ measurableSet_iff.2 .of_discrete⟩

end Option

variable {α : Type*} [MeasurableSpace α]

theorem measurableEmbedding_some : MeasurableEmbedding (some : α → Option α) where
  injective := Option.some_injective α
  measurable := Option.measurable_some
  measurableSet_image' s hs := by
    rwa [Option.measurableSet_iff, Set.preimage_image_eq _ (Option.some_injective α)]
