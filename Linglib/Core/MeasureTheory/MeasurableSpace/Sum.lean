/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Singletons in a sum of measurable spaces

A singleton in `α ⊕ β` is the image of a singleton under `Sum.inl` or `Sum.inr`, so it is
measurable when singletons in `α` and `β` are. `[UPSTREAM]` candidate for
`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`.
-/

instance Sum.instMeasurableSingletonClass {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton
    | .inl a => Set.image_singleton ▸ measurableSet_inl_image.2 (measurableSet_singleton a)
    | .inr b => Set.image_singleton ▸ measurableSet_inr_image.2 (measurableSet_singleton b)
