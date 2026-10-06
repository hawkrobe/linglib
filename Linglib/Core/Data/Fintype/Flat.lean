/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Linglib.Core.Order.Flat

/-!
# Fintype instances for `Flat α`

`Flat α` carries the elements of `Option α`, so it is finite when `α` is, with one more element.

[UPSTREAM] beside `Mathlib/Data/Fintype/WithTopBot.lean`, once `Flat` is upstream.
-/

@[expose] public section

variable {α : Type*}

instance [Fintype α] : Fintype (Flat α) :=
  inferInstanceAs <| Fintype (Option α)

instance [Finite α] : Finite (Flat α) :=
  inferInstanceAs <| Finite (Option α)

theorem Fintype.card_flat [Fintype α] : Fintype.card (Flat α) = Fintype.card α + 1 :=
  Fintype.card_option
