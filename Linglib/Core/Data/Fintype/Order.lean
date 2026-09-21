/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Basic

/-!
# Decidable order predicates on finite types

The pointwise order on `∀ i, α i` is decidable when the index type is finite and each
coordinate order is (mathlib's `DecidableLE (∀ a, β a)` instance in `Data/Fintype/Defs`); the
strict order follows as for any preorder with a decidable `≤`, as `Finsupp.decidableLT` does.
Minimality and maximality of an element are decidable on a finite type with a decidable `≤`.

`[UPSTREAM]` candidate for `Mathlib/Data/Fintype/Defs.lean`, beside the `DecidableLE` instance.
-/

@[expose] public section

namespace Fintype

variable {α : Type*} [Fintype α] [LE α] [DecidableLE α]

instance decidableIsMin (a : α) : Decidable (IsMin a) :=
  decidable_of_iff (∀ b, b ≤ a → a ≤ b) ⟨fun h _ hb ↦ h _ hb, fun h _ hb ↦ h hb⟩

instance decidableIsMax (a : α) : Decidable (IsMax a) :=
  decidable_of_iff (∀ b, a ≤ b → b ≤ a) ⟨fun h _ hb ↦ h _ hb, fun h _ hb ↦ h hb⟩

end Fintype

namespace Pi

variable {ι : Type*} {α : ι → Type*} [Fintype ι]

instance decidableLT [∀ i, Preorder (α i)] [∀ i, DecidableLE (α i)] :
    DecidableLT (∀ i, α i) :=
  decidableLTOfDecidableLE

end Pi
