/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Basic

/-!
# Decidable strict order on finite Pi types

The pointwise order on `∀ i, α i` is decidable when the index type is finite and each
coordinate order is (mathlib's `DecidableLE (∀ a, β a)` instance in `Data/Fintype/Defs`); the
strict order follows as for any preorder with a decidable `≤`, as `Finsupp.decidableLT` does.

`[UPSTREAM]` candidate for `Mathlib/Data/Fintype/Defs.lean`, beside the `DecidableLE` instance.
-/

namespace Pi

variable {ι : Type*} {α : ι → Type*} [Fintype ι]

instance decidableLT [∀ i, Preorder (α i)] [∀ i, DecidableLE (α i)] :
    DecidableLT (∀ i, α i) :=
  decidableLTOfDecidableLE

end Pi
