/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Basic

/-!
# Decidable order on finite Pi types

The pointwise order on `∀ i, α i` is decidable when the index type is finite and each
coordinate order is, since `f ≤ g` is `∀ i, f i ≤ g i`; the strict order follows as for any
preorder with a decidable `≤`, as `Finsupp.decidableLE` and `Finsupp.decidableLT` do.

`[UPSTREAM]` candidate for `Mathlib/Data/Fintype/Defs.lean`, beside
`Fintype.decidablePiFintype`.
-/

namespace Pi

variable {ι : Type*} {α : ι → Type*} [Fintype ι]

instance decidableLE [∀ i, LE (α i)] [∀ i, DecidableLE (α i)] : DecidableLE (∀ i, α i) :=
  λ f g => inferInstanceAs (Decidable (∀ i, f i ≤ g i))

instance decidableLT [∀ i, Preorder (α i)] [∀ i, DecidableLE (α i)] :
    DecidableLT (∀ i, α i) :=
  decidableLTOfDecidableLE

end Pi
