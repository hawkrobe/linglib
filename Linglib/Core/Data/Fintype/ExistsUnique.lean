/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Defs

/-!
# Decidability of unique existence on a finite type

`∃! a, p a` unfolds to an existential bounded by a universal, both decidable
over a `Fintype`, so unique existence is decidable. Mathlib has the
list-bounded version (`List.decidableBExistsUnique`) but no `Fintype`
instance.

[UPSTREAM] `Mathlib.Data.Fintype.Defs`, beside `Fintype.decidableExistsFintype`.
-/

instance Fintype.decidableExistsUniqueFintype {α : Type*} {p : α → Prop}
    [DecidablePred p] [Fintype α] [DecidableEq α] :
    Decidable (∃! a, p a) :=
  decidable_of_iff (∃ a, p a ∧ ∀ b, p b → b = a) Iff.rfl
