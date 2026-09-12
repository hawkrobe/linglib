/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.BourbakiWitt

/-!
# ω-suprema in complete lattices

Every complete lattice is an ω-complete partial order (through `ChainCompletePartialOrder`), and
there the ω-supremum of a chain is its indexed supremum. `[UPSTREAM]` candidate for
`Mathlib/Order/OmegaCompletePartialOrder.lean`.
-/

open OmegaCompletePartialOrder

/-- On a complete lattice, the ω-supremum of a chain is its indexed supremum. -/
theorem CompleteLattice.ωSup_eq_iSup {L : Type*} [CompleteLattice L] (c : Chain L) :
    ωSup c = ⨆ n, c n :=
  le_antisymm (ωSup_le _ _ fun n => le_iSup (fun n => c n) n) (iSup_le fun n => le_ωSup c n)
