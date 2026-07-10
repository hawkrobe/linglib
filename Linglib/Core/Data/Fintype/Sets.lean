/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Basic

/-!
# Set-subset decidability over finite types

`Set.decidableSubsetOfFintype` derives `Decidable (s ⊆ t)` from `Fintype`
plus decidable membership. Deliberately a `def`, not an `instance`,
following mathlib's `Set.decidableMemOfFintype`: global `Decidable`
instances on `Set` relations risk instance loops and higher-order
`DecidablePred` searches. Activate with
`attribute [local instance] Set.decidableSubsetOfFintype`.
-/

/-- `Decidable (s ⊆ t)` from `Fintype` plus decidable membership.
Not an instance; activate locally. -/
def Set.decidableSubsetOfFintype {α : Type*} [Fintype α]
    (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (s ⊆ t) :=
  show Decidable (∀ ⦃a⦄, a ∈ s → a ∈ t) from inferInstance
