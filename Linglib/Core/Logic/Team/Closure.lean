import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.SupClosed
import Mathlib.Order.Ideal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Union

/-!
# Flatness of team-sets

A team-set `T : Set (Finset α)` is *flat* if its membership reduces
pointwise: `s ∈ T ↔ ∀ w ∈ s, {w} ∈ T`. This file states Anttila's
Definition 2.2.1 and proves the closure-property characterisation
(Anttila Proposition 2.2.2): a flat team-set is downward-closed,
sup-closed, and contains `∅`.

Over `SemilatticeSup`-with-`OrderBot` carriers (which `Finset α` is)
the three closure properties coincide with the data of an
`Order.IsIdeal`: sup-closure ⟺ directedness (via
`SupClosed.directedOn`), and `∅ ∈ T` ⟺ `T.Nonempty` (via
`IsLowerSet.bot_mem`, both in mathlib). This file proves the bridge
`IsFlat T ↔ Order.IsIdeal T`, exposing mathlib's order-ideal
infrastructure to consumers of `IsFlat`.

## Main definitions

* `Core.Logic.Team.IsFlat T` — Anttila's pointwise flatness predicate.

## Main results

* `Core.Logic.Team.isFlat_iff` — Anttila Proposition 2.2.2.
* `Core.Logic.Team.isFlat_iff_isIdeal` — flat team-sets are precisely
  the carriers of order-ideals of `Finset α`.

## References

* Anttila, *The Logic of Free Choice*, MSc thesis 2021, Definition
  2.2.1 + Proposition 2.2.2.
* Väänänen, *Dependence Logic*, Cambridge University Press 2007.

## TODO

* Generalise `IsFlat` to atomistic lattices (`[SemilatticeSup L]
  [OrderBot L] [IsAtomistic L]`) once a non-`Finset` consumer surfaces.
-/

namespace Core.Logic.Team

variable {α : Type*} [DecidableEq α]

/-- A team-set `T : Set (Finset α)` is **flat** iff membership reduces
    pointwise: `s ∈ T ↔ every singleton from s is in T`.

    Anttila Definition 2.2.1 (the "for all w ∈ s" Yang-Väänänen
    formulation). Equivalent characterisations: `isFlat_iff` (via
    closure properties), `isFlat_iff_isIdeal` (via `Order.IsIdeal`). -/
def IsFlat (T : Set (Finset α)) : Prop :=
  ∀ s : Finset α, s ∈ T ↔ ∀ w ∈ s, ({w} : Finset α) ∈ T

/-- **Anttila Proposition 2.2.2**: a team-set is flat iff it is
    downward-closed under inclusion, closed under binary union, and
    contains the empty team. -/
theorem isFlat_iff (T : Set (Finset α)) :
    IsFlat T ↔ IsLowerSet T ∧ SupClosed T ∧ ∅ ∈ T := by
  constructor
  · intro hFlat
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab hb
      rw [hFlat]
      intro w hwa
      rw [hFlat] at hb
      exact hb w (hab hwa)
    · intro a ha b hb
      rw [hFlat]
      intro w hwab
      have hwab' : w ∈ a ∪ b := hwab
      rw [Finset.mem_union] at hwab'
      cases hwab' with
      | inl hwa => rw [hFlat] at ha; exact ha w hwa
      | inr hwb => rw [hFlat] at hb; exact hb w hwb
    · rw [hFlat]
      intro w hw
      exact absurd hw (Finset.notMem_empty w)
  · rintro ⟨hLower, hSup, hEmpty⟩
    intro s
    refine ⟨?_, ?_⟩
    · intro hs w hw
      exact hLower (show ({w} : Finset α) ≤ s from
        Finset.singleton_subset_iff.mpr hw) hs
    · intro hAll
      induction s using Finset.induction with
      | empty => exact hEmpty
      | @insert w t hwt ih =>
        have hsing : ({w} : Finset α) ∈ T :=
          hAll w (Finset.mem_insert_self w t)
        have ht : t ∈ T :=
          ih (fun w' hw' => hAll w' (Finset.mem_insert_of_mem hw'))
        rw [show insert w t = ({w} : Finset α) ∪ t from
          (Finset.singleton_union w t).symm]
        exact hSup hsing ht

theorem isFlat_of_isLowerSet_supClosed_empty {T : Set (Finset α)}
    (hLower : IsLowerSet T) (hSup : SupClosed T) (hEmpty : ∅ ∈ T) :
    IsFlat T :=
  (isFlat_iff T).mpr ⟨hLower, hSup, hEmpty⟩

theorem IsFlat.isLowerSet {T : Set (Finset α)} (h : IsFlat T) : IsLowerSet T :=
  ((isFlat_iff T).mp h).1

theorem IsFlat.supClosed {T : Set (Finset α)} (h : IsFlat T) : SupClosed T :=
  ((isFlat_iff T).mp h).2.1

theorem IsFlat.empty_mem {T : Set (Finset α)} (h : IsFlat T) : ∅ ∈ T :=
  ((isFlat_iff T).mp h).2.2

/-- Anttila Proposition 2.2.2 restated via `Order.IsIdeal`: flat
    team-sets are precisely the carriers of order-ideals of `Finset α`.

    Over `SemilatticeSup` + `OrderBot` the three closure-property
    coordinates of `IsFlat` translate to the three ideal-axiom
    coordinates: `SupClosed ↔ DirectedOn (·≤·)` (in `SemilatticeSup`)
    and `∅ ∈ T ↔ T.Nonempty` (in `OrderBot`, for lower sets). -/
theorem isFlat_iff_isIdeal (T : Set (Finset α)) :
    IsFlat T ↔ Order.IsIdeal T := by
  rw [isFlat_iff]
  refine ⟨fun ⟨hL, hS, hE⟩ => ⟨hL, ⟨∅, hE⟩, hS.directedOn⟩,
          fun ⟨hL, hne, hd⟩ => ⟨hL, ?_, hL.bot_mem.mpr hne⟩⟩
  intro a ha b hb
  obtain ⟨c, hc, hac, hbc⟩ := hd a ha b hb
  exact hL (sup_le hac hbc) hc

end Core.Logic.Team
