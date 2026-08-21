import Linglib.Semantics.Modality.Kratzer.Ordering
import Mathlib.Order.Preorder.Finite

/-!
# Best-worlds desire semantics

`a wants p` iff every best belief-world is a `p`-world, where belief-worlds are ordered by
the desires they satisfy — [von-fintel-1999]'s semantics, with [kratzer-1981]'s ordering
over the desire propositions. Some belief-world is always best on a finite frame
(`exists_undominated`), so `p` and `¬p` cannot both be wanted (`Want.not_compl`); the
semantics is upward monotone in `p` (`Want.mono`), which is the doxastic-closure problem
of [villalta-2008].
-/

namespace Desire.BestWorlds

open Modality.Kratzer

variable {W : Type*} (G : List (Finset W)) (bel p : Set W)

/-- `le G w z`: every desire in `G` satisfied at `z` is satisfied at `w`. -/
def le (w z : W) : Prop := atLeastAsGoodAs (G.map fun s w => w ∈ s) w z

theorem le_iff (w z : W) : le G w z ↔ ∀ s ∈ G, z ∈ s → w ∈ s := by
  simp [le, atLeastAsGoodAs_iff]

instance [DecidableEq W] (w z : W) : Decidable (le G w z) :=
  decidable_of_iff _ (le_iff G w z).symm

/-- No belief-world is strictly better than `w`. -/
def Undominated (w : W) : Prop := ∀ z ∈ bel, le G z w → le G w z

/-- `a wants p`: every best belief-world is a `p`-world. -/
def Want : Prop := ∀ w ∈ bel, Undominated G bel w → w ∈ p

section Decidable

instance [Fintype W] [DecidableEq W] [DecidablePred (· ∈ bel)] (w : W) :
    Decidable (Undominated G bel w) :=
  inferInstanceAs (Decidable (∀ z ∈ bel, le G z w → le G w z))

instance [Fintype W] [DecidableEq W] [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] :
    Decidable (Want G bel p) :=
  inferInstanceAs (Decidable (∀ w ∈ bel, Undominated G bel w → w ∈ p))

end Decidable

/-- On a finite frame every nonempty belief state has a best world. -/
theorem exists_undominated [Finite W] (h : bel.Nonempty) :
    ∃ w ∈ bel, Undominated G bel w := by
  let _ := kratzerPreorder (G.map fun s w => w ∈ s)
  obtain ⟨m, hm, hmin⟩ := Set.Finite.exists_minimal (Set.toFinite bel) h
  exact ⟨m, hm, fun z hz hzm => hmin hz hzm⟩

variable {G bel p}

theorem Want.not_compl [Finite W] (h : bel.Nonempty) (hp : Want G bel p) :
    ¬ Want G bel pᶜ := fun hnp =>
  let ⟨w, hw, hu⟩ := exists_undominated G bel h
  hnp w hw hu (hp w hw hu)

theorem Want.mono {q : Set W} (hpq : p ⊆ q) (h : Want G bel p) : Want G bel q :=
  fun w hw hu => hpq (h w hw hu)

end Desire.BestWorlds
