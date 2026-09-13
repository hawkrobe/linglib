import Linglib.Semantics.Modality.Kratzer.Ordering

/-!
# Best-worlds desire semantics

`a wants p` iff every best belief-world is a `p`-world, where belief-worlds are ordered by
the desires they satisfy: [von-fintel-1999]'s semantics, [kratzer-1981]'s ordering with the
desire propositions as ordering source and the belief set as domain, so that *want* is
Kratzer's necessity over the best belief-worlds (`Want`, `Modality.Kratzer.bestAmong`). Some
belief-world is always best on a finite frame, so `p` and `¬p` cannot both be wanted
(`Want.not_compl`); the semantics is upward monotone in `p` (`Want.mono`), which is the
doxastic-closure problem of [villalta-2008].

## References

* [von-fintel-1999]
* [kratzer-1981]
* [villalta-2008]
-/

namespace Desire.BestWorlds

open Modality.Kratzer

variable {W : Type*} (G : List (Finset W)) (bel p : Set W)

/-- The desires as an ordering source. -/
def source : List (W → Prop) := G.map λ s w => w ∈ s

/-- `le G w z`: every desire in `G` satisfied at `z` is satisfied at `w`. -/
abbrev le (w z : W) : Prop := w ≤[source G] z

theorem le_iff (w z : W) : le G w z ↔ ∀ s ∈ G, z ∈ s → w ∈ s := by
  simp [source, atLeastAsGoodAs_iff]

/-- `a wants p`: every best belief-world is a `p`-world. -/
def Want : Prop := ∀ w ∈ bestAmong bel (source G), w ∈ p

theorem mem_bestAmong_source (w : W) :
    w ∈ bestAmong bel (source G) ↔ w ∈ bel ∧ ∀ z ∈ bel, le G z w → le G w z :=
  Iff.rfl

theorem want_iff : Want G bel p ↔ ∀ w ∈ bel, (∀ z ∈ bel, le G z w → le G w z) → w ∈ p :=
  ⟨λ h w hw hb => h w ⟨hw, hb⟩, λ h w hw => h w hw.1 hw.2⟩

section Decidable

instance [DecidableEq W] (w z : W) : Decidable (le G w z) :=
  decidable_of_iff _ (le_iff G w z).symm

instance [Fintype W] [DecidableEq W] [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] :
    Decidable (Want G bel p) :=
  decidable_of_iff _ (want_iff G bel p).symm

end Decidable

variable {G bel p}

theorem Want.not_compl [Finite W] (h : bel.Nonempty) (hp : Want G bel p) :
    ¬ Want G bel pᶜ := λ hnp =>
  let ⟨w, hw⟩ := exists_mem_bestAmong (A := source G) h
  hnp w hw (hp w hw)

/-- Closure under doxastic entailment: what is wanted is wanted under every consequence the
agent believes it to have, the doxastic-closure problem of [villalta-2008]. -/
theorem Want.mono_on {q : Set W} (hpq : ∀ w ∈ bel, w ∈ p → w ∈ q) (h : Want G bel p) :
    Want G bel q :=
  λ w hw => hpq w hw.1 (h w hw)

theorem Want.mono {q : Set W} (hpq : p ⊆ q) (h : Want G bel p) : Want G bel q :=
  h.mono_on λ _ _ hw => hpq hw

end Desire.BestWorlds
