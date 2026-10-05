module

public import Linglib.Semantics.Modality.Kratzer.Ordering
public import Linglib.Semantics.Presupposition.Defs

/-!
# Best-worlds desire semantics

On the best-worlds semantics, *a wants p* when the best worlds of a domain, ranked by the
subject's preferences as a Kratzer ordering source, are `p`-worlds (`Want`). Von Fintel takes the
domain to be the worlds compatible with what the subject believes whatever she chooses to do,
and gives *want*, *glad* and *sorry* one family of entries: *want* presupposes that its domain
contains both `p`-worlds and non-`p`-worlds, *glad* adds that the subject believes `p` and that
the domain contains her belief worlds, and *sorry* has the presupposition of *glad* and the
assertion of wanting `p` false.

## Main definitions

* `Desire.BestWorlds.Want`: the best worlds of a domain under an ordering source are `p`-worlds.
* `Desire.BestWorlds.want`, `Desire.BestWorlds.glad`, `Desire.BestWorlds.regret`: von Fintel's
  entries as partial propositions, with world-indexed belief worlds, domain and ordering source.

## Main results

* `Desire.BestWorlds.Want.not_compl`: on a finite frame `p` and `¬p` are not both wanted.
* `Desire.BestWorlds.Want.mono`: the semantics is upward monotone in `p`, the doxastic-closure
  problem Villalta raises.
* `Desire.BestWorlds.want_inter_iff`: wanting a conjunction is wanting each conjunct, which makes
  *sorry* anti-additive in its complement.

## Implementation notes

The domain is a parameter. Von Fintel's is the set DOX* of worlds compatible with what the subject
believes however she acts, a superset of her belief worlds; Phillips-Brown's rendering takes the
belief worlds themselves. Von Fintel's condition that the domain of *want* be DOX* constrains the
domain rather than the complement and is left to the caller. Desires given as finite sets of
worlds enter as an ordering source through `source`.

## References

* [von-fintel-1999]
* [heim-1992]
* [kratzer-1981]
* [villalta-2008]
* [phillips-brown-2025]
-/

@[expose] public section

namespace Desire.BestWorlds

open Modality Presupposition

variable {W : Type*}

/-! ### Wanting over a domain -/

section Want

/-- `Want A dom p` holds when every best world of `dom` under the ordering source `A` is a
`p`-world. -/
def Want (A : List (W → Prop)) (dom p : Set W) : Prop := bestAmong dom A ⊆ p

variable {A : List (W → Prop)} {dom p q : Set W}

theorem want_iff_forall : Want A dom p ↔ ∀ w ∈ bestAmong dom A, w ∈ p := Iff.rfl

/-- Wanting a conjunction is wanting each conjunct. -/
theorem want_inter_iff : Want A dom (p ∩ q) ↔ Want A dom p ∧ Want A dom q :=
  Set.subset_inter_iff

/-- Wanting `p` false is having no best world be a `p`-world. -/
theorem want_compl_iff : Want A dom pᶜ ↔ Disjoint (bestAmong dom A) p :=
  Set.subset_compl_iff_disjoint_right

/-- What is wanted is wanted under every consequence it has in the domain, the doxastic-closure
problem of [villalta-2008]. -/
theorem Want.mono_on (hpq : ∀ w ∈ dom, w ∈ p → w ∈ q) (h : Want A dom p) : Want A dom q :=
  fun w hw ↦ hpq w hw.1 (h hw)

theorem Want.mono (hpq : p ⊆ q) (h : Want A dom p) : Want A dom q := h.trans hpq

theorem Want.not_compl [Finite W] (h : dom.Nonempty) (hp : Want A dom p) : ¬ Want A dom pᶜ :=
  fun hnp ↦
    let ⟨_, hw⟩ := exists_mem_bestAmong (A := A) h
    hnp hw (hp hw)

end Want

/-! ### Desires as finite sets of worlds -/

section Source

variable (G : List (Finset W)) (dom p : Set W)

/-- The desires as an ordering source. -/
def source : List (W → Prop) := G.map fun s w ↦ w ∈ s

/-- `le G w z` holds when every desire in `G` satisfied at `z` is satisfied at `w`. -/
abbrev le (w z : W) : Prop := w ≤[source G] z

theorem le_iff (w z : W) : le G w z ↔ ∀ s ∈ G, z ∈ s → w ∈ s := by
  simp [source, atLeastAsGoodAs_iff]

theorem mem_bestAmong_source (w : W) :
    w ∈ bestAmong dom (source G) ↔ w ∈ dom ∧ ∀ z ∈ dom, le G z w → le G w z :=
  Iff.rfl

theorem want_source_iff :
    Want (source G) dom p ↔ ∀ w ∈ dom, (∀ z ∈ dom, le G z w → le G w z) → w ∈ p :=
  ⟨fun h _ hw hb ↦ h ⟨hw, hb⟩, fun h w hw ↦ h w hw.1 hw.2⟩

instance [DecidableEq W] (w z : W) : Decidable (le G w z) :=
  decidable_of_iff _ (le_iff G w z).symm

instance [Fintype W] [DecidableEq W] [DecidablePred (· ∈ dom)] [DecidablePred (· ∈ p)] :
    Decidable (Want (source G) dom p) :=
  decidable_of_iff _ (want_source_iff G dom p).symm

end Source

/-! ### *Want*, *glad* and *sorry* -/

section Entries

variable (dox base : W → Set W) (g : W → List (W → Prop)) (p : Set W)

/-- *a wants p* presupposes that the domain `base` contains both `p`-worlds and non-`p`-worlds
and asserts that its best worlds under the ordering source `g` are `p`-worlds
([von-fintel-1999]'s (45)). -/
def want : PartialProp W where
  presup w := (base w ∩ p).Nonempty ∧ (base w \ p).Nonempty
  assertion w := Want (g w) (base w) p

/-- *a is glad that p* presupposes, besides the presupposition of *want*, that `a` believes `p`
and that the domain contains her belief worlds, and asserts that `a` wants `p`
([von-fintel-1999]'s (50)). -/
def glad : PartialProp W where
  presup w := dox w ⊆ p ∧ dox w ⊆ base w ∧ (want base g p).presup w
  assertion := (want base g p).assertion

/-- *a regrets that p* has the presupposition of *glad* and asserts that `a` wants `p` false
([von-fintel-1999]'s (53)). -/
def regret : PartialProp W where
  presup := (glad dox base g p).presup
  assertion := (want base g pᶜ).assertion

end Entries

end Desire.BestWorlds
