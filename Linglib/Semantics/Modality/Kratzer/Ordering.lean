module

public import Linglib.Semantics.Modality.Kratzer.ConversationalBackground
public import Linglib.Core.Order.Minimals
public import Mathlib.Order.Preorder.Finite

/-!
# Kratzer's ordering of worlds

This file defines the ordering that an ordering source induces on worlds and the best worlds
of a modal base under it, the two conversational backgrounds of Kratzer's semantics at work.

A world is at least as good as another when it verifies every proposition of the ordering
source that the other verifies. This is the criteria-derived preorder with truth at a world as
satisfaction (`kratzerPreorder`, `atLeastAsGoodAs`, written `w ≤[A] z`). The ordering is a
preorder and in general not total, so the best worlds of a domain are its minimal elements, the
worlds that no member strictly betters (`bestAmong`, through `Preorder.minimals`), and the best
worlds of a modal base at a world are the best among its accessible worlds (`bestWorlds`). On a
finite frame every nonempty domain has a best world (`exists_mem_bestAmong`). With an empty
ordering source every accessible world is best (`bestWorlds_emptyBackground`). When some member
verifies the whole ordering source, the best worlds are exactly those that do
(`bestAmong_eq_of_exists`).

## Main definitions

* `kratzerPreorder A`, `atLeastAsGoodAs A w z`, `strictlyBetter A w z`: the ordering induced
  by `A`, in its non-strict and strict forms.
* `f.accessibleWorlds w`: the worlds compatible with the modal base at `w`.
* `bestAmong worlds A`, `bestWorlds f g w`: the minimal worlds of a domain, and of the
  accessible worlds.

## References

* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

@[expose] public section


namespace Modality

variable {W : Type*}

/-! ### The ordering -/

/-- The preorder that an ordering source induces ranks `w` below `z` when every proposition of `A`
true at `z` is true at `w`. It is the criteria-derived preorder with truth as satisfaction. -/
abbrev kratzerPreorder (A : List (W → Prop)) : Preorder W :=
  Preorder.ofCriteria (fun w p ↦ p w) {p | p ∈ A}

/-- `w` is at least as good as `z` with respect to the ordering source `A`. -/
def atLeastAsGoodAs (A : List (W → Prop)) (w z : W) : Prop := (kratzerPreorder A).le w z

@[inherit_doc]
notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

theorem atLeastAsGoodAs_iff (A : List (W → Prop)) (w z : W) :
    (w ≤[A] z) ↔ ∀ p ∈ A, p z → p w :=
  Iff.rfl

theorem atLeastAsGoodAs_refl (A : List (W → Prop)) (w : W) : w ≤[A] w := fun _ _ h ↦ h

theorem atLeastAsGoodAs_trans {A : List (W → Prop)} {u v w : W} (huv : u ≤[A] v)
    (hvw : v ≤[A] w) : u ≤[A] w :=
  fun p hp h ↦ huv p hp (hvw p hp h)

/-- With an empty ordering source every world is at least as good as every other. -/
theorem atLeastAsGoodAs_nil (w z : W) : w ≤[([] : List (W → Prop))] z := fun _ h ↦ nomatch h

/-- An empty ordering source induces the preorder relating every two worlds. -/
@[simp] theorem kratzerPreorder_nil : kratzerPreorder ([] : List (W → Prop)) = ⊤ :=
  top_unique fun _ _ _ ↦ atLeastAsGoodAs_nil _ _

/-- `w` is strictly better than `z` when it is at least as good and not conversely. -/
def strictlyBetter (A : List (W → Prop)) (w z : W) : Prop := (kratzerPreorder A).lt w z

@[inherit_doc]
notation:50 w " <[" A "] " z => strictlyBetter A w z

theorem strictlyBetter_iff (A : List (W → Prop)) (w z : W) :
    (w <[A] z) ↔ (w ≤[A] z) ∧ ¬ (z ≤[A] w) :=
  Iff.rfl

/-! ### Accessible worlds -/

/-- The worlds accessible from `w` given the modal base `f` are those compatible with every
proposition of `f w`, Kratzer's `⋂f(w)`. -/
def ModalBase.accessibleWorlds (f : ModalBase W) (w : W) : Set W :=
  propIntersection (f w)

/-- Growing the modal base can only shrink the accessible worlds. -/
theorem accessibleWorlds_anti {f f' : ModalBase W} {w : W} (h : f w ⊆ f' w) :
    f'.accessibleWorlds w ⊆ f.accessibleWorlds w :=
  propIntersection_anti_of_subset h

/-- A modal base is realistic iff every world is accessible from itself. -/
theorem isRealistic_iff_mem_accessible (f : ModalBase W) :
    f.IsRealistic ↔ ∀ w, w ∈ f.accessibleWorlds w :=
  ⟨fun h w p hp ↦ h w p hp, fun h w p hp ↦ h w p hp⟩

/-! ### Best worlds -/

/-- The best worlds among a domain are the members that no other member strictly betters, the
minimal elements of the domain under the ordering. The dominance form, at least as good as every
member, is empty on an ordering that is not total, such as Kratzer's practical-inference example, so
minimality is the faithful reading. -/
def bestAmong (worlds : Set W) (A : List (W → Prop)) : Set W :=
  (kratzerPreorder A).minimals worlds

variable {worlds : Set W} {A : List (W → Prop)} {w : W}

theorem mem_bestAmong :
    w ∈ bestAmong worlds A ↔ w ∈ worlds ∧ ∀ v ∈ worlds, (v ≤[A] w) → (w ≤[A] v) :=
  Iff.rfl

theorem bestAmong_subset (worlds : Set W) (A : List (W → Prop)) : bestAmong worlds A ⊆ worlds :=
  fun _ h ↦ h.1

/-- With an empty ordering source every world of the domain is best. -/
theorem bestAmong_nil (worlds : Set W) : bestAmong worlds [] = worlds := by
  simp [bestAmong]

/-- A best world of a domain is best in any subdomain it belongs to, since a world unbettered among
more competitors is unbettered among fewer. -/
theorem bestAmong_superset {sub sup : Set W} (hSub : sub ⊆ sup) (hBest : w ∈ bestAmong sup A)
    (hMem : w ∈ sub) : w ∈ bestAmong sub A :=
  Preorder.mem_minimals_of_subset hSub hBest hMem

/-- When some member of the domain verifies every proposition of the ordering source, the best
worlds are exactly the members that do. -/
theorem bestAmong_eq_of_exists (hex : ∃ w ∈ worlds, ∀ p ∈ A, p w) :
    bestAmong worlds A = {w ∈ worlds | ∀ p ∈ A, p w} :=
  Preorder.minimals_ofCriteria_eq hex

/-- On a finite frame every nonempty domain has a best world. -/
theorem exists_mem_bestAmong [Finite W] (h : worlds.Nonempty) : (bestAmong worlds A).Nonempty :=
  let _ := kratzerPreorder A
  Set.Finite.exists_minimal (Set.toFinite worlds) h

/-- The best accessible worlds from `w` are the best among the accessible worlds under the ordering
source at `w`. Kratzer's official necessity is the limit-free `humanNecessity`, which quantifies
over exactly this set under the Limit Assumption (`humanNecessity_iff_necessity`). -/
def bestWorlds (f : ModalBase W) (g : OrderingSource W) (w : W) : Set W :=
  bestAmong (f.accessibleWorlds w) (g w)

theorem mem_bestWorlds {f : ModalBase W} {g : OrderingSource W} {w u : W} :
    u ∈ bestWorlds f g w ↔
      u ∈ f.accessibleWorlds w ∧ ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → (u ≤[g w] v) :=
  Iff.rfl

/-- With an empty ordering source the best worlds are the accessible ones. -/
theorem bestWorlds_emptyBackground (f : ModalBase W) (w : W) :
    bestWorlds f emptyBackground w = f.accessibleWorlds w :=
  bestAmong_nil _

/-- A best world verifying a member of the ordering source that excludes `p` stays best when `p` is
added, because no `p`-world is at least as good, since it fails the member, and the other worlds are
ordered as before. -/
theorem mem_bestWorlds_cons {f : ModalBase W} {g : OrderingSource W} {p q : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u) :
    u ∈ bestWorlds f (fun v ↦ p :: g v) w := by
  refine ⟨hu.1, fun v hv hvu ↦ ?_⟩
  have hvq : q v := hvu q (List.mem_cons_of_mem p hq) huq
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · exact fun hrv ↦ absurd hrv (hpq v hvq)
  · exact hu.2 hv (fun r' hr' ↦ hvu r' (List.mem_cons_of_mem p hr')) r hr

/-- A best world of a modal base is a best world of any narrower modal base it is accessible
under. -/
theorem mem_bestWorlds_of_subset {f f' : ModalBase W} {g : OrderingSource W} {w u : W}
    (h : f'.accessibleWorlds w ⊆ f.accessibleWorlds w) (hu : u ∈ bestWorlds f g w)
    (hu' : u ∈ f'.accessibleWorlds w) : u ∈ bestWorlds f' g w :=
  bestAmong_superset h hu hu'

end Modality
