import Linglib.Semantics.Modality.Kratzer.ConversationalBackground
import Linglib.Core.Order.Normality
import Mathlib.Order.Preorder.Finite

/-!
# Kratzer's ordering of worlds

This file defines the ordering that an ordering source induces on worlds and the best worlds
of a modal base under it, [kratzer-1981]'s two conversational backgrounds at work. A world is
at least as good as another when it verifies every proposition of the ordering source the
other verifies, the criteria-derived preorder with truth at a world as satisfaction
(`kratzerPreorder`, `atLeastAsGoodAs`, written `w ≤[A] z`). The ordering is a preorder and in
general not connected, so the best worlds of a domain are its minimal elements, the worlds no
member strictly betters (`bestAmong`, mathlib's `Minimal` through
`Core.Order.Normality.optimal`), and the best worlds of a modal base at a world are the best
among its accessible worlds (`bestWorlds`). On a finite frame every nonempty domain has a best
world (`exists_mem_bestAmong`); with an empty ordering source every accessible world is best
(`bestWorlds_emptyBackground`); when some member verifies the whole ordering source, the best
worlds are exactly those that do (`bestAmong_eq_of_exists`).

## Main definitions

* `kratzerPreorder A`, `atLeastAsGoodAs A w z`, `strictlyBetter A w z` — the ordering induced
  by `A`, its non-strict and strict forms.
* `accessibleWorlds f w` — the worlds compatible with the modal base at `w`.
* `bestAmong worlds A`, `bestWorlds f g w` — the minimal worlds of a domain, and of the
  accessible worlds.

## References

* [kratzer-1981]
* [kratzer-2012]
-/

namespace Modality.Kratzer

variable {W : Type*}

/-! ### The ordering -/

/-- The preorder an ordering source induces: `w ≤ z` iff every proposition of `A` true at `z`
is true at `w`, the criteria-derived preorder with truth as satisfaction. -/
abbrev kratzerPreorder (A : List (W → Prop)) : Preorder W := Core.Order.Normality.fromProps A

/-- `w` is at least as good as `z` with respect to the ordering source `A`. -/
def atLeastAsGoodAs (A : List (W → Prop)) (w z : W) : Prop := (kratzerPreorder A).le w z

@[inherit_doc]
notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

theorem atLeastAsGoodAs_iff (A : List (W → Prop)) (w z : W) :
    (w ≤[A] z) ↔ ∀ p ∈ A, p z → p w :=
  Iff.rfl

theorem atLeastAsGoodAs_refl (A : List (W → Prop)) (w : W) : w ≤[A] w := λ _ _ h => h

theorem atLeastAsGoodAs_trans {A : List (W → Prop)} {u v w : W} (huv : u ≤[A] v)
    (hvw : v ≤[A] w) : u ≤[A] w :=
  λ p hp h => huv p hp (hvw p hp h)

/-- With an empty ordering source every world is at least as good as every other. -/
theorem atLeastAsGoodAs_nil (w z : W) : w ≤[([] : List (W → Prop))] z := λ _ h => nomatch h

/-- `w` is strictly better than `z`: at least as good, and not conversely. -/
def strictlyBetter (A : List (W → Prop)) (w z : W) : Prop := (kratzerPreorder A).lt w z

@[inherit_doc]
notation:50 w " <[" A "] " z => strictlyBetter A w z

theorem strictlyBetter_iff (A : List (W → Prop)) (w z : W) :
    (w <[A] z) ↔ (w ≤[A] z) ∧ ¬ (z ≤[A] w) :=
  Iff.rfl

/-! ### Accessible worlds -/

/-- The worlds accessible from `w` given the modal base `f`: those compatible with every
proposition of `f w`, Kratzer's `⋂f(w)`. -/
def accessibleWorlds (f : ModalBase W) (w : W) : Set W :=
  propIntersection (f w)

/-- Growing the modal base can only shrink the accessible worlds. -/
theorem accessibleWorlds_anti {f f' : ModalBase W} {w : W} (h : f w ⊆ f' w) :
    accessibleWorlds f' w ⊆ accessibleWorlds f w :=
  propIntersection_anti_of_subset h

/-- A modal base is realistic iff every world is accessible from itself. -/
theorem isRealistic_iff_mem_accessible (f : ModalBase W) :
    isRealistic f ↔ ∀ w, w ∈ accessibleWorlds f w :=
  ⟨λ h w p hp => h w p hp, λ h w p hp => h w p hp⟩

/-! ### Best worlds -/

/-- The best worlds among a domain: the members no other member strictly betters, the minimal
elements of the domain under the ordering. The dominance form, at least as good as every
member, is empty on a non-connected ordering such as [kratzer-1981]'s practical-inference
example, so minimality is the faithful reading. -/
def bestAmong (worlds : Set W) (A : List (W → Prop)) : Set W :=
  Core.Order.Normality.optimal (kratzerPreorder A) worlds

variable {worlds : Set W} {A : List (W → Prop)} {w : W}

theorem mem_bestAmong :
    w ∈ bestAmong worlds A ↔ w ∈ worlds ∧ ∀ v ∈ worlds, (v ≤[A] w) → (w ≤[A] v) :=
  Iff.rfl

theorem bestAmong_subset (worlds : Set W) (A : List (W → Prop)) : bestAmong worlds A ⊆ worlds :=
  λ _ h => h.1

/-- With an empty ordering source every world of the domain is best. -/
theorem bestAmong_nil (worlds : Set W) : bestAmong worlds [] = worlds :=
  Set.ext λ _ => ⟨λ h => h.1, λ h => ⟨h, λ _ _ _ => atLeastAsGoodAs_nil _ _⟩⟩

/-- A best world of a domain is best in any subdomain it belongs to: unbettered among more
competitors, unbettered among fewer. -/
theorem bestAmong_superset {sub sup : Set W} (hSub : sub ⊆ sup) (hBest : w ∈ bestAmong sup A)
    (hMem : w ∈ sub) : w ∈ bestAmong sub A :=
  Core.Order.Normality.mem_optimal_of_subset hSub hBest hMem

/-- When some member of the domain verifies every proposition of the ordering source, the best
worlds are exactly the members that do. -/
theorem bestAmong_eq_of_exists (hex : ∃ w ∈ worlds, ∀ p ∈ A, p w) :
    bestAmong worlds A = {w ∈ worlds | ∀ p ∈ A, p w} :=
  Core.Order.Normality.optimal_ofCriteria_eq hex

/-- On a finite frame every nonempty domain has a best world. -/
theorem exists_mem_bestAmong [Finite W] (h : worlds.Nonempty) : (bestAmong worlds A).Nonempty :=
  let _ := kratzerPreorder A
  Set.Finite.exists_minimal (Set.toFinite worlds) h

/-- The best accessible worlds from `w`: the best among the accessible worlds under the
ordering source at `w`. [kratzer-1981]'s official necessity is the limit-free
`humanNecessity`; it quantifies over exactly this set under the Limit Assumption
(`humanNecessity_iff_necessity`). -/
def bestWorlds (f : ModalBase W) (g : OrderingSource W) (w : W) : Set W :=
  bestAmong (accessibleWorlds f w) (g w)

theorem mem_bestWorlds {f : ModalBase W} {g : OrderingSource W} {w u : W} :
    u ∈ bestWorlds f g w ↔
      u ∈ accessibleWorlds f w ∧ ∀ v ∈ accessibleWorlds f w, (v ≤[g w] u) → (u ≤[g w] v) :=
  Iff.rfl

/-- With an empty ordering source the best worlds are the accessible ones. -/
theorem bestWorlds_emptyBackground (f : ModalBase W) (w : W) :
    bestWorlds f emptyBackground w = accessibleWorlds f w :=
  bestAmong_nil _

/-- A best world verifying a member of the ordering source that excludes `p` stays best when
`p` is added: no `p`-world is at least as good, since it fails the member, and the other worlds
are ordered as before. -/
theorem mem_bestWorlds_cons {f : ModalBase W} {g : OrderingSource W} {p q : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u) :
    u ∈ bestWorlds f (λ v => p :: g v) w := by
  refine ⟨hu.1, λ v hv hvu => ?_⟩
  have hvq : q v := hvu q (List.mem_cons_of_mem p hq) huq
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · exact λ hrv => absurd hrv (hpq v hvq)
  · exact hu.2 hv (λ r' hr' => hvu r' (List.mem_cons_of_mem p hr')) r hr

/-- A best world of a modal base is a best world of any narrower modal base it is accessible
under. -/
theorem mem_bestWorlds_of_subset {f f' : ModalBase W} {g : OrderingSource W} {w u : W}
    (h : accessibleWorlds f' w ⊆ accessibleWorlds f w) (hu : u ∈ bestWorlds f g w)
    (hu' : u ∈ accessibleWorlds f' w) : u ∈ bestWorlds f' g w :=
  bestAmong_superset h hu hu'

end Modality.Kratzer
