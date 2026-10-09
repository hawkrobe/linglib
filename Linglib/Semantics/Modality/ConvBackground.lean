module

public import Linglib.Core.Order.Minimals
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# Conversational backgrounds

A premise set is a set of propositions `A : Set (W → Prop)`. In the complete Boolean algebra
`W → Prop` its infimum `sInf A` holds at the worlds verifying every premise, so `p` follows from
`A` when `sInf A ≤ p`, and `A` is consistent when `sInf A ≠ ⊥`. A premise set also ranks worlds:
`w` is at least as good as `z` when `w` verifies every premise `z` does, a preorder that is in
general not total, whose minimal elements in a domain are its best worlds.

A conversational background assigns each world a premise set. Kratzer's modal base and ordering
source are both conversational backgrounds, told apart only by their role: the premises of a
modal base at `w` fix the worlds accessible from `w`, and those of an ordering source rank them.

## Main definitions

* `ConvBackground W`: the backgrounds over `W`, a complete lattice pointwise, with `⊥` the empty
  background.
* `ConvBackground.accessibleWorlds f w`: the worlds verifying every premise of `f w`.
* `ConvBackground.IsRealistic`, `ConvBackground.IsTotallyRealistic`.
* `ConvBackground.restrict f α`: `f` with the premise `α` added at every world.
* `premisePreorder A`, `w ≤[A] z`, `w <[A] z`: the ordering a premise set induces.
* `bestAmong worlds A`, `bestWorlds f g w`: the minimal worlds of a domain, and of the worlds
  accessible under `f` ranked by `g`.

## References

* [kratzer-1977]
* [kratzer-1981]
* [kratzer-2012]
-/

@[expose] public section

namespace Modality

variable {W : Type*}

/-- A conversational background assigns each world a premise set. -/
abbrev ConvBackground (W : Type*) := W → Set (W → Prop)

namespace ConvBackground

variable {f f' : ConvBackground W} {w v : W}

/-- The worlds accessible from `w` under `f` are those verifying every premise of `f w`,
Kratzer's `⋂f(w)`. -/
def accessibleWorlds (f : ConvBackground W) (w : W) : Set W := {v | sInf (f w) v}

@[simp] theorem mem_accessibleWorlds : v ∈ f.accessibleWorlds w ↔ ∀ p ∈ f w, p v := by
  simp [accessibleWorlds]

/-- More premises leave fewer accessible worlds. -/
theorem accessibleWorlds_anti (h : f w ⊆ f' w) : f'.accessibleWorlds w ⊆ f.accessibleWorlds w :=
  fun v hv ↦ sInf_le_sInf h v hv

@[simp] theorem accessibleWorlds_bot (w : W) : (⊥ : ConvBackground W).accessibleWorlds w = .univ :=
  Set.eq_univ_of_forall fun _ ↦ by simp [accessibleWorlds]

/-- A background is realistic when every world is accessible from itself, verifying its own
premises. -/
def IsRealistic (f : ConvBackground W) : Prop := ∀ w, w ∈ f.accessibleWorlds w

/-- A background is totally realistic when its premises at a world single out that world. -/
def IsTotallyRealistic (f : ConvBackground W) : Prop := ∀ w, f.accessibleWorlds w = {w}

/-- The background `f` restricted by `α`, the premise a conditional antecedent adds, so that
*if α, must β* is `must_{f + α} β`. -/
def restrict (f : ConvBackground W) (α : W → Prop) : ConvBackground W := fun w ↦ insert α (f w)

@[simp] theorem mem_accessibleWorlds_restrict {α : W → Prop} :
    v ∈ (f.restrict α).accessibleWorlds w ↔ v ∈ f.accessibleWorlds w ∧ α v := by
  simp [restrict, and_comm]

theorem accessibleWorlds_restrict (f : ConvBackground W) (α : W → Prop) (w : W) :
    (f.restrict α).accessibleWorlds w = {v ∈ f.accessibleWorlds w | α v} :=
  Set.ext fun _ ↦ mem_accessibleWorlds_restrict

/-- A stronger antecedent leaves fewer accessible worlds. -/
theorem accessibleWorlds_restrict_mono {α₁ α₂ : W → Prop} (h : α₂ ≤ α₁) :
    (f.restrict α₂).accessibleWorlds w ⊆ (f.restrict α₁).accessibleWorlds w := fun v hv ↦
  mem_accessibleWorlds_restrict.2 ⟨(mem_accessibleWorlds_restrict.1 hv).1,
    h v (mem_accessibleWorlds_restrict.1 hv).2⟩

end ConvBackground

/-! ### The ordering -/

/-- The preorder that an ordering source induces ranks `w` below `z` when every proposition of `A`
true at `z` is true at `w`. It is the criteria-derived preorder with truth as satisfaction. -/
abbrev premisePreorder (A : Set (W → Prop)) : Preorder W :=
  Preorder.ofCriteria (fun w p ↦ p w) A

/-- `w` is at least as good as `z` with respect to the ordering source `A`. -/
def atLeastAsGoodAs (A : Set (W → Prop)) (w z : W) : Prop := (premisePreorder A).le w z

@[inherit_doc]
notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

theorem atLeastAsGoodAs_iff (A : Set (W → Prop)) (w z : W) :
    (w ≤[A] z) ↔ ∀ p ∈ A, p z → p w :=
  Iff.rfl

theorem atLeastAsGoodAs_refl (A : Set (W → Prop)) (w : W) : w ≤[A] w :=
  (premisePreorder A).le_refl w

theorem atLeastAsGoodAs_trans {A : Set (W → Prop)} {u v w : W} (huv : u ≤[A] v)
    (hvw : v ≤[A] w) : u ≤[A] w :=
  (premisePreorder A).le_trans u v w huv hvw

/-- With an empty ordering source every world is at least as good as every other. -/
theorem atLeastAsGoodAs_empty (w z : W) : w ≤[(∅ : Set (W → Prop))] z := fun _ h ↦ h.elim

instance decidableRel_atLeastAsGoodAs_empty :
    DecidableRel (atLeastAsGoodAs (∅ : Set (W → Prop))) :=
  fun w z ↦ isTrue (atLeastAsGoodAs_empty w z)

instance decidableRel_atLeastAsGoodAs_singleton (p : W → Prop) [DecidablePred p] :
    DecidableRel (atLeastAsGoodAs ({p} : Set (W → Prop))) :=
  fun w z ↦ decidable_of_iff (p z → p w) <| by simp [atLeastAsGoodAs_iff]

instance decidableRel_atLeastAsGoodAs_insert (p : W → Prop) [DecidablePred p]
    (A : Set (W → Prop)) [DecidableRel (atLeastAsGoodAs A)] :
    DecidableRel (atLeastAsGoodAs (insert p A)) :=
  fun w z ↦ decidable_of_iff ((p z → p w) ∧ w ≤[A] z) <| by
    simp only [atLeastAsGoodAs_iff, Set.forall_mem_insert]

/-- An empty ordering source induces the preorder relating every two worlds. -/
@[simp] theorem premisePreorder_empty : premisePreorder (∅ : Set (W → Prop)) = ⊤ :=
  top_unique fun _ _ _ ↦ atLeastAsGoodAs_empty _ _

/-- `w` is strictly better than `z` when it is at least as good and not conversely. -/
def strictlyBetter (A : Set (W → Prop)) (w z : W) : Prop := (premisePreorder A).lt w z

@[inherit_doc]
notation:50 w " <[" A "] " z => strictlyBetter A w z

theorem strictlyBetter_iff (A : Set (W → Prop)) (w z : W) :
    (w <[A] z) ↔ (w ≤[A] z) ∧ ¬ (z ≤[A] w) :=
  Iff.rfl

/-! ### Best worlds -/

/-- The best worlds among a domain are the members that no other member strictly betters, the
minimal elements of the domain under the ordering. The dominance form, at least as good as every
member, is empty on an ordering that is not total, such as Kratzer's practical-inference example, so
minimality is the faithful reading. -/
def bestAmong (worlds : Set W) (A : Set (W → Prop)) : Set W :=
  (premisePreorder A).minimals worlds

variable {worlds : Set W} {A : Set (W → Prop)} {w : W}

theorem mem_bestAmong :
    w ∈ bestAmong worlds A ↔ w ∈ worlds ∧ ∀ v ∈ worlds, (v ≤[A] w) → (w ≤[A] v) :=
  Iff.rfl

theorem bestAmong_subset (worlds : Set W) (A : Set (W → Prop)) : bestAmong worlds A ⊆ worlds :=
  fun _ h ↦ h.1

/-- With an empty ordering source every world of the domain is best. -/
theorem bestAmong_empty (worlds : Set W) : bestAmong worlds ∅ = worlds := by
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
  let _ := premisePreorder A
  Set.Finite.exists_minimal (Set.toFinite worlds) h

/-- The best accessible worlds from `w` are the best among the accessible worlds under the ordering
source at `w`. Kratzer's official necessity is the limit-free `humanNecessity`, which quantifies
over exactly this set under the Limit Assumption (`humanNecessity_iff_necessity`). -/
def bestWorlds (f g : ConvBackground W) (w : W) : Set W :=
  bestAmong (f.accessibleWorlds w) (g w)

theorem mem_bestWorlds {f g : ConvBackground W} {w u : W} :
    u ∈ bestWorlds f g w ↔
      u ∈ f.accessibleWorlds w ∧ ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → (u ≤[g w] v) :=
  Iff.rfl

/-- With the empty ordering source the best worlds are the accessible ones. -/
@[simp] theorem bestWorlds_bot (f : ConvBackground W) (w : W) :
    bestWorlds f ⊥ w = f.accessibleWorlds w :=
  bestAmong_empty _

/-- A best world verifying a member of the ordering source that excludes `p` stays best when `p` is
added, because no `p`-world is at least as good, since it fails the member, and the other worlds are
ordered as before. -/
theorem mem_bestWorlds_insert {f g : ConvBackground W} {p q : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u) :
    u ∈ bestWorlds f (fun v ↦ insert p (g v)) w := by
  refine ⟨hu.1, fun v hv hvu ↦ ?_⟩
  have hvq : q v := hvu q (Set.mem_insert_of_mem p hq) huq
  intro r hr
  rcases hr with rfl | hr
  · exact fun hrv ↦ absurd hrv (hpq v hvq)
  · exact hu.2 hv (fun r' hr' ↦ hvu r' (Set.mem_insert_of_mem p hr')) r hr

/-- A best world of a modal base is a best world of any narrower modal base it is accessible
under. -/
theorem mem_bestWorlds_of_subset {f f' g : ConvBackground W} {w u : W}
    (h : f'.accessibleWorlds w ⊆ f.accessibleWorlds w) (hu : u ∈ bestWorlds f g w)
    (hu' : u ∈ f'.accessibleWorlds w) : u ∈ bestWorlds f' g w :=
  bestAmong_superset h hu hu'

end Modality
