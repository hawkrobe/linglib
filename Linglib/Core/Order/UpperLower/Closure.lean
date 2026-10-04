module

public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.Closure
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# The order-convex hull

`[UPSTREAM]` candidate for `Mathlib/Order/UpperLower/Closure.lean`: the
order-convex hull of a set — the smallest `OrdConnected` superset — as a bundled
`ClosureOperator (Set α)`. It is the order-theoretic twin of `convexHull`
(segment-convexity), built the same way, via `ClosureOperator.ofCompletePred`
over the intersection-closed predicate `OrdConnected` (`Set.ordConnected_sInter`).
In a partial order, the minimal elements of an upper closure are those of the generating set.

mathlib already has the characterization
`ordConnected_iff_upperClosure_inter_lowerClosure` and `Set.OrdConnected`, but not
this bundled closure operator, and it has the minimal-element lemma only for antichains,
`IsAntichain.minimal_mem_upperClosure_iff_mem`, which follows from the general one with
`IsAntichain.minimal_mem_iff`. On upstreaming, these declarations move into
`Mathlib/Order/UpperLower/Closure.lean` (next to that characterization) and this
file is deleted.

## Main declarations

* `ordConnectedHull` — the order-convex hull as a `ClosureOperator (Set α)`.
* `mem_ordConnectedHull` — `c ∈ ordConnectedHull s ↔ ∃ a b ∈ s, a ≤ c ≤ b`.
* `ordConnectedHull_eq_upperClosure_inter_lowerClosure` — the bridge to
  `upperClosure`/`lowerClosure`.
* `minimal_mem_upperClosure_iff`, `maximal_mem_lowerClosure_iff` — the minimal (maximal)
  elements of an upper (lower) closure.
-/

@[expose] public section

open Set

variable {α : Type*}

section Preorder
variable [Preorder α]

/-- The order-convex hull of `s` is the smallest `OrdConnected` set containing `s`, as a
`ClosureOperator`. It is the order-theoretic twin of `convexHull`. -/
@[simps! isClosed]
def ordConnectedHull : ClosureOperator (Set α) :=
  .ofCompletePred OrdConnected fun _ ↦ ordConnected_sInter

/-- A set is contained in its order-convex hull. -/
theorem subset_ordConnectedHull (s : Set α) : s ⊆ ordConnectedHull s :=
  ordConnectedHull.le_closure s

/-- The order-convex hull is the smallest `OrdConnected` superset. -/
theorem ordConnectedHull_min {s t : Set α} (h : s ⊆ t) (ht : t.OrdConnected) :
    ordConnectedHull s ⊆ t :=
  ordConnectedHull.closure_min h ht

@[mono, gcongr]
theorem ordConnectedHull_mono : Monotone (ordConnectedHull : Set α → Set α) :=
  ordConnectedHull.monotone

/-- The order-convex hull is `OrdConnected`. -/
theorem ordConnected_ordConnectedHull (s : Set α) : (ordConnectedHull s).OrdConnected :=
  ordConnectedHull.isClosed_closure s

/-- A set equals its order-convex hull iff it is `OrdConnected`. -/
theorem ordConnectedHull_eq_self {s : Set α} : ordConnectedHull s = s ↔ s.OrdConnected :=
  ordConnectedHull.isClosed_iff.symm

alias ⟨_, _root_.Set.OrdConnected.ordConnectedHull_eq⟩ := ordConnectedHull_eq_self

/-- The order-convex hull is the intersection of the upper and lower closures. -/
theorem ordConnectedHull_eq_upperClosure_inter_lowerClosure (s : Set α) :
    (ordConnectedHull s : Set α) = ↑(upperClosure s) ∩ ↑(lowerClosure s) := by
  apply subset_antisymm
  · refine ordConnectedHull_min (fun x hx => ⟨subset_upperClosure hx, subset_lowerClosure hx⟩) ?_
    exact ((upperClosure s).upper.ordConnected).inter ((lowerClosure s).lower.ordConnected)
  · rintro c ⟨hcu, hcl⟩
    simp only [SetLike.mem_coe, mem_upperClosure] at hcu
    simp only [SetLike.mem_coe, mem_lowerClosure] at hcl
    obtain ⟨a, ha, hac⟩ := hcu
    obtain ⟨b, hb, hcb⟩ := hcl
    exact (ordConnected_ordConnectedHull s).out
      (subset_ordConnectedHull s ha) (subset_ordConnectedHull s hb) ⟨hac, hcb⟩

/-- An element is in the order-convex hull of `s` iff it lies between two members of `s`. -/
theorem mem_ordConnectedHull {s : Set α} {c : α} :
    c ∈ ordConnectedHull s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≤ c ∧ c ≤ b := by
  rw [ordConnectedHull_eq_upperClosure_inter_lowerClosure]
  simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_upperClosure, mem_lowerClosure]
  tauto

@[simp] theorem ordConnectedHull_empty : ordConnectedHull (∅ : Set α) = ∅ :=
  ordConnectedHull_eq_self.2 ordConnected_empty

@[simp] theorem ordConnectedHull_univ : ordConnectedHull (univ : Set α) = univ :=
  ordConnectedHull_eq_self.2 ordConnected_univ

end Preorder

section PartialOrder
variable [PartialOrder α] {s : Set α} {x : α}

/-- The minimal elements of the upper closure of `s` are those of `s`. -/
@[to_dual /-- The maximal elements of the lower closure of `s` are those of `s`. -/]
theorem minimal_mem_upperClosure_iff : Minimal (· ∈ upperClosure s) x ↔ Minimal (· ∈ s) x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨subset_upperClosure h.prop, fun y ⟨a, has, hay⟩ hyx ↦
    (h.eq_of_ge has (hay.trans hyx)).symm ▸ hay⟩⟩
  obtain ⟨a, has, hax⟩ := h.prop
  obtain rfl := h.eq_of_ge (subset_upperClosure has) hax
  exact h.mono (fun _ ↦ (subset_upperClosure ·)) has

end PartialOrder
