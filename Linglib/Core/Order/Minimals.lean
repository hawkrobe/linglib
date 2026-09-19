import Linglib.Core.Order.OfCriteria
import Linglib.Core.Order.PreorderLattice
import Mathlib.Order.Minimal

/-!
# Minimal elements under a preorder given as a term

This file defines the set of minimal elements of a set under a preorder that is passed as a
term rather than found by instance resolution. Mathlib's `Minimal` reads the order from the
`LE` instance of the type, which does not fit a setting where many preorders on one type are
in play and the preorder is itself data, as with the lattice of preorders on a type. The
definition here unfolds to `Minimal` for the membership predicate, so the lemmas of
`Mathlib.Order.Minimal` apply after `letI := p`.

## Main declarations

* `Preorder.minimals`: the minimal elements of a set under a preorder.
* `Preorder.mem_minimals_of_subset`: an element minimal in a set is minimal in any subset that
  contains it.
* `Preorder.exists_le_mem_minimals`: under a well-founded strict order, every element of a set
  lies above a minimal element of the set.
* `Preorder.mem_minimals_iff_forall_le`: under a total preorder the minimal elements are the
  least elements.
* `Preorder.minimals_ofCriteria_eq`: under a criteria-derived preorder, when some element of
  the set satisfies every criterion, the minimal elements are exactly those that do.
-/

namespace Preorder

variable {α : Type*} {p : Preorder α} {s t : Set α} {a : α}

/-- The minimal elements of `s` under the preorder `p`. -/
def minimals (p : Preorder α) (s : Set α) : Set α := {a | @Minimal α p.toLE (· ∈ s) a}

theorem mem_minimals_iff : a ∈ p.minimals s ↔ a ∈ s ∧ ∀ ⦃b⦄, b ∈ s → p.le b a → p.le a b :=
  Iff.rfl

theorem minimals_subset (p : Preorder α) (s : Set α) : p.minimals s ⊆ s := fun _ h ↦ h.1

/-- An element minimal in a set is minimal in any subset that contains it. -/
theorem mem_minimals_of_subset (h : s ⊆ t) (ha : a ∈ p.minimals t) (has : a ∈ s) :
    a ∈ p.minimals s :=
  Minimal.mono ha (fun _ hb ↦ h hb) has

/-- Under the preorder that relates every two elements, every element of a set is minimal. -/
@[simp] theorem minimals_top (s : Set α) : (⊤ : Preorder α).minimals s = s :=
  Set.ext fun _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ _ _ ↦ trivial⟩⟩

/-- Under a well-founded strict order every element of a set lies above a minimal element of
the set. -/
theorem exists_le_mem_minimals (hp : WellFounded p.lt) (ha : a ∈ s) :
    ∃ b ∈ p.minimals s, p.le b a :=
  letI := p
  haveI : WellFoundedLT α := hp
  let ⟨b, hba, hb⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ s) a ha
  ⟨b, hb, hba⟩

/-- Under a total preorder the minimal elements of a set are its least elements. -/
theorem mem_minimals_iff_forall_le (hp : Std.Total p.le) :
    a ∈ p.minimals s ↔ a ∈ s ∧ ∀ b ∈ s, p.le a b :=
  ⟨fun h ↦ ⟨h.1, fun b hb ↦ (hp.total a b).elim id (h.2 hb)⟩,
    fun h ↦ ⟨h.1, fun b hb _ ↦ h.2 b hb⟩⟩

/-- Under a criteria-derived preorder, when some element of the set satisfies every criterion,
the minimal elements are exactly those that do. -/
theorem minimals_ofCriteria_eq {C : Type*} {sat : α → C → Prop} {criteria : Set C}
    (hex : ∃ a ∈ s, ∀ c ∈ criteria, sat a c) :
    (Preorder.ofCriteria sat criteria).minimals s = {a ∈ s | ∀ c ∈ criteria, sat a c} :=
  let ⟨_, hb, hsat⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, fun c hc ↦ hmin hb (fun c' hc' _ ↦ hsat c' hc') c hc (hsat c hc)⟩,
      fun ⟨ha, hall⟩ ↦ ⟨ha, fun _ _ _ c hc _ ↦ hall c hc⟩⟩

end Preorder
