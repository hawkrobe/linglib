import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# The complete lattice of preorders on a type

[UPSTREAM] candidate. This mirrors `CompleteLattice (Setoid α)`
(`Mathlib.Data.Setoid.Basic`) for preorders: the preorders on a fixed type
`α`, ordered by relation inclusion (`p ≤ q` iff every `p`-related pair is
`q`-related), form a complete lattice.

* `⊤` is the **total** preorder (everything related) — the coarsest order.
* `⊥` is equality `(· = ·)` — the finest preorder.
* `p ⊓ q` is the **intersection** of the two relations.
* `⨅ i, p i` (`sInf`) is the intersection of a family.

This is the order-theoretic substrate of *refinement* in default-reasoning
and conditional semantics: refining a normality/plausibility ordering by a
criterion is meet with that criterion's induced preorder, so the refinement
calculus (commutativity, idempotence, the total order as unit) is just the
meet-semilattice laws. `Preorder.lift` (mathlib) supplies the criterion
orders; this file supplies the algebra that combines them.

`Mathlib` has `CompleteLattice (Setoid α)` but no order structure on
`Preorder α`; this fills that gap.
-/

namespace Preorder

variable {α : Type*}

/-- Smart constructor: a `Preorder` from a reflexive-transitive relation,
    with the strict order taken canonically (`a < b ↔ a ≤ b ∧ ¬ b ≤ a`).
    Avoids the default-`lt` synthesis failing on relations built pointwise. -/
@[reducible] def ofLE (r : α → α → Prop) (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c) : Preorder α where
  le := r
  le_refl := hrefl
  le_trans := htrans
  lt a b := r a b ∧ ¬ r b a
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Preorders are ordered by relation inclusion: `p ≤ q` iff every pair
    related by `p` is related by `q` (i.e. `p` is finer). -/
instance : LE (Preorder α) where
  le p q := ∀ ⦃a b⦄, p.le a b → q.le a b

theorem le_def {p q : Preorder α} : p ≤ q ↔ ∀ ⦃a b⦄, p.le a b → q.le a b :=
  Iff.rfl

instance : PartialOrder (Preorder α) where
  le := (· ≤ ·)
  lt p q := p ≤ q ∧ ¬ q ≤ p
  le_refl _ _ _ h := h
  le_trans _ _ _ hpq hqr _ _ h := hqr (hpq h)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ hpq hqp :=
    Preorder.toLE_injective (LE.ext (funext fun _ => funext fun _ =>
      propext ⟨fun h => hpq h, fun h => hqp h⟩))

instance : InfSet (Preorder α) where
  sInf S := ofLE (fun a b => ∀ p ∈ S, p.le a b)
    (fun a p _ => p.le_refl a)
    (fun a b c hab hbc p hp => p.le_trans a b c (hab p hp) (hbc p hp))

instance : CompleteLattice (Preorder α) :=
  { (completeLatticeOfInf (Preorder α) fun _ =>
      ⟨fun _ hp _ _ h => h _ hp, fun _ hr _ _ h _ hr' => hr hr' h⟩) with
    inf p q := ofLE (fun a b => p.le a b ∧ q.le a b)
      (fun a => ⟨p.le_refl a, q.le_refl a⟩)
      (fun a b c hab hbc =>
        ⟨p.le_trans a b c hab.1 hbc.1, q.le_trans a b c hab.2 hbc.2⟩)
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ofLE (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial)
    le_top := fun _ _ _ _ => trivial
    bot := ofLE (· = ·) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    bot_le := fun p _ _ h => h ▸ p.le_refl _ }

@[simp] theorem top_le (a b : α) : (⊤ : Preorder α).le a b := trivial

@[simp] theorem bot_le_iff {a b : α} : (⊥ : Preorder α).le a b ↔ a = b := Iff.rfl

theorem inf_le_iff {p q : Preorder α} {a b : α} :
    (p ⊓ q).le a b ↔ p.le a b ∧ q.le a b := Iff.rfl

theorem sInf_le_iff {S : Set (Preorder α)} {a b : α} :
    (sInf S).le a b ↔ ∀ p ∈ S, p.le a b := Iff.rfl

end Preorder
