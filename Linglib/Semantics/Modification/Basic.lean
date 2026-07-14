import Mathlib.Order.PropInstances

/-!
# Modifiers
[parsons-1970] [kamp-1975]

A **modifier** of `τ` is a function on the modificand's denotation
([parsons-1970]: "modifiers as functions on predicates"). Adjectives,
adverbs, and relative clauses are all modifiers — of *different* `τ` (nominal
`e ⇒ t`, event `Event → Prop`, …) — unified by *being* this type, not by
implementing an interface.

The [kamp-1975] meaning-postulate classification is order-theoretic and is
stated here at that generality: over an ordered carrier, **subsective**
modifiers are deflationary (`m x ≤ x`), **privative** modifiers have output
disjoint from the modificand, and **intersective** modifiers are
meet-translations (`m x = q ⊓ x`; at `α → Prop`, pointwise conjunction).
The intensional hierarchy (`Modification/Classification.lean`) and its
single-world specializations (`Studies/Kamp1975.lean` § 1) are these
classes at the carriers `W → E → Prop` and `E → Prop`.

## Main declarations

* `Modifier` — a modifier of `τ` is an endofunction `τ → τ`.
* `Modifier.intersective` — the intersective modifier built from `q`: meet
  the modificand with `q`.
* `Modifier.isIntersective` / `.isSubsective` / `.isPrivative` — the
  [kamp-1975] classification over an ordered carrier.
-/

/-- A modifier of `τ` is a function on the modificand's denotation
    ([parsons-1970]). Adjectives, adverbs, and relative clauses are modifiers
    of different `τ`; they compose as endofunctions (modifier stacking). -/
abbrev Modifier (τ : Type*) := τ → τ

namespace Modifier

variable {α : Type*}

/-- A modifier over an ordered carrier is **subsective** if its output lies
    below the modificand: a skillful surgeon is a surgeon. -/
def isSubsective [LE α] (m : Modifier α) : Prop :=
  ∀ x, m x ≤ x

/-- Subsectivity is the deflationary condition in the pointwise order on
    modifiers. -/
theorem isSubsective_iff_le_id [LE α] {m : Modifier α} :
    isSubsective m ↔ m ≤ id :=
  Iff.rfl

/-- A modifier is **privative** if its output is disjoint from the
    modificand: a fake gun is not a gun. -/
def isPrivative [PartialOrder α] [OrderBot α] (m : Modifier α) : Prop :=
  ∀ x, Disjoint (m x) x

/-- A modifier that is both privative and subsective sends every modificand
    to `⊥` — the order-theoretic core of "privative is incompatible with
    subsective". -/
theorem isPrivative.eq_bot [PartialOrder α] [OrderBot α] {m : Modifier α}
    (hp : isPrivative m) (hs : isSubsective m) (x : α) : m x = ⊥ :=
  le_bot_iff.mp (hp x le_rfl (hs x))

section SemilatticeInf

variable [SemilatticeInf α]

/-- A modifier is **intersective** if it is meet with some fixed element. -/
def isIntersective (m : Modifier α) : Prop :=
  ∃ q, ∀ x, m x = q ⊓ x

/-- Intersective ⟹ subsective ([kamp-1975]'s implication structure). -/
theorem isIntersective.isSubsective {m : Modifier α}
    (h : isIntersective m) : isSubsective m := by
  obtain ⟨q, hq⟩ := h
  intro x
  rw [hq]
  exact inf_le_right

/-- The intersective modifier built from `q`: meet the modificand with `q`.
    At `α → Prop` this is pointwise conjunction; at conjoinable `Denot`
    domains (`Intensional/Algebra.lean` instances) it is Partee-Rooth
    generalized conjunction with the head. The well-behaved special case
    (restrictive relative clauses, intersective adjectives, manner adverbs). -/
def intersective (q : α) : Modifier α := (q ⊓ ·)

@[simp] theorem intersective_apply {β : Type*} (P Q : β → Prop) (x : β) :
    intersective P Q x = (P x ∧ Q x) := rfl

/-- Modificand and modifier meet symmetrically. -/
theorem intersective_comm (q r : α) : intersective q r = intersective r q :=
  inf_comm q r

theorem intersective_isIntersective (q : α) : isIntersective (intersective q) :=
  ⟨q, fun _ => rfl⟩

end SemilatticeInf

end Modifier
