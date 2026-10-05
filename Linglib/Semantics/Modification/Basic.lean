module

public import Mathlib.Order.PropInstances

/-!
# Modifiers

A modifier of `τ` is a function from `τ` to itself, as Parsons treats adjectives and adverbs as
functions on the predicates they modify; adjectives, adverbs and relative clauses are modifiers
of different types `τ`. Kamp's classification of adjective meanings is order-theoretic: over an
ordered type, a modifier is subsective when it maps each argument below itself, privative when
its value is disjoint from its argument, and intersective when it is the meet with a fixed
element. `Semantics/Modification/Classification.lean` specializes the classes to intensional
properties.

## Main definitions

* `Modifier τ`: the functions from `τ` to `τ`.
* `Modifier.intersective q`: the meet with `q`.
* `Modifier.IsSubsective`, `Modifier.IsPrivative`, `Modifier.IsIntersective`: Kamp's classes.

## References

* [parsons-1970]
* [kamp-1975]
-/

@[expose] public section

/-- A modifier of `τ` is a function from `τ` to `τ`; modifiers stack by composition. -/
abbrev Modifier (τ : Type*) := τ → τ

namespace Modifier

variable {α : Type*}

/-- A modifier `m` is subsective if `m x ≤ x` for every `x`, so that a skillful surgeon is a
surgeon. -/
def IsSubsective [LE α] (m : Modifier α) : Prop :=
  ∀ x, m x ≤ x

/-- A modifier is subsective if and only if it lies below the identity. -/
theorem isSubsective_iff_le_id [LE α] {m : Modifier α} :
    IsSubsective m ↔ m ≤ id :=
  Iff.rfl

/-- A modifier `m` is privative if `m x` is disjoint from `x` for every `x`, so that a fake gun is
not a gun. -/
def IsPrivative [PartialOrder α] [OrderBot α] (m : Modifier α) : Prop :=
  ∀ x, Disjoint (m x) x

/-- A modifier that is both privative and subsective sends everything to `⊥`. -/
theorem IsPrivative.eq_bot [PartialOrder α] [OrderBot α] {m : Modifier α}
    (hp : IsPrivative m) (hs : IsSubsective m) (x : α) : m x = ⊥ :=
  le_bot_iff.mp (hp x le_rfl (hs x))

section SemilatticeInf

variable [SemilatticeInf α]

/-- A modifier is intersective if it is the meet with some fixed element. -/
def IsIntersective (m : Modifier α) : Prop :=
  ∃ q, ∀ x, m x = q ⊓ x

/-- Intersective modifiers are subsective. -/
theorem IsIntersective.isSubsective {m : Modifier α} (h : IsIntersective m) :
    IsSubsective m :=
  fun x ↦ h.elim fun _ hq ↦ (hq x).trans_le inf_le_right

/-- `intersective q` meets its argument with `q`; on predicates it is pointwise conjunction, the
meaning of restrictive relative clauses, intersective adjectives and manner adverbs. -/
def intersective (q : α) : Modifier α := (q ⊓ ·)

@[simp] theorem intersective_apply {β : Type*} (P Q : β → Prop) (x : β) :
    intersective P Q x = (P x ∧ Q x) := rfl

/-- The meet with `q` applied to `r` is the meet with `r` applied to `q`. -/
theorem intersective_comm (q r : α) : intersective q r = intersective r q :=
  inf_comm q r

theorem intersective_isIntersective (q : α) : IsIntersective (intersective q) :=
  ⟨q, fun _ ↦ rfl⟩

end SemilatticeInf

end Modifier
