import Mathlib.Logic.Basic

/-!
# Modifiers
[parsons-1970] [kamp-1975]

A **modifier** of `τ` is a function on the modificand's denotation
([parsons-1970]: "modifiers as functions on predicates"). Adjectives,
adverbs, and relative clauses are all modifiers — of *different* `τ` (nominal
`e ⇒ t`, event `Event → Prop`, …) — unified by *being* this type, not by
implementing an interface.

The well-behaved special case is **intersective** modification: conjunction with a
fixed property (`λx. P x ∧ Q x`), on which restrictive relative clauses,
intersective adjectives, and manner adverbs all converge.

## Main declarations

* `Modifier` — a modifier of `τ` is an endofunction `τ → τ`.
* `Modifier.intersective` — the intersective modifier built from a property `P`.
* `Modifier.isIntersective` / `.isSubsective` / `.isPrivative` — the
  [kamp-1975] modifier-meaning classification, as predicates on a modifier.

## Implementation notes

`Modifier.intersective` is the canonical intersective-modification operation; the
concrete reflexes reduce to it (`ArgumentStructure/LF.EventModifier.modify` over
events calls it; the type-driven interpreter's Predicate Modification step is it at
`e ⇒ t`). The adjective-specific classification in `Gradability/Classification`
(over `AdjMeaning`) is the remaining copy to fold onto these forms (follow-up).
-/

/-- A modifier of `τ` is a function on the modificand's denotation
    ([parsons-1970]). Adjectives, adverbs, and relative clauses are modifiers
    of different `τ`; they compose as endofunctions (modifier stacking). -/
abbrev Modifier (τ : Type*) := τ → τ

namespace Modifier

variable {α : Type*}

/-- The intersective modifier built from a property `P`: combine `P` with the
    modificand by pointwise conjunction. The well-behaved special case
    (restrictive relative clauses, intersective adjectives, manner adverbs). -/
def intersective (P : α → Prop) : Modifier (α → Prop) :=
  fun Q x => P x ∧ Q x

@[simp] theorem intersective_apply (P Q : α → Prop) (x : α) :
    intersective P Q x = (P x ∧ Q x) := rfl

/-- Head and modifier intersect symmetrically (conjunction is commutative). -/
theorem intersective_comm (P Q : α → Prop) : intersective P Q = intersective Q P := by
  funext x; exact propext And.comm

/-- A modifier is **intersective** if it is conjunction with some fixed property. -/
def isIntersective (m : Modifier (α → Prop)) : Prop :=
  ∃ P : α → Prop, ∀ Q, m Q = intersective P Q

/-- A modifier is **subsective** if its output always entails the modificand
    (`m Q ⊆ Q`): a skillful surgeon is a surgeon. -/
def isSubsective (m : Modifier (α → Prop)) : Prop :=
  ∀ Q x, m Q x → Q x

/-- A modifier is **privative** if its output is disjoint from the modificand
    (`m Q ∩ Q = ∅`): a fake gun is not a gun. -/
def isPrivative (m : Modifier (α → Prop)) : Prop :=
  ∀ Q x, m Q x → ¬ Q x

theorem intersective_isIntersective (P : α → Prop) : isIntersective (intersective P) :=
  ⟨P, fun _ => rfl⟩

/-- Intersective ⟹ subsective ([kamp-1975]'s implication structure). -/
theorem isSubsective_of_isIntersective {m : Modifier (α → Prop)}
    (h : isIntersective m) : isSubsective m := by
  obtain ⟨P, hP⟩ := h
  intro Q x hx
  rw [hP Q] at hx
  exact hx.2

end Modifier
