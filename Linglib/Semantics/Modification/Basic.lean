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

## Implementation notes

`Modifier.intersective` is the canonical intersective-modification operation; the
concrete reflexes reduce to it (`ArgumentStructure`'s `modify` over events calls
it; the type-driven interpreter's Predicate Modification step is it at `e ⇒ t`).
The [kamp-1975] modifier-meaning classification (intersective / subsective /
privative / extensional) lives at its intensional generality in
`Modification/Adjective.lean`; `Studies/Kamp1975.lean` § 1 specializes it to a
single world.
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

end Modifier
