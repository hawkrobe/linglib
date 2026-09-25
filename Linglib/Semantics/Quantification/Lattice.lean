module

public import Linglib.Semantics.Quantification.Properties
public import Mathlib.Order.BooleanSubalgebra

/-!
# The conservative determiners as a Boolean algebra

Conservative generalized quantifiers are closed under the pointwise Boolean operations
([keenan-stavi-1986]), so they form a Boolean subalgebra `conservativeSubalgebra` of `GQ α`, whose
elements `ConsGQ α` carry mathlib's Boolean algebra structure. [elliott-2025] identifies this
algebra with the predicates of polarized groups.

## Implementation notes

The Boolean algebra on `GQ α` is mathlib's Pi instance (`Prop` is a Boolean algebra and
`(α → Prop) → (α → Prop) → Prop` lifts pointwise); closure under `⊔` and `⊓` is
`Conservative.sup` and `Conservative.inf`, and the complement of a conservative quantifier
is conservative because conservativity is an equivalence at every restrictor and scope.

## References

* [keenan-stavi-1986]
* [elliott-2025]
-/

@[expose] public section

namespace Quantifier.GQ

variable {α : Type*}

/-- The conservative GQs, a Boolean subalgebra of `GQ α`. -/
def conservativeSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {q | Conservative q}
  supClosed' q₁ hq₁ q₂ hq₂ := Conservative.sup q₁ q₂ hq₁ hq₂
  infClosed' q₁ hq₁ q₂ hq₂ := Conservative.inf q₁ q₂ hq₁ hq₂
  compl_mem' hq R S := not_congr (hq R S)
  bot_mem' _ _ := Iff.rfl

@[simp] theorem mem_conservativeSubalgebra {q : GQ α} :
    q ∈ conservativeSubalgebra ↔ Conservative q :=
  Iff.rfl

/-- The conservative GQs form the subtype of `GQ α` satisfying conservativity, a Boolean algebra
under the pointwise propositional operations with pointwise implication as the order. -/
abbrev ConsGQ (α : Type*) := conservativeSubalgebra (α := α)

namespace ConsGQ

variable {α : Type*}

@[simp] theorem sup_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊔ q₂).1 R S = (q₁.1 R S ∨ q₂.1 R S) := rfl

@[simp] theorem inf_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊓ q₂).1 R S = (q₁.1 R S ∧ q₂.1 R S) := rfl

@[simp] theorem top_val (R S : α → Prop) : (⊤ : ConsGQ α).1 R S = True := rfl

@[simp] theorem bot_val (R S : α → Prop) : (⊥ : ConsGQ α).1 R S = False := rfl

@[simp] theorem compl_val (q : ConsGQ α) (R S : α → Prop) : qᶜ.1 R S = ¬ q.1 R S := rfl

end ConsGQ

end Quantifier.GQ
