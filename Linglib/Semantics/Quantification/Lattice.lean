import Linglib.Semantics.Quantification.Properties
import Mathlib.Order.BooleanSubalgebra

/-!
# The conservative determiners as a Boolean algebra

Conservative generalized quantifiers are closed under the pointwise Boolean operations
([keenan-stavi-1986]), so they form a Boolean subalgebra `conservativeSubalgebra` of `GQ α`, whose
elements `ConsGQ α` carry mathlib's Boolean algebra structure. [elliott-2025] identifies this
algebra with the predicates of polarized groups.

## Implementation notes

The Boolean algebra on `GQ α` is mathlib's Pi instance (`Prop` is a Boolean algebra and
`(α → Prop) → (α → Prop) → Prop` lifts pointwise); closure under `⊔` and `⊓` is
`conservative_gqJoin` and `conservative_gqMeet`, and the complement of a conservative quantifier
is conservative because conservativity is an equivalence at every restrictor and scope.

## References

* [keenan-stavi-1986]
* [elliott-2025]
-/

namespace Quantification

variable {α : Type*}

/-- The conservative GQs, a Boolean subalgebra of `GQ α`. -/
def conservativeSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {q | Conservative q}
  supClosed' q₁ hq₁ q₂ hq₂ := conservative_gqJoin q₁ q₂ hq₁ hq₂
  infClosed' q₁ hq₁ q₂ hq₂ := conservative_gqMeet q₁ q₂ hq₁ hq₂
  compl_mem' hq R S := not_congr (hq R S)
  bot_mem' _ _ := Iff.rfl

@[simp] theorem mem_conservativeSubalgebra {q : GQ α} :
    q ∈ conservativeSubalgebra ↔ Conservative q :=
  Iff.rfl

/-- Conservative GQs: the subtype of `GQ α` satisfying conservativity, a Boolean algebra under
the pointwise propositional operations, the order being pointwise implication. -/
abbrev ConsGQ (α : Type*) := conservativeSubalgebra (α := α)

namespace ConsGQ

variable {α : Type*}

/-- The join of conservative GQs agrees with `gqJoin`. -/
theorem sup_eq_gqJoin (q₁ q₂ : ConsGQ α) : (q₁ ⊔ q₂).1 = gqJoin q₁.1 q₂.1 := rfl

/-- The meet of conservative GQs agrees with `gqMeet`. -/
theorem inf_eq_gqMeet (q₁ q₂ : ConsGQ α) : (q₁ ⊓ q₂).1 = gqMeet q₁.1 q₂.1 := rfl

@[simp] theorem sup_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊔ q₂).1 R S = (q₁.1 R S ∨ q₂.1 R S) := rfl

@[simp] theorem inf_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊓ q₂).1 R S = (q₁.1 R S ∧ q₂.1 R S) := rfl

@[simp] theorem top_val (R S : α → Prop) : (⊤ : ConsGQ α).1 R S = True := rfl

@[simp] theorem bot_val (R S : α → Prop) : (⊥ : ConsGQ α).1 R S = False := rfl

@[simp] theorem compl_val (q : ConsGQ α) (R S : α → Prop) : qᶜ.1 R S = ¬ q.1 R S := rfl

end ConsGQ

end Quantification
