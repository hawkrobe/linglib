import Linglib.Semantics.Quantification.Properties
import Mathlib.Order.BooleanAlgebra.Defs

/-!
# The conservative determiners as a Boolean algebra

Conservative generalized quantifiers are closed under the pointwise Boolean operations
([keenan-stavi-1986]), so they form a sublattice of `GQ α`, bounded by the trivial quantifiers,
and with pointwise negation a Boolean algebra. [elliott-2025] identifies this algebra with the
predicates of polarized groups.

## Implementation notes

The `DistribLattice` on `GQ α` is mathlib's Pi instance (`Prop` is a distributive lattice and
`(α → Prop) → (α → Prop) → Prop` lifts pointwise); closure under `⊔` and `⊓` is
`conservative_gqJoin` and `conservative_gqMeet`, and the complement of a conservative quantifier
is conservative because conservativity is an equivalence at every restrictor and scope.

## References

* [keenan-stavi-1986]
* [elliott-2025]
-/

namespace Quantification

variable {α : Type*}

/-- Conservative GQs form a sublattice of `GQ α`. -/
def conservativeSublattice : Sublattice (GQ α) where
  carrier := { q | Conservative q }
  supClosed' q₁ hq₁ q₂ hq₂ := conservative_gqJoin q₁ q₂ hq₁ hq₂
  infClosed' q₁ hq₁ q₂ hq₂ := conservative_gqMeet q₁ q₂ hq₁ hq₂

/-- Conservative GQs: the subtype of `GQ α` satisfying conservativity, a distributive lattice
under the pointwise propositional operations, the order being pointwise implication. -/
abbrev ConsGQ (α : Type*) := conservativeSublattice (α := α)

namespace ConsGQ

variable {α : Type*}

/-- The join of conservative GQs agrees with `gqJoin`. -/
theorem sup_eq_gqJoin (q₁ q₂ : ConsGQ α) : (q₁ ⊔ q₂).1 = gqJoin q₁.1 q₂.1 := rfl

/-- The meet of conservative GQs agrees with `gqMeet`. -/
theorem inf_eq_gqMeet (q₁ q₂ : ConsGQ α) : (q₁ ⊓ q₂).1 = gqMeet q₁.1 q₂.1 := rfl

instance : Bot (ConsGQ α) := ⟨⟨⊥, λ _ _ => Iff.rfl⟩⟩
instance : Top (ConsGQ α) := ⟨⟨⊤, λ _ _ => Iff.rfl⟩⟩

instance : OrderBot (ConsGQ α) where
  bot_le q := show ⊥ ≤ q.1 from bot_le

instance : OrderTop (ConsGQ α) where
  le_top q := show q.1 ≤ ⊤ from le_top

@[simp] theorem sup_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊔ q₂).1 R S = (q₁.1 R S ∨ q₂.1 R S) := rfl

@[simp] theorem inf_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊓ q₂).1 R S = (q₁.1 R S ∧ q₂.1 R S) := rfl

@[simp] theorem top_val (R S : α → Prop) : (⊤ : ConsGQ α).1 R S = True := rfl

@[simp] theorem bot_val (R S : α → Prop) : (⊥ : ConsGQ α).1 R S = False := rfl

/-- The complement of a conservative GQ is its pointwise negation, again conservative. -/
noncomputable instance : Compl (ConsGQ α) where
  compl q := ⟨λ R S => ¬ q.1 R S, λ R S => not_congr (q.2 R S)⟩

noncomputable instance : SDiff (ConsGQ α) where
  sdiff q₁ q₂ := q₁ ⊓ q₂ᶜ

noncomputable instance : HImp (ConsGQ α) where
  himp q₁ q₂ := q₂ ⊔ q₁ᶜ

noncomputable instance : BooleanAlgebra (ConsGQ α) where
  inf_compl_le_bot _ _ _ h := h.2 h.1
  top_le_sup_compl q _ _ _ := Classical.em (q.1 _ _)
  le_top _ := le_top
  bot_le _ := bot_le
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

@[simp] theorem compl_val (q : ConsGQ α) (R S : α → Prop) : qᶜ.1 R S = ¬ q.1 R S := rfl

end ConsGQ

end Quantification
