module

public import Mathlib.Order.Basic
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The strict order and decidability on propositions and predicates

In the implication order on `Prop`, `p < q` holds exactly when `p` fails and `q` holds, so it is
decidable whenever both propositions are; mathlib gives `Prop` its partial order in `Order.Basic`
without either fact. Likewise the pointwise difference `p \ q` of two decidable predicates is
decidable, the sibling of mathlib's `Prop.decidablePredBot` and `Prop.decidablePredTop`.

## References

* [UPSTREAM] candidate for `Mathlib.Order.Basic` and `Mathlib.Order.PropInstances`.
-/

@[expose] public section

variable {p q : Prop}

theorem Prop.lt_iff : p < q ↔ ¬ p ∧ q := by
  rw [lt_iff_le_not_ge]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨fun hp ↦ h fun _ ↦ hp, by_contra fun hq ↦ h fun hq' ↦ (hq hq').elim⟩,
    fun ⟨hp, hq⟩ ↦ ⟨fun _ ↦ hq, fun h ↦ hp (h hq)⟩⟩

instance Prop.decidableLT [Decidable p] [Decidable q] : Decidable (p < q) :=
  decidable_of_iff _ Prop.lt_iff.symm

/-- The difference of two decidable predicates is decidable. -/
instance Prop.decidablePredSDiff {α : Type*} (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] : DecidablePred (p \ q) :=
  fun x ↦ decidable_of_iff (p x ∧ ¬ q x) Iff.rfl
