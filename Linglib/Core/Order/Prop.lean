module

public import Mathlib.Order.Basic

/-!
# The strict order on propositions

In the implication order on `Prop`, `p < q` holds exactly when `p` fails and `q` holds, so it is
decidable whenever both propositions are. Mathlib gives `Prop` its partial order in
`Order.Basic` without either fact.

## References

* [UPSTREAM] candidate for `Mathlib.Order.Basic`.
-/

@[expose] public section

variable {p q : Prop}

theorem Prop.lt_iff : p < q ↔ ¬ p ∧ q := by
  rw [lt_iff_le_not_ge]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨fun hp ↦ h fun _ ↦ hp, by_contra fun hq ↦ h fun hq' ↦ (hq hq').elim⟩,
    fun ⟨hp, hq⟩ ↦ ⟨fun _ ↦ hq, fun h ↦ hp (h hq)⟩⟩

instance Prop.decidableLT [Decidable p] [Decidable q] : Decidable (p < q) :=
  decidable_of_iff _ Prop.lt_iff.symm
