import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Minimal

/-!
# Decidability of minimality

`Minimal P x` unfolds to a conjunction of `P x` with a bounded quantifier over the type, so on
a finite type with a decidable order and predicate it is decidable. Mathlib's `Order.Minimal`
proves its facts classically and carries no instance.

## References

* [UPSTREAM] candidate for `Mathlib.Order.Minimal`.
-/

variable {α : Type*} [LE α] {P : α → Prop}

instance Minimal.decidable [Fintype α] [DecidableLE α] [DecidablePred P] (x : α) :
    Decidable (Minimal P x) :=
  decidable_of_iff (P x ∧ ∀ y, P y → y ≤ x → x ≤ y) .rfl
