module

public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Comparative probability: the derived modal operators

A relation `r a b` on a Boolean algebra `α` reads "`a` is at least as likely as `b`"
([holliday-icard-2013]); `QualitativeProbability.ge` and the measure-induced orders of
`Core/Order/Probability` are its models. This file defines the operators that the
comparative epistemic modals are built from: strict comparison `a ≻ b`, *probably*
`△a` (`a` is strictly more likely than its complement) and *possibly* `◇a` (`a` is
not certainly impossible).

## References

* [holliday-icard-2013]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α]

/-- `Strict r a b` ("`a ≻ b`"): `a` is at least as likely as `b` but not conversely. -/
def Strict (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ r b a

instance {r : α → α → Prop} [DecidableRel r] : DecidableRel (Strict r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- `Probably r a` ("`△a`"): `a` is strictly more likely than its complement. -/
def Probably (r : α → α → Prop) (a : α) : Prop := Strict r a aᶜ

/-- `Possibly r a` ("`◇a`"): `a` is not certainly impossible (`¬ ⊥ ≽ a`). -/
def Possibly (r : α → α → Prop) (a : α) : Prop := ¬ r ⊥ a

end ComparativeProbability
