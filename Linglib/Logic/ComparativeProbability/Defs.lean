module

public import Linglib.Core.Order.Probability.Defs

/-!
# The modal operators of comparative probability

The logics of comparative probability ([holliday-icard-2013]) read a likelihood order
`r` on a Boolean algebra as the comparative *at least as likely as* and define the graded
epistemic modals from it: *probably* `△a`, `a` strictly more likely than its complement,
and *possibly* `◇a`, `a` not certainly impossible.

## References

* [holliday-icard-2013]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α]

/-- `Probably r a` ("`△a`"): `a` is strictly more likely than its complement. -/
def Probably (r : α → α → Prop) (a : α) : Prop := Strict r a aᶜ

/-- `Possibly r a` ("`◇a`"): `a` is not certainly impossible (`¬ ⊥ ≽ a`). -/
def Possibly (r : α → α → Prop) (a : α) : Prop := ¬ r ⊥ a

end ComparativeProbability
