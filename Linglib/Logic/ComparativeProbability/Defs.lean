module

public import Linglib.Core.Order.Probability.Defs

/-!
# *Probably* in comparative probability

A likelihood order `r` on a Boolean algebra, read as the comparative *at least as likely as*,
defines *probably*: `△a` holds when `a` is strictly more likely than its complement, as in the
logics of comparative probability that Holliday and Icard compare. Over a monotone order the
contradiction is never probable and, when the order is non-trivial, the tautology always is;
over a monotone transitive order *probably* is upward closed. `RightUnion` is Halpern's union
property `J`.

## References

* [holliday-icard-2013]
* [halpern-2003]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α]

/-- `Probably r a` ("`△a`") says that `a` is strictly more likely than its complement. -/
def Probably (r : α → α → Prop) (a : α) : Prop := Strict r a aᶜ

/-- A relation is right-union closed, Halpern's axiom `J`, when `a ≽ b` and `a ≽ c` give
`a ≽ (b ⊔ c)`. This union property separates the l-lifting from the additive semantics. -/
def RightUnion {β : Type*} [SemilatticeSup β] (r : β → β → Prop) : Prop :=
  ∀ a b c, r a b → r a c → r a (b ⊔ c)

variable {r : α → α → Prop} {a b : α}

/-- *Probably* is upward closed over a monotone transitive order, since a larger event is at
least as likely and its complement at most as likely. -/
theorem Probably.mono [IsLikelihoodMono r] [IsTrans α r] (hab : a ≤ b) (ha : Probably r a) :
    Probably r b :=
  strict_of_strict_of_rel (strict_of_rel_of_strict (IsLikelihoodMono.mono _ _ hab) ha)
    (IsLikelihoodMono.mono _ _ (compl_le_compl hab))

theorem probably_top [IsLikelihoodMono r] [IsNontrivial r] : Probably r ⊤ := by
  rw [Probably, compl_top]
  exact ⟨mono _ _ bot_le, IsNontrivial.bot_not_ge_top⟩

theorem not_probably_bot [IsLikelihoodMono r] : ¬ Probably r ⊥ := fun h ↦
  h.2 (by rw [compl_bot]; exact mono _ _ le_top)

end ComparativeProbability
