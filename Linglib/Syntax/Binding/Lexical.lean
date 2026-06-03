import Linglib.Syntax.Pronoun.Basic
import Linglib.Features.CoreferenceStatus

/-!
# Binding-class predicates on the pronoun
[chomsky-1981]

A pro-form's binding role is its `Features.BindingClass`, declared on the entry as
`Pronoun.bindingClass` — one `Features.BindingSource Pronoun` (the *lexical* source). The
framework-neutral binding engine is polymorphic over the source (`Features.BindingSource`): a
theory may instead source the class structurally (HPSG sorts) or from syntactic context
(minimal-pronoun / DM). These predicates read the declared class as the Principle A / B / C
partition.

## Main declarations

* `Pronoun.{IsAnaphor, IsPronominal, IsRExpression}` — the Principle A / B / C partitions, read
  off `Pronoun.bindingClass`.
-/

namespace Pronoun

/-- `p` declares a Principle-A anaphor (reflexive or reciprocal). -/
def IsAnaphor (p : Pronoun) : Prop :=
  p.bindingClass = some .reflexive ∨ p.bindingClass = some .reciprocal

/-- `p` declares a Principle-B pronominal. -/
def IsPronominal (p : Pronoun) : Prop := p.bindingClass = some .pronoun

/-- `p` declares a Principle-C R-expression. -/
def IsRExpression (p : Pronoun) : Prop := p.bindingClass = some .rExpression

instance (p : Pronoun) : Decidable p.IsAnaphor := by unfold IsAnaphor; infer_instance
instance (p : Pronoun) : Decidable p.IsPronominal := by unfold IsPronominal; infer_instance
instance (p : Pronoun) : Decidable p.IsRExpression := by unfold IsRExpression; infer_instance

end Pronoun
