import Linglib.Syntax.Pronoun.Basic
import Linglib.Syntax.Pronoun.Mixin
import Linglib.Features.CoreferenceStatus

/-!
# The lexical interface to binding
[chomsky-1981]

A pro-form's binding role is its `Features.BindingClass` (which binding principle — A / B / C —
governs it), declared on the entry as `Pronoun.bindingClass`. A binding theory reads this
declaration rather than recovering the class from surface form strings: the lexical entry is
the source of truth for its own binding role.

The connection is kept deliberately concrete — predicates on the `Pronoun` record. A
`Lexicon`/`HasBindingClass` *typeclass* over the class accessor is intentionally **not**
introduced: a `Word`'s class is language-dependent (so `Lexicon Word` would be non-canonical),
and a `Pronoun` instance would only project the field — so that abstraction waits for a second
intrinsic-declaration carrier, or a carrier-based engine, to justify it.

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

/-! ### Validation: Principle A is driven by the declaration

Inlining the reflexive clause of `Binding.reflexiveLicensed` (`Syntax/Binding/Basic.lean`) —
*local command ∧ φ-agreement* for a dependent that declares `.reflexive` — shows the engine's
Principle-A logic reads the lexical declaration (`bindingClass`) and the `[PronounLike]`
φ-features, with no `classify : Word → BindingClass` form-string recovery. -/

private def exHe : Pronoun :=
  { form := "he", person := some .third, number := some .sg,
    gender := some .masculine, bindingClass := some .pronoun }
private def exHimself : Pronoun :=
  { form := "himself", person := some .third, number := some .sg,
    gender := some .masculine, bindingClass := some .reflexive }

/-- `himself` declares `.reflexive`, and — φ-agreeing with and locally commanded by `he` —
satisfies Principle A (`command ∧ φ-agreement`), read entirely off the declaration. -/
example :
    (match exHimself.bindingClass with
     | some .reflexive => True ∧ (PronounLike.phi exHe).compatible (PronounLike.phi exHimself)
     | _ => True) :=
  ⟨trivial, by decide⟩

end Pronoun
