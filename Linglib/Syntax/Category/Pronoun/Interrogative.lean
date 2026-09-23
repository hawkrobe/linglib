module

public import Linglib.Semantics.Quantification.Indefinite
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Interrogative pronouns

An interrogative pronoun is a pronoun with the ontological category it asks about: a person for
*who*, a thing for *what*, a place for *where*. The categories are those of the indefinite
series, which many languages build on their interrogatives ([haspelmath-1997]), and they take
in the pro-forms for place, time and manner, which surface as adverbs.

## Main declarations

* `InterrogativePronoun` — a pronoun with its ontological category
* `InterrogativePronoun.toWord`, `InterrogativePronoun.isWh_toWord` — its word, wh-marked

## References

* [M. Haspelmath, *Indefinite Pronouns* (1997)][haspelmath-1997]
-/

@[expose] public section

/-- An interrogative pronoun: the general `Pronoun` with the ontological category it asks
about. -/
structure InterrogativePronoun extends Pronoun where
  /-- The ontological category the form asks about. -/
  ontology : Indefinite.OntologicalCategory
  deriving DecidableEq, Repr

namespace InterrogativePronoun

variable (p : InterrogativePronoun)

instance : HasPhi InterrogativePronoun := ⟨fun p ↦ p.toPronoun.phi⟩

/-- The form is a pro-adverb: it asks about a place, a time or a manner. -/
def IsAdverbial : Prop := p.ontology = .place ∨ p.ontology = .time ∨ p.ontology = .manner

instance : Decidable p.IsAdverbial := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- An interrogative's word is of UD pronoun type `Int`, an adverb when the form is a
pro-adverb and a pronoun otherwise. -/
def toWord : Morphology.Word :=
  { p.toPronoun.toWord (some .Int) with cat := if p.IsAdverbial then .ADV else .PRON }

/-- An interrogative projects a wh-marked word. -/
theorem isWh_toWord : p.toWord.features.IsWh :=
  .inl rfl

end InterrogativePronoun
