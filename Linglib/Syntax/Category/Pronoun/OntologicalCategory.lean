module

public import Linglib.Data.UD.UPOS

/-!
# Ontological categories of pro-forms

The members of an interrogative or indefinite series differ in the ontological category they
stand for: a person (*who*, *someone*), a thing (*what*, *something*), a place (*where*,
*somewhere*) and so on. The category fixes the word class of the member, a pro-adverb for a
place, a time or a manner and a pronoun otherwise.

## Main definitions

* `Pronoun.OntologicalCategory`: the categories pro-forms stand for.
* `Pronoun.OntologicalCategory.upos`: the word class a category fixes.

## References

* [haspelmath-1997]
-/

@[expose] public section

/-- The ontological categories of pro-forms. Person, thing, property, place, time, manner and
amount are the seven Haspelmath finds expressed by simple means in most languages, the cut between
person and thing (*somebody* against *something*) being made nearly everywhere. Determiners
(*some* N) and reasons (*for some reason*) are common but not universal, English and German
having no *somewhy*. -/
inductive Pronoun.OntologicalCategory where
  /-- Person is the category of *somebody*, *someone* and interrogative *who*. -/
  | person
  /-- Thing is the category of *something* and interrogative *what*. -/
  | thing
  /-- Property or kind is the category of *some kind of* and interrogative *what kind*. -/
  | property
  /-- Place is the category of *somewhere* and interrogative *where*. -/
  | place
  /-- Time is the category of *sometime* and interrogative *when*. -/
  | time
  /-- Manner is the category of *somehow* and interrogative *how*. -/
  | manner
  /-- Amount is the category of *some amount* and interrogative *how much*. -/
  | amount
  /-- Determiner is the category of *some* N and interrogative *which*. -/
  | determiner
  /-- Reason is the category of *for some reason* and interrogative *why*. -/
  | reason
  deriving DecidableEq, Repr

namespace Pronoun.OntologicalCategory

/-- A category is adverbial when its pro-forms are pro-adverbs, of a place, a time or a
manner. -/
def IsAdverbial (c : OntologicalCategory) : Prop := c = .place ∨ c = .time ∨ c = .manner

instance : DecidablePred IsAdverbial := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The word class of a pro-form is an adverb in an adverbial category and a pronoun
otherwise. -/
def upos (c : OntologicalCategory) : UD.UPOS := if c.IsAdverbial then .ADV else .PRON

end Pronoun.OntologicalCategory
