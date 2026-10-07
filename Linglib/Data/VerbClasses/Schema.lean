module

public import Mathlib.Tactic.DeriveFintype

/-!
# Verb class catalogues: schema

Typed schema for a book's catalogue of verb classes: for each class, the section number and title
the book prints, its members, and its properties, each an alternation of the book's catalogue of
alternations, named by its section number, or a further property, with the diacritic and scope the
book gives it. Generated catalogues live in `Data/VerbClasses/<Book>.lean`, emitted from the
canonical `<Book>.json` by `scripts/gen_verb_classes.py`.

This is data: it imports nothing from `Linglib/` and states no theorems. The vocabulary is that of
Levin's catalogue: an alternation is named by its section number in her Part One, and the further
properties are those her class descriptions name. A catalogue with another vocabulary, such as
VerbNet's thematic roles and frames, needs its own schema.

## References

* [levin-1993]
-/

@[expose] public section

namespace Data.VerbClasses

/-- A property carries no diacritic, an asterisk for a property the class lacks, or a question
mark for a marginal one. -/
inductive Diacritic where
  | none
  | star
  | question
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The share of a class's members that a property line speaks for, as the book qualifies it:
all of them when it does not, or "most", "many", "some" or "a few" verbs. -/
inductive Scope where
  | all
  | most
  | many
  | some
  | few
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- A derived nominal may have only its active or only its passive interpretation. -/
inductive NominalReading where
  | active
  | passive
  deriving DecidableEq, Repr, Fintype

/-- The goal of a verb of communication is expressed by an object or by a *to* phrase. -/
inductive GoalPhrase where
  | object
  | toPhrase
  deriving DecidableEq, Repr, Fintype

/-- A sentential complement's goal is expressed as the book leaves it, not at all, by a required
phrase, or by an optional one. -/
inductive GoalRealization where
  | unspecified
  | absent
  | required (g : GoalPhrase)
  | optional (g : GoalPhrase)
  deriving DecidableEq, Repr

/-- A property the book lists for a class that is not one of its alternations. -/
inductive PageProperty where
  | zeroRelatedNominal
  | erNominal
  | ingNominal
  | processNominal
  | resultNominal
  | derivedNominal (reading : NominalReading)
  | ableAdjective
  | zeroRelatedAdjective
  | sententialComplement (goal : GoalRealization)
  | extraposition
  | directSpeech
  | parentheticalUse
  | infinitivalCopularClause
  | measurePhrase
  | pathPhrase
  | depictivePhrase
  | substanceObject
  | bodyPartObject
  | collectiveNPSubject
  | impersonalPassive
  | passivePrepositionChoice
  | fromPhrase
  | withAlternatesWithIn
  | ofAlternatesWithOut
  | unspecifiedObjectPlusLocativePP
  | coreferentialInterpretationVaries
  deriving DecidableEq, Repr

/-- A property line names an alternation by its section number in the book's catalogue of
alternations, or a further property. -/
inductive Heading where
  | alternation (number : List ℕ)
  | property (p : PageProperty)
  deriving DecidableEq, Repr

/-- A line of a class's property table records what it names, its diacritic and scope, and any
further qualifier the book prints with it, such as "based on with variant" or "except *kill*". -/
structure PropertyLine where
  heading : Heading
  diacritic : Diacritic
  scope : Scope
  qualifier : Option String
  deriving DecidableEq, Repr

/-- A verb class as the book describes it has the section number and title the book prints, the
page on which the class begins, the members and those of them the book marks as doubtful, and the
property table in the book's order. -/
structure VerbClass where
  number : String
  title : String
  page : ℕ
  members : List String
  doubtful : List String
  properties : List PropertyLine
  deriving Repr

instance : Inhabited VerbClass := ⟨⟨"", "", 0, [], [], []⟩⟩

end Data.VerbClasses
