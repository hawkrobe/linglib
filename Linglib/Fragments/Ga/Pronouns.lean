/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Gã personal pronouns

The pronoun paradigm of [allotey-2021]'s Table 3 (Gã, ISO 639-3 `gaa`; Kwa,
Ghana) as `PersonalPronoun` entries. Each person–number cell has one form that
serves the subjective (nominative) and possessive (genitive) columns, and only
the second and third person singular add a dedicated objective (accusative)
form, *bo* and *lɛ*; the other cells use the one form in every column. Gã has
no clusivity and no gender.

## Implementation notes

The case-neutral form of a cell is entered with `case_ := none` and the
dedicated objective form with `case_ := some .acc`, so a cell's paradigm
(`paradigm`) has two forms exactly where Table 3 has a distinct objective
column. Not recorded: the clipped past-tense 1SG variant *ĩ* and the impersonal
subject *a*, which has neither objective nor possessive form. The paper does
not classify the subject pronouns by structural deficiency: [campbell-2017]
writes them as clitics prefixed to the verb, which the paper rejects on the
strength of the negation that intervenes between the embedded subject and its
verb, so `strength` stays `none`. Lean does not accept `ɛ` or `ŋ` in plain
identifiers, so names use Latin letters (`le`, `wo`, `nye`, `ame`) and the
orthography lives in `form`.

## References

* [allotey-2021]
* [campbell-2017]
-/

namespace Ga.Pronouns

/-- *mi* — first person singular, the one form of all three columns. -/
def mi : PersonalPronoun := { form := "mi", person := some .first, number := some .singular }

/-- *o* — second person singular subjective and possessive. -/
def o : PersonalPronoun := { form := "o", person := some .second, number := some .singular }

/-- *bo* — second person singular objective. -/
def bo : PersonalPronoun :=
  { form := "bo", person := some .second, number := some .singular, case_ := some .acc }

/-- *e* — third person singular subjective and possessive. -/
def e : PersonalPronoun := { form := "e", person := some .third, number := some .singular }

/-- *lɛ* — third person singular objective. -/
def le : PersonalPronoun :=
  { form := "lɛ", person := some .third, number := some .singular, case_ := some .acc }

/-- *wɔ* — first person plural, the one form of all three columns. -/
def wo : PersonalPronoun := { form := "wɔ", person := some .first, number := some .plural }

/-- *nyɛ* — second person plural, the one form of all three columns. -/
def nye : PersonalPronoun := { form := "nyɛ", person := some .second, number := some .plural }

/-- *amɛ* — third person plural, the one form of all three columns. -/
def ame : PersonalPronoun := { form := "amɛ", person := some .third, number := some .plural }

/-- The personal pronoun inventory of Table 3. -/
def pronouns : Finset PersonalPronoun := {mi, o, bo, e, le, wo, nye, ame}

/-- The forms of each referential category. -/
def paradigm : Person.Category → Finset String := PersonalPronoun.paradigm pronouns

/-- The subject forms of a person–number cell: those of its case-neutral
    entries, one per cell of Table 3. In the paper's control examples the
    embedded subject of a controlled `ni`-clause is one of these, never
    silent; merged with the irrealis high tone the 1SG form surfaces as the
    portmanteau *má*. -/
def subjectForms (p : Person) (n : Number) : Finset String :=
  (pronouns.filter fun q ↦ q.person = some p ∧ q.number = some n ∧ q.case_ = none).image
    (·.form)

end Ga.Pronouns
