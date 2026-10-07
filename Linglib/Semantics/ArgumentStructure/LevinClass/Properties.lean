module

public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Semantics.ArgumentStructure.DiathesisAlternation

/-!
# The property tables of the Levin classes

`LevinClass.properties` is the property table of a class's entry in Part II of Levin's *English
Verb Classes and Alternations*: each line names an alternation of Part One by its section number,
or a further property, with the book's asterisk or question mark, its scope and any further
qualifier. A class shows an alternation (`LevinClass.Participates`) when a line names it without a
diacritic, lacks it (`LevinClass.Stars`) when a line stars it or the section grouping it, and
tests it (`LevinClass.Tests`) when it does either.

## Implementation notes

* A starred family heading, such as "*Causative Alternations", denies each of the family's
  subsections, so `Stars` descends to them. An attested family heading is entered as the
  subsection whose Part One list carries the class, so `Participates` reads the lines as they
  stand.
* A heading phrased as a denial ("not available", "not possible") is the alternation starred.
* A class may list related alternations under different bases: the spray/load class attests the
  other causative alternations of its locative variant and stars the causative alternations of its
  *with* variant, so `Participates` and `Stars` are not disjoint, and the qualifiers tell the lines
  apart.

## References

* [levin-1993]
-/

@[expose] public section

namespace ArgumentStructure.LevinClass

open Data.VerbClasses

/-- The alternation of Part One a property line names, if it names one. -/
def _root_.Data.VerbClasses.PropertyLine.alternation? (l : PropertyLine) :
    Option DiathesisAlternation :=
  match l.heading with
  | .alternation n => DiathesisAlternation.ofNumber? n
  | .property _ => none

/-- The property table of the class's entry, in the book's order. -/
def properties (c : LevinClass) : List PropertyLine := (entry c).properties

/-- The class's table lists the alternation with the given diacritic. -/
def Lists (c : LevinClass) (a : DiathesisAlternation) (d : Diacritic) : Prop :=
  ∃ l ∈ c.properties, l.heading = .alternation a.number ∧ l.diacritic = d

instance (c : LevinClass) (a : DiathesisAlternation) (d : Diacritic) : Decidable (c.Lists a d) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The class shows the alternation when its table lists it without a diacritic. -/
def Participates (c : LevinClass) (a : DiathesisAlternation) : Prop := c.Lists a .none

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Participates a) :=
  inferInstanceAs (Decidable (c.Lists a .none))

/-- The class lacks the alternation when its table stars it or the section grouping it. -/
def Stars (c : LevinClass) (a : DiathesisAlternation) : Prop :=
  c.Lists a .star ∨ ∃ p ∈ a.parent?, c.Lists p .star

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Stars a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The class's table tests the alternation, attesting or starring it. -/
def Tests (c : LevinClass) (a : DiathesisAlternation) : Prop := c.Participates a ∨ c.Stars a

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Tests a) :=
  inferInstanceAs (Decidable (_ ∨ _))

end ArgumentStructure.LevinClass
