import Mathlib.Data.Finset.Union
import Linglib.Data.UD.Features
import Linglib.Morphology.Morph
import Linglib.Syntax.Clause.Chaining

/-!
# Turkish converbs

Turkish chains clauses with converbal suffixes (*zarf-fiil*) on the verb stem of each medial
clause before a single final verb. There is no switch-reference: each converb encodes the
relation between its clause and the next. *-(y)ip* 'and then, having done' sequences events
with shared or different subjects, *-(y)erek* 'by doing, while doing' gives the manner of or
accompanies the following event, *-(y)ince* 'when, once' anchors or conditions it, *-ken*
'while' marks an ongoing state on the aorist or progressive stem, *-dikce* 'as, the more'
marks a proportional relation, *-meden* 'without doing' is inherently negative and has no
affirmative counterpart, *-AlI* 'since doing' marks a starting point, as in *geleli üç gün
oldu* 'it's been three days since (s/he) came', and *-casina* 'as if' is simulative. The
converbal verb carries no person or number agreement, which only the final verb carries, and
some converbs admit tense or aspect. Every converb but *-meden* has a negative form:
*-meyip*, *-meyerek*, *-meyince*, *-mazken*, *-medikce*, *-meyeli* and *-mezcesine*. The
converbs are the textbook converbs of Universal Dependencies.

## Main definitions

* `Turkish.Converb` — the eight converbs, with their morphs (`morphs`, `form`), gloss, the
  relations they encode (`relations`), their negative form (`negative`), whether they are
  inherently negative (`InherentlyNegative`) or negatable at all (`Negatable`), and their
  verb form (`verbForm`); they are an instance of `Clause.Chaining.MedialForm`

## Implementation notes

The clause-chaining typology over these forms is in `Studies/SarvasyAikhenvald2025.lean`. The
proportional converb encodes a relation the inventory of interclausal relations does not name.

## References

* [goksel-kerslake-2005]
* [kornfilt-1997]
-/

namespace Turkish

open Clause.Chaining (InterclauseRelation)
open Morphology (Morph)

/-- The converbal suffixes, romanized, with vowel harmony shown by a capital archiphoneme
and a buffer consonant in parentheses. -/
inductive Converb where
  /-- *-(y)ip* 'and then, having done', the most common converb for narrative sequencing. -/
  | ip
  /-- *-(y)erek* 'by doing, while doing'. -/
  | erek
  /-- *-(y)ince* 'when, once, upon doing'. -/
  | ince
  /-- *-ken* 'while', on the aorist or progressive stem. -/
  | ken
  /-- *-dikce* 'as, the more … the more'. -/
  | dikce
  /-- *-meden* 'without doing, before doing', inherently negative. -/
  | meden
  /-- *-AlI* 'since doing'. -/
  | ali
  /-- *-casina* 'as if, as though'. -/
  | casina
  deriving DecidableEq, Repr, Fintype

namespace Converb

/-- The morphs of a converb. -/
def morphs : Converb → List Morph
  | ip => [.suff "(y)ip"]
  | erek => [.suff "(y)erek"]
  | ince => [.suff "(y)ince"]
  | ken => [.suff "ken"]
  | dikce => [.suff "dikce"]
  | meden => [.suff "meden"]
  | ali => [.suff "AlI"]
  | casina => [.suff "casina"]

/-- The form of a converb in boundary notation. -/
def form (c : Converb) : String := Morph.surface c.morphs

/-- The gloss. -/
def gloss : Converb → String
  | ip => "and then, having done"
  | erek => "by doing, while doing"
  | ince => "when, once"
  | ken => "while"
  | dikce => "as, the more"
  | meden => "without doing"
  | ali => "since doing"
  | casina => "as if"

/-- The interclausal relations a converb encodes. -/
def relations : Converb → Finset InterclauseRelation
  | ip | ali => {.sequential}
  | erek => {.manner, .simultaneous}
  | ince => {.sequential, .conditional}
  | ken => {.simultaneous}
  | dikce => ∅
  | meden | casina => {.manner}

/-- The negative form of a converb, none for the inherently negative one. -/
def negative : Converb → Option Morph
  | ip => some (.suff "meyip")
  | erek => some (.suff "meyerek")
  | ince => some (.suff "meyince")
  | ken => some (.suff "mazken")
  | dikce => some (.suff "medikce")
  | meden => none
  | ali => some (.suff "meyeli")
  | casina => some (.suff "mezcesine")

/-- The converb is inherently negative. -/
def InherentlyNegative (c : Converb) : Prop := c = meden

instance : DecidablePred InherentlyNegative := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The converb can be negated, having a negative form or being negative itself. -/
def Negatable (c : Converb) : Prop := c.InherentlyNegative ∨ c.negative ≠ none

instance : DecidablePred Negatable := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The verb form of a converb. -/
def verbForm (_ : Converb) : UD.VerbForm := .Conv

/-- The converbs as medial forms, neutral to switch-reference, encoding their relations, and
never indexing the subject. -/
instance : Clause.Chaining.MedialForm Converb where
  sr _ := none
  relations := relations
  IndexesSubject _ := False

end Converb

end Turkish
