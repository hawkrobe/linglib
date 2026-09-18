import Mathlib.Data.Finset.Union
import Linglib.Data.UD.Features
import Linglib.Morphology.Morph
import Linglib.Fragments.Turkish.Morphotactics
import Linglib.Fragments.Turkish.Negation
import Linglib.Syntax.Clause.Chaining

/-!
# Turkish converbs

Turkish chains clauses with converbial suffixes on the verb of each medial clause before a
single final verb. There is no switch-reference: each converb encodes the relation between
its clause and the next, and the subjects of the two clauses are in general free to differ,
though *-(y)Ip* and the manner converbs seldom take a subject of their own. The
subordinating suffixes are nominalizing and any verb form containing one is non-finite; the
converbial suffixes proper combine with no person markers, except that *-(y)ken* optionally
takes the third-person plural *-lAr* and *-mIşçAsInA* may take a person marker. Eight of them
attach to a single verb. *-(y)Ip* conjoins clauses of equal status in place of the tense,
aspect and modality suffixes, *koşup al-* 'run and get', and *-(y)ArAk* 'by doing, doing' is
used the same way beside its manner and means readings, *koşarak* 'running'. *-(y)IncA*
'when' sequences two events, *kalkmayınca* 'when [s.o.] doesn't get up'. *-(y)ken* 'while,
as, when' contains the copula and so attaches not to the stem but to a position-3
tense, aspect or modality marker or to a nominal, *bakarken* 'while watching', *çocukken*
'as a child', the converb's temporal value coming from what precedes it. *-(y)AlI* 'since',
colloquial, marks the starting point of the main situation, *geleli* 'since arriving'.
*-mAdAn* 'without doing, before doing' contains the negative *-mA* and is stressed on the
syllable before it, *bağırmadan* 'without shouting'. *-cAsInA* 'as if' attaches to the aorist
or to *-mIş*, *hissedercesine* 'as if feeling'. *-DIkçA* marks proportionality, *çikolata
yedikçe* 'the more chocolate you eat'. Two further converbial subordinators are added to a
doubled verb: the positive and negative aorist stems *-(A/I)r … -mAz* 'as soon as', *su
kaynar kaynamaz* 'as soon as the water boils', and *-(y)A … -(y)A*, emphatic continuous
manner, *ağlaya ağlaya* 'weeping continually'. The negative *-mA* precedes the converbs that
attach to the stem, and the aorist negative *-mAz* the ones that attach to a tensed stem,
*-mAzdAn önce* 'before'.

## Main definitions

* `Turkish.Converb` — the eight converbs, with their morphs (`morphs`, `form`), gloss, the
  relations they encode (`relations`), the last slot of the finite verb they follow
  (`follows`), whether an exponent of a slot may precede them (`Admits`), from which whether
  they take a tense marker (`Tensed`) and a negative (`Negatable`) follow, whether they are
  inherently negative (`InherentlyNegative`) or may carry a person marker (`PersonMarked`),
  and their verb form (`verbForm`); they are an instance of `Clause.Chaining.MedialForm`
* `Turkish.arMaz`, `Turkish.aA` — the two converbial subordinators on a doubled verb

## Implementation notes

The slot a converb follows is read against the finite verb's template in
`Turkish.Verb.system`, so that a converb takes tense when a position-3 marker may precede
it and a negative when the negation slot may. The clause-chaining typology over the
converbs is in `Studies/SarvasyAikhenvald2025.lean`; the proportional converb encodes a
relation the inventory of interclausal relations does not name.

## References

* [goksel-kerslake-2005]
-/

namespace Turkish

open Clause.Chaining (InterclauseRelation)
open Morphology (Morph)

/-- The converbial suffixes on a single verb, with vowel harmony shown by a capital
archiphoneme and a buffer consonant in parentheses. -/
inductive Converb where
  /-- *-(y)Ip*, conjunctive 'and, and then'. -/
  | ip
  /-- *-(y)ArAk* 'by doing, doing', manner and means, also conjunctive. -/
  | arak
  /-- *-(y)IncA* 'when'. -/
  | inca
  /-- *-(y)ken* 'while, as, when', the copula on a tensed stem or a nominal. -/
  | ken
  /-- *-(y)AlI* 'since', colloquial. -/
  | ali
  /-- *-mAdAn* 'without doing, before doing', containing the negative. -/
  | madan
  /-- *-cAsInA* 'as if', on the aorist or *-mIş*. -/
  | casina
  /-- *-DIkçA* 'the more, as', proportional. -/
  | dikca
  deriving DecidableEq, Repr, Fintype

namespace Converb

/-- The morphs of a converb. -/
def morphs : Converb → List Morph
  | ip => [.suff "(y)Ip"]
  | arak => [.suff "(y)ArAk"]
  | inca => [.suff "(y)IncA"]
  | ken => [.suff "(y)ken"]
  | ali => [.suff "(y)AlI"]
  | madan => Negation.mA.morphs ++ [.suff "DAn"]
  | casina => [.suff "cAsInA"]
  | dikca => [.suff "DIkçA"]

/-- The form of a converb in boundary notation. -/
def form (c : Converb) : String := Morph.surface c.morphs

/-- The gloss. -/
def gloss : Converb → String
  | ip => "and, and then"
  | arak => "by doing, doing"
  | inca => "when"
  | ken => "while, as, when"
  | ali => "since"
  | madan => "without doing, before doing"
  | casina => "as if"
  | dikca => "the more, as"

/-- The interclausal relations a converb encodes. -/
def relations : Converb → Finset InterclauseRelation
  | ip => {.sequential, .additive}
  | arak => {.manner, .simultaneous, .additive}
  | inca | ali => {.sequential}
  | ken => {.simultaneous}
  | madan | casina => {.manner}
  | dikca => ∅

/-- The last slot of the finite verb whose exponent may precede the converb, which is the
negative for the converbs on the stem, a position-3 marker for *-(y)ken* and *-cAsInA*, and
the possibility suffix for *-mAdAn*, which contains the negative itself. -/
def follows : Converb → Verb.Slot
  | ip | arak | inca | ali | dikca => .negation
  | ken | casina => .tam
  | madan => .possibility

/-- An exponent of the slot may precede the converb. -/
def Admits (c : Converb) (s : Verb.Slot) : Prop :=
  c.follows = s ∨ Verb.system.Precedes Verb.system.template.suffixSlots s c.follows

instance (c : Converb) (s : Verb.Slot) : Decidable (c.Admits s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The converb is inherently negative. -/
def InherentlyNegative (c : Converb) : Prop := c = madan

instance : DecidablePred InherentlyNegative := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The converb can be negated, being negative itself or admitting the negative before it. -/
def Negatable (c : Converb) : Prop := c.InherentlyNegative ∨ c.Admits .negation

instance : DecidablePred Negatable := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A tense, aspect or modality marker may precede the converb. -/
def Tensed (c : Converb) : Prop := c.Admits .tam

instance : DecidablePred Tensed := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The converb may carry a person marker, the third-person plural on *-(y)ken* and a person
marker on *-mIşçAsInA*. -/
def PersonMarked (c : Converb) : Prop := c = ken ∨ c = casina

instance : DecidablePred PersonMarked := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The verb form of a converb. -/
def verbForm (_ : Converb) : UD.VerbForm := .Conv

/-- The converbs as medial forms, neutral to switch-reference, encoding their relations, and
indexing the subject where they may carry a person marker. -/
instance : Clause.Chaining.MedialForm Converb where
  sr _ := none
  relations := relations
  IndexesSubject := PersonMarked

end Converb

/-- *-(A/I)r … -mAz* 'as soon as', the positive and negative aorist on a doubled verb. -/
def arMaz : List (List Morph) := [[.suff "(A/I)r"], Negation.mA.morphs ++ [.suff "z"]]

/-- *-(y)A … -(y)A*, emphatic continuous manner on a doubled verb. -/
def aA : List (List Morph) := [[.suff "(y)A"], [.suff "(y)A"]]

end Turkish
