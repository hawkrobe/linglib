import Linglib.Fragments.Basque.Pronouns
import Linglib.Morphology.Morph
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Syntax.Category.Verb.Tense

/-!
# Basque verbal agreement

The finite verb of Basque, in most clauses an auxiliary, agrees with the absolutive, the dative
and the ergative phrase of its clause. Each case has its own marker and its own place: the
absolutive marker stands before the root, the dative marker after it, and the ergative marker
after that, as in *d-i-da-zu* 'you have (sold) it to me'. The dative and ergative markers are
the same for the first and second persons and differ in the third, where the dative has *-o* and
*-e* and the ergative has nothing in the singular and *-te* in the plural. The familiar second
person *hi* is the one place where the verb marks gender, *-k* for a man and *-n* for a woman.

The absolutive slot treats the third person differently from the others. The first and second
persons have the prefixes *n-*, *h-*, *g-* and *z-* in every tense. A third person absolutive
has no prefix of its own: the slot holds *d-* in the present and *z-* in the past, whatever the
number, and the number of the absolutive phrase shows only in a separate plural marker. In a
past-tense transitive verb with a third person absolutive the slot is taken over by the ergative
phrase, which then has no suffix, so that *n-u-en* 'I had it' begins like *n-ind-u-zu-n* 'you
had me'. This is the pattern known as ergative displacement.

The pronoun *zu*, once a plural and now the ordinary way of addressing one person, still agrees
as a plural, and the newer plural *zuek* adds a further plural marker to the forms of *zu*.

## Main declarations

* `Basque.absolutive`, `Basque.dative`, `Basque.ergative`: the marker of each slot for each
  person and number, in the present tense.
* `Basque.thirdAbsolutive`: what fills the absolutive slot by tense when the absolutive phrase
  is third person.
* `Basque.displacedErgative`: the ergative markers of a past-tense verb with a third person
  absolutive.
* `Basque.HasPersonPrefix`: the absolutive slot has a prefix for the person and number.

## Main results

* `Basque.hasPersonPrefix_iff_isSAP`: the absolutive prefixes are those of the first and second
  persons.
* `Basque.dative_eq_ergative`: the dative and ergative markers of the first and second persons
  coincide.
* `Basque.displacedErgative_head`: a displaced ergative begins with what would fill the
  absolutive slot for its own person and number in the past.
* `Basque.allocutive_eq_ergative`: the familiar allocutive suffixes are the ergative suffixes of
  *hi*.

## Implementation notes

The cells are the bundles of `Syntax/Agreement/Bundle.lean`, so that a pronoun's features index
a table directly. The second person plural cell is that of *zu*, following the forms rather than
the meaning, and *zuek* has no cell of its own. The two cells of *hi* with a gender occur only in
the dative and ergative tables. The first and second person singular suffixes are given as they
stand at the end of the word; before another suffix they are *-da-*, *-a-* and *-na-*. Forms
with modal markers, where the third person filler is *l-*, are not covered.

## References

* [laka-1996]
-/

namespace Basque

open Agreement Morphology

/-- The cell of the familiar second person *hi* addressed to a person of the given gender. -/
def familiar (g : Gender) : Bundle := Function.update (Bundle.pn .second .singular) .gender ↑g

/-! ### The three slots -/

/-- The absolutive prefixes. Only the first and second persons have one. -/
def absolutive : Paradigm (List Morph) :=
  [(.pn .first .singular, [.pref "n"]), (.pn .second .singular, [.pref "h"]),
   (.pn .first .plural, [.pref "g"]), (.pn .second .plural, [.pref "z"])]

/-- The suffixes of the first and second persons, which the dative and ergative slots share. -/
private def participantSuffixes : Paradigm (List Morph) :=
  [(.pn .first .singular, [.suff "t"]), (familiar .masculine, [.suff "k"]),
   (familiar .feminine, [.suff "n"]), (.pn .first .plural, [.suff "gu"]),
   (.pn .second .plural, [.suff "zu"])]

/-- The dative suffixes. -/
def dative : Paradigm (List Morph) :=
  participantSuffixes ++ [(.pn .third .singular, [.suff "o"]), (.pn .third .plural, [.suff "e"])]

/-- The ergative suffixes. The third person singular has none. -/
def ergative : Paradigm (List Morph) :=
  participantSuffixes ++ [(.pn .third .singular, []), (.pn .third .plural, [.suff "te"])]

/-- The element in the absolutive slot when the absolutive phrase is third person, *d-* in the
present and *z-* in the past. Basque has no future inflection. -/
def thirdAbsolutive : Tense → Option Morph
  | .present => some (.pref "d")
  | .past => some (.pref "z")
  | .future => none

/-- The ergative markers of a past-tense verb whose absolutive phrase is third person. They
stand in the absolutive slot, and the third person plural keeps its suffix. -/
def displacedErgative : Paradigm (List Morph) :=
  [(.pn .first .singular, [.pref "n"]), (.pn .second .singular, [.pref "h"]),
   (.pn .third .singular, [.pref "z"]), (.pn .first .plural, [.pref "g", .pref "en"]),
   (.pn .second .plural, [.pref "z", .pref "en"]), (.pn .third .plural, [.pref "z", .suff "te"])]

/-! ### Person in the absolutive slot -/

/-- The absolutive slot has a prefix for the cell. -/
def HasPersonPrefix (c : Bundle) : Prop := (absolutive.realize c).isSome

instance : DecidablePred HasPersonPrefix := fun _ ↦ inferInstanceAs (Decidable (_ = true))

/-- The absolutive prefixes are those of the first and second persons. -/
theorem hasPersonPrefix_iff_isSAP : ∀ c ∈ Bundle.pnCells, HasPersonPrefix c ↔ c.IsSAP := by
  decide

/-- Every personal pronoun but the third person ones has an absolutive prefix. -/
theorem hasPersonPrefix_phi_iff : ∀ p ∈ Pronouns.pronouns,
    HasPersonPrefix (HasPhi.phi p) ↔ p.person ≠ some .third := by
  decide

/-- The dative and ergative markers of the first and second persons coincide. -/
theorem dative_eq_ergative {c : Bundle} (h : c.IsSAP) : dative.realize c = ergative.realize c := by
  have h3 (n : Number) : Bundle.pn .third n ≠ c := by
    rintro rfl
    simp [Bundle.IsSAP] at h
  simp [dative, ergative, Paradigm.realize, List.find?_append, h3]

/-- A displaced ergative begins with what would fill the absolutive slot for its own person and
number in the past: the absolutive prefix of a first or second person, the past filler of a
third. -/
theorem displacedErgative_head : ∀ c ∈ Bundle.pnCells,
    (displacedErgative.realize c).bind (·.head?) =
      ((absolutive.realize c).bind (·.head?)).or (thirdAbsolutive .past) := by
  decide

/-- The allocutive suffixes that mark the gender of an addressee who is no argument of the verb
are the ergative suffixes of *hi*. -/
theorem allocutive_eq_ergative : ∀ m ∈ Pronouns.allocutiveMarkers, ∀ g ∈ m.gender,
    (ergative.realize (familiar g)).map Morph.surface = some m.form := by
  decide +kernel

end Basque
