import Linglib.Morphology.Morphotactics.Template
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Fragments.Turkish.Phonology

/-!
# Turkish morphotactics

This file defines the inflectional suffixes of the Turkish finite verb and nominal and the
order in which they appear, following the reference grammar of Göksel and Kerslake.

Turkish is suffixing. Derivational suffixes precede inflectional ones, and clitics follow both
(§6.3). The inflectional suffixes of a finite verb appear in the order root, voice, negation,
tense/aspect/modality, copular marker, person marker, -DIr (§8.2). The tense/aspect/modality
markers themselves fall into five positions (§8.2.3): the possibility suffix -(y)A (1), which
precedes the negative (§8.2.3.1), the bound auxiliaries (2), the markers of tense, aspect and
modality proper (3), the copular markers (4) and -DIr (5). Markers of one position cannot
co-occur, and every finite verb but the imperative and the third-person optative carries one
of position 3. The voice slot alone admits a sequence of suffixes, up to four (§8.2 (7),
§8.2.1.1). The inflectional suffixes of a nominal appear in the order number, possession, case
(§8.1).

The finite verb and the nominal are each a `Morphology.PositionClassSystem`, which consists of
a slot inventory, its template, and the exponents of each slot. The person markers (§8.4) and
the possessives (§8.1.2) are `Agreement.Paradigm`s.

## Main definitions

* `Turkish.Verb.Slot`, `Turkish.Verb.Exponent`, `Turkish.Verb.system`: the slots, exponents
  and position-class system of the finite verb.
* `Turkish.Nominal.Slot`, `Turkish.Nominal.Exponent`, `Turkish.Nominal.system`: the same for
  the nominal.
* `Exponent.form`: the form of an exponent after a consonant-final stem, as segments.

## Implementation notes

The clitics mI and dA, which can interrupt the inflectional string (§6.3 (5)), are Chapter 11
material outside both systems. The markers' meanings are the matter of Chapter 21 and
Appendix 2. There -DI marks past tense, perfective aspect and direct knowledge, -mIş marks
relative past tense, perfective aspect and indirect knowledge (evidential modality, §21.4.3),
and the copular -(y)mIş marks evidential modality alone; -mIş followed by a copular marker or
-DIr is perfective only (§8.2.3.3). Negation of the aorist is irregular, -mAz for -(A/I)r
(§8.2.2; see `Turkish.Negation`). The grammar's examples are checked against both systems in
`Studies/GokselKerslake2005.lean`.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

open Phonology

namespace Turkish

open Turkish.Phonology

/-! ### The finite verb -/

namespace Verb

/-- The suffix slots of a finite verb (§8.2, §8.2.3). -/
inductive Slot where
  /-- Causative, passive, reflexive and reciprocal (§8.2.1). -/
  | voice
  /-- The possibility suffix -(y)A of negative forms, position 1 (§8.2.3.1). -/
  | possibility
  /-- -mA (§8.2.2). -/
  | negation
  /-- The bound auxiliaries -(y)Abil, -(y)Iver, -(y)Agel, -(y)Ayaz, -(y)Akal and
  -(y)Adur, position 2 (§8.2.3.2). -/
  | auxiliary
  /-- The position 3 markers -DI, -mIş, -sA, the aorist, -(y)AcAK, -(I)yor, -mAlI, -mAktA and
  the optative -(y)A (§8.2.3.3). -/
  | tam
  /-- The copular markers -(y)DI, -(y)mIş and -(y)sA, position 4 (§8.3.2). -/
  | copula
  /-- Person markers (§8.4). -/
  | person
  /-- The generalizing-modality marker -DIr, position 5 (§8.3.3). -/
  | generalizing
  deriving DecidableEq, Repr

/-- A person-marker group of §8.4. Group 1 follows -DI, -sA and the copular markers -(y)DI and
-(y)sA, and group 2 follows the other position-3 markers, the copular -(y)mIş and nominal
predicates. The optative and imperative groups 3 and 4 are not represented. -/
inductive PersonGroup where
  | one
  | two
  deriving DecidableEq, Repr

/-- The person markers of group 1 (§8.4); the second-person plural is also the formal
singular, and the third-person singular is zero. -/
def PersonGroup.one.paradigm : Agreement.Paradigm (List Segment) :=
  [(.pn .first .singular, [m]), (.pn .second .singular, [n]), (.pn .third .singular, []),
   (.pn .first .plural, [k]), (.pn .second .plural, [n, I, z]), (.pn .third .plural, [l, A, r])]

/-- The person markers of group 2 (§8.4). -/
def PersonGroup.two.paradigm : Agreement.Paradigm (List Segment) :=
  [(.pn .first .singular, [I, m]), (.pn .second .singular, [s, I, n]), (.pn .third .singular, []),
   (.pn .first .plural, [I, z]), (.pn .second .plural, [s, I, n, I, z]),
   (.pn .third .plural, [l, A, r])]

/-- The paradigm of a person-marker group. -/
def PersonGroup.paradigm : PersonGroup → Agreement.Paradigm (List Segment)
  | .one => PersonGroup.one.paradigm
  | .two => PersonGroup.two.paradigm

/-- The exponents of each slot (§8.2.1 to §8.4). -/
inductive Exponent : Slot → Type where
  /-- -(I)ş (§8.2.1.4). -/
  | reciprocal : Exponent .voice
  /-- -(I)n (§8.2.1.3). -/
  | reflexive : Exponent .voice
  /-- -DIr, with the stem-conditioned allomorphs -t, -It, -Ir, -Ar and -Art (§8.2.1.1). -/
  | causative : Exponent .voice
  /-- -Il, with -In after `l` and -n after a vowel (§8.2.1.2). -/
  | passive : Exponent .voice
  /-- -(y)A, possibility; negative forms only (§8.2.3.1). -/
  | possibility : Exponent .possibility
  /-- -mA (§8.2.2). -/
  | negative : Exponent .negation
  /-- -(y)Abil, possibility (§8.2.3.2). -/
  | abil : Exponent .auxiliary
  /-- -(y)Iver, non-premeditative. -/
  | iver : Exponent .auxiliary
  | agel : Exponent .auxiliary
  | ayaz : Exponent .auxiliary
  | akal : Exponent .auxiliary
  | adur : Exponent .auxiliary
  /-- -DI, perfective (§8.2.3.3). -/
  | di : Exponent .tam
  /-- -mIş, perfective/evidential. -/
  | miş : Exponent .tam
  /-- -sA, conditional. -/
  | sa : Exponent .tam
  /-- -(A/I)r, negative -z. -/
  | aorist : Exponent .tam
  /-- -(y)AcAK, future. -/
  | acak : Exponent .tam
  /-- -(I)yor, imperfective. -/
  | iyor : Exponent .tam
  /-- -mAlI, obligative. -/
  | mali : Exponent .tam
  /-- -mAktA, imperfective. -/
  | makta : Exponent .tam
  /-- -(y)A, optative. -/
  | optative : Exponent .tam
  /-- -(y)DI, past copula (§8.3.2). -/
  | pastCopula : Exponent .copula
  /-- -(y)mIş, evidential copula. -/
  | evidentialCopula : Exponent .copula
  /-- -(y)sA, conditional copula. -/
  | conditionalCopula : Exponent .copula
  /-- A person marker, the cell of a group's paradigm (§8.4). -/
  | person (group : PersonGroup) (cell : Agreement.Bundle) : Exponent .person
  /-- -DIr, generalizing modality (§8.3.3). -/
  | dir : Exponent .generalizing
  deriving DecidableEq

variable {σ : Slot}

/-- The form of an exponent after a consonant-final stem. The deletable vowels and buffer `y`
of §6.1.3 are not represented, except that `Turkish.Phonology.surface` resolves the `I` of
-(I)yor after a vowel; nor are the stem-conditioned allomorphs of §8.2.1. A person cell outside
its group's paradigm has no form. -/
def Exponent.form : Exponent σ → List Segment
  | .reciprocal => [I, ş]
  | .reflexive => [I, n]
  | .causative => [D, I, r]
  | .passive => [I, l]
  | .possibility => [A]
  | .negative => [m, A]
  | .abil => [A, b, i, l]
  | .iver => [I, v, e, r]
  | .agel => [A, g, e, l]
  | .ayaz => [A, y, a, z]
  | .akal => [A, k, a, l]
  | .adur => [A, d, u, r]
  | .di => [D, I]
  | .miş => [m, I, ş]
  | .sa => [s, A]
  | .aorist => [I, r]
  | .acak => [A, c, A, K]
  | .iyor => [I, y, o, r]
  | .mali => [m, A, l, I]
  | .makta => [m, A, k, t, A]
  | .optative => [A]
  | .pastCopula => [D, I]
  | .evidentialCopula => [m, I, ş]
  | .conditionalCopula => [s, A]
  | .person g c => (g.paradigm.realize c).getD []
  | .dir => [D, I, r]

/-- The finite verb has its slots in the order of §8.2, and its voice slot is iterable. -/
def system : Morphology.PositionClassSystem where
  Slot := Slot
  template :=
    { suffixSlots :=
        [.voice, .possibility, .negation, .auxiliary, .tam, .copula, .person, .generalizing] }
  Exponent := Exponent
  Iterable := (· = .voice)

end Verb

/-! ### The nominal -/

namespace Nominal

/-- The inflectional suffix slots of a nominal (§8.1). -/
inductive Slot where
  | number
  | possession
  | case
  deriving DecidableEq, Repr

/-- The possessive suffixes (§8.1.2); the second-person plural is also the formal singular,
and the third-person forms lose their final `n` word-finally. -/
def possessives : Agreement.Paradigm (List Segment) :=
  [(.pn .first .singular, [I, m]), (.pn .second .singular, [I, n]), (.pn .third .singular, [I]),
   (.pn .first .plural, [I, m, I, z]), (.pn .second .plural, [I, n, I, z]),
   (.pn .third .plural, [l, A, r, I])]

/-- The exponents of each slot (§8.1.1 to §8.1.3). -/
inductive Exponent : Slot → Type where
  /-- -lAr (§8.1.1). -/
  | plural : Exponent .number
  /-- A possessive suffix: a cell of `possessives` (§8.1.2). -/
  | possessive (cell : Agreement.Bundle) : Exponent .possession
  /-- -(y)I. -/
  | accusative : Exponent .case
  /-- -(y)A. -/
  | dative : Exponent .case
  /-- -DA. -/
  | locative : Exponent .case
  /-- -DAn. -/
  | ablative : Exponent .case
  /-- -(n)In. -/
  | genitive : Exponent .case
  deriving DecidableEq

variable {σ : Slot}

/-- The form of an exponent after a consonant-final stem (§6.1.3 as for the verb). -/
def Exponent.form : Exponent σ → List Segment
  | .plural => [l, A, r]
  | .possessive c => (possessives.realize c).getD []
  | .accusative => [I]
  | .dative => [A]
  | .locative => [D, A]
  | .ablative => [D, A, n]
  | .genitive => [I, n]

/-- The nominal has the slots number, possession and case, in that order (§8.1). -/
def system : Morphology.PositionClassSystem where
  Slot := Slot
  template := { suffixSlots := [.number, .possession, .case] }
  Exponent := Exponent

end Nominal

end Turkish
