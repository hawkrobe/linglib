import Linglib.Morphology.Morphotactics.Template
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Fragments.Turkish.VowelHarmony

/-!
# Turkish morphotactics

Turkish is suffixing: derivational suffixes precede inflectional ones and clitics follow
both ([goksel-kerslake-2005] §6.3). The inflectional suffixes of a finite verb appear in
the order root - voice - negation - tense/aspect/modality - copular marker - person
marker - -DIr (§8.2), the tense/aspect/modality markers themselves falling into five
positions (§8.2.3): the possibility suffix -(y)A (1), which precedes the negative
(§8.2.3.1), the bound auxiliaries (2), the markers of tense, aspect and modality proper
(3), the copular markers (4) and -DIr (5). Markers of one position cannot co-occur, and
every finite verb but the imperative and the third-person optative carries one of
position 3; the voice slot alone admits a sequence of suffixes, up to four (§8.2 (7),
§8.2.1.1). The inflectional suffixes of a nominal appear in the order number -
possession - case (§8.1). The finite verb and the nominal are each a
`Morphology.PositionClassSystem`: a slot inventory, its template, and the exponents of
each slot, with the person markers (§8.4) and the possessives (§8.1.2) as
`Agreement.Paradigm`s. The clitics mI and dA, which can interrupt the inflectional string
(§6.3 (5)), are Chapter 11 material outside both systems. The markers' meanings are the
matter of Chapter 21 and Appendix 2: -DI marks past tense, perfective aspect and direct
knowledge, -mIş relative past tense, perfective aspect and indirect knowledge (evidential
modality, §21.4.3), the copular -(y)mIş evidential modality alone; -mIş followed by a
copular marker or -DIr is perfective only (§8.2.3.3). Negation of the aorist is
irregular, -mAz for -(A/I)r (§8.2.2; see `Turkish.Negation`). The grammar's examples are
checked against both systems in `Studies/GokselKerslake2005.lean`.

## Main definitions

* `Turkish.Verb.Slot`, `Turkish.Verb.Exponent`, `Turkish.Verb.system` — the finite verb.
* `Turkish.Nominal.Slot`, `Turkish.Nominal.Exponent`, `Turkish.Nominal.system` — the nominal.
* `Exponent.form` — each exponent's form after a consonant-final stem, as segments.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

open Phonology (Segment)

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
  /-- Position 3: -DI, -mIş, -sA, the aorist, -(y)AcAK, -(I)yor, -mAlI, -mAktA and the
  optative -(y)A (§8.2.3.3). -/
  | tam
  /-- The copular markers -(y)DI, -(y)mIş and -(y)sA, position 4 (§8.3.2). -/
  | copula
  /-- Person markers (§8.4). -/
  | person
  /-- The generalizing-modality marker -DIr, position 5 (§8.3.3). -/
  | generalizing
  deriving DecidableEq, Repr

/-- The person-marker groups of §8.4: group 1 after -DI, -sA and the copular markers -(y)DI
and -(y)sA; group 2 after the other position-3 markers, the copular -(y)mIş and nominal
predicates. The optative and imperative groups 3 and 4 are not represented. -/
inductive PersonGroup where
  | one
  | two
  deriving DecidableEq, Repr

/-- The person markers of group 1 (§8.4); the second-person plural is also the formal
singular, and the third-person singular is zero. -/
def PersonGroup.one.paradigm : Agreement.Paradigm (List Segment) :=
  [(.pn .first .Sing, [m]), (.pn .second .Sing, [n]), (.pn .third .Sing, []),
   (.pn .first .Plur, [k]), (.pn .second .Plur, [n, I, z]), (.pn .third .Plur, [l, A, r])]

/-- The person markers of group 2 (§8.4). -/
def PersonGroup.two.paradigm : Agreement.Paradigm (List Segment) :=
  [(.pn .first .Sing, [I, m]), (.pn .second .Sing, [s, I, n]), (.pn .third .Sing, []),
   (.pn .first .Plur, [I, z]), (.pn .second .Plur, [s, I, n, I, z]),
   (.pn .third .Plur, [l, A, r])]

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
  /-- A person marker: the cell of a group's paradigm (§8.4). -/
  | person (group : PersonGroup) (cell : Agreement.Cell) : Exponent .person
  /-- -DIr, generalizing modality (§8.3.3). -/
  | dir : Exponent .generalizing
  deriving DecidableEq

variable {σ : Slot}

/-- The form of an exponent after a consonant-final stem; the deletable vowels and buffer
`y` of §6.1.3 and the stem-conditioned allomorphs of §8.2.1 are not represented, and a
person cell outside its group's paradigm has no form. -/
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

/-- The finite verb: its slots in the order of §8.2, the voice slot iterable. -/
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
  [(.pn .first .Sing, [I, m]), (.pn .second .Sing, [I, n]), (.pn .third .Sing, [I]),
   (.pn .first .Plur, [I, m, I, z]), (.pn .second .Plur, [I, n, I, z]),
   (.pn .third .Plur, [l, A, r, I])]

/-- The exponents of each slot (§8.1.1 to §8.1.3). -/
inductive Exponent : Slot → Type where
  /-- -lAr (§8.1.1). -/
  | plural : Exponent .number
  /-- A possessive suffix: a cell of `possessives` (§8.1.2). -/
  | possessive (cell : Agreement.Cell) : Exponent .possession
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

/-- The nominal: number - possession - case (§8.1). -/
def system : Morphology.PositionClassSystem where
  Slot := Slot
  template := { suffixSlots := [.number, .possession, .case] }
  Exponent := Exponent

end Nominal

end Turkish
