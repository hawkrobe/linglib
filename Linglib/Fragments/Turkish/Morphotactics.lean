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

Vowels do not occur next to each other in Turkish, and the grammar brackets in a suffix's
citation form the initial segment whose presence depends on the stem (§6.1.3). The vowel of
-(I)m is lost after a vowel, as in *araba-m*, and the consonant of -(y)A, -(n)In and -(s)I
appears only after one, as in *masa-ya*. Both cases are one rule: a bracketed segment appears
exactly when it differs from the last segment of the stem in being a vowel.

## Main definitions

* `Turkish.Verb.Slot`, `Turkish.Verb.Exponent`, `Turkish.Verb.system`: the slots, exponents
  and position-class system of the finite verb.
* `Turkish.Nominal.Slot`, `Turkish.Nominal.Exponent`, `Turkish.Nominal.system`: the same for
  the nominal.
* `Turkish.Suffix`, `Suffix.attach`: a suffix in citation form, with its bracketed initial
  segment, and its attachment to a stem.
* `Turkish.underlying`, `Turkish.realize`: the underlying and the surface form of a stem with
  a string of suffixes.
* `Exponent.form`: the citation form of an exponent.

## Main results

* `Suffix.attach_concat_alternates`: a bracketed suffix attaches with vowels and consonants
  alternating across the juncture.

## Implementation notes

The clitics mI and dA, which can interrupt the inflectional string (§6.3 (5)), are Chapter 11
material outside both systems. The markers' meanings are the matter of Chapter 21 and
Appendix 2. There -DI marks past tense, perfective aspect and direct knowledge, -mIş marks
relative past tense, perfective aspect and indirect knowledge (evidential modality, §21.4.3),
and the copular -(y)mIş marks evidential modality alone; -mIş followed by a copular marker or
-DIr is perfective only (§8.2.3.3). The final `n` that the third-person possessives take
before a case suffix (§8.1.2) is not represented. Negation of the aorist is irregular, -mAz for -(A/I)r
(§8.2.2; see `Turkish.Negation`). The grammar's examples are checked against both systems in
`Studies/GokselKerslake2005.lean`.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

open Phonology

namespace Turkish

open Turkish.Phonology

/-! ### Suffixes and their attachment -/

/-- A suffix in citation form consists of the segments that always appear, preceded by a
bracketed initial segment if it has one, as the `y` of -(y)A and the `I` of -(I)m (§6.1.3). -/
structure Suffix where
  /-- The bracketed initial segment. -/
  bracketed : Option Segment := none
  /-- The segments that always appear. -/
  segments : List Segment
  deriving DecidableEq

namespace Suffix

/-- `s.initial w` is what the bracketed segment of `s` contributes after the stem `w`. The
segment appears exactly when it keeps vowels and consonants apart, a vowel after a consonant
and a consonant after a vowel (§6.1.3). -/
def initial (s : Suffix) (w : List Segment) : List Segment :=
  (s.bracketed.filter fun b ↦ decide (∀ l ∈ w.getLast?, ¬ (b.IsVowel ↔ l.IsVowel))).toList

/-- `s.attach w` is the stem `w` with the suffix `s` attached. -/
def attach (w : List Segment) (s : Suffix) : List Segment := w ++ s.initial w ++ s.segments

@[simp] theorem initial_of_bracketed_eq_none {s : Suffix} (h : s.bracketed = none)
    (w : List Segment) : s.initial w = [] := by
  simp [initial, h]

theorem initial_concat {s : Suffix} {b : Segment} (h : s.bracketed = some b)
    (w : List Segment) (l : Segment) :
    s.initial (w ++ [l]) = if (b.IsVowel ↔ l.IsVowel) then [] else [b] := by
  by_cases hb : (b.IsVowel ↔ l.IsVowel) <;> simp [initial, h, hb]

/-- A suffix whose bracketed segment differs from its first fixed segment in being a vowel, as
every bracketed suffix of the grammar does, attaches with vowels and consonants alternating
across the juncture: the segment after the stem-final `l` differs from `l` in being a vowel. -/
theorem attach_concat_alternates {s : Suffix} {b h : Segment} {t : List Segment}
    (hb : s.bracketed = some b) (hs : s.segments = h :: t) (hbh : ¬ (b.IsVowel ↔ h.IsVowel))
    (w : List Segment) (l : Segment) :
    ∃ x r, s.attach (w ++ [l]) = w ++ l :: x :: r ∧ ¬ (l.IsVowel ↔ x.IsVowel) := by
  by_cases hbl : (b.IsVowel ↔ l.IsVowel)
  · exact ⟨h, t, by simp [attach, initial_concat hb, hbl, hs], fun hlh ↦ hbh (hbl.trans hlh)⟩
  · exact ⟨b, h :: t, by simp [attach, initial_concat hb, hbl, hs], fun hlb ↦ hbl hlb.symm⟩

end Suffix

/-- `underlying w sfxs` is the underlying form of the stem `w` with the suffixes `sfxs`
attached in turn. -/
def underlying (w : List Segment) (sfxs : List Suffix) : List Segment :=
  sfxs.foldl Suffix.attach w

@[simp] theorem underlying_nil (w : List Segment) : underlying w [] = w := rfl

@[simp] theorem underlying_cons (w : List Segment) (s : Suffix) (sfxs : List Suffix) :
    underlying w (s :: sfxs) = underlying (s.attach w) sfxs := rfl

theorem underlying_append (w : List Segment) (sfxs sfxs' : List Suffix) :
    underlying w (sfxs ++ sfxs') = underlying (underlying w sfxs) sfxs' :=
  List.foldl_append

/-- `realize w sfxs` is the surface form of the stem `w` with the suffixes `sfxs`. -/
def realize (w : List Segment) (sfxs : List Suffix) : List Segment := surface (underlying w sfxs)

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

/-- The person markers of group 1 (§8.4). The second-person plural is also the formal
singular, and the third-person singular is zero. -/
def PersonGroup.one.paradigm : Agreement.Paradigm Suffix :=
  [(.pn .first .singular, ⟨none, [m]⟩), (.pn .second .singular, ⟨none, [n]⟩),
   (.pn .third .singular, ⟨none, []⟩), (.pn .first .plural, ⟨none, [k]⟩),
   (.pn .second .plural, ⟨none, [n, I, z]⟩), (.pn .third .plural, ⟨none, [l, A, r]⟩)]

/-- The person markers of group 2 (§8.4), whose first-person markers -(y)Im and -(y)Iz take
the buffer `y`. -/
def PersonGroup.two.paradigm : Agreement.Paradigm Suffix :=
  [(.pn .first .singular, ⟨some y, [I, m]⟩), (.pn .second .singular, ⟨none, [s, I, n]⟩),
   (.pn .third .singular, ⟨none, []⟩), (.pn .first .plural, ⟨some y, [I, z]⟩),
   (.pn .second .plural, ⟨none, [s, I, n, I, z]⟩), (.pn .third .plural, ⟨none, [l, A, r]⟩)]

/-- The paradigm of a person-marker group. -/
def PersonGroup.paradigm : PersonGroup → Agreement.Paradigm Suffix
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

/-- The citation form of an exponent. The stem-conditioned allomorphs of the causative and the
passive (§8.2.1) and the `A` of the aorist -(A/I)r are not represented, and a person cell
outside its group's paradigm has the empty form. -/
def Exponent.form : Exponent σ → Suffix
  | .reciprocal => ⟨some I, [ş]⟩
  | .reflexive => ⟨some I, [n]⟩
  | .causative => ⟨none, [D, I, r]⟩
  | .passive => ⟨none, [I, l]⟩
  | .possibility => ⟨some y, [A]⟩
  | .negative => ⟨none, [m, A]⟩
  | .abil => ⟨some y, [A, b, i, l]⟩
  | .iver => ⟨some y, [I, v, e, r]⟩
  | .agel => ⟨some y, [A, g, e, l]⟩
  | .ayaz => ⟨some y, [A, y, a, z]⟩
  | .akal => ⟨some y, [A, k, a, l]⟩
  | .adur => ⟨some y, [A, d, u, r]⟩
  | .di => ⟨none, [D, I]⟩
  | .miş => ⟨none, [m, I, ş]⟩
  | .sa => ⟨none, [s, A]⟩
  | .aorist => ⟨some I, [r]⟩
  | .acak => ⟨some y, [A, c, A, K]⟩
  | .iyor => ⟨some I, [y, o, r]⟩
  | .mali => ⟨none, [m, A, l, I]⟩
  | .makta => ⟨none, [m, A, k, t, A]⟩
  | .optative => ⟨some y, [A]⟩
  | .pastCopula => ⟨some y, [D, I]⟩
  | .evidentialCopula => ⟨some y, [m, I, ş]⟩
  | .conditionalCopula => ⟨some y, [s, A]⟩
  | .person g c => (g.paradigm.realize c).getD ⟨none, []⟩
  | .dir => ⟨none, [D, I, r]⟩

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

/-- The possessive suffixes (§8.1.2). The second-person plural is also the formal singular, and
the final `n` that the third-person forms take before a case suffix is not represented. -/
def possessives : Agreement.Paradigm Suffix :=
  [(.pn .first .singular, ⟨some I, [m]⟩), (.pn .second .singular, ⟨some I, [n]⟩),
   (.pn .third .singular, ⟨some s, [I]⟩), (.pn .first .plural, ⟨some I, [m, I, z]⟩),
   (.pn .second .plural, ⟨some I, [n, I, z]⟩), (.pn .third .plural, ⟨none, [l, A, r, I]⟩)]

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

/-- The citation form of an exponent. -/
def Exponent.form : Exponent σ → Suffix
  | .plural => ⟨none, [l, A, r]⟩
  | .possessive c => (possessives.realize c).getD ⟨none, []⟩
  | .accusative => ⟨some y, [I]⟩
  | .dative => ⟨some y, [A]⟩
  | .locative => ⟨none, [D, A]⟩
  | .ablative => ⟨none, [D, A, n]⟩
  | .genitive => ⟨some n, [I, n]⟩

/-- The nominal has the slots number, possession and case, in that order (§8.1). -/
def system : Morphology.PositionClassSystem where
  Slot := Slot
  template := { suffixSlots := [.number, .possession, .case] }
  Exponent := Exponent

end Nominal

end Turkish
