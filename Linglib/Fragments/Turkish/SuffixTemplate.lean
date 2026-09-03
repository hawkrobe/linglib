import Linglib.Morphology.Morphotactics.Template

/-!
# Turkish suffix templates

Turkish is suffixing: derivational suffixes precede inflectional ones and clitics
follow both ([goksel-kerslake-2005] §6.3). The inflectional suffixes of a finite verb
appear in the order root - voice - negation - tense/aspect/modality - copular marker -
person marker - -DIr (§8.2), the tense/aspect/modality markers themselves falling
into five positions of which the fourth is the copular markers and the fifth -DIr
(§8.2.3), the possibility suffix -(y)A of position 1 preceding the negative
(§8.2.3.1). The inflectional suffixes of a nominal appear in the order number -
possession - case (§8.1). Both are `Morphology.AffixTemplate`s: the voice slot is a
position class, filled by up to four stacked voice suffixes (§8.2 (7)), and the
clitics mI and dA, which can interrupt the inflectional string (§6.3 (5)), are
Chapter 11 material outside them. The grammar's examples are checked against the
templates in `Studies/GokselKerslake2005.lean`.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

namespace Turkish.SuffixTemplate

/-- The suffix slots of a finite verb (§8.2, §8.2.3). -/
inductive VerbSlot where
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

/-- The suffix slots of a nominal (§6.3, §8.1). -/
inductive NounSlot where
  | derivational
  | number
  | possession
  | case
  deriving DecidableEq, Repr

/-- The finite-verb template, stem-outward (§8.2). -/
def verbTemplate : Morphology.AffixTemplate VerbSlot where
  suffixSlots :=
    [.voice, .possibility, .negation, .auxiliary, .tam, .copula, .person, .generalizing]

/-- The nominal template, stem-outward (§8.1). -/
def nounTemplate : Morphology.AffixTemplate NounSlot where
  suffixSlots := [.derivational, .number, .possession, .case]

end Turkish.SuffixTemplate
