import Linglib.Morphology.Morphotactics.Template

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
position 3. The inflectional suffixes of a nominal appear in the order number -
possession - case (§8.1). Both templates are `Morphology.AffixTemplate`s: the voice slot
is a position class, filled by up to four stacked voice suffixes (§8.2 (7)), and the
clitics mI and dA, which can interrupt the inflectional string (§6.3 (5)), are Chapter 11
material outside them. The markers' meanings are the matter of Chapter 21 and Appendix 2:
-DI marks past tense, perfective aspect and direct knowledge, -mIş relative past tense,
perfective aspect and indirect knowledge (evidential modality, §21.4.3), the copular
-(y)mIş evidential modality alone; -mIş followed by a copular marker or -DIr is
perfective only (§8.2.3.3). Negation of the aorist is irregular, -mAz for -(A/I)r
(§8.2.2; see `Turkish.Negation`). The grammar's examples are checked against the
templates in `Studies/GokselKerslake2005.lean`.

## Main definitions

* `VerbSlot`, `NounSlot`, `verbTemplate`, `nounTemplate` — the slot inventories and templates.
* `Marker`, `Marker.slot` — the tense/aspect/modality markers by position.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

namespace Turkish.Morphotactics

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

/-- The tense/aspect/modality markers of §8.2.3, by position. -/
inductive Marker where
  /-- -(y)A, possibility; position 1, negative forms only. -/
  | possibility
  /-- -(y)Abil, possibility; position 2. -/
  | abil
  /-- -(y)Iver, non-premeditative. -/
  | iver
  | agel
  | ayaz
  | akal
  | adur
  /-- -DI, perfective; position 3. -/
  | di
  /-- -mIş, perfective/evidential. -/
  | miş
  /-- -sA, conditional. -/
  | sa
  /-- -(A/I)r, negative -z. -/
  | aorist
  /-- -(y)AcAK, future. -/
  | acak
  /-- -(I)yor, imperfective. -/
  | iyor
  /-- -mAlI, obligative. -/
  | mali
  /-- -mAktA, imperfective. -/
  | makta
  /-- -(y)A, optative. -/
  | optative
  /-- -(y)DI, past copula; position 4. -/
  | pastCopula
  /-- -(y)mIş, evidential copula. -/
  | evidentialCopula
  /-- -(y)sA, conditional copula. -/
  | conditionalCopula
  /-- -DIr, generalizing modality; position 5. -/
  | dir
  deriving DecidableEq, Repr

/-- The template slot of a marker: positions 1 to 5 are the slots `possibility`,
`auxiliary`, `tam`, `copula` and `generalizing`. -/
def Marker.slot : Marker → VerbSlot
  | .possibility => .possibility
  | .abil | .iver | .agel | .ayaz | .akal | .adur => .auxiliary
  | .di | .miş | .sa | .aorist | .acak | .iyor | .mali | .makta | .optative => .tam
  | .pastCopula | .evidentialCopula | .conditionalCopula => .copula
  | .dir => .generalizing

end Turkish.Morphotactics
