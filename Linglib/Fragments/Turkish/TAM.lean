import Linglib.Fragments.Turkish.SuffixTemplate

/-!
# Turkish tense, aspect and modality markers

The tense/aspect/modality markers of a finite verb occupy five positions
([goksel-kerslake-2005] §8.2.3): the possibility suffix -(y)A (1), the bound
auxiliaries (2), the markers of tense, aspect and modality proper (3), the copular
markers (4) and -DIr (5). Markers of one position cannot co-occur, and every finite
verb but the imperative and the third-person optative carries one of position 3. Their
meanings are the matter of Chapter 21 and Appendix 2: -DI marks past tense, perfective
aspect and direct knowledge, -mIş relative past tense, perfective aspect and indirect
knowledge (evidential modality, §21.4.3), the copular -(y)mIş evidential modality
alone; -mIş followed by a copular marker or -DIr is perfective only (§8.2.3.3).
Negation of the aorist is irregular, -mAz for -(A/I)r (§8.2.2; see
`Turkish.Negation`).

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

namespace Turkish.TAM

open Turkish.SuffixTemplate (VerbSlot)

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

end Turkish.TAM
