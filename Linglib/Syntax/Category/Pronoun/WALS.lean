import Linglib.Data.WALS.Features.F35A
import Linglib.Data.WALS.Features.F39A
import Linglib.Data.WALS.Features.F39B
import Linglib.Data.WALS.Features.F40A
import Linglib.Data.WALS.Features.F44A
import Linglib.Data.WALS.Features.F45A
import Linglib.Data.WALS.Features.F46A
import Linglib.Data.WALS.Features.F47A
import Linglib.Data.WALS.Features.F48A
import Linglib.Data.WALS.Features.F136A
import Linglib.Data.WALS.Features.F136B
import Linglib.Data.WALS.Features.F137A
import Linglib.Data.WALS.Features.F137B
import Linglib.Features.Clusivity

/-!
# Pronoun — typological survey (WALS)
[wals-2013] [nichols-peterson-2013]

The cross-linguistic WALS-survey facet of the pronoun object: the friendly
feature enums (Chs 39–48) and phonological-shape enums (Chs 136–137), their
`fromWALS*` converters, the iso-keyed accessors that read a language's value
from the `Data.WALS` layer, and the distribution theorems.

A language's WALS pronoun fact is a *function of its ISO code*
(`Pronoun.genderDistinction "kor"`), derived from `Data.WALS` — there is no
per-language `Profile` bundle (that was write-only and is gone). When a study
needs to ground a Fragment analysis against WALS, it states a `decide`-checked
theorem over the accessor in that study file.

## Main declarations

* `Pronoun.genderDistinction`, `politeness`, `inclusiveExclusive`, … —
  iso-keyed accessors for the WALS Chs 39–48 feature-system survey, derived
  from `Data.WALS` via the `fromWALS*` converters.
* `Pronoun.mtPattern`, `mIn1sg`, `nmPattern`, `mIn2sg` — iso-keyed accessors
  for the M-T / N-M phonological-shape survey, WALS Chs 136–137
  ([nichols-peterson-2013]).
* `Pronoun.Plurality` — how independent personal pronouns encode number,
  WALS Ch 35. The canonical home for this pronoun-paradigm feature.
-/

set_option autoImplicit false

namespace Pronoun

/-- WALS Ch 39: inclusive/exclusive distinction in independent pronouns. -/
inductive InclusiveExclusive where
  /-- No first-person plural pronoun at all. -/
  | noWe
  /-- 'We' = 'I' (no number distinction in 1st person). -/
  | weEqualsI
  /-- 1st-pl exists but no incl/excl distinction. -/
  | noDistinction
  /-- Only inclusive form; no dedicated exclusive pronoun. -/
  | onlyInclusive
  /-- Full inclusive/exclusive distinction in 1st-pl. -/
  | inclusiveExclusive
  deriving DecidableEq, Repr

/-- WALS Ch 39B: incl/excl forms in Pama-Nyungan languages
    (areal sub-feature). -/
inductive InclusiveExclusivePamaNyungan where
  /-- No incl/excl opposition in 1st-pl. -/
  | noOpposition
  /-- Inclusive and exclusive forms differentiated. -/
  | differentiated
  deriving DecidableEq, Repr

/-- WALS Ch 40: incl/excl distinction in verbal inflection. -/
inductive InclusiveExclusiveVerbal where
  /-- No person marking on verbs at all. -/
  | noPersonMarking
  /-- 'We' verbal form = 'I' form. -/
  | weEqualsI
  /-- Person marking exists but no incl/excl. -/
  | noDistinction
  /-- Only inclusive marking in verbal inflection. -/
  | onlyInclusive
  /-- Full incl/excl distinction in verbal inflection. -/
  | inclusiveExclusive
  deriving DecidableEq, Repr

/-- WALS Ch 44: where gender distinctions appear in the pronoun paradigm. -/
inductive GenderDistinction where
  /-- Gender in 3rd person AND in 1st/2nd person (e.g., Arabic, Hebrew). -/
  | in3rdAndOtherPersons
  /-- Gender in 3rd person only, including non-singular forms
      (e.g., Polish, Albanian). -/
  | in3rdPersonIncludingNonSg
  /-- Gender in 3rd person singular only (e.g., English he/she/it). -/
  | in3rdPersonSgOnly
  /-- Gender in 1st or 2nd person but not 3rd (rare; e.g., Iraqw). -/
  | in1stOr2ndOnly
  /-- Gender in 3rd person non-singular only (extremely rare). -/
  | in3rdPersonNonSgOnly
  /-- No gender distinctions in pronouns (e.g., Finnish, Turkish, Japanese). -/
  | noGenderDistinctions
  deriving DecidableEq, Repr

/-- WALS Ch 45: politeness (honorific/formality) distinctions in pronouns. -/
inductive PolitenessDistinction where
  /-- No politeness distinction (e.g., English). -/
  | none
  /-- Binary T/V distinction (e.g., French tu/vous, German du/Sie). -/
  | binary
  /-- Multiple levels (e.g., Japanese, Hindi, Tagalog). -/
  | multiple
  /-- Pronouns avoided entirely for politeness; titles/kin terms used
      instead (e.g., Korean, Thai). -/
  | pronounsAvoided
  deriving DecidableEq, Repr

/-- WALS Ch 46: morphological source of indefinite pronouns. -/
inductive IndefiniteType where
  /-- Based on interrogative forms (e.g., Japanese dare-ka 'who-Q' = 'someone'). -/
  | interrogativeBased
  /-- Based on generic nouns (e.g., English 'somebody' = 'some' + 'body'). -/
  | genericNounBased
  /-- Special, dedicated forms unrelated to interrogatives or generic nouns. -/
  | special
  /-- Mixed: some interrogative-based, others generic-noun-based. -/
  | mixed
  /-- Existential construction used instead of indefinite pronouns. -/
  | existentialConstruction
  deriving DecidableEq, Repr

/-- WALS Ch 47: relationship between intensifiers and reflexives. -/
inductive IntensifierReflexive where
  /-- Identical forms ('she herself did it' / 'she saw herself'). -/
  | identical
  /-- Different, morphologically unrelated forms. -/
  | differentiated
  deriving DecidableEq, Repr

/-- WALS Ch 48: whether adpositions bear person-marking morphology. -/
inductive PersonMarkingOnAdpositions where
  /-- Language has no adpositions (head-marking or caseless). -/
  | noAdpositions
  /-- Adpositions exist but bear no person marking. -/
  | noPersonMarking
  /-- Only pronominal complements trigger person marking
      (e.g., Hebrew be-xa 'in-you'). -/
  | pronounsOnly
  /-- Both pronominal and nominal complements trigger person marking. -/
  | pronounsAndNouns
  deriving DecidableEq, Repr

end Pronoun

/-! ### WALS converters (Chs 39, 39B, 40, 44–48) -/

namespace Pronoun

def fromWALS39A : Data.WALS.F39A.InclusiveExclusiveDistinctionInIndependentPronouns →
    InclusiveExclusive
  | .noWe => .noWe
  | .weTheSameAsI => .weEqualsI
  | .noInclusiveExclusive => .noDistinction
  | .onlyInclusive => .onlyInclusive
  | .inclusiveExclusive => .inclusiveExclusive

def fromWALS39B : Data.WALS.F39B.InclusiveExclusiveFormsInPamaNyungan →
    InclusiveExclusivePamaNyungan
  | .noInclusiveExclusiveOpposition => .noOpposition
  | .inclusiveAndExclusiveDifferentiated => .differentiated

def fromWALS40A : Data.WALS.F40A.InclusiveExclusiveDistinctionInVerbalInflection →
    InclusiveExclusiveVerbal
  | .noPersonMarking => .noPersonMarking
  | .weTheSameAsI => .weEqualsI
  | .noInclusiveExclusive => .noDistinction
  | .onlyInclusive => .onlyInclusive
  | .inclusiveExclusive => .inclusiveExclusive

def fromWALS44A : Data.WALS.F44A.GenderDistinctionsInIndependentPersonalPronouns →
    GenderDistinction
  | .in3rdPerson1stAndOr2ndPerson => .in3rdAndOtherPersons
  | .v3rdPersonOnlyButAlsoNonSingular => .in3rdPersonIncludingNonSg
  | .v3rdPersonSingularOnly => .in3rdPersonSgOnly
  | .v1stOr2ndPersonButNot3rd => .in1stOr2ndOnly
  | .v3rdPersonNonSingularOnly => .in3rdPersonNonSgOnly
  | .noGenderDistinctions => .noGenderDistinctions

def fromWALS45A : Data.WALS.F45A.PolitenessDistinctionsInPronouns →
    PolitenessDistinction
  | .noPolitenessDistinction => .none
  | .binaryPolitenessDistinction => .binary
  | .multiplePolitenessDistinctions => .multiple
  | .pronounsAvoidedForPoliteness => .pronounsAvoided

def fromWALS46A : Data.WALS.F46A.IndefinitePronouns → IndefiniteType
  | .interrogativeBased => .interrogativeBased
  | .genericNounBased => .genericNounBased
  | .special => .special
  | .mixed => .mixed
  | .existentialConstruction => .existentialConstruction

def fromWALS47A : Data.WALS.F47A.IntensifierReflexive → IntensifierReflexive
  | .identical => .identical
  | .differentiated => .differentiated

def fromWALS48A : Data.WALS.F48A.PersonMarkingOnAdpositions → PersonMarkingOnAdpositions
  | .noAdpositions => .noAdpositions
  | .noPersonMarking => .noPersonMarking
  | .pronounsOnly => .pronounsOnly
  | .pronounsAndNouns => .pronounsAndNouns

/-! ### Per-language WALS accessors (Chs 39–48)

Each pronoun-system feature is a function of a language's ISO 639-3 code, derived
from the `Data.WALS` layer through the `fromWALS*` converters — no per-language
stipulation, replacing the former hand-stipulated `Profile` bundle. A fragment
attaches a feature as a `Lang.pronoun…` one-liner over its `iso`; `none` means
WALS did not sample that language for that chapter. -/

/-- WALS Ch 39: incl/excl distinction in independent pronouns. -/
def inclusiveExclusive (iso : String) : Option InclusiveExclusive :=
  (Data.WALS.F39A.lookupISO iso).map (fromWALS39A ·.value)

/-- WALS Ch 40: incl/excl distinction in verbal inflection. -/
def inclusiveExclusiveVerbal (iso : String) : Option InclusiveExclusiveVerbal :=
  (Data.WALS.F40A.lookupISO iso).map (fromWALS40A ·.value)

/-- WALS Ch 44: gender distinctions in the pronoun paradigm. -/
def genderDistinction (iso : String) : Option GenderDistinction :=
  (Data.WALS.F44A.lookupISO iso).map (fromWALS44A ·.value)

/-- WALS Ch 45: politeness distinctions in pronouns. -/
def politeness (iso : String) : Option PolitenessDistinction :=
  (Data.WALS.F45A.lookupISO iso).map (fromWALS45A ·.value)

/-- WALS Ch 46: indefinite-pronoun strategy. -/
def indefiniteType (iso : String) : Option IndefiniteType :=
  (Data.WALS.F46A.lookupISO iso).map (fromWALS46A ·.value)

/-- WALS Ch 47: intensifier–reflexive relationship. -/
def intensifierReflexive (iso : String) : Option IntensifierReflexive :=
  (Data.WALS.F47A.lookupISO iso).map (fromWALS47A ·.value)

/-- WALS Ch 48: person marking on adpositions. -/
def personMarkingAdpositions (iso : String) : Option PersonMarkingOnAdpositions :=
  (Data.WALS.F48A.lookupISO iso).map (fromWALS48A ·.value)

/-! ### Distribution theorems -/

private abbrev ch39 := Data.WALS.F39A.allData
private abbrev ch39b := Data.WALS.F39B.allData
private abbrev ch40 := Data.WALS.F40A.allData
private abbrev ch44 := Data.WALS.F44A.allData
private abbrev ch45 := Data.WALS.F45A.allData
private abbrev ch46 := Data.WALS.F46A.allData
private abbrev ch47 := Data.WALS.F47A.allData
private abbrev ch48 := Data.WALS.F48A.allData

set_option maxRecDepth 8192 in
/-- Majority of languages (120/200) make no inclusive/exclusive
    distinction in independent pronouns. -/
theorem noDistinction_is_majority_ch39 :
    (ch39.filter (·.value == .noInclusiveExclusive)).length >
    (ch39.filter (·.value == .inclusiveExclusive)).length := by decide

set_option maxRecDepth 8192 in
/-- No gender distinctions in pronouns is the majority pattern (254/378 = 67.2%). -/
theorem noGender_is_majority_ch44 :
    (ch44.filter (·.value == .noGenderDistinctions)).length >
    (ch44.filter (·.value == .v3rdPersonSingularOnly)).length +
    (ch44.filter (·.value == .v3rdPersonOnlyButAlsoNonSingular)).length +
    (ch44.filter (·.value == .in3rdPerson1stAndOr2ndPerson)).length := by decide

set_option maxRecDepth 8192 in
/-- Most languages lack politeness distinctions in pronouns (136/207 = 65.7%). -/
theorem noPoliteness_is_majority_ch45 :
    (ch45.filter (·.value == .noPolitenessDistinction)).length >
    (ch45.filter (·.value == .binaryPolitenessDistinction)).length +
    (ch45.filter (·.value == .multiplePolitenessDistinctions)).length +
    (ch45.filter (·.value == .pronounsAvoidedForPoliteness)).length := by decide

end Pronoun

/-! ### Phonological shape (WALS Chs 136–137, [nichols-peterson-2013]) -/

namespace Pronoun

/-- M-T pronoun pattern (WALS Ch 136A, [nichols-peterson-2013]):
    whether 1SG has /m/ and 2SG has /t/, a widespread cross-linguistic
    pattern hypothesized to reflect deep genealogical signal. -/
inductive MTPattern where
  /-- No M-T pattern in the pronoun paradigm. -/
  | absent
  /-- M-T pattern is paradigmatic (systematic across forms). -/
  | paradigmatic
  /-- M-T pattern is non-paradigmatic (sporadic). -/
  | nonParadigmatic
  deriving DecidableEq, Repr

/-- Whether 1SG has an m-initial or m-containing form (WALS Ch 136B). -/
inductive MIn1SG where
  | absent
  | present
  deriving DecidableEq, Repr

/-- N-M pronoun pattern (WALS Ch 137A, [nichols-peterson-2013]):
    whether 1SG has /n/ and 2SG has /m/. -/
inductive NMPattern where
  | absent
  | paradigmatic
  | nonParadigmatic
  deriving DecidableEq, Repr

/-- Whether 2SG has an m-initial or m-containing form (WALS Ch 137B). -/
inductive MIn2SG where
  | absent
  | present
  deriving DecidableEq, Repr

-- WALS converters for the four shape features.

def fromWALS136A : Data.WALS.F136A.MTPronouns → MTPattern
  | .noMTPronouns              => .absent
  | .mTPronounsParadigmatic    => .paradigmatic
  | .mTPronounsNonParadigmatic => .nonParadigmatic

def fromWALS136B : Data.WALS.F136B.MInFirstPersonSingular → MIn1SG
  | .noMInFirstPersonSingular => .absent
  | .mInFirstPersonSingular   => .present

def fromWALS137A : Data.WALS.F137A.NMPronouns → NMPattern
  | .noNMPronouns              => .absent
  | .nMPronounsParadigmatic    => .paradigmatic
  | .nMPronounsNonParadigmatic => .nonParadigmatic

def fromWALS137B : Data.WALS.F137B.MInSecondPersonSingular → MIn2SG
  | .noMInSecondPersonSingular => .absent
  | .mInSecondPersonSingular   => .present

/-! ### Per-language pronoun-shape accessors (Chs 136–137) -/

/-- WALS Ch 136A: M-T pronoun pattern, for the language with ISO `iso`. -/
def mtPattern (iso : String) : Option MTPattern :=
  (Data.WALS.F136A.lookupISO iso).map (fromWALS136A ·.value)

/-- WALS Ch 136B: /m/ in 1SG. -/
def mIn1sg (iso : String) : Option MIn1SG :=
  (Data.WALS.F136B.lookupISO iso).map (fromWALS136B ·.value)

/-- WALS Ch 137A: N-M pronoun pattern. -/
def nmPattern (iso : String) : Option NMPattern :=
  (Data.WALS.F137A.lookupISO iso).map (fromWALS137A ·.value)

/-- WALS Ch 137B: /m/ in 2SG. -/
def mIn2sg (iso : String) : Option MIn2SG :=
  (Data.WALS.F137B.lookupISO iso).map (fromWALS137B ·.value)

/-- WALS Ch 136A distribution: M-T pronoun patterns
    ([nichols-peterson-2013], n = 230). -/
structure MTCounts where
  absent : Nat
  paradigmatic : Nat
  nonParadigmatic : Nat
  deriving Repr

def MTCounts.total (c : MTCounts) : Nat :=
  c.absent + c.paradigmatic + c.nonParadigmatic

/-- WALS Ch 136A counts (230 languages). -/
def walsMT : MTCounts :=
  { absent := 200
  , paradigmatic := 27
  , nonParadigmatic := 3 }

/-- The M-T pronoun pattern is a clear minority cross-linguistically: only
    30/230 languages (~13%) show any form of it; 200/230 lack it entirely.
    Despite its visibility in Indo-European, it is not a typological default. -/
theorem mt_pronouns_minority :
    walsMT.absent > walsMT.paradigmatic + walsMT.nonParadigmatic := by decide

end Pronoun

/-! ### Clusivity bridge -/

namespace Pronoun

/-- WALS Ch 39 image of a Cysouw first-person-complex type
    (`Features.Clusivity.System`): WALS Ch 39 (Cysouw's own chapter)
    collapses the minimal/augmented split, so the map is many-to-one —
    given a WALS value, the paradigm type is underdetermined. -/
def InclusiveExclusive.fromClusivity : Features.Clusivity.System → InclusiveExclusive
  | .noWe                => .noWe
  | .unifiedWe           => .noDistinction
  | .onlyInclusive       => .onlyInclusive
  | .inclusiveExclusive  => .inclusiveExclusive
  | .minimalAugmented    => .inclusiveExclusive

end Pronoun

/-! ### Pronoun plurality (WALS Ch 35) -/

namespace Pronoun

/-- WALS Ch 35: how independent personal pronouns encode number. The canonical
    home for this pronoun-paradigm feature. -/
inductive Plurality where
  /-- No independent subject pronouns (e.g., Acoma). -/
  | noIndependentPronouns
  /-- Same form for sg and pl (e.g., Pirahã ti 'I/we'). -/
  | numberIndifferent
  /-- Both person and number are affixal. -/
  | personNumberAffixes
  /-- Person+number fused in stem (e.g., Dogon mi/emme). -/
  | personNumberStem
  /-- Person-number stem + pronominal plural affix. -/
  | pnStemPronominalAffix
  /-- Person-number stem + nominal plural affix (e.g., Russian). -/
  | pnStemNominalAffix
  /-- Person stem + pronominal plural affix (e.g., Chuvash). -/
  | personStemPronominalAffix
  /-- Person stem + nominal plural affix (e.g., Mandarin -men). -/
  | personStemNominalAffix
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 35 raw values → the friendly `Plurality` labels. -/
def fromWALS35A : Data.WALS.F35A.PronounPlurality → Plurality
  | .noIndependentSubjectPronouns          => .noIndependentPronouns
  | .numberIndifferentPronouns             => .numberIndifferent
  | .personNumberAffixes                   => .personNumberAffixes
  | .personNumberStem                      => .personNumberStem
  | .personNumberStemPronominalPluralAffix => .pnStemPronominalAffix
  | .personNumberStemNominalPluralAffix    => .pnStemNominalAffix
  | .personStemPronominalPluralAffix       => .personStemPronominalAffix
  | .personStemNominalPluralAffix          => .personStemNominalAffix

private abbrev ch35 := Data.WALS.F35A.allData

set_option maxRecDepth 8192 in
/-- A fused person-number stem is the single most common pronoun-plurality
    strategy cross-linguistically (114/261 languages in WALS Ch 35). -/
theorem personNumberStem_is_plurality (other : Data.WALS.F35A.PronounPlurality) :
    (ch35.filter (·.value == .personNumberStem)).length ≥
    (ch35.filter (·.value == other)).length := by
  cases other <;> decide

end Pronoun

