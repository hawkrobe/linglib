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
@cite{wals-2013} @cite{nichols-peterson-2013}

The cross-linguistic WALS-survey facet of the pronoun object: per-language
feature-system `Profile` (Chs 39–48) and phonological `ShapeProfile`
(Chs 136–137), with the WALS converters and distribution theorems.

## Main declarations

* `Pronoun.Profile` — per-language feature-system survey (incl/excl, gender,
  politeness, indefinite strategy, intensifier–reflexive, adpositional person
  marking), WALS Chs 39–48.
* `Pronoun.ShapeProfile` — per-language M-T / N-M phonological-shape survey,
  WALS Chs 136–137 (@cite{nichols-peterson-2013}).
* `Pronoun.Plurality` — how independent personal pronouns encode number,
  WALS Ch 35. The canonical home for this pronoun-paradigm feature; the
  per-language values are carried by `Typology.PluralityProfile` (which bundles
  it with the nominal-plurality Chs 33/34/36).
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

/-- A language's pronoun-system profile across WALS Chs 39–40, 44–48.
    Not all chapters have data for every language (sample varies by
    chapter), so each field is `Option`. -/
structure Profile where
  language : String
  family : String
  iso : String := ""
  /-- Ch 39: incl/excl in independent pronouns. -/
  inclusiveExclusive : Option InclusiveExclusive := .none
  /-- Ch 40: incl/excl in verbal inflection. -/
  inclusiveExclusiveVerbal : Option InclusiveExclusiveVerbal := .none
  /-- Ch 44: gender distinctions. -/
  genderInPronouns : Option GenderDistinction := .none
  /-- Ch 45: politeness distinctions. -/
  politeness : Option PolitenessDistinction := .none
  /-- Ch 46: indefinite pronoun strategy. -/
  indefiniteType : Option IndefiniteType := .none
  /-- Ch 47: intensifier-reflexive relationship. -/
  intensifierReflexive : Option IntensifierReflexive := .none
  /-- Ch 48: person marking on adpositions. -/
  personMarkingAdpositions : Option PersonMarkingOnAdpositions := .none
  deriving Repr, DecidableEq

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

/-! ### Phonological shape (WALS Chs 136–137, @cite{nichols-peterson-2013}) -/

namespace Pronoun

/-- M-T pronoun pattern (WALS Ch 136A, @cite{nichols-peterson-2013}):
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

/-- N-M pronoun pattern (WALS Ch 137A, @cite{nichols-peterson-2013}):
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

/-- A language's pronoun-shape profile across @cite{wals-2013} Chs 136–137.
    Sister to `Profile` (Chs 39–48). Kept as a separate struct to
    avoid contaminating the feature-system bundle with phonological-shape
    fields. -/
structure ShapeProfile where
  language : String
  iso : String := ""
  /-- Ch 136A: M-T pronoun pattern. -/
  mtPronouns : Option MTPattern := none
  /-- Ch 136B: M in 1SG. -/
  mIn1sg : Option MIn1SG := none
  /-- Ch 137A: N-M pronoun pattern. -/
  nmPronouns : Option NMPattern := none
  /-- Ch 137B: M in 2SG. -/
  mIn2sg : Option MIn2SG := none
  deriving Repr, DecidableEq

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

/-- WALS Ch 136A distribution: M-T pronoun patterns
    (@cite{nichols-peterson-2013}, n = 230). -/
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

/-- WALS Ch 39 image of a Cysouw clusivity system (`Features.Clusivity.System`):
    WALS Ch 39 collapses Cysouw's `.inclExcl`, `.minimalAugmented`, and
    `.unitAugmented` into the single value `.inclusiveExclusive`. The
    function is therefore many-to-one: given a WALS Ch 39 value, the
    Cysouw value is underdetermined. -/
def InclusiveExclusive.fromClusivity : Features.Clusivity.System → InclusiveExclusive
  | .noClusivity        => .noDistinction
  | .inclExcl           => .inclusiveExclusive
  | .minimalAugmented   => .inclusiveExclusive
  | .unitAugmented      => .inclusiveExclusive
  | .numberIndifferent  => .weEqualsI

end Pronoun

/-! ### Pronoun plurality (WALS Ch 35) -/

namespace Pronoun

/-- WALS Ch 35: how independent personal pronouns encode number. The canonical
    home for this pronoun-paradigm feature; `Typology.PluralityProfile` carries
    the per-language values alongside the nominal-plurality chapters (33/34/36). -/
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

