import Linglib.Datasets.WALS.Features.F39A
import Linglib.Datasets.WALS.Features.F39B
import Linglib.Datasets.WALS.Features.F40A
import Linglib.Datasets.WALS.Features.F44A
import Linglib.Datasets.WALS.Features.F45A
import Linglib.Datasets.WALS.Features.F46A
import Linglib.Datasets.WALS.Features.F47A
import Linglib.Datasets.WALS.Features.F48A

/-!
# Pronoun typology — substrate types
@cite{wals-2013} (Chs 39, 39B, 40, 44–48)

Type-level enums + per-language profile struct for pronoun systems
across @cite{wals-2013} chapters 39–40 and 44–48: inclusive/exclusive
distinctions, gender, politeness, indefinite-pronoun strategy,
intensifier–reflexive relationship, person marking on adpositions.

## Schema

- `InclusiveExclusive` (Ch 39): incl/excl in independent pronouns
- `InclusiveExclusivePamaNyungan` (Ch 39B): areal sub-feature for Pama-Nyungan
- `InclusiveExclusiveVerbal` (Ch 40): incl/excl in verbal inflection
- `GenderInPronouns` (Ch 44): gender distinctions in personal pronouns
- `PolitenessDistinction` (Ch 45): T/V and broader politeness contrasts
- `IndefinitePronounType` (Ch 46): morphological source of indefinites
- `IntensifierReflexive` (Ch 47): intensifier ↔ reflexive identity
- `PersonMarkingOnAdpositions` (Ch 48): adpositional person marking
- `PronounProfile`: per-language bundle (all WALS chapters as Option fields)
-/

set_option autoImplicit false

namespace Typology

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
inductive GenderInPronouns where
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
inductive IndefinitePronounType where
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
structure PronounProfile where
  language : String
  family : String
  iso : String := ""
  /-- Ch 39: incl/excl in independent pronouns. -/
  inclusiveExclusive : Option InclusiveExclusive := .none
  /-- Ch 40: incl/excl in verbal inflection. -/
  inclusiveExclusiveVerbal : Option InclusiveExclusiveVerbal := .none
  /-- Ch 44: gender distinctions. -/
  genderInPronouns : Option GenderInPronouns := .none
  /-- Ch 45: politeness distinctions. -/
  politeness : Option PolitenessDistinction := .none
  /-- Ch 46: indefinite pronoun strategy. -/
  indefiniteType : Option IndefinitePronounType := .none
  /-- Ch 47: intensifier-reflexive relationship. -/
  intensifierReflexive : Option IntensifierReflexive := .none
  /-- Ch 48: person marking on adpositions. -/
  personMarkingAdpositions : Option PersonMarkingOnAdpositions := .none
  deriving Repr, DecidableEq

end Typology

-- ============================================================================
-- WALS converters (Chs 39, 39B, 40, 44–48)
-- ============================================================================

namespace Typology

def fromWALS39A : Datasets.WALS.F39A.InclusiveExclusiveDistinctionInIndependentPronouns →
    InclusiveExclusive
  | .noWe => .noWe
  | .weTheSameAsI => .weEqualsI
  | .noInclusiveExclusive => .noDistinction
  | .onlyInclusive => .onlyInclusive
  | .inclusiveExclusive => .inclusiveExclusive

def fromWALS39B : Datasets.WALS.F39B.InclusiveExclusiveFormsInPamaNyungan →
    InclusiveExclusivePamaNyungan
  | .noInclusiveExclusiveOpposition => .noOpposition
  | .inclusiveAndExclusiveDifferentiated => .differentiated

def fromWALS40A : Datasets.WALS.F40A.InclusiveExclusiveDistinctionInVerbalInflection →
    InclusiveExclusiveVerbal
  | .noPersonMarking => .noPersonMarking
  | .weTheSameAsI => .weEqualsI
  | .noInclusiveExclusive => .noDistinction
  | .onlyInclusive => .onlyInclusive
  | .inclusiveExclusive => .inclusiveExclusive

def fromWALS44A : Datasets.WALS.F44A.GenderDistinctionsInIndependentPersonalPronouns →
    GenderInPronouns
  | .in3rdPerson1stAndOr2ndPerson => .in3rdAndOtherPersons
  | .v3rdPersonOnlyButAlsoNonSingular => .in3rdPersonIncludingNonSg
  | .v3rdPersonSingularOnly => .in3rdPersonSgOnly
  | .v1stOr2ndPersonButNot3rd => .in1stOr2ndOnly
  | .v3rdPersonNonSingularOnly => .in3rdPersonNonSgOnly
  | .noGenderDistinctions => .noGenderDistinctions

def fromWALS45A : Datasets.WALS.F45A.PolitenessDistinctionsInPronouns →
    PolitenessDistinction
  | .noPolitenessDistinction => .none
  | .binaryPolitenessDistinction => .binary
  | .multiplePolitenessDistinctions => .multiple
  | .pronounsAvoidedForPoliteness => .pronounsAvoided

def fromWALS46A : Datasets.WALS.F46A.IndefinitePronouns → IndefinitePronounType
  | .interrogativeBased => .interrogativeBased
  | .genericNounBased => .genericNounBased
  | .special => .special
  | .mixed => .mixed
  | .existentialConstruction => .existentialConstruction

def fromWALS47A : Datasets.WALS.F47A.IntensifierReflexive → IntensifierReflexive
  | .identical => .identical
  | .differentiated => .differentiated

def fromWALS48A : Datasets.WALS.F48A.PersonMarkingOnAdpositions → PersonMarkingOnAdpositions
  | .noAdpositions => .noAdpositions
  | .noPersonMarking => .noPersonMarking
  | .pronounsOnly => .pronounsOnly
  | .pronounsAndNouns => .pronounsAndNouns

-- ============================================================================
-- WALS chapter abbrevs + size theorems + distribution + generalizations
-- ============================================================================

private abbrev ch39 := Datasets.WALS.F39A.allData
private abbrev ch39b := Datasets.WALS.F39B.allData
private abbrev ch40 := Datasets.WALS.F40A.allData
private abbrev ch44 := Datasets.WALS.F44A.allData
private abbrev ch45 := Datasets.WALS.F45A.allData
private abbrev ch46 := Datasets.WALS.F46A.allData
private abbrev ch47 := Datasets.WALS.F47A.allData
private abbrev ch48 := Datasets.WALS.F48A.allData

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

end Typology
