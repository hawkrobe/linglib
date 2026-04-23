import Linglib.Datasets.WALS.Features.F39A
import Linglib.Datasets.WALS.Features.F39B
import Linglib.Datasets.WALS.Features.F40A
import Linglib.Datasets.WALS.Features.F44A
import Linglib.Datasets.WALS.Features.F45A
import Linglib.Datasets.WALS.Features.F46A
import Linglib.Datasets.WALS.Features.F47A
import Linglib.Datasets.WALS.Features.F48A

/-!
# Cross-Linguistic Typology of Pronouns (WALS Chapters 39--40, 44--48)
@cite{dryer-haspelmath-2013} @cite{dryer-haspelmath-2013}

Typological data on pronoun systems across languages, drawn from seven
chapters of the World Atlas of Language Structures. These chapters cover the
major dimensions along which pronoun systems vary cross-linguistically:
clusivity, gender, politeness, indefiniteness strategy, the intensifier--
reflexive connection, and person marking on adpositions.

## Ch 39: Inclusive/Exclusive in Independent Pronouns (200 languages)

Whether a language distinguishes inclusive ('we including you') from exclusive
('we excluding you') first-person plural pronouns. The majority of languages
(120/200 = 60%) make no such distinction. Languages with the distinction
(63/200 = 31.5%) are concentrated in Oceanic, Australian, and some
South American families.

## Ch 40: Inclusive/Exclusive in Verbal Inflection (200 languages)

The same inclusive/exclusive dimension, but in verbal agreement morphology
rather than independent pronouns. Many languages that distinguish clusivity in
pronouns lack it in verbal inflection: 70/200 languages have no person marking
on verbs at all.

## Ch 44: Gender Distinctions in Independent Personal Pronouns (378 languages)

Where in the person paradigm gender is marked. The majority of languages
(254/378 = 67.2%) have no gender distinctions in pronouns at all. When
gender is marked, it most commonly appears in the 3rd person singular
(61/378 = 16.1%), consistent with the functional explanation that gender
is most useful for disambiguating reference where multiple potential
antecedents exist.

## Ch 45: Politeness Distinctions in Pronouns (207 languages)

Whether and how pronouns encode social relationships. Most languages lack
politeness distinctions in pronouns (136/207 = 65.7%). Binary T/V systems
(49/207 = 23.7%) are the most common positive value. Some languages avoid
pronouns entirely for politeness (7/207 = 3.4%), using titles or kin terms
instead.

## Ch 46: Indefinite Pronouns (326 languages)

The morphological source of indefinite pronouns ('someone', 'something').
Interrogative-based indefinites (194/326 = 59.5%) are the most common
strategy worldwide, reflecting the well-known interrogative--indefinite
connection. Generic-noun-based indefinites (85/326 = 26.1%) use words
like 'person' or 'thing' as bases.

## Ch 47: Intensifiers and Reflexive Pronouns (168 languages)

Whether intensifiers ('X herself did it') and reflexive pronouns ('X saw
herself') use the same or different forms. Languages split nearly evenly:
94/168 (56%) use identical forms, 74/168 (44%) differentiate them.

## Ch 48: Person Marking on Adpositions (378 languages)

Whether adpositions (prepositions/postpositions) can bear person marking.
The majority of languages (209/378 = 55.3%) have adpositions but no person
marking on them. A substantial minority (83/378 = 22.0%) mark pronouns on
adpositions (e.g. Hebrew 'in-me', 'in-you'). 63 languages (16.7%) lack
adpositions entirely.
-/

namespace Phenomena.Pronouns.Typology

-- ============================================================================
-- Types: WALS Ch 39 -- Inclusive/Exclusive in Independent Pronouns
-- ============================================================================

/-- WALS Ch 39: Inclusive/exclusive distinction in independent pronouns. -/
inductive InclusiveExclusive where
  /-- No first-person plural pronoun at all. -/
  | noWe
  /-- 'We' is the same form as 'I' (no number distinction in 1st person). -/
  | weEqualsI
  /-- First-person plural exists but does not distinguish
      inclusive from exclusive. -/
  | noDistinction
  /-- Only an inclusive form; no dedicated exclusive pronoun. -/
  | onlyInclusive
  /-- Full inclusive/exclusive distinction in 1st-person plural. -/
  | inclusiveExclusive
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Ch 40 -- Inclusive/Exclusive in Verbal Inflection
-- ============================================================================

/-- WALS Ch 40: Inclusive/exclusive distinction in verbal inflection. -/
inductive InclusiveExclusiveVerbal where
  /-- No person marking on verbs at all. -/
  | noPersonMarking
  /-- 'We' verbal form is the same as 'I' form. -/
  | weEqualsI
  /-- Person marking exists but no inclusive/exclusive distinction. -/
  | noDistinction
  /-- Only inclusive marking in verbal inflection. -/
  | onlyInclusive
  /-- Full inclusive/exclusive distinction in verbal inflection. -/
  | inclusiveExclusive
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Ch 44 -- Gender Distinctions in Independent Personal Pronouns
-- ============================================================================

/-- WALS Ch 44: Where gender distinctions appear in the pronoun paradigm. -/
inductive GenderInPronouns where
  /-- Gender in 3rd person AND in 1st and/or 2nd person
      (e.g. Arabic, Hebrew). -/
  | in3rdAndOtherPersons
  /-- Gender in 3rd person only, including non-singular forms
      (e.g. Polish, Albanian). -/
  | in3rdPersonIncludingNonSg
  /-- Gender in 3rd person singular only (e.g. English he/she/it). -/
  | in3rdPersonSgOnly
  /-- Gender in 1st or 2nd person but not 3rd (rare; e.g. Iraqw). -/
  | in1stOr2ndOnly
  /-- Gender in 3rd person non-singular only (extremely rare). -/
  | in3rdPersonNonSgOnly
  /-- No gender distinctions in pronouns at all (e.g. Finnish,
      Turkish, Japanese). -/
  | noGenderDistinctions
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Ch 45 -- Politeness Distinctions in Pronouns
-- ============================================================================

/-- WALS Ch 45: Politeness (honorific/formality) distinctions in pronouns. -/
inductive PolitenessDistinction where
  /-- No politeness distinction in pronouns (e.g. English). -/
  | none
  /-- Binary T/V distinction (e.g. French tu/vous, German du/Sie). -/
  | binary
  /-- Multiple levels of politeness (e.g. Japanese, Hindi, Tagalog). -/
  | multiple
  /-- Pronouns avoided entirely for politeness; titles or kin terms
      used instead (e.g. Korean, Thai). -/
  | pronounsAvoided
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Ch 46 -- Indefinite Pronouns
-- ============================================================================

/-- WALS Ch 46: Morphological source of indefinite pronouns
    ('someone', 'something'). -/
inductive IndefinitePronounType where
  /-- Based on interrogative forms (e.g. Japanese dare-ka 'who-Q' =
      'someone'). -/
  | interrogativeBased
  /-- Based on generic nouns (e.g. English 'somebody' from 'some' + 'body'). -/
  | genericNounBased
  /-- Special, dedicated indefinite forms unrelated to interrogatives
      or generic nouns. -/
  | special
  /-- Mixed: some indefinites are interrogative-based, others
      generic-noun-based. -/
  | mixed
  /-- Existential construction used instead of indefinite pronouns. -/
  | existentialConstruction
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Ch 47 -- Intensifiers and Reflexive Pronouns
-- ============================================================================

/-- WALS Ch 47: Relationship between intensifiers and reflexive pronouns. -/
inductive IntensifierReflexive where
  /-- Identical forms for intensifier ('she herself did it') and
      reflexive ('she saw herself'). -/
  | identical
  /-- Different, morphologically unrelated forms for intensifier
      and reflexive. -/
  | differentiated
  deriving DecidableEq, Repr

-- ============================================================================
-- Types: WALS Ch 48 -- Person Marking on Adpositions
-- ============================================================================

/-- WALS Ch 48: Whether adpositions bear person-marking morphology. -/
inductive PersonMarkingOnAdpositions where
  /-- Language has no adpositions at all (typically head-marking or
      caseless languages). -/
  | noAdpositions
  /-- Adpositions exist but do not bear person marking. -/
  | noPersonMarking
  /-- Only pronominal complements trigger person marking on
      adpositions (e.g. Hebrew be-xa 'in-you'). -/
  | pronounsOnly
  /-- Both pronominal and nominal complements trigger person marking
      on adpositions. -/
  | pronounsAndNouns
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

private abbrev ch39 := Datasets.WALS.F39A.allData
private abbrev ch39b := Datasets.WALS.F39B.allData
private abbrev ch40 := Datasets.WALS.F40A.allData
private abbrev ch44 := Datasets.WALS.F44A.allData
private abbrev ch45 := Datasets.WALS.F45A.allData
private abbrev ch46 := Datasets.WALS.F46A.allData
private abbrev ch47 := Datasets.WALS.F47A.allData
private abbrev ch48 := Datasets.WALS.F48A.allData

private def fromWALS39A : Datasets.WALS.F39A.InclusiveExclusiveDistinctionInIndependentPronouns → InclusiveExclusive
  | .noWe => .noWe
  | .weTheSameAsI => .weEqualsI
  | .noInclusiveExclusive => .noDistinction
  | .onlyInclusive => .onlyInclusive
  | .inclusiveExclusive => .inclusiveExclusive

/-- WALS Ch 39B: Inclusive/exclusive forms in Pama-Nyungan languages.

    An areal sub-feature restricted to the Pama-Nyungan family of Australian
    languages. Of 71 languages sampled, 40 (56%) differentiate inclusive and
    exclusive first-person plural, while 31 (44%) do not. -/
inductive InclusiveExclusivePamaNyungan where
  /-- No inclusive/exclusive opposition in first-person plural. -/
  | noOpposition
  /-- Inclusive and exclusive forms are differentiated. -/
  | differentiated
  deriving DecidableEq, Repr

private def fromWALS39B : Datasets.WALS.F39B.InclusiveExclusiveFormsInPamaNyungan →
    InclusiveExclusivePamaNyungan
  | .noInclusiveExclusiveOpposition => .noOpposition
  | .inclusiveAndExclusiveDifferentiated => .differentiated

private def fromWALS40A : Datasets.WALS.F40A.InclusiveExclusiveDistinctionInVerbalInflection → InclusiveExclusiveVerbal
  | .noPersonMarking => .noPersonMarking
  | .weTheSameAsI => .weEqualsI
  | .noInclusiveExclusive => .noDistinction
  | .onlyInclusive => .onlyInclusive
  | .inclusiveExclusive => .inclusiveExclusive

private def fromWALS44A : Datasets.WALS.F44A.GenderDistinctionsInIndependentPersonalPronouns → GenderInPronouns
  | .in3rdPerson1stAndOr2ndPerson => .in3rdAndOtherPersons
  | .v3rdPersonOnlyButAlsoNonSingular => .in3rdPersonIncludingNonSg
  | .v3rdPersonSingularOnly => .in3rdPersonSgOnly
  | .v1stOr2ndPersonButNot3rd => .in1stOr2ndOnly
  | .v3rdPersonNonSingularOnly => .in3rdPersonNonSgOnly
  | .noGenderDistinctions => .noGenderDistinctions

private def fromWALS45A : Datasets.WALS.F45A.PolitenessDistinctionsInPronouns → PolitenessDistinction
  | .noPolitenessDistinction => .none
  | .binaryPolitenessDistinction => .binary
  | .multiplePolitenessDistinctions => .multiple
  | .pronounsAvoidedForPoliteness => .pronounsAvoided

private def fromWALS46A : Datasets.WALS.F46A.IndefinitePronouns → IndefinitePronounType
  | .interrogativeBased => .interrogativeBased
  | .genericNounBased => .genericNounBased
  | .special => .special
  | .mixed => .mixed
  | .existentialConstruction => .existentialConstruction

private def fromWALS47A : Datasets.WALS.F47A.IntensifierReflexive → IntensifierReflexive
  | .identical => .identical
  | .differentiated => .differentiated

private def fromWALS48A : Datasets.WALS.F48A.PersonMarkingOnAdpositions → PersonMarkingOnAdpositions
  | .noAdpositions => .noAdpositions
  | .noPersonMarking => .noPersonMarking
  | .pronounsOnly => .pronounsOnly
  | .pronounsAndNouns => .pronounsAndNouns

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/--
A language's pronoun system profile across WALS Chapters 39--40, 44--48.

Not all chapters have data for every language (WALS samples vary by chapter),
so each field is optional.
-/
structure PronounProfile where
  /-- Language name. -/
  language : String
  /-- Language family. -/
  family : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 39: Inclusive/exclusive distinction in independent pronouns. -/
  inclusiveExclusive : Option InclusiveExclusive := .none
  /-- Ch 40: Inclusive/exclusive distinction in verbal inflection. -/
  inclusiveExclusiveVerbal : Option InclusiveExclusiveVerbal := .none
  /-- Ch 44: Gender distinctions in independent personal pronouns. -/
  genderInPronouns : Option GenderInPronouns := .none
  /-- Ch 45: Politeness distinctions in pronouns. -/
  politeness : Option PolitenessDistinction := .none
  /-- Ch 46: Indefinite pronoun strategy. -/
  indefiniteType : Option IndefinitePronounType := .none
  /-- Ch 47: Intensifier--reflexive relationship. -/
  intensifierReflexive : Option IntensifierReflexive := .none
  /-- Ch 48: Person marking on adpositions. -/
  personMarkingAdpositions : Option PersonMarkingOnAdpositions := .none
  deriving Repr

-- ============================================================================
-- Language Data: 15 Language Profiles
-- ============================================================================

/-- English (Indo-European, Germanic).
    No inclusive/exclusive distinction in pronouns or verbal inflection.
    Gender in 3rd person singular only (he/she/it).
    No politeness distinction in pronouns.
    Generic-noun-based indefinites (somebody, something).
    Intensifier and reflexive use identical forms (himself/herself).
    No person marking on adpositions. -/
def english : PronounProfile :=
  { language := "English"
  , family := "Indo-European"
  , iso := "eng"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .weEqualsI
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .none
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

/-- German (Indo-European, Germanic).
    No inclusive/exclusive distinction.
    Gender in 3rd person singular only (er/sie/es).
    Binary politeness distinction (du/Sie).
    Mixed indefinite strategy (jemand is special, irgendwer interrogative-based).
    Intensifier (selbst) differentiated from reflexive (sich).
    No person marking on adpositions. -/
def german : PronounProfile :=
  { language := "German"
  , family := "Indo-European"
  , iso := "deu"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .mixed
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- French (Indo-European, Romance).
    No inclusive/exclusive distinction.
    Gender in 3rd person singular only (il/elle).
    Binary politeness distinction (tu/vous).
    Generic-noun-based indefinites (quelqu'un from quel + un).
    Intensifier (meme) differentiated from reflexive (se).
    No person marking on adpositions. -/
def french : PronounProfile :=
  { language := "French"
  , family := "Indo-European"
  , iso := "fra"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- Spanish (Indo-European, Romance).
    No inclusive/exclusive distinction.
    Gender in 3rd person AND 1st/2nd person (nosotros/nosotras, etc.).
    Binary politeness distinction (tu/usted).
    Special indefinite forms (alguien, algo).
    Intensifier (mismo) differentiated from reflexive (se).
    No person marking on adpositions. -/
def spanish : PronounProfile :=
  { language := "Spanish"
  , family := "Indo-European"
  , iso := "spa"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdAndOtherPersons
  , politeness := some .binary
  , indefiniteType := some .special
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- Russian (Indo-European, Slavic).
    No inclusive/exclusive distinction.
    Gender in 3rd person singular only (on/ona/ono).
    Binary politeness distinction (ty/vy).
    Interrogative-based indefinites (kto-to, kto-nibud').
    Intensifier (sam) differentiated from reflexive (sebja).
    No person marking on adpositions. -/
def russian : PronounProfile :=
  { language := "Russian"
  , family := "Indo-European"
  , iso := "rus"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .interrogativeBased
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- Japanese (Japonic).
    No inclusive/exclusive distinction in pronouns.
    No person marking on verbs (hence no clusivity in verbal inflection).
    3rd-person pronoun gender: WALS classifies as 3rd person only, including
    non-singular (kare/kanojo distinction).
    Pronouns avoided for politeness (titles, kin terms, names used instead).
    Interrogative-based indefinites (dare-ka 'who-Q' = 'someone').
    Intensifier and reflexive use identical form (jibun).
    No person marking on adpositions. -/
def japanese : PronounProfile :=
  { language := "Japanese"
  , family := "Japonic"
  , iso := "jpn"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .in3rdPersonIncludingNonSg
  , politeness := some .pronounsAvoided
  , indefiniteType := some .interrogativeBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

/-- Mandarin Chinese (Sino-Tibetan).
    Inclusive/exclusive distinction in independent pronouns (women vs zanmen).
    No person marking on verbs.
    Gender in 3rd person singular only (ta with different characters).
    Binary politeness distinction (ni/nin).
    Mixed indefinite strategy (interrogative-based and others).
    Intensifier and reflexive use identical form (ziji).
    No person marking on adpositions. -/
def mandarin : PronounProfile :=
  { language := "Mandarin"
  , family := "Sino-Tibetan"
  , iso := "cmn"
  , inclusiveExclusive := some .inclusiveExclusive
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .mixed
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

/-- Korean (Koreanic).
    No inclusive/exclusive distinction.
    No person marking on verbs.
    Gender in 3rd person singular only (ku/kunyo).
    Pronouns avoided for politeness (elaborate honorific system uses
    titles and names instead of pronouns).
    Interrogative-based indefinites (nwukwunka from nwukwu 'who').
    Intensifier and reflexive use identical form (caki).
    No person marking on adpositions. -/
def korean : PronounProfile :=
  { language := "Korean"
  , family := "Koreanic"
  , iso := "kor"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .pronounsAvoided
  , indefiniteType := some .interrogativeBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

/-- Turkish (Turkic).
    No inclusive/exclusive distinction.
    No inclusive/exclusive in verbal inflection (but has person marking).
    No gender distinctions in pronouns (o is used for all genders).
    Binary politeness distinction (sen/siz).
    Generic-noun-based indefinites (birisi from bir 'one').
    Intensifier and reflexive use identical form (kendi).
    No person marking on adpositions. -/
def turkish : PronounProfile :=
  { language := "Turkish"
  , family := "Turkic"
  , iso := "tur"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .binary
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

/-- Finnish (Uralic).
    No inclusive/exclusive distinction.
    No inclusive/exclusive in verbal inflection (but has person marking).
    No gender distinctions in pronouns (han is used for all genders).
    Binary politeness distinction (sina/te).
    Special indefinite forms (joku, jokin).
    Intensifier and reflexive use identical form (itse).
    Person marking on adpositions (pronouns only: kanssa-ni 'with-me'). -/
def finnish : PronounProfile :=
  { language := "Finnish"
  , family := "Uralic"
  , iso := "fin"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .binary
  , indefiniteType := some .special
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .pronounsOnly }

/-- Hungarian (Uralic).
    No inclusive/exclusive distinction.
    No inclusive/exclusive in verbal inflection (but has person marking).
    No gender distinctions in pronouns (o is used for all genders).
    Multiple politeness distinctions (te/On/maga).
    Interrogative-based indefinites (valaki from val- 'some' + ki 'who').
    Intensifier and reflexive use identical form (maga).
    Person marking on adpositions (pronouns only: velem 'with-me'). -/
def hungarian : PronounProfile :=
  { language := "Hungarian"
  , family := "Uralic"
  , iso := "hun"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .multiple
  , indefiniteType := some .interrogativeBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .pronounsOnly }

/-- Hindi (Indo-European, Indo-Aryan).
    No inclusive/exclusive distinction in pronouns.
    No person marking on verbs (WALS classification).
    No gender distinctions in pronouns (vah/ye are gender-neutral).
    Multiple politeness distinctions (tu/tum/aap).
    Special indefinite forms (koi, kuch).
    Intensifier and reflexive use identical form (apne-aap/khud).
    No person marking on adpositions. -/
def hindi : PronounProfile :=
  { language := "Hindi"
  , family := "Indo-European"
  , iso := "hin"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .multiple
  , indefiniteType := some .special
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

/-- Arabic (Egyptian) (Afro-Asiatic, Semitic).
    No inclusive/exclusive distinction.
    No inclusive/exclusive in verbal inflection (but has person marking).
    Gender in 3rd person AND 1st/2nd person (inta/inti, huwwa/hiyya).
    No politeness distinction in pronouns.
    Generic-noun-based indefinites (hadd 'person' = 'someone').
    No data for intensifier/reflexive in WALS Ch 47.
    Person marking on adpositions (pronouns only: fi-ya 'in-me'). -/
def arabic : PronounProfile :=
  { language := "Arabic (Egyptian)"
  , family := "Afro-Asiatic"
  , iso := "arz"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdAndOtherPersons
  , politeness := some .none
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := Option.none
  , personMarkingAdpositions := some .pronounsOnly }

/-- Swahili (Niger-Congo, Bantu).
    No inclusive/exclusive distinction.
    No inclusive/exclusive in verbal inflection (but has person marking).
    Gender in 3rd person only, including non-singular (via noun-class system).
    No politeness distinction in pronouns.
    Generic-noun-based indefinites (mtu 'person' = 'someone').
    Intensifier (mwenyewe) differentiated from reflexive (ji-).
    No person marking on adpositions. -/
def swahili : PronounProfile :=
  { language := "Swahili"
  , family := "Niger-Congo"
  , iso := "swh"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonIncludingNonSg
  , politeness := some .none
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- Tagalog (Austronesian, Philippine).
    Inclusive/exclusive distinction in independent pronouns (kami vs tayo).
    No person marking on verbs (WALS classification).
    No gender distinctions in pronouns (siya is gender-neutral).
    Multiple politeness distinctions (ikaw/kayo/po system).
    Existential construction for indefinite reference.
    Intensifier (mismo) differentiated from reflexive (sarili).
    No adpositions (WALS classification). -/
def tagalog : PronounProfile :=
  { language := "Tagalog"
  , family := "Austronesian"
  , iso := "tgl"
  , inclusiveExclusive := some .inclusiveExclusive
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .multiple
  , indefiniteType := some .existentialConstruction
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noAdpositions }

/-- All 15 language profiles. -/
def allLanguages : List PronounProfile :=
  [ english, german, french, spanish, russian, japanese, mandarin
  , korean, turkish, finnish, hungarian, hindi, arabic, swahili
  , tagalog ]

-- ============================================================================
-- WALS Data Totals
-- ============================================================================

theorem ch39_total : ch39.length = 200 := by native_decide
theorem ch39b_total : ch39b.length = 71 := by native_decide
theorem ch40_total : ch40.length = 200 := by native_decide
theorem ch44_total : ch44.length = 378 := by native_decide
theorem ch45_total : ch45.length = 207 := by native_decide
theorem ch46_total : ch46.length = 326 := by native_decide
theorem ch47_total : ch47.length = 168 := by native_decide
theorem ch48_total : ch48.length = 378 := by native_decide

-- ============================================================================
-- WALS Distribution Count Verification
-- ============================================================================

-- Ch 39: Inclusive/exclusive in independent pronouns
theorem ch39_noWe :
    (ch39.filter (·.value == .noWe)).length = 2 := by native_decide
theorem ch39_weTheSameAsI :
    (ch39.filter (·.value == .weTheSameAsI)).length = 10 := by native_decide
theorem ch39_noInclusiveExclusive :
    (ch39.filter (·.value == .noInclusiveExclusive)).length = 120 := by native_decide
theorem ch39_onlyInclusive :
    (ch39.filter (·.value == .onlyInclusive)).length = 5 := by native_decide
theorem ch39_inclusiveExclusive :
    (ch39.filter (·.value == .inclusiveExclusive)).length = 63 := by native_decide

-- Ch 39B: Inclusive/exclusive forms in Pama-Nyungan
theorem ch39b_noInclusiveExclusiveOpposition :
    (ch39b.filter (·.value == .noInclusiveExclusiveOpposition)).length = 31 := by native_decide
theorem ch39b_inclusiveAndExclusiveDifferentiated :
    (ch39b.filter (·.value == .inclusiveAndExclusiveDifferentiated)).length = 40 := by native_decide

-- Ch 40: Inclusive/exclusive in verbal inflection
theorem ch40_noPersonMarking :
    (ch40.filter (·.value == .noPersonMarking)).length = 70 := by native_decide
theorem ch40_weTheSameAsI :
    (ch40.filter (·.value == .weTheSameAsI)).length = 12 := by native_decide
theorem ch40_noInclusiveExclusive :
    (ch40.filter (·.value == .noInclusiveExclusive)).length = 79 := by native_decide
theorem ch40_onlyInclusive :
    (ch40.filter (·.value == .onlyInclusive)).length = 9 := by native_decide
theorem ch40_inclusiveExclusive :
    (ch40.filter (·.value == .inclusiveExclusive)).length = 30 := by native_decide

-- Ch 44: Gender distinctions in independent personal pronouns
theorem ch44_in3rdPerson1stAndOr2ndPerson :
    (ch44.filter (·.value == .in3rdPerson1stAndOr2ndPerson)).length = 18 := by native_decide
theorem ch44_v3rdPersonOnlyButAlsoNonSingular :
    (ch44.filter (·.value == .v3rdPersonOnlyButAlsoNonSingular)).length = 42 := by native_decide
theorem ch44_v3rdPersonSingularOnly :
    (ch44.filter (·.value == .v3rdPersonSingularOnly)).length = 61 := by native_decide
theorem ch44_v1stOr2ndPersonButNot3rd :
    (ch44.filter (·.value == .v1stOr2ndPersonButNot3rd)).length = 2 := by native_decide
theorem ch44_v3rdPersonNonSingularOnly :
    (ch44.filter (·.value == .v3rdPersonNonSingularOnly)).length = 1 := by native_decide
theorem ch44_noGenderDistinctions :
    (ch44.filter (·.value == .noGenderDistinctions)).length = 254 := by native_decide

-- Ch 45: Politeness distinctions in pronouns
theorem ch45_noPolitenessDistinction :
    (ch45.filter (·.value == .noPolitenessDistinction)).length = 136 := by native_decide
theorem ch45_binaryPolitenessDistinction :
    (ch45.filter (·.value == .binaryPolitenessDistinction)).length = 49 := by native_decide
theorem ch45_multiplePolitenessDistinctions :
    (ch45.filter (·.value == .multiplePolitenessDistinctions)).length = 15 := by native_decide
theorem ch45_pronounsAvoidedForPoliteness :
    (ch45.filter (·.value == .pronounsAvoidedForPoliteness)).length = 7 := by native_decide

-- Ch 46: Indefinite pronouns
theorem ch46_interrogativeBased :
    (ch46.filter (·.value == .interrogativeBased)).length = 194 := by native_decide
theorem ch46_genericNounBased :
    (ch46.filter (·.value == .genericNounBased)).length = 85 := by native_decide
theorem ch46_special :
    (ch46.filter (·.value == .special)).length = 22 := by native_decide
theorem ch46_mixed :
    (ch46.filter (·.value == .mixed)).length = 23 := by native_decide
theorem ch46_existentialConstruction :
    (ch46.filter (·.value == .existentialConstruction)).length = 2 := by native_decide

-- Ch 47: Intensifiers and reflexive pronouns
theorem ch47_identical :
    (ch47.filter (·.value == .identical)).length = 94 := by native_decide
theorem ch47_differentiated :
    (ch47.filter (·.value == .differentiated)).length = 74 := by native_decide

-- Ch 48: Person marking on adpositions
theorem ch48_noAdpositions :
    (ch48.filter (·.value == .noAdpositions)).length = 63 := by native_decide
theorem ch48_noPersonMarking :
    (ch48.filter (·.value == .noPersonMarking)).length = 209 := by native_decide
theorem ch48_pronounsOnly :
    (ch48.filter (·.value == .pronounsOnly)).length = 83 := by native_decide
theorem ch48_pronounsAndNouns :
    (ch48.filter (·.value == .pronounsAndNouns)).length = 23 := by native_decide

-- ============================================================================
-- Grounding Theorems: Per-Language WALS Verification
-- ============================================================================

-- English
theorem english_ch39 :
    ch39.find? (·.walsCode == "eng") = some ⟨"eng", "eng", .noInclusiveExclusive⟩ := by
  native_decide
theorem english_ch39_agrees :
    (ch39.find? (·.walsCode == "eng")).map (fromWALS39A ·.value) = english.inclusiveExclusive := by
  native_decide
theorem english_ch40_agrees :
    (ch40.find? (·.walsCode == "eng")).map (fromWALS40A ·.value) = english.inclusiveExclusiveVerbal := by
  native_decide
theorem english_ch44_agrees :
    (ch44.find? (·.walsCode == "eng")).map (fromWALS44A ·.value) = english.genderInPronouns := by
  native_decide
theorem english_ch45_agrees :
    (ch45.find? (·.walsCode == "eng")).map (fromWALS45A ·.value) = english.politeness := by
  native_decide
theorem english_ch46_agrees :
    (ch46.find? (·.walsCode == "eng")).map (fromWALS46A ·.value) = english.indefiniteType := by
  native_decide
theorem english_ch47_agrees :
    (ch47.find? (·.walsCode == "eng")).map (fromWALS47A ·.value) = english.intensifierReflexive := by
  native_decide
theorem english_ch48_agrees :
    (ch48.find? (·.walsCode == "eng")).map (fromWALS48A ·.value) = english.personMarkingAdpositions := by
  native_decide

-- German
theorem german_ch39_agrees :
    (ch39.find? (·.walsCode == "ger")).map (fromWALS39A ·.value) = german.inclusiveExclusive := by
  native_decide
theorem german_ch40_agrees :
    (ch40.find? (·.walsCode == "ger")).map (fromWALS40A ·.value) = german.inclusiveExclusiveVerbal := by
  native_decide
theorem german_ch44_agrees :
    (ch44.find? (·.walsCode == "ger")).map (fromWALS44A ·.value) = german.genderInPronouns := by
  native_decide
theorem german_ch45_agrees :
    (ch45.find? (·.walsCode == "ger")).map (fromWALS45A ·.value) = german.politeness := by
  native_decide
theorem german_ch46_agrees :
    (ch46.find? (·.walsCode == "ger")).map (fromWALS46A ·.value) = german.indefiniteType := by
  native_decide
theorem german_ch47_agrees :
    (ch47.find? (·.walsCode == "ger")).map (fromWALS47A ·.value) = german.intensifierReflexive := by
  native_decide
theorem german_ch48_agrees :
    (ch48.find? (·.walsCode == "ger")).map (fromWALS48A ·.value) = german.personMarkingAdpositions := by
  native_decide

-- French
theorem french_ch39_agrees :
    (ch39.find? (·.walsCode == "fre")).map (fromWALS39A ·.value) = french.inclusiveExclusive := by
  native_decide
theorem french_ch40_agrees :
    (ch40.find? (·.walsCode == "fre")).map (fromWALS40A ·.value) = french.inclusiveExclusiveVerbal := by
  native_decide
theorem french_ch44_agrees :
    (ch44.find? (·.walsCode == "fre")).map (fromWALS44A ·.value) = french.genderInPronouns := by
  native_decide
theorem french_ch45_agrees :
    (ch45.find? (·.walsCode == "fre")).map (fromWALS45A ·.value) = french.politeness := by
  native_decide
theorem french_ch46_agrees :
    (ch46.find? (·.walsCode == "fre")).map (fromWALS46A ·.value) = french.indefiniteType := by
  native_decide
theorem french_ch47_agrees :
    (ch47.find? (·.walsCode == "fre")).map (fromWALS47A ·.value) = french.intensifierReflexive := by
  native_decide
theorem french_ch48_agrees :
    (ch48.find? (·.walsCode == "fre")).map (fromWALS48A ·.value) = french.personMarkingAdpositions := by
  native_decide

-- Spanish
theorem spanish_ch39_agrees :
    (ch39.find? (·.walsCode == "spa")).map (fromWALS39A ·.value) = spanish.inclusiveExclusive := by
  native_decide
theorem spanish_ch40_agrees :
    (ch40.find? (·.walsCode == "spa")).map (fromWALS40A ·.value) = spanish.inclusiveExclusiveVerbal := by
  native_decide
theorem spanish_ch44_agrees :
    (ch44.find? (·.walsCode == "spa")).map (fromWALS44A ·.value) = spanish.genderInPronouns := by
  native_decide
theorem spanish_ch45_agrees :
    (ch45.find? (·.walsCode == "spa")).map (fromWALS45A ·.value) = spanish.politeness := by
  native_decide
theorem spanish_ch46_agrees :
    (ch46.find? (·.walsCode == "spa")).map (fromWALS46A ·.value) = spanish.indefiniteType := by
  native_decide
theorem spanish_ch47_agrees :
    (ch47.find? (·.walsCode == "spa")).map (fromWALS47A ·.value) = spanish.intensifierReflexive := by
  native_decide
theorem spanish_ch48_agrees :
    (ch48.find? (·.walsCode == "spa")).map (fromWALS48A ·.value) = spanish.personMarkingAdpositions := by
  native_decide

-- Russian
theorem russian_ch39_agrees :
    (ch39.find? (·.walsCode == "rus")).map (fromWALS39A ·.value) = russian.inclusiveExclusive := by
  native_decide
theorem russian_ch40_agrees :
    (ch40.find? (·.walsCode == "rus")).map (fromWALS40A ·.value) = russian.inclusiveExclusiveVerbal := by
  native_decide
theorem russian_ch44_agrees :
    (ch44.find? (·.walsCode == "rus")).map (fromWALS44A ·.value) = russian.genderInPronouns := by
  native_decide
theorem russian_ch45_agrees :
    (ch45.find? (·.walsCode == "rus")).map (fromWALS45A ·.value) = russian.politeness := by
  native_decide
theorem russian_ch46_agrees :
    (ch46.find? (·.walsCode == "rus")).map (fromWALS46A ·.value) = russian.indefiniteType := by
  native_decide
theorem russian_ch47_agrees :
    (ch47.find? (·.walsCode == "rus")).map (fromWALS47A ·.value) = russian.intensifierReflexive := by
  native_decide
theorem russian_ch48_agrees :
    (ch48.find? (·.walsCode == "rus")).map (fromWALS48A ·.value) = russian.personMarkingAdpositions := by
  native_decide

-- Japanese
theorem japanese_ch39_agrees :
    (ch39.find? (·.walsCode == "jpn")).map (fromWALS39A ·.value) = japanese.inclusiveExclusive := by
  native_decide
theorem japanese_ch40_agrees :
    (ch40.find? (·.walsCode == "jpn")).map (fromWALS40A ·.value) = japanese.inclusiveExclusiveVerbal := by
  native_decide
theorem japanese_ch44_agrees :
    (ch44.find? (·.walsCode == "jpn")).map (fromWALS44A ·.value) = japanese.genderInPronouns := by
  native_decide
theorem japanese_ch45_agrees :
    (ch45.find? (·.walsCode == "jpn")).map (fromWALS45A ·.value) = japanese.politeness := by
  native_decide
theorem japanese_ch46_agrees :
    (ch46.find? (·.walsCode == "jpn")).map (fromWALS46A ·.value) = japanese.indefiniteType := by
  native_decide
theorem japanese_ch47_agrees :
    (ch47.find? (·.walsCode == "jpn")).map (fromWALS47A ·.value) = japanese.intensifierReflexive := by
  native_decide
theorem japanese_ch48_agrees :
    (ch48.find? (·.walsCode == "jpn")).map (fromWALS48A ·.value) = japanese.personMarkingAdpositions := by
  native_decide

-- Mandarin
theorem mandarin_ch39_agrees :
    (ch39.find? (·.walsCode == "mnd")).map (fromWALS39A ·.value) = mandarin.inclusiveExclusive := by
  native_decide
theorem mandarin_ch40_agrees :
    (ch40.find? (·.walsCode == "mnd")).map (fromWALS40A ·.value) = mandarin.inclusiveExclusiveVerbal := by
  native_decide
theorem mandarin_ch44_agrees :
    (ch44.find? (·.walsCode == "mnd")).map (fromWALS44A ·.value) = mandarin.genderInPronouns := by
  native_decide
theorem mandarin_ch45_agrees :
    (ch45.find? (·.walsCode == "mnd")).map (fromWALS45A ·.value) = mandarin.politeness := by
  native_decide
theorem mandarin_ch46_agrees :
    (ch46.find? (·.walsCode == "mnd")).map (fromWALS46A ·.value) = mandarin.indefiniteType := by
  native_decide
theorem mandarin_ch47_agrees :
    (ch47.find? (·.walsCode == "mnd")).map (fromWALS47A ·.value) = mandarin.intensifierReflexive := by
  native_decide
theorem mandarin_ch48_agrees :
    (ch48.find? (·.walsCode == "mnd")).map (fromWALS48A ·.value) = mandarin.personMarkingAdpositions := by
  native_decide

-- Korean
theorem korean_ch39_agrees :
    (ch39.find? (·.walsCode == "kor")).map (fromWALS39A ·.value) = korean.inclusiveExclusive := by
  native_decide
theorem korean_ch40_agrees :
    (ch40.find? (·.walsCode == "kor")).map (fromWALS40A ·.value) = korean.inclusiveExclusiveVerbal := by
  native_decide
theorem korean_ch44_agrees :
    (ch44.find? (·.walsCode == "kor")).map (fromWALS44A ·.value) = korean.genderInPronouns := by
  native_decide
theorem korean_ch45_agrees :
    (ch45.find? (·.walsCode == "kor")).map (fromWALS45A ·.value) = korean.politeness := by
  native_decide
theorem korean_ch46_agrees :
    (ch46.find? (·.walsCode == "kor")).map (fromWALS46A ·.value) = korean.indefiniteType := by
  native_decide
theorem korean_ch47_agrees :
    (ch47.find? (·.walsCode == "kor")).map (fromWALS47A ·.value) = korean.intensifierReflexive := by
  native_decide
theorem korean_ch48_agrees :
    (ch48.find? (·.walsCode == "kor")).map (fromWALS48A ·.value) = korean.personMarkingAdpositions := by
  native_decide

-- Turkish
theorem turkish_ch39_agrees :
    (ch39.find? (·.walsCode == "tur")).map (fromWALS39A ·.value) = turkish.inclusiveExclusive := by
  native_decide
theorem turkish_ch40_agrees :
    (ch40.find? (·.walsCode == "tur")).map (fromWALS40A ·.value) = turkish.inclusiveExclusiveVerbal := by
  native_decide
theorem turkish_ch44_agrees :
    (ch44.find? (·.walsCode == "tur")).map (fromWALS44A ·.value) = turkish.genderInPronouns := by
  native_decide
theorem turkish_ch45_agrees :
    (ch45.find? (·.walsCode == "tur")).map (fromWALS45A ·.value) = turkish.politeness := by
  native_decide
theorem turkish_ch46_agrees :
    (ch46.find? (·.walsCode == "tur")).map (fromWALS46A ·.value) = turkish.indefiniteType := by
  native_decide
theorem turkish_ch47_agrees :
    (ch47.find? (·.walsCode == "tur")).map (fromWALS47A ·.value) = turkish.intensifierReflexive := by
  native_decide
theorem turkish_ch48_agrees :
    (ch48.find? (·.walsCode == "tur")).map (fromWALS48A ·.value) = turkish.personMarkingAdpositions := by
  native_decide

-- Finnish
theorem finnish_ch39_agrees :
    (ch39.find? (·.walsCode == "fin")).map (fromWALS39A ·.value) = finnish.inclusiveExclusive := by
  native_decide
theorem finnish_ch40_agrees :
    (ch40.find? (·.walsCode == "fin")).map (fromWALS40A ·.value) = finnish.inclusiveExclusiveVerbal := by
  native_decide
theorem finnish_ch44_agrees :
    (ch44.find? (·.walsCode == "fin")).map (fromWALS44A ·.value) = finnish.genderInPronouns := by
  native_decide
theorem finnish_ch45_agrees :
    (ch45.find? (·.walsCode == "fin")).map (fromWALS45A ·.value) = finnish.politeness := by
  native_decide
theorem finnish_ch46_agrees :
    (ch46.find? (·.walsCode == "fin")).map (fromWALS46A ·.value) = finnish.indefiniteType := by
  native_decide
theorem finnish_ch47_agrees :
    (ch47.find? (·.walsCode == "fin")).map (fromWALS47A ·.value) = finnish.intensifierReflexive := by
  native_decide
theorem finnish_ch48_agrees :
    (ch48.find? (·.walsCode == "fin")).map (fromWALS48A ·.value) = finnish.personMarkingAdpositions := by
  native_decide

-- Hungarian
theorem hungarian_ch39_agrees :
    (ch39.find? (·.walsCode == "hun")).map (fromWALS39A ·.value) = hungarian.inclusiveExclusive := by
  native_decide
theorem hungarian_ch40_agrees :
    (ch40.find? (·.walsCode == "hun")).map (fromWALS40A ·.value) = hungarian.inclusiveExclusiveVerbal := by
  native_decide
theorem hungarian_ch44_agrees :
    (ch44.find? (·.walsCode == "hun")).map (fromWALS44A ·.value) = hungarian.genderInPronouns := by
  native_decide
theorem hungarian_ch45_agrees :
    (ch45.find? (·.walsCode == "hun")).map (fromWALS45A ·.value) = hungarian.politeness := by
  native_decide
theorem hungarian_ch46_agrees :
    (ch46.find? (·.walsCode == "hun")).map (fromWALS46A ·.value) = hungarian.indefiniteType := by
  native_decide
theorem hungarian_ch47_agrees :
    (ch47.find? (·.walsCode == "hun")).map (fromWALS47A ·.value) = hungarian.intensifierReflexive := by
  native_decide
theorem hungarian_ch48_agrees :
    (ch48.find? (·.walsCode == "hun")).map (fromWALS48A ·.value) = hungarian.personMarkingAdpositions := by
  native_decide

-- Hindi
theorem hindi_ch39_agrees :
    (ch39.find? (·.walsCode == "hin")).map (fromWALS39A ·.value) = hindi.inclusiveExclusive := by
  native_decide
theorem hindi_ch40_agrees :
    (ch40.find? (·.walsCode == "hin")).map (fromWALS40A ·.value) = hindi.inclusiveExclusiveVerbal := by
  native_decide
theorem hindi_ch44_agrees :
    (ch44.find? (·.walsCode == "hin")).map (fromWALS44A ·.value) = hindi.genderInPronouns := by
  native_decide
theorem hindi_ch45_agrees :
    (ch45.find? (·.walsCode == "hin")).map (fromWALS45A ·.value) = hindi.politeness := by
  native_decide
theorem hindi_ch46_agrees :
    (ch46.find? (·.walsCode == "hin")).map (fromWALS46A ·.value) = hindi.indefiniteType := by
  native_decide
theorem hindi_ch47_agrees :
    (ch47.find? (·.walsCode == "hin")).map (fromWALS47A ·.value) = hindi.intensifierReflexive := by
  native_decide
theorem hindi_ch48_agrees :
    (ch48.find? (·.walsCode == "hin")).map (fromWALS48A ·.value) = hindi.personMarkingAdpositions := by
  native_decide

-- Arabic (Egyptian)
theorem arabic_ch39_agrees :
    (ch39.find? (·.walsCode == "aeg")).map (fromWALS39A ·.value) = arabic.inclusiveExclusive := by
  native_decide
theorem arabic_ch40_agrees :
    (ch40.find? (·.walsCode == "aeg")).map (fromWALS40A ·.value) = arabic.inclusiveExclusiveVerbal := by
  native_decide
theorem arabic_ch44_agrees :
    (ch44.find? (·.walsCode == "aeg")).map (fromWALS44A ·.value) = arabic.genderInPronouns := by
  native_decide
theorem arabic_ch45_agrees :
    (ch45.find? (·.walsCode == "aeg")).map (fromWALS45A ·.value) = arabic.politeness := by
  native_decide
theorem arabic_ch46_agrees :
    (ch46.find? (·.walsCode == "aeg")).map (fromWALS46A ·.value) = arabic.indefiniteType := by
  native_decide
theorem arabic_ch48_agrees :
    (ch48.find? (·.walsCode == "aeg")).map (fromWALS48A ·.value) = arabic.personMarkingAdpositions := by
  native_decide

-- Swahili
theorem swahili_ch39_agrees :
    (ch39.find? (·.walsCode == "swa")).map (fromWALS39A ·.value) = swahili.inclusiveExclusive := by
  native_decide
theorem swahili_ch40_agrees :
    (ch40.find? (·.walsCode == "swa")).map (fromWALS40A ·.value) = swahili.inclusiveExclusiveVerbal := by
  native_decide
theorem swahili_ch44_agrees :
    (ch44.find? (·.walsCode == "swa")).map (fromWALS44A ·.value) = swahili.genderInPronouns := by
  native_decide
theorem swahili_ch45_agrees :
    (ch45.find? (·.walsCode == "swa")).map (fromWALS45A ·.value) = swahili.politeness := by
  native_decide
theorem swahili_ch46_agrees :
    (ch46.find? (·.walsCode == "swa")).map (fromWALS46A ·.value) = swahili.indefiniteType := by
  native_decide
theorem swahili_ch47_agrees :
    (ch47.find? (·.walsCode == "swa")).map (fromWALS47A ·.value) = swahili.intensifierReflexive := by
  native_decide
theorem swahili_ch48_agrees :
    (ch48.find? (·.walsCode == "swa")).map (fromWALS48A ·.value) = swahili.personMarkingAdpositions := by
  native_decide

-- Tagalog
theorem tagalog_ch39_agrees :
    (ch39.find? (·.walsCode == "tag")).map (fromWALS39A ·.value) = tagalog.inclusiveExclusive := by
  native_decide
theorem tagalog_ch40_agrees :
    (ch40.find? (·.walsCode == "tag")).map (fromWALS40A ·.value) = tagalog.inclusiveExclusiveVerbal := by
  native_decide
theorem tagalog_ch44_agrees :
    (ch44.find? (·.walsCode == "tag")).map (fromWALS44A ·.value) = tagalog.genderInPronouns := by
  native_decide
theorem tagalog_ch45_agrees :
    (ch45.find? (·.walsCode == "tag")).map (fromWALS45A ·.value) = tagalog.politeness := by
  native_decide
theorem tagalog_ch46_agrees :
    (ch46.find? (·.walsCode == "tag")).map (fromWALS46A ·.value) = tagalog.indefiniteType := by
  native_decide
theorem tagalog_ch47_agrees :
    (ch47.find? (·.walsCode == "tag")).map (fromWALS47A ·.value) = tagalog.intensifierReflexive := by
  native_decide
theorem tagalog_ch48_agrees :
    (ch48.find? (·.walsCode == "tag")).map (fromWALS48A ·.value) = tagalog.personMarkingAdpositions := by
  native_decide

-- ============================================================================
-- Cross-Linguistic Generalizations
-- ============================================================================

/--
The majority of languages (120/200 = 60%) make no inclusive/exclusive
distinction in independent pronouns.
-/
theorem noDistinction_is_majority_ch39 :
    (ch39.filter (·.value == .noInclusiveExclusive)).length >
    (ch39.filter (·.value == .inclusiveExclusive)).length := by
  native_decide

/--
No gender distinctions in pronouns is the majority pattern (254/378 = 67.2%).
When gender is present, 3rd-person-singular-only is the most common locus.
-/
theorem noGender_is_majority_ch44 :
    (ch44.filter (·.value == .noGenderDistinctions)).length >
    (ch44.filter (·.value == .v3rdPersonSingularOnly)).length +
    (ch44.filter (·.value == .v3rdPersonOnlyButAlsoNonSingular)).length +
    (ch44.filter (·.value == .in3rdPerson1stAndOr2ndPerson)).length := by
  native_decide

/--
Most languages lack politeness distinctions in pronouns (136/207 = 65.7%).
-/
theorem noPoliteness_is_majority_ch45 :
    (ch45.filter (·.value == .noPolitenessDistinction)).length >
    (ch45.filter (·.value == .binaryPolitenessDistinction)).length +
    (ch45.filter (·.value == .multiplePolitenessDistinctions)).length +
    (ch45.filter (·.value == .pronounsAvoidedForPoliteness)).length := by
  native_decide

/--
Interrogative-based indefinites are the most common strategy (194/326 = 59.5%),
reflecting the cross-linguistically robust interrogative--indefinite connection.
-/
theorem interrogativeBased_is_majority_ch46 :
    (ch46.filter (·.value == .interrogativeBased)).length >
    (ch46.filter (·.value == .genericNounBased)).length ∧
    (ch46.filter (·.value == .interrogativeBased)).length >
    (ch46.filter (·.value == .special)).length +
    (ch46.filter (·.value == .mixed)).length +
    (ch46.filter (·.value == .existentialConstruction)).length := by
  native_decide

/--
Languages split nearly evenly on whether intensifiers and reflexives are
identical (94) or differentiated (74), with a slight majority using
identical forms.
-/
theorem intensifier_reflexive_near_even :
    (ch47.filter (·.value == .identical)).length >
    (ch47.filter (·.value == .differentiated)).length ∧
    (ch47.filter (·.value == .differentiated)).length * 2 >
    (ch47.filter (·.value == .identical)).length := by
  native_decide

end Phenomena.Pronouns.Typology
