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
import Linglib.Core.Word
import Linglib.Features.Case
import Linglib.Features.Register
import Linglib.Features.Prominence
import Linglib.Features.Gender
import Linglib.Features.Clusivity
import Mathlib.Order.Basic

/-!
# Pronoun

Descriptive substrate for the pronoun as a grammatical object, gathering its
facets: the lexical `Entry` schema fragments instantiate, the structural
`Strength` (deficiency) classification, and the cross-linguistic typological
survey (per-language `Profile` + phonological-shape patterns).

Cross-categorial features a pronoun carries — `Person`, `Number`, `Gender`,
`Case` — are not redefined here; they live under `Features/` and are composed
in as `Entry` fields.

## Main declarations

* `Pronoun.Entry` — cross-linguistic lexical pronoun entry (form + features).
* `Pronoun.Strength` — @cite{cardinaletti-starke-1999} strong/weak/clitic
  deficiency order. Orthogonal to @cite{dechaine-wiltschko-2002}'s categorial
  pro-DP/φP/NP axis; a framework's structural account of the order stays in its
  study file.
* `Pronoun.Profile` — per-language pronoun-system survey across @cite{wals-2013}
  Chs 39–48 (incl/excl, gender, politeness, indefinite strategy,
  intensifier–reflexive, adpositional person marking).
* `Pronoun.AllocutiveEntry` — speaker–addressee (allocutive) markers.

## Implementation notes

The typological survey is a *facet* of the pronoun object, hence `Pronoun.Profile`
rather than a parent `Typology.` namespace. Phonological-shape patterns (M-T, N-M;
@cite{nichols-peterson-2013}) and allocutive markers are likewise co-located facets.
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

/-! ### Structural deficiency (@cite{cardinaletti-starke-1999}) -/

namespace Pronoun

/-- @cite{cardinaletti-starke-1999}'s three pronoun classes, ordered by
    structural deficiency (strong > weak > clitic). Framework-neutral: only the
    ranking lives here, and it is orthogonal to @cite{dechaine-wiltschko-2002}'s
    pro-DP/pro-φP/pro-NP categorial axis. A framework's structural account of
    the ranking stays in its study file (e.g. @cite{patel-grosz-grosz-2017}). -/
inductive Strength where
  /-- Full, stressed forms (e.g., English *me*, French *moi*). -/
  | strong
  /-- Reduced, unstressed but phonologically independent (e.g., German *es*). -/
  | weak
  /-- Phonologically deficient, attached to a host (e.g., French *me*, *te*, *le*). -/
  | clitic
  deriving DecidableEq, Repr

/-- Structural-richness rank: 2 (strong, least deficient) to 0 (clitic, most
    deficient). The @cite{cardinaletti-starke-1999} deficiency hierarchy is the
    reverse order. -/
def Strength.rank : Strength → Nat
  | .strong => 2
  | .weak   => 1
  | .clitic => 0

theorem Strength.rank_injective : Function.Injective Strength.rank := by
  intro a b h; cases a <;> cases b <;> simp_all [Strength.rank]

/-- Total order via the rank pullback (clitic < weak < strong), mirroring
    `LinearOrder AccessibilityLevel` in `Features/Accessibility.lean`. -/
instance : LinearOrder Strength :=
  LinearOrder.lift' Strength.rank Strength.rank_injective

end Pronoun

-- ============================================================================
-- WALS converters (Chs 39, 39B, 40, 44–48)
-- ============================================================================

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

-- ============================================================================
-- WALS chapter abbrevs + size theorems + distribution + generalizations
-- ============================================================================

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

-- ============================================================================
-- Pronoun phonological shape — WALS Chs 136, 137 @cite{nichols-peterson-2013}
-- ============================================================================

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
  deriving Repr

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

-- ════════════════════════════════════════════════════
-- § N. Cross-linguistic Pronoun Entry Schemas
-- ════════════════════════════════════════════════════

/-! ## Cross-linguistic pronoun and allocutive entry schemas
@cite{alok-bhalla-2026} @cite{arnold-2026}

Cross-linguistic structures for pronoun inventories and allocutive markers,
shared across all `Fragments/{Lang}/Pronouns.lean` files.

Moved here from `Core/Lexical/Pronouns.lean` in the cleanup that
dissolved `Core/Lexical/`. The 21-consumer footprint (20 Fragments + 1
Phenomena study) is precisely the per-language entry-schema pattern
this file already serves for WALS-anchored substrate enums.

### Entry

Covers the union of fields needed by all language fragments:
- Core: form, person, number (all fragments)
- Morphosyntactic: case_, gender (Galician, English, French, etc.)
- Sociolinguistic: register (all SA-based fragments)
- Orthographic: script (Korean hangul, Japanese kanji)

### Spec

Personal pronoun specification — which pronouns a person uses. A
social-linguistic fact independent of grammatical gender.
@cite{arnold-2026}'s pragmatic condition for *personal* singular *they*:
referent's pronouns are known to be *they/them*.

### AllocutiveEntry

Verbal suffixes (Hindi, Magahi, Maithili, Punjabi, Tamil, Basque),
particles (Korean, Japanese), or clitics (Galician) realising
speaker-addressee agreement. -/

namespace Pronoun

open Features.Register (Level)
open Features (SurfaceGender)

/-- Personal pronoun specification — which pronouns a person uses.

    A social-linguistic fact that may or may not be in common ground.
    Independent of grammatical gender: a person with known feminine
    gender may use she/her, they/them, or neopronouns.
    @cite{arnold-2026}: the pragmatic condition for *personal*
    singular *they* is knowing that the referent's personal pronouns
    are *they/them*. -/
inductive Spec where
  | heHim      -- he/him/his
  | sheHer     -- she/her/hers
  | theyThem   -- they/them/theirs
  deriving DecidableEq, Repr, BEq

/-- Cross-linguistic pronoun entry.

Covers personal pronouns across all Fragment languages. Language-specific
extensions (e.g., English PronounType/wh) remain in their respective
Fragment files. -/
structure Entry where
  /-- Surface form (romanization or orthographic) -/
  form : String
  /-- Grammatical person (UD.Person via Core.Word abbrev) -/
  person : Option Person := none
  /-- Grammatical number -/
  number : Option Number := none
  /-- Grammatical case -/
  case_ : Option Features.Case := none
  /-- Grammatical gender. For 3rd-person pronouns in gendered languages
      (French il/elle, German er/sie/es, etc.). 1st/2nd-person pronouns
      and languages without pronominal gender leave this as `none`. -/
  gender : Option SurfaceGender := none
  /-- Register level (formality/honorifics). Binary T/V systems use
      `.informal`/`.formal`; ternary honorific systems (Hindi, Magahi,
      Maithili, Korean) use all three levels. -/
  register : Level := .informal
  /-- Referential person — who the pronoun refers to in terms of discourse
      role — when it diverges from formal/agreement person. For polite
      pronouns (Italian LEI, Spanish USTED, German SIE), the formal `person`
      field is 3rd (governing agreement, clitic allomorphy, reflexive binding),
      while `referentialPerson` is 2nd (governing the PCC, Fancy Constraint,
      resolved agreement). For ordinary pronouns, leave as `none` —
      referential person coincides with formal person.
      @cite{adamson-zompi-2025} -/
  referentialPerson : Option Features.Prominence.PersonLevel := none
  /-- Native script form (hangul, kanji, Devanagari, etc.) -/
  script : Option String := none
  deriving Repr, BEq

/-- Cross-linguistic allocutive marker entry.

Covers verbal suffixes, particles, and clitics that realize allocutive
agreement across all Fragment languages. -/
structure AllocutiveEntry where
  /-- Surface form of the marker -/
  form : String
  /-- Register level (matching Entry.register scale) -/
  register : Level
  /-- Gloss string (e.g., "IMP.NH", "POL", "2sg.DAT.fam") -/
  gloss : String
  deriving Repr, BEq

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

