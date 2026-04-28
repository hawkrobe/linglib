import Linglib.Datasets.WALS.Features.F37A
import Linglib.Datasets.WALS.Features.F38A
import Linglib.Datasets.WALS.Features.F41A
import Linglib.Datasets.WALS.Features.F42A
import Linglib.Datasets.WALS.Features.F43A

/-!
# Article-and-demonstrative typology — substrate types and WALS data
@cite{wals-2013} (Chs 37, 38, 41, 42, 43)
@cite{bhat-2013} @cite{diessel-2013} @cite{dryer-haspelmath-2013}
@cite{greenberg-1978} @cite{himmelmann-1997}

Type-level enums + per-language profile struct for definiteness marking,
indefinite articles, and demonstrative systems across @cite{wals-2013}
chapters 37, 38, 41, 42, 43, plus WALS distribution data, the principal
cross-linguistic generalizations, and the demonstrative→article→affix
grammaticalization cline.

## Schema

- `DefiniteArticleType` (Ch 37): how (or whether) definiteness is marked
- `IndefiniteArticleType` (Ch 38): indefinite article strategy
- `DemDistanceSystem` (Ch 41): number of distance contrasts
- `DemOrientationType`: distance- vs person-oriented (for 3-way systems)
- `DemFormRelation` (Ch 42): pronominal vs adnominal demonstrative form
- `PronounDemRelation` (Ch 43): 3rd-pronoun ↔ demonstrative relationship
- `ArticleDemProfile`: per-language bundle (all five chapters)
- `GrammaticalizationStage`: stages of definiteness grammaticalization

Per-language data lives in `Fragments/{Lang}/Reference.lean`.
-/

set_option autoImplicit false

namespace Typology

-- ============================================================================
-- WALS Ch 37: Definite articles
-- ============================================================================

/-- Definite article type (WALS Ch 37, @cite{dryer-haspelmath-2013}).
    Categories ordered along the grammaticalization cline:
    demonstrative → definite word → definite affix. -/
inductive DefiniteArticleType where
  /-- Definite word distinct from demonstratives (e.g., English *the*). -/
  | definiteWord
  /-- Definite affix on the noun (e.g., Danish *-en*, Arabic *al-*). -/
  | definiteAffix
  /-- No dedicated definite article; a demonstrative is used for
      definiteness (e.g., Ojibwa, Swahili). -/
  | demonstrativeUsed
  /-- No definite article, but language has an indefinite article. -/
  | noDefButIndef
  /-- Neither definite nor indefinite article. -/
  | noArticle
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 38: Indefinite articles
-- ============================================================================

/-- Indefinite article type (WALS Ch 38, @cite{dryer-haspelmath-2013}).
    Languages either have a dedicated indefinite word, use the numeral
    'one' as an indefinite (the most common grammaticalization path),
    have an indefinite affix, or lack indefinite articles entirely. -/
inductive IndefiniteArticleType where
  /-- Indefinite word distinct from the numeral 'one' (e.g., English *a*). -/
  | indefiniteWord
  /-- Numeral 'one' used as indefinite article (e.g., German *ein*). -/
  | numeralOne
  /-- Indefinite affix on noun. -/
  | indefiniteAffix
  /-- No indefinite article, but language has a definite article. -/
  | noIndefButDef
  /-- Neither indefinite nor definite article. -/
  | noArticle
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 41: Distance contrasts in demonstratives
-- ============================================================================

/-- Number of distance contrasts in adnominal demonstratives
    (WALS Ch 41, @cite{diessel-2013}). Two-way systems are by far the most
    common (54.3%), followed by three-way (37.6%). -/
inductive DemDistanceSystem where
  /-- No distance contrast (e.g., Modern German *dieser*). -/
  | noContrast
  /-- Two-way contrast: proximal vs distal (e.g., English *this*/*that*). -/
  | twoWay
  /-- Three-way contrast (e.g., Japanese *ko*/*so*/*a*, Latin *hic*/*iste*/*ille*). -/
  | threeWay
  /-- Four-way contrast (e.g., Hausa). -/
  | fourWay
  /-- Five or more distance contrasts. -/
  | fiveOrMore
  deriving DecidableEq, Repr

/-- Whether a three-way demonstrative system is distance- or person-oriented.
    @cite{diessel-2013}: about 2/3 of three-way systems are distance-oriented,
    1/3 person-oriented (e.g., Japanese is the canonical person-oriented system). -/
inductive DemOrientationType where
  /-- All terms encode distance from speaker (proximal/medial/distal). -/
  | distanceOriented
  /-- One term encodes proximity to the hearer
      (near-speaker / near-hearer / distal). -/
  | personOriented
  /-- Not applicable (system is not three-way). -/
  | notApplicable
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 42: Pronominal and adnominal demonstratives
-- ============================================================================

/-- Relationship between pronominal and adnominal demonstratives
    (WALS Ch 42, @cite{diessel-2013}). English uses the same forms;
    French uses different stems (*ce*/*cette* vs *celui*/*celle*);
    Turkish uses the same stems but different inflectional features. -/
inductive DemFormRelation where
  /-- Same forms for pronominal and adnominal use (e.g., English). -/
  | sameForms
  /-- Different stems (e.g., French *ce*/*celui*). -/
  | differentStems
  /-- Same stems but different inflectional features (e.g., Turkish). -/
  | differentInflection
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 43: Third-person pronouns and demonstratives
-- ============================================================================

/-- Relationship between third-person pronouns and demonstratives
    (WALS Ch 43, @cite{bhat-2013}). In "two-person languages", 3rd-person
    pronouns are demonstrative-derived; in "three-person languages", 3rd-person
    pronouns form an independent person paradigm. -/
inductive PronounDemRelation where
  /-- 3rd-person pronouns unrelated to demonstratives (e.g., Ainu, Polish). -/
  | unrelated
  /-- Related to all demonstratives (e.g., Basque). -/
  | relatedAll
  /-- Related specifically to remote/distal demonstratives
      (e.g., Eastern Armenian: 3sg *na* = distal *na*). -/
  | relatedRemote
  /-- Related specifically to non-remote (proximal/medial) demonstratives
      (e.g., Brahui). -/
  | relatedNonRemote
  /-- Related via shared gender/noun-class markers (e.g., Venda). -/
  | relatedGender
  /-- Demonstratives used as 3rd-person pronouns for nonhuman reference only
      (e.g., Jaqaru). -/
  | relatedNonhuman
  deriving DecidableEq, Repr

/-- Whether 3rd-person pronouns show ANY relationship to demonstratives
    (Bhat's "two-person" vs "three-person" distinction). -/
def PronounDemRelation.isRelated : PronounDemRelation → Bool
  | .unrelated => false
  | _ => true

-- ============================================================================
-- Per-language profile
-- ============================================================================

/-- A language's article-and-demonstrative profile across @cite{wals-2013}
    Chs 37, 38, 41, 42, 43. WALS samples vary by chapter, so each field
    is optional. -/
structure ArticleDemProfile where
  language : String
  family : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 37: definite article type. -/
  defArticle : Option DefiniteArticleType := none
  /-- Ch 38: indefinite article type. -/
  indefArticle : Option IndefiniteArticleType := none
  /-- Ch 41: distance contrasts in demonstratives. -/
  demDistance : Option DemDistanceSystem := none
  /-- Ch 41 subtype: distance- vs person-oriented (for three-way systems). -/
  demOrientation : Option DemOrientationType := none
  /-- Ch 42: pronominal vs adnominal demonstrative form. -/
  demFormType : Option DemFormRelation := none
  /-- Ch 43: 3rd-person pronoun ~ demonstrative relationship. -/
  pronDemRelation : Option PronounDemRelation := none
  deriving Repr

/-- Does this language have any form of definite marking
    (word, affix, or demonstrative used as definite)? -/
def ArticleDemProfile.hasDefinite (p : ArticleDemProfile) : Bool :=
  match p.defArticle with
  | some .definiteWord => true
  | some .definiteAffix => true
  | some .demonstrativeUsed => true
  | _ => false

/-- Does this language have any indefinite article (word, numeral 'one',
    or affix)? -/
def ArticleDemProfile.hasIndefinite (p : ArticleDemProfile) : Bool :=
  match p.indefArticle with
  | some .indefiniteWord => true
  | some .numeralOne => true
  | some .indefiniteAffix => true
  | _ => false

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert WALS 37A definite-article values into the substrate enum. -/
def fromWALS37A : Datasets.WALS.F37A.DefiniteArticleType → DefiniteArticleType
  | .definiteWordDistinctFromDemonstrative => .definiteWord
  | .demonstrativeWordUsedAsDefiniteArticle => .demonstrativeUsed
  | .definiteAffix => .definiteAffix
  | .noDefiniteButIndefiniteArticle => .noDefButIndef
  | .noDefiniteOrIndefiniteArticle => .noArticle

/-- Convert WALS 38A indefinite-article values into the substrate enum. -/
def fromWALS38A : Datasets.WALS.F38A.IndefiniteArticleType → IndefiniteArticleType
  | .indefiniteWordDistinctFromOne => .indefiniteWord
  | .indefiniteWordSameAsOne => .numeralOne
  | .indefiniteAffix => .indefiniteAffix
  | .noIndefiniteButDefiniteArticle => .noIndefButDef
  | .noDefiniteOrIndefiniteArticle => .noArticle

/-- Convert WALS 41A distance-contrast values into the substrate enum. -/
def fromWALS41A : Datasets.WALS.F41A.DistanceContrastsInDemonstratives → DemDistanceSystem
  | .noDistanceContrast => .noContrast
  | .twoWayContrast => .twoWay
  | .threeWayContrast => .threeWay
  | .fourWayContrast => .fourWay
  | .fiveWayContrast => .fiveOrMore

/-- Convert WALS 42A pronominal/adnominal-form values into the substrate enum. -/
def fromWALS42A : Datasets.WALS.F42A.PronominalAndAdnominalDemonstratives → DemFormRelation
  | .identical => .sameForms
  | .differentStem => .differentStems
  | .differentInflection => .differentInflection

/-- Convert WALS 43A 3rd-person-pronoun values into the substrate enum. -/
def fromWALS43A : Datasets.WALS.F43A.ThirdPersonPronounsAndDemonstratives → PronounDemRelation
  | .unrelated => .unrelated
  | .relatedForAllDemonstratives => .relatedAll
  | .relatedToRemoteDemonstratives => .relatedRemote
  | .relatedToNonRemoteDemonstratives => .relatedNonRemote
  | .relatedByGenderMarkers => .relatedGender
  | .relatedForNonHumanReference => .relatedNonhuman

-- ============================================================================
-- WALS distribution data
-- ============================================================================

/-- WALS Ch 37: definite article distribution (@cite{dryer-haspelmath-2013},
    n = 566). -/
structure DefiniteArticleCounts where
  definiteWord : Nat
  demonstrativeUsed : Nat
  definiteAffix : Nat
  noDefButIndef : Nat
  noArticle : Nat
  deriving Repr

def DefiniteArticleCounts.total (c : DefiniteArticleCounts) : Nat :=
  c.definiteWord + c.demonstrativeUsed + c.definiteAffix + c.noDefButIndef + c.noArticle

/-- WALS Ch 37 counts (566 languages). -/
def walsDefiniteArticle : DefiniteArticleCounts :=
  { definiteWord := 197
  , demonstrativeUsed := 56
  , definiteAffix := 84
  , noDefButIndef := 41
  , noArticle := 188 }

/-- WALS Ch 38: indefinite article distribution (@cite{dryer-haspelmath-2013},
    n = 473). -/
structure IndefiniteArticleCounts where
  indefiniteWord : Nat
  numeralOne : Nat
  indefiniteAffix : Nat
  noIndefButDef : Nat
  noArticle : Nat
  deriving Repr

def IndefiniteArticleCounts.total (c : IndefiniteArticleCounts) : Nat :=
  c.indefiniteWord + c.numeralOne + c.indefiniteAffix + c.noIndefButDef + c.noArticle

/-- WALS Ch 38 counts (473 languages). -/
def walsIndefiniteArticle : IndefiniteArticleCounts :=
  { indefiniteWord := 91
  , numeralOne := 90
  , indefiniteAffix := 23
  , noIndefButDef := 81
  , noArticle := 188 }

/-- WALS Ch 41: demonstrative distance contrasts (@cite{diessel-2013},
    n = 234). -/
structure DemDistanceCounts where
  noContrast : Nat
  twoWay : Nat
  threeWay : Nat
  fourWay : Nat
  fiveOrMore : Nat
  deriving Repr

def DemDistanceCounts.total (c : DemDistanceCounts) : Nat :=
  c.noContrast + c.twoWay + c.threeWay + c.fourWay + c.fiveOrMore

/-- WALS Ch 41 counts (234 languages). -/
def walsDemDistance : DemDistanceCounts :=
  { noContrast := 7
  , twoWay := 127
  , threeWay := 88
  , fourWay := 8
  , fiveOrMore := 4 }

/-- WALS Ch 42: pronominal/adnominal demonstrative form
    (@cite{diessel-2013}, n = 201). -/
structure DemFormCounts where
  sameForms : Nat
  differentStems : Nat
  differentInflection : Nat
  deriving Repr

def DemFormCounts.total (c : DemFormCounts) : Nat :=
  c.sameForms + c.differentStems + c.differentInflection

/-- WALS Ch 42 counts (201 languages). -/
def walsDemForm : DemFormCounts :=
  { sameForms := 143
  , differentStems := 37
  , differentInflection := 21 }

/-- WALS Ch 43: 3rd-person pronoun ~ demonstrative relationship
    (@cite{bhat-2013}, n = 225). -/
structure PronounDemCounts where
  unrelated : Nat
  relatedAll : Nat
  relatedRemote : Nat
  relatedNonRemote : Nat
  relatedGender : Nat
  relatedNonhuman : Nat
  deriving Repr

def PronounDemCounts.total (c : PronounDemCounts) : Nat :=
  c.unrelated + c.relatedAll + c.relatedRemote +
  c.relatedNonRemote + c.relatedGender + c.relatedNonhuman

/-- Total count of languages where 3rd-person pronouns show any
    relationship to demonstratives. -/
def PronounDemCounts.totalRelated (c : PronounDemCounts) : Nat :=
  c.relatedAll + c.relatedRemote + c.relatedNonRemote +
  c.relatedGender + c.relatedNonhuman

/-- WALS Ch 43 counts (225 languages). -/
def walsPronounDem : PronounDemCounts :=
  { unrelated := 100
  , relatedAll := 52
  , relatedRemote := 18
  , relatedNonRemote := 14
  , relatedGender := 24
  , relatedNonhuman := 17 }

-- ============================================================================
-- Cross-linguistic generalizations: demonstrative distance (Ch 41)
-- ============================================================================

/-- Two-way demonstrative systems (proximal/distal) are the most common type:
    127 of 234 languages (54.3%). @cite{diessel-2013}: "the vast majority of
    the world's languages employ two or three distance-marked demonstratives". -/
theorem twoWay_most_common :
    walsDemDistance.twoWay > walsDemDistance.threeWay ∧
    walsDemDistance.twoWay > walsDemDistance.fourWay ∧
    walsDemDistance.twoWay > walsDemDistance.fiveOrMore ∧
    walsDemDistance.twoWay > walsDemDistance.noContrast := by decide

/-- Two-way and three-way systems together account for over 90% of languages;
    one-way, four-way, and five-or-more systems together are under 10%. -/
theorem twoAndThreeWay_dominate :
    walsDemDistance.twoWay + walsDemDistance.threeWay >
    9 * (walsDemDistance.noContrast + walsDemDistance.fourWay + walsDemDistance.fiveOrMore) := by
  decide

-- ============================================================================
-- Cross-linguistic generalizations: definite/indefinite asymmetry (Ch 37/38)
-- ============================================================================

/-- Languages with definite articles tend to also have indefinite articles.
    The asymmetry: 81 languages have a definite but no indefinite article,
    vs. 41 languages with indefinite but no definite article. Definiteness
    marking is the typologically prior category. -/
theorem defArticle_more_robust_than_indef :
    walsIndefiniteArticle.noIndefButDef > walsDefiniteArticle.noDefButIndef := by decide

/-- Languages with some form of definite marking (word, affix, or demonstrative)
    outnumber those without. 337 of 566 languages (59.5%) have definite marking. -/
theorem majority_have_some_definite_marking :
    walsDefiniteArticle.definiteWord +
    walsDefiniteArticle.demonstrativeUsed +
    walsDefiniteArticle.definiteAffix >
    walsDefiniteArticle.noDefButIndef + walsDefiniteArticle.noArticle := by decide

-- ============================================================================
-- Cross-linguistic generalizations: 3rd pronoun ↔ demonstrative (Ch 43)
-- ============================================================================

/-- In a majority of languages (125 of 225 = 55.6%), 3rd-person pronouns show
    some relationship to demonstratives. Supports the diachronic pathway
    demonstrative → 3rd-person pronoun (@cite{bhat-2013}). -/
theorem majority_pronoun_dem_related :
    walsPronounDem.totalRelated > walsPronounDem.unrelated := by decide

/-- The most common subtype of pronoun-demonstrative relationship is "related
    to all demonstratives" (52 languages), where any demonstrative can serve
    as a 3rd-person pronoun. -/
theorem relatedAll_most_common_subtype :
    walsPronounDem.relatedAll > walsPronounDem.relatedRemote ∧
    walsPronounDem.relatedAll > walsPronounDem.relatedNonRemote ∧
    walsPronounDem.relatedAll > walsPronounDem.relatedGender ∧
    walsPronounDem.relatedAll > walsPronounDem.relatedNonhuman := by decide

-- ============================================================================
-- Cross-linguistic generalizations: pronominal/adnominal forms (Ch 42)
-- ============================================================================

/-- In most languages (143 of 201 = 71.1%), pronominal and adnominal
    demonstratives have the same forms (@cite{diessel-2013}). Differential
    marking via different stems (37) or different inflection (21) is the
    minority. -/
theorem sameForm_demonstratives_majority :
    walsDemForm.sameForms >
    walsDemForm.differentStems + walsDemForm.differentInflection := by decide

-- ============================================================================
-- Grammaticalization cline: demonstrative → article → affix
-- ============================================================================

/-- The grammaticalization hierarchy for definiteness marking
    (@cite{greenberg-1978}, @cite{himmelmann-1997}):

      Stage 0 — No definiteness marking (bare nouns; e.g., Mandarin, Russian)
      Stage 1 — Demonstrative used for definiteness (e.g., Swahili, Ojibwa)
      Stage 2 — Definite word distinct from demonstrative (e.g., English)
      Stage 3 — Definite affix (e.g., Danish, Arabic)

    Each stage represents further grammaticalization: phonological reduction,
    semantic bleaching (loss of deictic content), and increased obligatoriness. -/
inductive GrammaticalizationStage where
  | noMarking
  | demonstrative
  | definiteWord
  | definiteAffix
  deriving DecidableEq, Repr

/-- Map a `DefiniteArticleType` to its grammaticalization stage. -/
def DefiniteArticleType.stage : DefiniteArticleType → GrammaticalizationStage
  | .noArticle | .noDefButIndef => .noMarking
  | .demonstrativeUsed => .demonstrative
  | .definiteWord => .definiteWord
  | .definiteAffix => .definiteAffix

/-- Numeric rank for the grammaticalization stage (higher = more grammaticalized). -/
def GrammaticalizationStage.ord : GrammaticalizationStage → Nat
  | .noMarking => 0
  | .demonstrative => 1
  | .definiteWord => 2
  | .definiteAffix => 3

/-- All three intermediate stages of the grammaticalization cline are well
    attested cross-linguistically: 56 languages use demonstratives as definite
    markers (Stage 1), 197 have distinct definite words (Stage 2), and 84 have
    definite affixes (Stage 3). The transitional Stage 1 is smaller than both
    later stages. -/
theorem grammaticalization_cline_attested :
    walsDefiniteArticle.demonstrativeUsed > 0 ∧
    walsDefiniteArticle.definiteWord > 0 ∧
    walsDefiniteArticle.definiteAffix > 0 ∧
    walsDefiniteArticle.demonstrativeUsed < walsDefiniteArticle.definiteWord ∧
    walsDefiniteArticle.demonstrativeUsed < walsDefiniteArticle.definiteAffix := by decide

end Typology
