import Linglib.Core.Lexical.Word
import Linglib.Features.Definiteness
import Linglib.Core.Nominal.ArticleInventory
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Phenomena.Reference.DirectReference

/-!
# Pronoun Typology: PER/DEM Classification + Gradient Measures
@cite{cardinaletti-starke-1999} @cite{elbourne-2005} @cite{patel-grosz-grosz-2017} @cite{postal-1966} @cite{schwarz-2009} @cite{schwarz-2013} @cite{levshina-stoynova-2023}

@cite{patel-grosz-grosz-2017} "Revisiting Pronominal Typology" (LI 48(2)) argue
that 3rd-person pronouns split into two structural types:
- **PER** (personal): D_det + NP (weak article only)
- **DEM** (demonstrative): D_deix + D_det + NP (strong article)

Minimize DP! makes PER the default; DEM requires pragmatic licensing
(emotivity, disambiguation, register).

## Key Claims

1. If a language has DEM pronouns, it also has PER pronouns (DEM ⊂ PER)
2. DEM use requires pragmatic licensing (Minimize DP!)
3. Article system predicts D-layer structure

## Gradient Component

Following @cite{levshina-stoynova-2023} / `WordOrder/Gradience.lean`, we encode
continuous measures of pronoun system complexity: inventory sizes, licensing
context counts, and strength-level counts.

-/

namespace Phenomena.Anaphora.Typology

open Phenomena.Anaphora.Coreference

open Features.Definiteness (ArticleType DefiniteUseType BridgingSubtype WeakArticleStrategy
  useTypeToPresupType bridgingPresupType DefPresupType)
open Core.Nominal (ArticleInventory)

-- ============================================================================
-- §A: Inductive Types
-- ============================================================================

/-- @cite{patel-grosz-grosz-2017}: structural classification of 3rd-person pronouns.

PER pronouns project only D_det (weak article layer).
DEM pronouns project D_deix + D_det (strong article layer). -/
inductive PronounClass where
  | per   -- Personal: D_det + NP (weak article only)
  | dem   -- Demonstrative: D_deix + D_det + NP (strong article)
  deriving DecidableEq, Repr


/-- @cite{cardinaletti-starke-1999}: pronoun strength.

Three-way typology based on phonological/syntactic deficiency:
- Strong: full, stressed (can be coordinated, modified, focused)
- Weak: reduced, unstressed (cannot be coordinated/focused)
- Clitic: phonologically deficient, must attach to host -/
inductive PronounStrength where
  | strong  -- Full, stressed forms
  | weak    -- Reduced, unstressed
  | clitic  -- Phonologically deficient, attached to host
  deriving DecidableEq, Repr

/-- Pragmatic contexts that license DEM pronoun use (@cite{patel-grosz-grosz-2017} §3).

Minimize DP! requires DEM to be pragmatically licensed. These are the
five licensing contexts identified by PG&G. -/
inductive DEMLicensingContext where
  | emotivity       -- Emotional engagement with referent
  | disambiguation  -- Multiple potential antecedents
  | register        -- Colloquial/informal register
  | deixis          -- Spatial/temporal pointing
  | contrast        -- Contrastive topic/focus
  deriving DecidableEq, Repr

-- ============================================================================
-- §B: Per-Language Datum Structure
-- ============================================================================

/-- A 3rd-person pronoun form in a language's inventory. -/
structure PronounForm where
  form : String
  pronClass : PronounClass
  gender : Option String := none  -- "m"/"f"/"n" or none
  number : Option Number := none
  strengths : List PronounStrength := [.strong]
  deriving Repr, BEq

/-- Per-language pronoun system datum (@cite{patel-grosz-grosz-2017} + @cite{cardinaletti-starke-1999}).

Each datum records the full 3rd-person pronoun inventory, article inventory,
D-layer count, DEM licensing contexts, and DEM productivity. The article
system type (`articleType`) is *derived* from `articleInventory` rather than
stipulated — `Core.Nominal.ArticleInventory` is the single source of truth
for definiteness data. -/
structure PronounSystemDatum where
  language : String
  isoCode : String
  /-- Available 3rd-person pronoun forms -/
  forms : List PronounForm
  /-- Morphological article inventory (single source of truth from which
      `articleType` is derived). -/
  articleInventory : ArticleInventory
  /-- Number of D-layers: 1 = D_det only (PER), 2 = D_deix + D_det (PER+DEM) -/
  dLayers : Nat
  /-- Pragmatic contexts licensing DEM use (empty for PER-only languages) -/
  demLicensing : List DEMLicensingContext
  /-- Whether DEM pronouns are productive (freely usable) as 3rd-person reference -/
  demProductive : Bool

/-- Schwarz/Patel-Grosz–Grosz `ArticleType` classification, derived from the
    morphological inventory. Not stipulated — this is the projection of the
    inventory bools through `ArticleInventory.toArticleType`. -/
def PronounSystemDatum.articleType (d : PronounSystemDatum) : ArticleType :=
  d.articleInventory.toArticleType

-- ============================================================================
-- §C: Language Data (~11 languages from @cite{patel-grosz-grosz-2017})
-- ============================================================================

/-- Inventory shorthand: bipartite (German/Bavarian/Portuguese — distinct
    weak vs strong articles, no syncretism). Derives `.weakAndStrong`. -/
private def bipartiteInv : ArticleInventory :=
  { hasIndefinite := True, hasUniqueArticle := True
    hasAnaphoricArticle := True, uniqueAnaphoricSyncretism := False
    hasDemonstrative := True, hasPossessive := True }

/-- Inventory shorthand: syncretic single article (English/Romance — *the*,
    *le/la*, *il*, *el*, *o/a*, *ell*). Derives `.weakOnly` via
    `.generallyMarked`. -/
private def syncreticInv : ArticleInventory :=
  { hasIndefinite := True, hasUniqueArticle := True
    hasAnaphoricArticle := True, uniqueAnaphoricSyncretism := True
    hasDemonstrative := True, hasPossessive := True }

/-- Inventory shorthand: no overt articles (Hebrew/Czech/Finnish — no
    article paradigm). Derives `.none_` via `.unmarked`. -/
private def noArticleInv : ArticleInventory :=
  { hasIndefinite := False, hasUniqueArticle := False
    hasAnaphoricArticle := False, uniqueAnaphoricSyncretism := False
    hasDemonstrative := True, hasPossessive := True }

/-- Inventory shorthand: weak only (Kutchi Gujarati — single postnominal
    definite marker, no separate anaphoric form). Derives `.weakOnly` via
    `.generallyMarked`. -/
private def weakOnlyInv : ArticleInventory :=
  { hasIndefinite := False, hasUniqueArticle := True
    hasAnaphoricArticle := False, uniqueAnaphoricSyncretism := False
    hasDemonstrative := True, hasPossessive := True }

def germanData : PronounSystemDatum :=
  { language := "German", isoCode := "de"
    forms := [ ⟨"er",  .per, some "m", some .sg, [.strong, .weak]⟩
             , ⟨"sie", .per, some "f", some .sg, [.strong, .weak]⟩
             , ⟨"es",  .per, some "n", some .sg, [.strong, .weak]⟩
             , ⟨"der", .dem, some "m", some .sg, [.strong]⟩
             , ⟨"die", .dem, some "f", some .sg, [.strong]⟩
             , ⟨"das", .dem, some "n", some .sg, [.strong]⟩ ]
    articleInventory := bipartiteInv
    dLayers := 2
    demLicensing := [.emotivity, .disambiguation, .register, .deixis, .contrast]
    demProductive := true }

def bavarianData : PronounSystemDatum :=
  { language := "Bavarian", isoCode := "bar"
    forms := [ ⟨"er",  .per, some "m", some .sg, [.strong, .weak]⟩
             , ⟨"sie", .per, some "f", some .sg, [.strong, .weak]⟩
             , ⟨"es",  .per, some "n", some .sg, [.strong, .weak]⟩
             , ⟨"der", .dem, some "m", some .sg, [.strong]⟩
             , ⟨"die", .dem, some "f", some .sg, [.strong]⟩
             , ⟨"des", .dem, some "n", some .sg, [.strong]⟩ ]
    articleInventory := bipartiteInv
    dLayers := 2
    demLicensing := [.emotivity, .disambiguation, .register, .deixis, .contrast]
    demProductive := true }

def portugueseData : PronounSystemDatum :=
  { language := "Portuguese", isoCode := "pt"
    forms := [ ⟨"ele",    .per, some "m", some .sg, [.strong]⟩
             , ⟨"ela",    .per, some "f", some .sg, [.strong]⟩
             , ⟨"esse",   .dem, some "m", some .sg, [.strong]⟩
             , ⟨"aquele", .dem, some "m", some .sg, [.strong]⟩ ]
    articleInventory := bipartiteInv
    dLayers := 2
    demLicensing := [.deixis, .contrast]
    demProductive := false }

def hebrewData : PronounSystemDatum :=
  { language := "Hebrew", isoCode := "he"
    forms := [ ⟨"hu", .per, some "m", some .sg, [.strong]⟩
             , ⟨"hi", .per, some "f", some .sg, [.strong]⟩
             , ⟨"ze", .dem, some "m", some .sg, [.strong]⟩
             , ⟨"zo", .dem, some "f", some .sg, [.strong]⟩ ]
    articleInventory := noArticleInv
    dLayers := 2
    demLicensing := [.deixis, .disambiguation]
    demProductive := false }

def czechData : PronounSystemDatum :=
  { language := "Czech", isoCode := "cs"
    forms := [ ⟨"on",  .per, some "m", some .sg, [.strong, .weak, .clitic]⟩
             , ⟨"ona", .per, some "f", some .sg, [.strong, .weak, .clitic]⟩
             , ⟨"ono", .per, some "n", some .sg, [.strong, .weak, .clitic]⟩
             , ⟨"ten", .dem, some "m", some .sg, [.strong]⟩
             , ⟨"ta",  .dem, some "f", some .sg, [.strong]⟩
             , ⟨"to",  .dem, some "n", some .sg, [.strong]⟩ ]
    articleInventory := noArticleInv
    dLayers := 2
    demLicensing := [.emotivity, .disambiguation, .contrast]
    demProductive := false }

def frenchData : PronounSystemDatum :=
  { language := "French", isoCode := "fr"
    forms := [ ⟨"il",   .per, some "m", some .sg, [.strong, .weak, .clitic]⟩
             , ⟨"elle", .per, some "f", some .sg, [.strong, .weak, .clitic]⟩ ]
    articleInventory := syncreticInv
    dLayers := 1
    demLicensing := []
    demProductive := false }

def italianData : PronounSystemDatum :=
  { language := "Italian", isoCode := "it"
    forms := [ ⟨"lui", .per, some "m", some .sg, [.strong, .weak, .clitic]⟩
             , ⟨"lei", .per, some "f", some .sg, [.strong, .weak, .clitic]⟩ ]
    articleInventory := syncreticInv
    dLayers := 1
    demLicensing := []
    demProductive := false }

def spanishData : PronounSystemDatum :=
  { language := "Spanish", isoCode := "es"
    forms := [ ⟨"él",   .per, some "m", some .sg, [.strong, .weak, .clitic]⟩
             , ⟨"ella", .per, some "f", some .sg, [.strong, .weak, .clitic]⟩ ]
    articleInventory := syncreticInv
    dLayers := 1
    demLicensing := []
    demProductive := false }

def catalanData : PronounSystemDatum :=
  { language := "Catalan", isoCode := "ca"
    forms := [ ⟨"ell",  .per, some "m", some .sg, [.strong, .weak, .clitic]⟩
             , ⟨"ella", .per, some "f", some .sg, [.strong, .weak, .clitic]⟩ ]
    articleInventory := syncreticInv
    dLayers := 1
    demLicensing := []
    demProductive := false }

def kutchiGujaratiData : PronounSystemDatum :=
  { language := "Kutchi Gujarati", isoCode := "gju"
    forms := [ ⟨"a",  .per, none, some .sg, [.strong]⟩
             , ⟨"ā",  .per, none, some .pl, [.strong]⟩ ]
    articleInventory := weakOnlyInv
    dLayers := 1
    demLicensing := []
    demProductive := false }

def englishData : PronounSystemDatum :=
  { language := "English", isoCode := "en"
    forms := [ ⟨"he",  .per, some "m", some .sg, [.strong]⟩
             , ⟨"she", .per, some "f", some .sg, [.strong]⟩
             , ⟨"it",  .per, some "n", some .sg, [.strong]⟩ ]
    articleInventory := syncreticInv
    dLayers := 1
    demLicensing := []
    demProductive := false }

/-- All 11 languages from @cite{patel-grosz-grosz-2017} survey. -/
def allData : List PronounSystemDatum :=
  [ germanData, bavarianData, portugueseData, hebrewData, czechData
  , frenchData, italianData, spanishData, catalanData, kutchiGujaratiData
  , englishData ]

theorem allData_count : allData.length = 11 := by native_decide

/-- Finnish: "hän" (3sg human, PER, no gender), "he" (3pl human, PER),
    "se" (3sg non-human / DEM), "tämä" (proximal DEM), "tuo" (distal DEM).
    No articles. "se" is productively used as 3rd-person reference in
    colloquial Finnish.
    Not part of @cite{patel-grosz-grosz-2017} sample — a counterexample to the article-DEM
    productivity correlation (2 D-layers, productive DEM, but no articles). -/
def finnishData : PronounSystemDatum :=
  { language := "Finnish", isoCode := "fi"
    forms := [ ⟨"hän",  .per, none, some .sg, [.strong]⟩
             , ⟨"he",   .per, none, some .pl, [.strong]⟩
             , ⟨"se",   .dem, none, some .sg, [.strong]⟩
             , ⟨"tämä", .dem, none, some .sg, [.strong]⟩
             , ⟨"tuo",  .dem, none, some .sg, [.strong]⟩ ]
    articleInventory := noArticleInv
    dLayers := 2
    demLicensing := [.deixis, .contrast]
    demProductive := true }

-- ============================================================================
-- §D: Gradient Measures (following WordOrder/Gradience.lean pattern)
-- ============================================================================

/-- Gradient pronoun system profile, analogous to `GradientWOProfile`.

Captures continuous variation in pronoun system complexity across languages. -/
structure PronounComplexityProfile where
  name : String
  isoCode : String
  /-- Number of distinct PER pronoun forms -/
  perInventory : Nat
  /-- Number of distinct DEM pronoun forms usable as pronouns -/
  demInventory : Nat
  /-- Number of pragmatic contexts licensing DEM use (0–5 scale) -/
  demLicensingCount : Nat
  /-- Pronoun strength levels available: 1=strong only, 2=strong+weak, 3=strong+weak+clitic -/
  strengthLevels : Nat
  deriving Repr, DecidableEq

/-- Compute gradient profile from a `PronounSystemDatum`. -/
def PronounSystemDatum.toProfile (d : PronounSystemDatum) : PronounComplexityProfile :=
  let perForms := d.forms.filter (·.pronClass == .per)
  let demForms := d.forms.filter (·.pronClass == .dem)
  let allStrengths : List PronounStrength := d.forms.flatMap (·.strengths)
  let hasClitic : Bool := allStrengths.any (· == .clitic)
  let hasWeak : Bool := allStrengths.any (· == .weak)
  let levels := 1 + (if hasWeak then 1 else 0) + (if hasClitic then 1 else 0)
  { name := d.language
    isoCode := d.isoCode
    perInventory := perForms.length
    demInventory := demForms.length
    demLicensingCount := d.demLicensing.length
    strengthLevels := levels }

def germanProfile : PronounComplexityProfile := germanData.toProfile
def bavarianProfile : PronounComplexityProfile := bavarianData.toProfile
def portugueseProfile : PronounComplexityProfile := portugueseData.toProfile
def hebrewProfile : PronounComplexityProfile := hebrewData.toProfile
def czechProfile : PronounComplexityProfile := czechData.toProfile
def frenchProfile : PronounComplexityProfile := frenchData.toProfile
def italianProfile : PronounComplexityProfile := italianData.toProfile
def spanishProfile : PronounComplexityProfile := spanishData.toProfile
def catalanProfile : PronounComplexityProfile := catalanData.toProfile
def kutchiGujaratiProfile : PronounComplexityProfile := kutchiGujaratiData.toProfile
def englishProfile : PronounComplexityProfile := englishData.toProfile

/-- All 11 gradient pronoun system profiles. -/
def allProfiles : List PronounComplexityProfile :=
  [ germanProfile, bavarianProfile, portugueseProfile, hebrewProfile, czechProfile
  , frenchProfile, italianProfile, spanishProfile, catalanProfile
  , kutchiGujaratiProfile, englishProfile ]

theorem allProfiles_count : allProfiles.length = 11 := by native_decide

def finnishProfile : PronounComplexityProfile := finnishData.toProfile

/-- Finnish has productive DEM with no articles — a counterexample to the
    PG&G sample's dem_productivity_from_article_system generalization. -/
theorem finnish_counterexample_to_article_dem :
    finnishData.dLayers == 2 ∧ finnishData.demProductive ∧
    finnishData.articleType == .none_ := by native_decide

-- ============================================================================
-- §E: Verified Generalizations
-- ============================================================================

/-! ### PG&G Core Claims -/

/-- **Minimize DP!** (@cite{patel-grosz-grosz-2017} §3): Languages where DEM is productive
all require pragmatic licensing (demLicensing is non-empty).

DEM is the marked choice; PER is the default. -/
theorem minimize_dp :
    (allData.filter (·.demProductive)).all
      (·.demLicensing.length > 0) = true := by native_decide

/-- **Implicational universal**: If DEM exists in a language's inventory,
PER also exists. No language has DEM without PER.

This follows from PG&G's structural claim: DEM = D_deix + D_det + NP,
where D_det is the PER layer. DEM presupposes PER structurally. -/
theorem dem_implies_per :
    allData.all (λ d =>
      if d.forms.any (·.pronClass == .dem)
      then d.forms.any (·.pronClass == .per)
      else true) = true := by native_decide

/-- **Article-D-layer correlation** (@cite{schwarz-2009} → PG&G):
Languages with both weak and strong articles have 2 D-layers. -/
theorem strong_article_two_layers :
    (allData.filter (·.articleType == .weakAndStrong)).all
      (·.dLayers == 2) = true := by native_decide

/-- PER-only languages (1 D-layer) have only weak or no articles.
The converse of `strong_article_two_layers`. -/
theorem one_layer_no_strong_articles :
    (allData.filter (·.dLayers == 1)).all
      (·.articleType != .weakAndStrong) = true := by native_decide

/-! ### Gradient Claims -/

/-- **PER inventory is continuous**: ranges from 2 (Kutchi Gujarati)
to 3 (most languages with m/f/n), not a binary split. -/
theorem per_inventory_range :
    kutchiGujaratiProfile.perInventory = 2 ∧
    germanProfile.perInventory = 3 ∧
    allProfiles.all (·.perInventory ≥ 2) = true := by native_decide

/-- **DEM inventory correlates with article system**: languages with
weakAndStrong articles have non-zero DEM inventory. -/
theorem strong_articles_have_dem_forms :
    (allData.filter (·.articleType == .weakAndStrong)).all
      (λ d => (d.forms.filter (·.pronClass == .dem)).length > 0) = true := by native_decide

/-- **Strength levels vary**: Romance languages (French, Italian, Spanish, Catalan)
have 3 strength levels (strong+weak+clitic), while Germanic typically has 2. -/
theorem romance_three_strength_levels :
    let romance := [frenchProfile, italianProfile, spanishProfile, catalanProfile]
    romance.all (·.strengthLevels == 3) = true := by native_decide

/-- Germanic languages with DEM (German, Bavarian) have 2 strength levels. -/
theorem germanic_two_strength_levels :
    let germanic := [germanProfile, bavarianProfile]
    germanic.all (·.strengthLevels == 2) = true := by native_decide

/-- DEM licensing count ranges from 0 to 5, forming a continuum
rather than a binary productive/non-productive distinction. -/
theorem dem_licensing_is_gradient :
    englishProfile.demLicensingCount = 0 ∧
    germanProfile.demLicensingCount = 5 ∧
    allProfiles.any (·.demLicensingCount == 2) = true ∧
    allProfiles.any (·.demLicensingCount == 3) = true := by native_decide

/-! ### Open Problem -/

/-- **DEM productivity tracks overt strong articles** (pattern in PG&G data):

Among 2-layer languages, only those with overt weak+strong article
morphology (German, Bavarian) have productive DEM. Languages with
2 D-layers but no overt articles (Hebrew, Czech) or limited article
systems restrict DEM.

@cite{schwarz-2013} §5.5 provides the theoretical link: the strong article
conventionalizes the D_deix layer, making DEM pronouns (which also
project D_deix) more accessible. Without overt strong articles, D_deix
is available syntactically but not conventionalized for reference tracking.

Open question: *why* does article-system conventionalization affect pronoun
productivity? PG&G suggest familiarity/frequency; @cite{schwarz-2013} suggests
the strong article's anaphoric function naturally extends to pronominal use. -/
theorem dem_productivity_from_article_system :
    (allData.filter (λ d => d.dLayers == 2 ∧ d.demProductive)).all
      (·.articleType == .weakAndStrong) = true := by native_decide

-- ============================================================================
-- §F: @cite{schwarz-2013} Article Typology
-- ============================================================================

/-! ### Definite use types (@cite{hawkins-1978}, @cite{schwarz-2013} §2.1)

Types and mappings are defined in `Features/Definiteness.lean`:
`DefiniteUseType`, `BridgingSubtype`, `useTypeToPresupType`, `bridgingPresupType`. -/

/-! ### @cite{schwarz-2013} cross-linguistic article paradigm data -/


/-- Per-language article paradigm from @cite{schwarz-2013}. -/
structure SchwarzArticleDatum where
  language : String
  isoCode : String
  /-- Morphological form of the strong article (if any) -/
  strongForm : Option String
  /-- Morphological form of the weak article (if any) -/
  weakForm : Option String
  /-- How weak definites are expressed -/
  weakStrategy : WeakArticleStrategy
  /-- Strong article used for anaphoric definites -/
  strongForAnaphoric : Bool
  /-- Weak article/bare nominal used for uniqueness/situational -/
  weakForUniqueness : Bool
  /-- Bridging shows the split (part-whole = weak, producer = strong) -/
  bridgingSplit : Bool
  deriving Repr, BEq

-- Germanic (@cite{schwarz-2013} §3)

def schwarz_german : SchwarzArticleDatum :=
  { language := "German", isoCode := "de"
    strongForm := some "dem"     -- full/uncontracted: von dem
    weakForm := some "vom"       -- contracted: vom = von + dem
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §3.1.1: ex. (9)
    weakForUniqueness := true    -- §3.1.2: ex. (15)
    bridgingSplit := true }      -- §3.2: ex. (16a) weak, (16b) strong

def schwarz_fering : SchwarzArticleDatum :=
  { language := "Fering", isoCode := "frr"
    strongForm := some "di/det"  -- Ebert's D-form: di (m), det (f/n)
    weakForm := some "a/at"      -- Ebert's A-form: a (m/pl), at (f/n)
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §3.1.1: ex. (8)
    weakForUniqueness := true    -- §3.1.2: ex. (13), (14)
    bridgingSplit := true }      -- §3.2: ex. (17a) weak, (17b) strong

-- Non-Germanic with strong article only (@cite{schwarz-2013} §4.1)

def schwarz_akan : SchwarzArticleDatum :=
  { language := "Akan", isoCode := "ak"
    strongForm := some "nó"      -- strong article / Fam marker
    weakForm := none              -- bare nominal for weak definites
    weakStrategy := .bareNominal
    strongForAnaphoric := true   -- §4.1.1: ex. (18b), (19)
    weakForUniqueness := true    -- §4.1.1: bare nominals for situation uses, ex. (22)
    bridgingSplit := true }      -- §4.1.1: producer bridging takes nó, ex. (23)

def schwarz_mauritianCreole : SchwarzArticleDatum :=
  { language := "Mauritian Creole", isoCode := "mfe"
    strongForm := some "la"      -- post-nominal clitic
    weakForm := none              -- bare nominal for weak definites
    weakStrategy := .bareNominal
    strongForAnaphoric := true   -- §4.1.2: ex. (25)
    weakForUniqueness := true    -- §4.1.2: bare nominals, ex. (26)
    bridgingSplit := true }      -- §4.1.2: ex. (28)/(29)

-- Languages with two overt articles (@cite{schwarz-2013} §4.2)

def schwarz_lakhota : SchwarzArticleDatum :=
  { language := "Lakhota", isoCode := "lkt"
    strongForm := some "k'uŋ"   -- anaphoric/previously-mentioned
    weakForm := some "kiŋ"       -- situational uniqueness
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §4.2.1: ex. (32), (33)
    weakForUniqueness := true    -- §4.2.1: ex. (30), (31)
    bridgingSplit := true }      -- §4.2.1: ex. (34) weak for part-whole

def schwarz_hausa : SchwarzArticleDatum :=
  { language := "Hausa", isoCode := "ha"
    strongForm := some "ɗîn"    -- anaphoric determiner
    weakForm := some "-n"        -- suffixal weak article
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §4.2.2: ex. (37) ɗîn for anaphoric
    weakForUniqueness := true    -- §4.2.2: ex. (36) -n for uniqueness
    bridgingSplit := false }     -- insufficient data in @cite{schwarz-2013}

-- Exceptional: single form for both uses (@cite{schwarz-2013} §4.3)

def schwarz_haitianCreole : SchwarzArticleDatum :=
  { language := "Haitian Creole", isoCode := "ht"
    strongForm := some "la"      -- used for all definite types
    weakForm := some "la"         -- same form
    weakStrategy := .sameAsStrong
    strongForAnaphoric := true   -- §4.3: ex. (40)
    weakForUniqueness := true    -- §4.3: ex. (39)
    bridgingSplit := false }     -- §4.3: la used for both bridging types

/-- All 7 languages from @cite{schwarz-2013} survey. -/
def allSchwarzData : List SchwarzArticleDatum :=
  [ schwarz_german, schwarz_fering, schwarz_akan, schwarz_mauritianCreole
  , schwarz_lakhota, schwarz_hausa, schwarz_haitianCreole ]

theorem allSchwarzData_count : allSchwarzData.length = 7 := by native_decide

/-! ### @cite{schwarz-2013} verified generalizations -/

/-- **Strong article → anaphoric use** (@cite{schwarz-2013} §3.1.1):
All surveyed languages use the strong article for anaphoric definites. -/
theorem strong_for_anaphoric :
    allSchwarzData.all (·.strongForAnaphoric) = true := by native_decide

/-- **Weak form → uniqueness/situational use** (@cite{schwarz-2013} §3.1.2):
All surveyed languages use weak articles (or bare nominals) for
uniqueness-based definites. -/
theorem weak_for_uniqueness :
    allSchwarzData.all (·.weakForUniqueness) = true := by native_decide

/-- **Bridging split** (@cite{schwarz-2013} §3.2): Most languages split bridging
across article forms (part-whole = weak, producer = strong). 5 of 7
languages show this pattern; Hausa lacks data, and Haitian Creole
uses a single form for everything. -/
theorem bridging_split_is_majority :
    (allSchwarzData.filter (·.bridgingSplit)).length = 5 := by native_decide

/-- **Bare-nominal strategy** (@cite{schwarz-2013} §4.1): Languages with only
one overt article form (Akan, Mauritian Creole) use bare nominals
for weak-article definites. -/
theorem bare_nominal_languages :
    (allSchwarzData.filter (·.weakStrategy == .bareNominal)).length = 2 := by native_decide

/-- **Haitian Creole is exceptional** (@cite{schwarz-2013} §4.3): single determiner
`la` for both anaphoric and uniqueness uses — no weak/strong split. -/
theorem haitian_creole_no_split :
    schwarz_haitianCreole.weakStrategy == .sameAsStrong := by native_decide

/-! ### Bridge: Schwarz article types ↔ PG&G pronoun D-layers

@cite{schwarz-2013} §5.5 explicitly connects the article contrast to
pronouns: "pronouns are definite articles without overt NP". German d-pronouns (der/die/das) are identical
to strong articles. The pronominal domain shows parallel contrasts
(/2007, /2011).

The structural mapping:
- Schwarz weak article = PG&G D_det layer = PER pronoun
- Schwarz strong article = PG&G D_deix + D_det = DEM pronoun -/

/-- Languages with two overt article forms in @cite{schwarz-2013} correspond to
2-D-layer languages in @cite{patel-grosz-grosz-2017}. Verified for German, which appears
in both datasets. -/
theorem schwarz_pgg_german_consistent :
    schwarz_german.strongForm.isSome ∧
    schwarz_german.weakForm.isSome ∧
    germanData.dLayers == 2 ∧
    germanData.articleType == .weakAndStrong := by native_decide

/-- The semantic mapping is compositional (@cite{schwarz-2013} §2.2):
- Weak article contributes uniqueness presupposition (ι-operator)
- Strong article contributes familiarity/anaphoricity (index variable)
This parallels PG&G's D_det (weak/uniqueness) vs D_deix (strong/deixis). -/
theorem semantic_mapping_parallel :
    useTypeToPresupType .anaphoric = .familiarity ∧
    useTypeToPresupType .immediateSituation = .uniqueness ∧
    useTypeToPresupType .largerSituation = .uniqueness := by decide

-- ============================================================================
-- §G: Bridges
-- ============================================================================

/-! ### Bridge 1: PronounClass ↔ AnaphorType (Coreference.lean) -/

/-- PER pronouns correspond to `AnaphorType.pronoun` in Coreference.lean.
DEM pronouns have no direct AnaphorType counterpart — they are structurally
richer than simple pronouns but not descriptions either. -/
def pronClassToAnaphorType : PronounClass → AnaphorType
  | .per => .pronoun
  | .dem => .pronoun  -- DEM is a subtype of pronoun in binding theory

/-- All PER forms map to the pronoun binding pattern (Principle B domain). -/
theorem per_is_pronoun_binding :
    pronClassToAnaphorType .per = .pronoun := rfl

/-! ### Bridge 2: DEM pronouns ↔ Kaplan-style true demonstratives

DEM pronouns require D_deix — the same structural layer that hosts
Kaplan's demonstration. True demonstratives in `Demonstratives.lean`
have a `Demonstration` component; DEM pronouns require D_deix licensing.

The connection: D_deix is the syntactic home of the demonstration.
PER pronouns lack D_deix, so they cannot be true demonstratives. -/

/-- DEM pronouns require D_deix (dLayers = 2), which is the structural
position for Kaplan's demonstration. PER-only languages (dLayers = 1)
cannot have true demonstrative pronouns. -/
theorem dem_requires_deixis_layer :
    allData.all (λ d =>
      if d.forms.any (·.pronClass == .dem)
      then d.dLayers == 2
      else true) = true := by native_decide

/-! ### Bridge 3: PER pronouns ↔ Direct Reference

PER pronouns are directly referential in Kaplan's sense: they
contribute their referent to the proposition, with no descriptive
content (no D_deix, no demonstration, no descriptive component).

This connects to `DirectReference.lean`'s modal argument: PER
pronouns, like names, are rigid designators. DEM pronouns may
involve a descriptive/deictic component (D_deix), making them
potentially non-rigid under some analyses. -/

/-- PER-only languages have no descriptive D-layer: all forms are
directly referential (rigid designators). -/
theorem per_only_directly_referential :
    (allData.filter (·.dLayers == 1)).all
      (λ d => d.forms.all (·.pronClass == .per)) = true := by native_decide

/-! ### Bridge 4: Article system ↔ D-layer count

@cite{schwarz-2009} establishes that the weak/strong article distinction
is structurally real (D_det vs D_deix + D_det). PG&G build on this:
languages with both article types have the structural space for DEM. -/

/-- No-article languages with DEM (Hebrew, Czech) show that D-layers
can exist without overt article morphology. The D_deix layer is
present in the syntax even without morphological exponence. -/
theorem covert_deixis_layer :
    (allData.filter (λ d => d.articleType == .none_ ∧ d.dLayers == 2)).length > 0 := by
  native_decide

end Phenomena.Anaphora.Typology
