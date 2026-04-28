import Linglib.Features.Definiteness

/-!
# Schwarz (2013): Two Kinds of Definites Cross-Linguistically
@cite{schwarz-2013} @cite{hawkins-1978} @cite{schwarz-2009}

Cross-linguistic typology of the weak/strong article distinction. Schwarz
identifies seven languages where the morphological article paradigm
distinguishes a *weak* article (uniqueness/situational use) from a *strong*
article (anaphoric/familiarity use), supporting his earlier @cite{schwarz-2009}
analysis that the two definite articles correspond to different syntactic
projections (D_det vs D_deix + D_det).

## Core Generalizations

1. **Strong → anaphoric**: every surveyed language uses the strong article
   for anaphoric definites (§3.1.1).
2. **Weak → uniqueness**: every surveyed language uses the weak article
   (or a bare nominal) for uniqueness-based definites (§3.1.2).
3. **Bridging splits**: most languages split bridging across article forms —
   part-whole bridging takes weak, producer bridging takes strong (§3.2).
4. **Bare-nominal strategy**: languages with only one overt article form
   (Akan, Mauritian Creole) use bare nominals for weak-article definites (§4.1).
5. **Haitian Creole exception**: single determiner *la* for both anaphoric
   and uniqueness uses — no weak/strong split (§4.3).

The article-pronoun parallel (§5.5) is exploited by
@cite{patel-grosz-grosz-2017} (`Studies/PatelGroszGrosz2017.lean`), where
weak article ↔ PER pronoun and strong article ↔ DEM pronoun.
-/

set_option autoImplicit false

namespace Phenomena.Anaphora.Studies.Schwarz2013

open Features.Definiteness (WeakArticleStrategy DefiniteUseType DefPresupType
  useTypeToPresupType)

/-- Per-language article paradigm from @cite{schwarz-2013}. -/
structure SchwarzArticleDatum where
  language : String
  isoCode : String
  /-- Morphological form of the strong article (if any). -/
  strongForm : Option String
  /-- Morphological form of the weak article (if any). -/
  weakForm : Option String
  /-- How weak definites are expressed. -/
  weakStrategy : WeakArticleStrategy
  /-- Strong article used for anaphoric definites. -/
  strongForAnaphoric : Bool
  /-- Weak article/bare nominal used for uniqueness/situational. -/
  weakForUniqueness : Bool
  /-- Bridging shows the split (part-whole = weak, producer = strong). -/
  bridgingSplit : Bool
  deriving Repr, BEq

-- Germanic (@cite{schwarz-2013} §3)

def german : SchwarzArticleDatum :=
  { language := "German", isoCode := "de"
    strongForm := some "dem"     -- full/uncontracted: von dem
    weakForm := some "vom"       -- contracted: vom = von + dem
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §3.1.1: ex. (9)
    weakForUniqueness := true    -- §3.1.2: ex. (15)
    bridgingSplit := true }      -- §3.2: ex. (16a) weak, (16b) strong

def fering : SchwarzArticleDatum :=
  { language := "Fering", isoCode := "frr"
    strongForm := some "di/det"  -- Ebert's D-form: di (m), det (f/n)
    weakForm := some "a/at"      -- Ebert's A-form: a (m/pl), at (f/n)
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §3.1.1: ex. (8)
    weakForUniqueness := true    -- §3.1.2: ex. (13), (14)
    bridgingSplit := true }      -- §3.2: ex. (17a) weak, (17b) strong

-- Non-Germanic with strong article only (@cite{schwarz-2013} §4.1)

def akan : SchwarzArticleDatum :=
  { language := "Akan", isoCode := "ak"
    strongForm := some "nó"      -- strong article / Fam marker
    weakForm := none              -- bare nominal for weak definites
    weakStrategy := .bareNominal
    strongForAnaphoric := true   -- §4.1.1: ex. (18b), (19)
    weakForUniqueness := true    -- §4.1.1: bare nominals for situation uses, ex. (22)
    bridgingSplit := true }      -- §4.1.1: producer bridging takes nó, ex. (23)

def mauritianCreole : SchwarzArticleDatum :=
  { language := "Mauritian Creole", isoCode := "mfe"
    strongForm := some "la"      -- post-nominal clitic
    weakForm := none              -- bare nominal for weak definites
    weakStrategy := .bareNominal
    strongForAnaphoric := true   -- §4.1.2: ex. (25)
    weakForUniqueness := true    -- §4.1.2: bare nominals, ex. (26)
    bridgingSplit := true }      -- §4.1.2: ex. (28)/(29)

-- Languages with two overt articles (@cite{schwarz-2013} §4.2)

def lakhota : SchwarzArticleDatum :=
  { language := "Lakhota", isoCode := "lkt"
    strongForm := some "k'uŋ"   -- anaphoric/previously-mentioned
    weakForm := some "kiŋ"       -- situational uniqueness
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §4.2.1: ex. (32), (33)
    weakForUniqueness := true    -- §4.2.1: ex. (30), (31)
    bridgingSplit := true }      -- §4.2.1: ex. (34) weak for part-whole

def hausa : SchwarzArticleDatum :=
  { language := "Hausa", isoCode := "ha"
    strongForm := some "ɗîn"    -- anaphoric determiner
    weakForm := some "-n"        -- suffixal weak article
    weakStrategy := .overtArticle
    strongForAnaphoric := true   -- §4.2.2: ex. (37) ɗîn for anaphoric
    weakForUniqueness := true    -- §4.2.2: ex. (36) -n for uniqueness
    bridgingSplit := false }     -- insufficient data in @cite{schwarz-2013}

-- Exceptional: single form for both uses (@cite{schwarz-2013} §4.3)

def haitianCreole : SchwarzArticleDatum :=
  { language := "Haitian Creole", isoCode := "ht"
    strongForm := some "la"      -- used for all definite types
    weakForm := some "la"         -- same form
    weakStrategy := .sameAsStrong
    strongForAnaphoric := true   -- §4.3: ex. (40)
    weakForUniqueness := true    -- §4.3: ex. (39)
    bridgingSplit := false }     -- §4.3: la used for both bridging types

/-- All 7 languages from @cite{schwarz-2013} survey. -/
def allData : List SchwarzArticleDatum :=
  [ german, fering, akan, mauritianCreole, lakhota, hausa, haitianCreole ]

-- ============================================================================
-- Verified generalizations
-- ============================================================================

/-- **Strong article → anaphoric use** (@cite{schwarz-2013} §3.1.1):
    all surveyed languages use the strong article for anaphoric definites. -/
theorem strong_for_anaphoric :
    allData.all (·.strongForAnaphoric) = true := by decide

/-- **Weak form → uniqueness/situational use** (@cite{schwarz-2013} §3.1.2):
    all surveyed languages use weak articles (or bare nominals) for
    uniqueness-based definites. -/
theorem weak_for_uniqueness :
    allData.all (·.weakForUniqueness) = true := by decide

/-- **Bridging split** (@cite{schwarz-2013} §3.2): most languages split bridging
    across article forms (part-whole = weak, producer = strong). 5 of 7
    languages show this pattern; Hausa lacks data, and Haitian Creole uses
    a single form for everything. -/
theorem bridging_split_is_majority :
    (allData.filter (·.bridgingSplit)).length = 5 := by decide

/-- **Bare-nominal strategy** (@cite{schwarz-2013} §4.1): languages with only
    one overt article form (Akan, Mauritian Creole) use bare nominals for
    weak-article definites. -/
theorem bare_nominal_languages :
    (allData.filter (·.weakStrategy == .bareNominal)).length = 2 := by decide

/-- **Haitian Creole is exceptional** (@cite{schwarz-2013} §4.3): single
    determiner *la* for both anaphoric and uniqueness uses — no weak/strong
    split. -/
theorem haitian_creole_no_split :
    haitianCreole.weakStrategy == .sameAsStrong := by decide

/-- The semantic mapping is compositional (@cite{schwarz-2013} §2.2):
    weak article contributes uniqueness presupposition (ι-operator);
    strong article contributes familiarity/anaphoricity (index variable). -/
theorem semantic_mapping :
    useTypeToPresupType .anaphoric = .familiarity ∧
    useTypeToPresupType .immediateSituation = .uniqueness ∧
    useTypeToPresupType .largerSituation = .uniqueness := by decide

end Phenomena.Anaphora.Studies.Schwarz2013
