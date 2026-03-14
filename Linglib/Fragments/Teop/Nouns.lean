import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Theories.Morphology.DM.Categorizer

/-!
# Teop Noun Inventory @cite{adamson-2024}

Gender I and gender II nouns in Teop (Austronesian, Oceanic), drawn from
@cite{adamson-2024} Table 1 (sampled from Mosel & Spriggs 2000:336–40).

Teop has two genders distinguished by article form:
- **Gender I** (article *a*): animates — encoded via [±ANIM] on n
- **Gender II** (article *o*): inanimates — plain n

Body-part nouns appear in **both** genders depending on possession:
iPossessed (with n_{body-part{D}}) → gender I; unpossessed or
aPossessed (with n_{alienator}) → gender II.
-/

namespace Fragments.Teop

open Morphology.DM

-- ============================================================================
-- § 1: Gender Classes
-- ============================================================================

/-- Teop gender: two classes (Mosel & Spriggs 2000, Mosel 2014). -/
inductive Gender where
  | gI   -- article *a/ra*; animates
  | gII  -- article *o/ro*; inanimates
  deriving DecidableEq, BEq, Repr

/-- A Teop noun with its gloss and gender assignment. -/
structure Noun where
  form : String
  gloss : String
  gender : Gender
  /-- Body-part nouns can be iPossessed, switching to gender I. -/
  isBodyPart : Bool := false
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Gender I Nouns (@cite{adamson-2024} Table 1, left column)
-- ============================================================================

def moon     : Noun := ⟨"moon",      "woman",                   .gI, false⟩
def beikoo   : Noun := ⟨"beikoo",    "child",                   .gI, false⟩
def keusu    : Noun := ⟨"keusu",     "rat",                     .gI, false⟩
def naovana  : Noun := ⟨"naovana",   "bird",                    .gI, false⟩
def overe_c  : Noun := ⟨"overe",     "coconut",                 .gI, false⟩
def pauna    : Noun := ⟨"pauna",     "banana",                  .gI, false⟩
def kepaa    : Noun := ⟨"kepaa",     "clay pot",                .gI, false⟩
def anoo     : Noun := ⟨"anoo",      "peeler (pearl shell)",    .gI, false⟩
def tabaani  : Noun := ⟨"taba'ani",  "food",                    .gI, false⟩
def tahii    : Noun := ⟨"tahii",     "sea",                     .gI, false⟩
def huan     : Noun := ⟨"huan",      "rain",                    .gI, false⟩
def uruuru   : Noun := ⟨"uruuru",    "love",                    .gI, false⟩

-- ============================================================================
-- § 3: Gender II Nouns (@cite{adamson-2024} Table 1, right column)
-- ============================================================================

def paka     : Noun := ⟨"paka",      "leaf",                    .gII, false⟩
def pus      : Noun := ⟨"pus",       "stump",                   .gII, false⟩
def hinahoo  : Noun := ⟨"hinahoo",   "taro planting stick",     .gII, false⟩
def sinivi   : Noun := ⟨"sinivi",    "canoe",                   .gII, false⟩
def overe_p  : Noun := ⟨"overe",     "coconut palm",            .gII, false⟩
def overe_bt : Noun := ⟨"overe",     "banana tree",             .gII, false⟩
def kurita   : Noun := ⟨"kurita",    "octopus",                 .gII, false⟩
def demdem   : Noun := ⟨"demdem",    "snail",                   .gII, false⟩
def paku     : Noun := ⟨"paku",      "feast",                   .gII, false⟩
def suraa    : Noun := ⟨"suraa",     "fire",                    .gII, false⟩
def giigii   : Noun := ⟨"giigii",    "shooting star",           .gII, false⟩
def koara    : Noun := ⟨"koara",     "language",                .gII, false⟩

-- ============================================================================
-- § 4: Body-Part Nouns (gender switches with iPossession)
-- ============================================================================

/-- Body-part nouns: gender I when iPossessed, gender II when free.
    The `gender` field records the UNPOSSESSED (default) gender II;
    iPossession switches them to gender I via n_{body-part{D}}. -/
def bina     : Noun := ⟨"bina",      "spleen",                  .gII, true⟩
def kuri     : Noun := ⟨"kuri",      "hand",                    .gII, true⟩
def iru      : Noun := ⟨"iru",       "back of head",            .gII, true⟩
def vuha     : Noun := ⟨"vuha",      "heart",                   .gII, true⟩
def ihu      : Noun := ⟨"ihu",       "nose",                    .gII, true⟩
def revasin  : Noun := ⟨"revasin",   "blood",                   .gII, true⟩
def hena     : Noun := ⟨"hena",      "name",                    .gII, true⟩
def moo      : Noun := ⟨"moo",       "leg",                     .gII, true⟩

/-- Body-part nouns when iPossessed switch to gender I. -/
def iPossessedGender (n : Noun) : Gender :=
  if n.isBodyPart then .gI else n.gender

-- ============================================================================
-- § 5: Article Paradigm (Mosel & Spriggs 2000)
-- ============================================================================

/-- Teop articles, conditioned by gender and number.
    Gender Ie (proprial *e*) is treated as gender I with a proprial
    feature, following @cite{adamson-2024} §3.1. -/
structure ArticleCtx where
  gender : Gender
  plural : Bool
  proprial : Bool := false
  deriving DecidableEq, BEq, Repr

def articleForm : ArticleCtx → String
  | ⟨.gI,  _, true⟩      => "e"
  | ⟨.gI,  false, false⟩  => "a"
  | ⟨.gI,  true,  false⟩  => "ra"
  | ⟨.gII, false, _⟩      => "o"
  | ⟨.gII, true,  _⟩      => "ro"

-- ============================================================================
-- § 6: Verification
-- ============================================================================

/-- Gender I nouns are animate (Mosel & Spriggs 2000:337–38). -/
def genderINouns : List Noun :=
  [moon, beikoo, keusu, naovana, overe_c, pauna, kepaa, anoo,
   tabaani, tahii, huan, uruuru]

/-- Gender II nouns are inanimate (Mosel & Spriggs 2000:338–40). -/
def genderIINouns : List Noun :=
  [paka, pus, hinahoo, sinivi, overe_p, overe_bt, kurita, demdem,
   paku, suraa, giigii, koara]

def bodyPartNouns : List Noun :=
  [bina, kuri, iru, vuha, ihu, revasin, hena, moo]

theorem genderI_all_gI : genderINouns.all (·.gender == .gI) = true := by native_decide
theorem genderII_all_gII : genderIINouns.all (·.gender == .gII) = true := by native_decide
theorem bodyParts_all_marked : bodyPartNouns.all (·.isBodyPart) = true := by native_decide
theorem bodyParts_default_gII : bodyPartNouns.all (·.gender == .gII) = true := by native_decide
theorem bodyParts_iPossessed_gI :
    bodyPartNouns.all (iPossessedGender · == .gI) = true := by native_decide

/-- The article paradigm: iPossessed body part gets *a*,
    unpossessed body part gets *o*. -/
theorem spleen_ipossessed_article :
    articleForm ⟨iPossessedGender bina, false, false⟩ = "a" := rfl
theorem spleen_unpossessed_article :
    articleForm ⟨bina.gender, false, false⟩ = "o" := rfl

-- ============================================================================
-- § 7: Bridge to DM Categorizer (@cite{kramer-2015} Ch 5)
-- ============================================================================

open Morphology.DM in
/-- Map Teop gender classes to their DM categorizing heads.
    Gender I (animates) ↔ n i[+ANIM]; Gender II (inanimates) ↔ plain n. -/
def Gender.toCatHead : Gender → CatHead
  | .gI  => CatHead.n_iAnim
  | .gII => CatHead.n_plain

open Morphology.DM in
/-- Gender I maps to a natural (interpretable) gender feature. -/
theorem gI_natural_gender :
    Gender.gI.toCatHead.phi.gender = some ⟨.i, ⟨.anim, .pos⟩⟩ := rfl

open Morphology.DM in
/-- Gender II maps to plain n (no gender feature). -/
theorem gII_no_gender :
    Gender.gII.toCatHead.phi.gender = none := rfl

open Morphology.DM in
/-- Body-part nouns when iPossessed switch to n with u[+ANIM]
    (@cite{adamson-2024} §3.1). -/
def iPossessedCatHead (n : Noun) : CatHead :=
  if n.isBodyPart then CatHead.n_uAnim else n.gender.toCatHead

open Morphology.DM in
theorem spleen_ipossessed_cathead :
    iPossessedCatHead bina = CatHead.n_uAnim := rfl

open Morphology.DM in
theorem spleen_free_cathead :
    bina.gender.toCatHead = CatHead.n_plain := rfl

end Fragments.Teop
