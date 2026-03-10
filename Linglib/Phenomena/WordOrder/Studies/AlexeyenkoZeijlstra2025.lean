import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F87A

/-!
# Linearization of Complex Modifiers: (Dis)obeying the Head-Final Filter
@cite{alexeyenko-zeijlstra-2025}

The Head-Final Filter (HFF, Williams 1982) states that prenominal modifiers
must not contain post-head material. @cite{alexeyenko-zeijlstra-2025} show
that the HFF both **overgenerates** (Greek and Russian allow A–XP–N) and
**undergenerates** (Basque and Chácobo display mirror-HFF effects).

They propose the **Modifier-Noun Adjacency Generalization (MAG)**: an XP can
intervene between N and its modifying adjective A only if A exhibits

(a) an overt agreement marker also present on the predicative form and
    specified for all φ/κ-features available in the DP, or
(b) an overt attributive marker morphophonologically independent of A
    (clitic or free word).

The MAG is derived from two independent factors: feature percolation
(§5.1 — adjectives must be φ/κ-complete for direct modification without
an attributivizer) and the morphophonological status of Attr (§5.2 —
affixal Attr must be adjacent to its host per the ICP).

We formalize the MAG as a decision procedure, encode 24 languages from
the paper's Table 3, and verify that the MAG correctly predicts all of
them while the HFF fails for 11.
-/

namespace Phenomena.WordOrder.Studies.AlexeyenkoZeijlstra2025

open Core.WALS.F87A

-- ============================================================================
-- § 1: Core Types
-- ============================================================================

/-- Morphophonological status of the attributivizer (Attr head, §5.2).
    Determines whether Attr imposes linear adjacency with the adjective. -/
inductive AttrStatus where
  | affix     -- adjacent to host (ICP): German {er,e,es}, Dutch {e}
  | clitic    -- morphophonologically independent: Mandarin 的, Farsi ezafe
  | freeWord  -- independent word form
  | null      -- covert but syntactically present: English ∅
  deriving DecidableEq, BEq, Repr

/-- Position of attributive adjectives relative to the modified noun. -/
inductive AdjPosition where
  | prenominal   -- A–N: English, German, Russian, Greek
  | postnominal  -- N–A: Basque, Farsi, Eastern Oromo
  | both         -- both orders productive: Latin, Tagalog
  deriving DecidableEq, BEq, Repr

/-- Morphosyntactic profile of adjectives in a language, capturing
    the two factors that determine MAG-related linearization.
    Fields: adjPosition, apDirection, phiKappaComplete, attrStatus. -/
structure AdjMorphProfile where
  adjPosition      : AdjPosition
  apDirection      : HeadDirection
  phiKappaComplete : Bool
  attrStatus       : AttrStatus
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Decision Procedures
-- ============================================================================

/-- Does the combination of adjective position and AP-internal direction
    create a configuration where XP could intervene between A and N?
    - Prenominal A–XP–N requires head-initial AP (A–XP)
    - Postnominal N–XP–A requires head-final AP (XP–A) -/
def interventionGeometryExists (prof : AdjMorphProfile) : Bool :=
  match prof.adjPosition with
  | .prenominal  => prof.apDirection == .headInitial
  | .postnominal => prof.apDirection == .headFinal
  | .both        => true

/-- MAG conditions (34a,b): does the language's morphosyntax license
    intervention when geometry supports it? -/
def magLicensesIntervention (prof : AdjMorphProfile) : Bool :=
  prof.phiKappaComplete ||
  match prof.attrStatus with
  | .clitic | .freeWord => true
  | .affix  | .null     => false

/-- MAG prediction: intervention is observed iff geometry exists AND
    MAG conditions license it. -/
def interventionPredicted (prof : AdjMorphProfile) : Bool :=
  interventionGeometryExists prof && magLicensesIntervention prof

-- ============================================================================
-- § 3: Language Profiles (Table 3)
-- ============================================================================

-- HFF-violating: prenominal, A–XP–N IS possible.
-- MAG correctly predicts via condition (a) [φ/κ-complete] or (b) [clitic].

/-- Greek: pred & attr identically φ/κ-inflected (37). MAG(a). -/
def greek : AdjMorphProfile := ⟨.prenominal, .headInitial, true, .null⟩

/-- Russian: long forms fully φ/κ-marked in both pred & attr (24, 39). MAG(a). -/
def russian : AdjMorphProfile := ⟨.prenominal, .headInitial, true, .null⟩

/-- Bulgarian: affixal agreement, pred & attr identical for φ/κ. MAG(a). -/
def bulgarian : AdjMorphProfile := ⟨.prenominal, .headInitial, true, .null⟩

/-- Polish: fully inflected pred & attr, like Russian. MAG(a). -/
def polish : AdjMorphProfile := ⟨.prenominal, .headInitial, true, .null⟩

/-- Lithuanian: affixal φ/κ-agreement on pred & attr alike. MAG(a). -/
def lithuanian : AdjMorphProfile := ⟨.prenominal, .headInitial, true, .null⟩

/-- Latin: full φ/κ-marking in both positions (35). MAG(a). -/
def latin : AdjMorphProfile := ⟨.both, .headInitial, true, .null⟩

/-- Mandarin: attributivizer 的 (de) is a clitic (26). MAG(b). -/
def mandarin : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .clitic⟩

/-- Tagalog: attributivizer -ng/na is a clitic (27). MAG(b). -/
def tagalog : AdjMorphProfile := ⟨.both, .headInitial, false, .clitic⟩

-- HFF-obeying: prenominal, A–XP–N is NOT possible.
-- MAG correctly predicts adjacency: MAG(a) fails (pred ≠ attr or
-- incomplete φ/κ), MAG(b) fails (Attr is affix or null).

/-- German: attr affix {er,e,es}, pred is bare (38, 60–63). -/
def german : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .affix⟩

/-- English: no overt agreement, null Attr (71). -/
def english : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .null⟩

/-- Dutch: attr schwa -e or null, both affixal (65–68). -/
def dutch : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .affix⟩

/-- Icelandic: strong/weak distinction → pred ≠ attr featurally (40–42). -/
def icelandic : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .affix⟩

/-- Serbo-Croatian: short (pred) vs long (attr) → featural difference (21, 43). -/
def serboCroatian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .affix⟩

/-- Hungarian: bare pred adjectives, null Attr (18). -/
def hungarian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .null⟩

/-- Georgian: HFF-obeying, null Attr (17). -/
def georgian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .null⟩

/-- Armenian (Modern Eastern): HFF-obeying, null Attr (20). -/
def armenian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, .null⟩

/-- Italian: postnominal primary, head-initial APs → no N–XP–A geometry (36). -/
def italian : AdjMorphProfile := ⟨.postnominal, .headInitial, false, .null⟩

/-- Japanese: strictly head-final APs → no post-head material, trivially HFF. -/
def japanese : AdjMorphProfile := ⟨.prenominal, .headFinal, false, .null⟩

-- Mirror-HFF: postnominal, N–XP–A is NOT possible.
-- MAG correctly predicts adjacency via the same conditions.

/-- Basque: postnominal, head-final. Complex attr APs blocked (3, 28). -/
def basque : AdjMorphProfile := ⟨.postnominal, .headFinal, false, .affix⟩

/-- Chácobo (Panoan): postnominal, head-final. Must relativize (29). -/
def chacobo : AdjMorphProfile := ⟨.postnominal, .headFinal, false, .null⟩

/-- Eastern Oromo: postnominal, head-final. Must relativize (30). -/
def easternOromo : AdjMorphProfile := ⟨.postnominal, .headFinal, false, .null⟩

-- Mirror-HFF-violating: postnominal, N–XP–A IS possible.
-- MAG correctly predicts via condition (a) or (b).

/-- Farsi: ezafe is a clitic (4, 33). MAG(b). -/
def farsi : AdjMorphProfile := ⟨.postnominal, .headFinal, false, .clitic⟩

/-- Atong (Sino-Tibetan): clitic attributivizer =gaba/=aw (32). MAG(b). -/
def atong : AdjMorphProfile := ⟨.postnominal, .headFinal, false, .clitic⟩

/-- Kalaallisut: full affixal φ/κ-agreement, pred = attr (31). MAG(a). -/
def kalaallisut : AdjMorphProfile := ⟨.postnominal, .headFinal, true, .affix⟩

-- ============================================================================
-- § 4: Empirical Data (Table 3)
-- ============================================================================

/-- Whether XP-intervention between A and N is empirically attested. -/
structure InterventionDatum where
  name    : String
  profile : AdjMorphProfile
  observed : Bool
  deriving Repr

def table3 : List InterventionDatum :=
  [ -- HFF-violating (intervention observed)
    ⟨"Greek",          greek,         true⟩
  , ⟨"Russian",        russian,       true⟩
  , ⟨"Bulgarian",      bulgarian,     true⟩
  , ⟨"Polish",         polish,        true⟩
  , ⟨"Lithuanian",     lithuanian,    true⟩
  , ⟨"Latin",          latin,         true⟩
  , ⟨"Mandarin",       mandarin,      true⟩
  , ⟨"Tagalog",        tagalog,       true⟩
    -- HFF-obeying (no intervention)
  , ⟨"German",         german,        false⟩
  , ⟨"English",        english,       false⟩
  , ⟨"Dutch",          dutch,         false⟩
  , ⟨"Icelandic",      icelandic,     false⟩
  , ⟨"Serbo-Croatian", serboCroatian, false⟩
  , ⟨"Hungarian",      hungarian,     false⟩
  , ⟨"Georgian",       georgian,      false⟩
  , ⟨"Armenian",       armenian,      false⟩
  , ⟨"Italian",        italian,       false⟩
  , ⟨"Japanese",       japanese,      false⟩
    -- Mirror-HFF (no intervention)
  , ⟨"Basque",         basque,        false⟩
  , ⟨"Chácobo",        chacobo,       false⟩
  , ⟨"Eastern Oromo",  easternOromo,  false⟩
    -- Mirror-HFF-violating (intervention observed)
  , ⟨"Farsi",          farsi,         true⟩
  , ⟨"Atong",          atong,         true⟩
  , ⟨"Kalaallisut",    kalaallisut,   true⟩ ]

-- ============================================================================
-- § 5: MAG Verification
-- ============================================================================

def magCorrect (d : InterventionDatum) : Bool :=
  interventionPredicted d.profile == d.observed

/-- The MAG correctly predicts intervention possibilities for all
    24 languages in Table 3. -/
theorem mag_predicts_all : table3.all magCorrect = true := by native_decide

-- Per-language theorems: changing one profile breaks exactly one theorem.

theorem mag_greek : interventionPredicted greek = true := by native_decide
theorem mag_russian : interventionPredicted russian = true := by native_decide
theorem mag_bulgarian : interventionPredicted bulgarian = true := by native_decide
theorem mag_polish : interventionPredicted polish = true := by native_decide
theorem mag_lithuanian : interventionPredicted lithuanian = true := by native_decide
theorem mag_latin : interventionPredicted latin = true := by native_decide
theorem mag_mandarin : interventionPredicted mandarin = true := by native_decide
theorem mag_tagalog : interventionPredicted tagalog = true := by native_decide

theorem mag_german : interventionPredicted german = false := by native_decide
theorem mag_english : interventionPredicted english = false := by native_decide
theorem mag_dutch : interventionPredicted dutch = false := by native_decide
theorem mag_icelandic : interventionPredicted icelandic = false := by native_decide
theorem mag_serboCroatian : interventionPredicted serboCroatian = false := by native_decide
theorem mag_hungarian : interventionPredicted hungarian = false := by native_decide
theorem mag_georgian : interventionPredicted georgian = false := by native_decide
theorem mag_armenian : interventionPredicted armenian = false := by native_decide
theorem mag_italian : interventionPredicted italian = false := by native_decide
theorem mag_japanese : interventionPredicted japanese = false := by native_decide

theorem mag_basque : interventionPredicted basque = false := by native_decide
theorem mag_chacobo : interventionPredicted chacobo = false := by native_decide
theorem mag_easternOromo : interventionPredicted easternOromo = false := by native_decide

theorem mag_farsi : interventionPredicted farsi = true := by native_decide
theorem mag_atong : interventionPredicted atong = true := by native_decide
theorem mag_kalaallisut : interventionPredicted kalaallisut = true := by native_decide

-- ============================================================================
-- § 6: HFF Inadequacy
-- ============================================================================

/-- The HFF (+ mirror) predicts no intervention whenever geometry exists.
    It is wrong for every language where geometry exists but intervention
    IS observed — the 11 languages satisfying MAG conditions (a) or (b). -/
def hffWrong (d : InterventionDatum) : Bool :=
  interventionGeometryExists d.profile && d.observed

theorem hff_wrong_count :
    (table3.filter hffWrong).length = 11 := by native_decide

theorem mag_correct_count :
    (table3.filter magCorrect).length = 24 := by native_decide

/-- HFF overgenerates: blocks Greek (prenominal, head-initial) but
    intervention is observed. -/
theorem hff_overgenerates_greek :
    interventionGeometryExists greek = true ∧
    interventionPredicted greek = true := by decide

/-- HFF overgenerates: blocks Mandarin but clitic 的 licenses intervention. -/
theorem hff_overgenerates_mandarin :
    interventionGeometryExists mandarin = true ∧
    interventionPredicted mandarin = true := by decide

/-- HFF undergenerates: Basque (postnominal) shows mirror-HFF effects
    that the original HFF cannot state. -/
theorem hff_undergenerates_basque :
    interventionGeometryExists basque = true ∧
    interventionPredicted basque = false := by decide

/-- The two MAG conditions are independent: Greek uses (a) [φ/κ-complete],
    Mandarin uses (b) [clitic]. Neither alone covers both. -/
theorem mag_conditions_independent :
    greek.phiKappaComplete = true ∧ greek.attrStatus = .null ∧
    mandarin.phiKappaComplete = false ∧ mandarin.attrStatus = .clitic := by decide

-- ============================================================================
-- § 7: Bridge to WALS F87A (Adjective-Noun Order)
-- ============================================================================

def walsOrder (code : String) : Option AdjectiveNounOrder :=
  (allData.find? (·.walsCode == code)).map (·.value)

def walsToPosition : AdjectiveNounOrder → AdjPosition
  | .adjectiveNoun => .prenominal
  | .nounAdjective => .postnominal
  | .noDominantOrder => .both
  | .onlyInternallyHeadedRelativeClauses => .both

/-- WALS consistency: profile adjPosition matches WALS F87A. -/
def walsConsistent (code : String) (prof : AdjMorphProfile) : Bool :=
  match walsOrder code with
  | none => true
  | some order => walsToPosition order == prof.adjPosition

theorem wals_greek : walsConsistent "grk" greek = true := by native_decide
theorem wals_russian : walsConsistent "rus" russian = true := by native_decide
theorem wals_german : walsConsistent "ger" german = true := by native_decide
theorem wals_mandarin : walsConsistent "mnd" mandarin = true := by native_decide
theorem wals_basque : walsConsistent "bsq" basque = true := by native_decide
theorem wals_hungarian : walsConsistent "hun" hungarian = true := by native_decide
theorem wals_italian : walsConsistent "ita" italian = true := by native_decide
theorem wals_farsi : walsConsistent "prs" farsi = true := by native_decide
theorem wals_tagalog : walsConsistent "tag" tagalog = true := by native_decide

end Phenomena.WordOrder.Studies.AlexeyenkoZeijlstra2025
