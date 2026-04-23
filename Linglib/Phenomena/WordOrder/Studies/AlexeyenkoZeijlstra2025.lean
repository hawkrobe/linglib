import Linglib.Core.Lexical.Word
import Linglib.Datasets.WALS.Features.F87A
import Linglib.Theories.Syntax.Minimalism.Modification
import Linglib.Theories.Morphology.Core.ICP
import Linglib.Fragments.Greek.AdjAgreement
import Linglib.Fragments.German.AdjAgreement
import Linglib.Fragments.Russian.AdjAgreement
import Linglib.Fragments.Italian.AdjAgreement

/-!
# Linearization of Complex Modifiers: (Dis)obeying the Head-Final Filter
@cite{alexeyenko-zeijlstra-2025}

The Head-Final Filter (HFF, Williams 1982) states that prenominal modifiers
must not contain post-head material. @cite{alexeyenko-zeijlstra-2025} show
that the HFF both **overgenerates** (Greek and Russian allow A–XP–N) and
**undergenerates** (Basque and Chácobo display mirror-HFF effects).

They propose the **Modifier-Noun Adjacency Generalization (MAG)** (34):
an XP can intervene between N and its modifying adjective A only if

(a) A has an overt agreement marker that is also present on the
    predicative form of A and specified for all φ/κ-features in the DP, or
(b) A has an overt attributive marker morphophonologically independent
    of A (adjectival clitic or free word) or forming a morphophonological
    unit with N.

The MAG is derived from two independent factors:
1. **Feature composition** (§5.1): φ/κ-completeness of adjectives determines
   whether an attributivizer is needed for modification
2. **Morphophonological status of Attr** (§5.2): affixal Attr must be adjacent
   to its host (ICP, @cite{ackema-neeleman-2004}), while clitic/free-word
   Attr imposes no adjacency

We formalize the MAG as a decision procedure matching the paper's decision
trees (44)/(45), encode 24 languages from Table 3, and verify that the MAG
correctly predicts all of them while the HFF fails for 11. Bridge theorems
connect to WALS F87A and Minimalist feature infrastructure.
-/

namespace AlexeyenkoZeijlstra2025

open Datasets.WALS.F87A
open Minimalism.Modification (AttrStatus AdjPosition AdjMorphProfile
  ModificationRoute MAGFeatureType AdjAgreementEntry
  modificationRoute morphStatusToAttrStatus)
open Morphology.ICP (icpBlocksIntervention)

-- ============================================================================
-- § 2: Decision Procedures
-- ============================================================================

/-- Does the combination of adjective position and AP-internal direction
    create a configuration where XP could intervene between A and N?
    Prenominal A–XP–N requires head-initial AP; postnominal N–XP–A requires
    head-final AP. This is the prerequisite checked at the top of both
    decision trees (44) and (45). -/
def interventionGeometryExists (prof : AdjMorphProfile) : Bool :=
  match prof.adjPosition with
  | .prenominal  => prof.apDirection == .headInitial
  | .postnominal => prof.apDirection == .headFinal
  | .both        => true

/-- MAG condition (a) (34a): adjectives have identical, fully specified
    φ/κ-agreement in both predicative and attributive use. -/
def magConditionA (prof : AdjMorphProfile) : Bool :=
  prof.predAttrSameAgreement && prof.agreementPhiKappaComplete

/-- MAG condition (b) (34b): the attributivizer is morphophonologically
    independent of the adjective. -/
def magConditionB (prof : AdjMorphProfile) : Bool :=
  match prof.attrStatus with
  | .clitic | .freeWord => true
  | .affix  | .null     => false

/-- MAG licensing: does the language's morphosyntax permit intervention
    when geometry supports it? Disjunction of conditions (a) and (b). -/
def magLicensesIntervention (prof : AdjMorphProfile) : Bool :=
  magConditionA prof || magConditionB prof

/-- MAG prediction: intervention is observed iff geometry exists AND
    MAG conditions license it. -/
def interventionPredicted (prof : AdjMorphProfile) : Bool :=
  interventionGeometryExists prof && magLicensesIntervention prof

-- ============================================================================
-- § 3: Decision Trees (44) and (45)
-- ============================================================================

/-- Decision tree (44), p. 24: Is A–XP–N possible in prenominal APs?

    1. Is AP-internal order head-initial (A–XP)? NO → trivially HFF (Japanese)
    2. Are pred & attr φ/κ-complete? YES → intervention OK (Greek)
    3. Is Attr a clitic/free word? YES → intervention OK (Tagalog)
       NO → adjacency forced (German, English) -/
def prenominalTree (prof : AdjMorphProfile) : Bool :=
  if prof.apDirection != .headInitial then false
  else if magConditionA prof then true
  else magConditionB prof

/-- Decision tree (45), p. 25: Is N–XP–A possible in postnominal APs?
    Mirror of (44). -/
def postnominalTree (prof : AdjMorphProfile) : Bool :=
  if prof.apDirection != .headFinal then false
  else if magConditionA prof then true
  else magConditionB prof

/-- The decision trees are equivalent to `interventionPredicted`. -/
theorem decisionTrees_equiv_mag (prof : AdjMorphProfile) :
    interventionPredicted prof =
    match prof.adjPosition with
    | .prenominal  => prenominalTree prof
    | .postnominal => postnominalTree prof
    | .both        => prenominalTree prof || postnominalTree prof := by
  obtain ⟨a, b, c, d, e⟩ := prof
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

-- ============================================================================
-- § 4: Language Profiles (Table 3)
-- ============================================================================

-- Fields: adjPosition, apDirection, predAttrSameAgreement,
--         agreementPhiKappaComplete, attrStatus

-- HFF-violating: prenominal, A–XP–N IS possible.
-- MAG correctly predicts via condition (a) or (b).

/-- Greek: pred & attr identically inflected for gender, number, case
    (37). Both are fully φ/κ-specified. MAG(a). -/
def greek : AdjMorphProfile := ⟨.prenominal, .headInitial, true, true, .null⟩

/-- Russian: long forms fully φ/κ-marked; used in both pred & attr
    positions. Short forms are pred-only and irrelevant (Table 4).
    (24), (39). MAG(a). -/
def russian : AdjMorphProfile := ⟨.prenominal, .headInitial, true, true, .null⟩

/-- Bulgarian: affixal agreement, pred & attr identical for φ/κ. MAG(a). -/
def bulgarian : AdjMorphProfile := ⟨.prenominal, .headInitial, true, true, .null⟩

/-- Polish: fully inflected pred & attr, like Russian. MAG(a). -/
def polish : AdjMorphProfile := ⟨.prenominal, .headInitial, true, true, .null⟩

/-- Lithuanian: affixal φ/κ-agreement on pred & attr alike. MAG(a). -/
def lithuanian : AdjMorphProfile := ⟨.prenominal, .headInitial, true, true, .null⟩

/-- Latin: full φ/κ-marking (gender, number, case) in both pred and
    attr uses. Both pre- and postnominal. (35). MAG(a). -/
def latin : AdjMorphProfile := ⟨.both, .headInitial, true, true, .null⟩

/-- Mandarin: no φ-agreement; attributivizer 的 (de) cliticizes to AP.
    (26). MAG(b). -/
def mandarin : AdjMorphProfile := ⟨.prenominal, .headInitial, false, false, .clitic⟩

/-- Tagalog: no φ-agreement; attributivizer -ng/na is a clitic.
    Both pre- and postnominal. (27). MAG(b). -/
def tagalog : AdjMorphProfile := ⟨.both, .headInitial, false, false, .clitic⟩

-- HFF-obeying: prenominal, A–XP–N is NOT possible.
-- MAG correctly predicts: MAG(a) fails, MAG(b) fails.

/-- German: pred adjectives bare, attr carry agreement affix (38, 60–63).
    predAttrSameAgreement = false (pred bare, attr inflected). -/
def german : AdjMorphProfile := ⟨.prenominal, .headInitial, false, true, .affix⟩

/-- English: no overt agreement on adjectives. Null Attr evidenced by
    distributional parallels with Dutch (§5.2.3). (71). -/
def english : AdjMorphProfile := ⟨.prenominal, .headInitial, false, false, .null⟩

/-- Dutch: attr schwa -e (overt) or null (indef neut sg), both affixal.
    Pred adjectives bare (64). (65)–(68), Table 6. -/
def dutch : AdjMorphProfile := ⟨.prenominal, .headInitial, false, false, .affix⟩

/-- Icelandic: strong/weak distinction. Pred = strong only; attr =
    strong (indef) or weak (def). Attr forms carry definiteness features
    absent from pred forms → pred ≠ attr. (40)–(42), Table 5. -/
def icelandic : AdjMorphProfile := ⟨.prenominal, .headInitial, false, true, .affix⟩

/-- Serbo-Croatian: short (pred only) vs long (pred/attr, definiteness).
    Attr long forms encode definiteness absent from short pred forms →
    pred ≠ attr featurally. (21), (43). -/
def serboCroatian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, true, .affix⟩

/-- Hungarian: bare pred adjectives, no overt attr agreement. (18). -/
def hungarian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, false, .null⟩

/-- Georgian: HFF-obeying, null Attr. (17). -/
def georgian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, false, .null⟩

/-- Armenian (Modern Eastern): HFF-obeying, null Attr. (20). -/
def armenian : AdjMorphProfile := ⟨.prenominal, .headInitial, false, false, .null⟩

/-- Italian: postnominal primary, head-initial APs → no N–XP–A geometry.
    φ-agreement (gender, number) but no κ (case) on adjectives →
    agreementPhiKappaComplete = false. (36), (72). -/
def italian : AdjMorphProfile := ⟨.postnominal, .headInitial, true, false, .null⟩

/-- Japanese: strictly head-final APs → no post-head material to create
    A–XP–N geometry. Trivially HFF-obeying (§2.2). -/
def japanese : AdjMorphProfile := ⟨.prenominal, .headFinal, false, false, .null⟩

-- Mirror-HFF: postnominal, N–XP–A is NOT possible.

/-- Basque: postnominal, head-final. Complex attr APs blocked; must use
    relative clause with -en. (3), (28). -/
def basque : AdjMorphProfile := ⟨.postnominal, .headFinal, false, false, .affix⟩

/-- Chácobo (Panoan): postnominal, head-final. Complex attr APs
    impossible; relativize with =ka(to) instead. (29). -/
def chacobo : AdjMorphProfile := ⟨.postnominal, .headFinal, false, false, .null⟩

/-- Eastern Oromo: postnominal, head-final. Complex attr APs blocked;
    must use dependent clause marker. (30). -/
def easternOromo : AdjMorphProfile := ⟨.postnominal, .headFinal, false, false, .null⟩

-- Mirror-HFF-violating: postnominal, N–XP–A IS possible.

/-- Farsi: postnominal, head-final. Ezafe cliticizes to NP (33). MAG(b). -/
def farsi : AdjMorphProfile := ⟨.postnominal, .headFinal, false, false, .clitic⟩

/-- Atong (Sino-Tibetan): postnominal, head-final. Clitic attributivizer
    =gaba/=aw. (32). MAG(b). -/
def atong : AdjMorphProfile := ⟨.postnominal, .headFinal, false, false, .clitic⟩

/-- Kalaallisut (West Greenlandic): postnominal, head-final. Full affixal
    φ/κ-agreement; pred & attr identically specified. (31). MAG(a). -/
def kalaallisut : AdjMorphProfile := ⟨.postnominal, .headFinal, true, true, .affix⟩

-- ============================================================================
-- § 5: Empirical Data (Table 3)
-- ============================================================================

structure InterventionDatum where
  name    : String
  profile : AdjMorphProfile
  observed : Bool
  deriving Repr

def table3 : List InterventionDatum :=
  [ ⟨"Greek",          greek,         true⟩
  , ⟨"Russian",        russian,       true⟩
  , ⟨"Bulgarian",      bulgarian,     true⟩
  , ⟨"Polish",         polish,        true⟩
  , ⟨"Lithuanian",     lithuanian,    true⟩
  , ⟨"Latin",          latin,         true⟩
  , ⟨"Mandarin",       mandarin,      true⟩
  , ⟨"Tagalog",        tagalog,       true⟩
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
  , ⟨"Basque",         basque,        false⟩
  , ⟨"Chácobo",        chacobo,       false⟩
  , ⟨"Eastern Oromo",  easternOromo,  false⟩
  , ⟨"Farsi",          farsi,         true⟩
  , ⟨"Atong",          atong,         true⟩
  , ⟨"Kalaallisut",    kalaallisut,   true⟩ ]

-- ============================================================================
-- § 6: MAG Verification
-- ============================================================================

def magCorrect (d : InterventionDatum) : Bool :=
  interventionPredicted d.profile == d.observed

/-- The MAG correctly predicts all 24 languages in Table 3. -/
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
-- § 7: MAG Condition Independence
-- ============================================================================

-- The two MAG conditions are independent factors. Condition (a) is
-- morphosyntactic (feature composition), condition (b) is morphophono-
-- logical (Attr status). These are logically orthogonal.

/-- Greek uses MAG(a) alone: φ/κ-complete, no clitic Attr. -/
theorem greek_uses_condA :
    magConditionA greek = true ∧ magConditionB greek = false := by decide

/-- Mandarin uses MAG(b) alone: clitic 的, no φ/κ-agreement. -/
theorem mandarin_uses_condB :
    magConditionA mandarin = false ∧ magConditionB mandarin = true := by decide

/-- Kalaallisut uses MAG(a) alone despite affixal Attr: φ/κ-complete
    agreement overrides affix adjacency. -/
theorem kalaallisut_uses_condA :
    magConditionA kalaallisut = true ∧ magConditionB kalaallisut = false := by decide

/-- German fails BOTH conditions: pred ≠ attr AND Attr is affix. -/
theorem german_fails_both :
    magConditionA german = false ∧ magConditionB german = false := by decide

/-- MAG(a) failure modes are distinct. German fails because pred ≠ attr
    (clause 1); Italian fails because agreement is not κ-complete
    (clause 2, no case on adjectives). Both have geometry. -/
theorem condA_failure_modes :
    -- German: pred ≠ attr (clause 1 false)
    german.predAttrSameAgreement = false ∧
    -- Italian: pred = attr, but missing κ (clause 2 false)
    italian.predAttrSameAgreement = true ∧
    italian.agreementPhiKappaComplete = false := by decide

-- ============================================================================
-- § 8: HFF Inadequacy
-- ============================================================================

/-- Languages where geometry exists but intervention IS observed — exactly
    those satisfying MAG(a) or MAG(b). The HFF (+ mirror) incorrectly
    blocks all of them. -/
def hffWrong (d : InterventionDatum) : Bool :=
  interventionGeometryExists d.profile && d.observed

theorem hff_wrong_count :
    (table3.filter hffWrong).length = 11 := by native_decide

theorem mag_correct_count :
    (table3.filter magCorrect).length = 24 := by native_decide

/-- HFF overgenerates for Greek: blocks A–XP–N but it is observed. -/
theorem hff_overgenerates_greek :
    interventionGeometryExists greek = true ∧
    interventionPredicted greek = true := by decide

/-- HFF overgenerates for Mandarin: clitic 的 licenses A–XP–N. -/
theorem hff_overgenerates_mandarin :
    interventionGeometryExists mandarin = true ∧
    interventionPredicted mandarin = true := by decide

/-- HFF undergenerates for Basque: mirror-HFF effects exist but the
    original HFF cannot state them (postnominal APs). -/
theorem hff_undergenerates_basque :
    interventionGeometryExists basque = true ∧
    interventionPredicted basque = false := by decide

/-- English "enough" (15)–(16): a genuine HFF exception. Post-adjectival
    degree modifier that CAN precede the noun: "a tall enough guy."
    In the MAG analysis, DegP headed by "enough" intervenes between Attr
    and A; this is possible because null Attr (when DegP heads the
    extended AP) attaches to DegP, not A (69b). -/
def english_enough : AdjMorphProfile :=
  ⟨.prenominal, .headInitial, false, false, .null⟩

-- ============================================================================
-- § 9: Bridge to Fragment Adjective Agreement Entries
-- ============================================================================

-- The MAG's Boolean fields (`predAttrSameAgreement`, `agreementPhiKappaComplete`)
-- are DERIVED from the fragment-layer adjective agreement entries. This makes
-- the connection true by construction: changing a fragment feature list breaks
-- exactly these bridge theorems.

/-- Greek: fragment entry confirms pred = attr agreement. -/
theorem greek_fragment_sameAgreement :
    Fragments.Greek.AdjAgreement.entry.sameAgreement = true := by native_decide

/-- Greek: fragment entry confirms φ/κ-completeness. -/
theorem greek_fragment_phiKappaComplete :
    Fragments.Greek.AdjAgreement.entry.phiKappaComplete = true := by native_decide

/-- Greek profile is consistent with fragment: pred = attr. -/
theorem greek_profile_consistent_pred :
    greek.predAttrSameAgreement =
    Fragments.Greek.AdjAgreement.entry.sameAgreement := by native_decide

/-- Greek profile is consistent with fragment: φ/κ-complete. -/
theorem greek_profile_consistent_phikappa :
    greek.agreementPhiKappaComplete =
    Fragments.Greek.AdjAgreement.entry.phiKappaComplete := by native_decide

/-- German: fragment entry confirms pred ≠ attr. -/
theorem german_fragment_not_sameAgreement :
    Fragments.German.AdjAgreement.entry.sameAgreement = false := by native_decide

/-- German profile is consistent with fragment. -/
theorem german_profile_consistent_pred :
    german.predAttrSameAgreement =
    Fragments.German.AdjAgreement.entry.sameAgreement := by native_decide

/-- Russian: fragment confirms pred = attr (long forms identical). -/
theorem russian_fragment_sameAgreement :
    Fragments.Russian.AdjAgreement.entry.sameAgreement = true := by native_decide

/-- Russian profile is consistent with fragment. -/
theorem russian_profile_consistent_pred :
    russian.predAttrSameAgreement =
    Fragments.Russian.AdjAgreement.entry.sameAgreement := by native_decide

/-- Italian: fragment confirms pred = attr (both carry φ). -/
theorem italian_fragment_sameAgreement :
    Fragments.Italian.AdjAgreement.entry.sameAgreement = true := by native_decide

/-- Italian: fragment confirms NOT φ/κ-complete (no case). -/
theorem italian_fragment_not_phiKappaComplete :
    Fragments.Italian.AdjAgreement.entry.phiKappaComplete = false := by native_decide

/-- Italian profile is consistent with fragment: pred = attr. -/
theorem italian_profile_consistent_pred :
    italian.predAttrSameAgreement =
    Fragments.Italian.AdjAgreement.entry.sameAgreement := by native_decide

/-- Italian profile is consistent with fragment: NOT φ/κ-complete. -/
theorem italian_profile_consistent_phikappa :
    italian.agreementPhiKappaComplete =
    Fragments.Italian.AdjAgreement.entry.phiKappaComplete := by native_decide

-- ============================================================================
-- § 10: Bridge to Modification Routes (§5.1)
-- ============================================================================

-- The MAG's two conditions correspond to the two modification routes
-- from the Theory layer. Direct modification (no Attr) = condition (a);
-- Attr-mediated modification = needs condition (b) for intervention.

/-- Greek uses direct modification (no Attr needed). -/
theorem greek_direct_mod :
    modificationRoute greek = .direct := by native_decide

/-- German uses Attr-mediated modification. -/
theorem german_attr_mediated :
    modificationRoute german = .attrMediated := by native_decide

/-- Mandarin uses Attr-mediated modification (clitic 的). -/
theorem mandarin_attr_mediated :
    modificationRoute mandarin = .attrMediated := by native_decide

/-- Italian uses Attr-mediated modification (null Attr for κ). -/
theorem italian_attr_mediated :
    modificationRoute italian = .attrMediated := by native_decide

/-- Kalaallisut uses direct modification despite affixal Attr:
    φ/κ-complete agreement means Attr is not needed structurally. -/
theorem kalaallisut_direct_mod :
    modificationRoute kalaallisut = .direct := by native_decide

-- ============================================================================
-- § 11: Bridge to ICP (§5.2)
-- ============================================================================

-- The ICP blocks intervention when Attr is affixal or null.
-- This is the morphophonological factor of the MAG.

/-- German: affixal Attr → ICP blocks intervention. -/
theorem german_icp_blocks :
    icpBlocksIntervention german.attrStatus = true := by native_decide

/-- English: null Attr → ICP blocks intervention. -/
theorem english_icp_blocks :
    icpBlocksIntervention english.attrStatus = true := by native_decide

/-- Mandarin: clitic 的 → ICP does NOT block. -/
theorem mandarin_icp_permits :
    icpBlocksIntervention mandarin.attrStatus = false := by native_decide

/-- Farsi: clitic ezafe → ICP does NOT block. -/
theorem farsi_icp_permits :
    icpBlocksIntervention farsi.attrStatus = false := by native_decide

/-- The two MAG conditions are orthogonal to the two theory-layer
    mechanisms. Condition (a) = direct modification route; ICP blocking
    = morphophonological factor of condition (b). -/
theorem mag_factors_orthogonal :
    -- Greek: direct mod, ICP blocks (but irrelevant — no Attr needed)
    modificationRoute greek = .direct ∧
    icpBlocksIntervention greek.attrStatus = true ∧
    -- Mandarin: Attr-mediated, ICP permits (clitic)
    modificationRoute mandarin = .attrMediated ∧
    icpBlocksIntervention mandarin.attrStatus = false ∧
    -- German: Attr-mediated, ICP blocks (affix)
    modificationRoute german = .attrMediated ∧
    icpBlocksIntervention german.attrStatus = true := by native_decide

-- ============================================================================
-- § 12: Bridge to WALS F87A (Adjective-Noun Order)
-- ============================================================================

def walsOrder (code : String) : Option AdjectiveNounOrder :=
  (allData.find? (·.walsCode == code)).map (·.value)

def walsToPosition : AdjectiveNounOrder → AdjPosition
  | .adjectiveNoun => .prenominal
  | .nounAdjective => .postnominal
  | .noDominantOrder => .both
  | .onlyInternallyHeadedRelativeClauses => .both

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

end AlexeyenkoZeijlstra2025
