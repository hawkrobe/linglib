import Linglib.Features.WordOrder
import Linglib.Features.Number.Basic
import Linglib.Features.Gender.Basic
import Linglib.Features.Case.Basic
import Linglib.Morphology.MorphRule
import Linglib.Fragments.Slavic.Russian.Case
import Linglib.Fragments.German.Case
import Linglib.Fragments.Greek.Case

/-!
# Linearization of Complex Modifiers: (Dis)obeying the Head-Final Filter
[alexeyenko-zeijlstra-2025]

The Head-Final Filter (HFF, Williams 1982) states that prenominal modifiers
must not contain post-head material. [alexeyenko-zeijlstra-2025] show
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
   to its host (ICP, [ackema-neeleman-2004]), while clitic/free-word
   Attr imposes no adjacency

We formalize the MAG as a decision procedure matching the paper's decision
trees (44)/(45), encode 24 languages from Table 3, and verify that the MAG
correctly predicts all of them while the HFF fails for 11. Per-language
concord data (case inventories imported from `Fragments/*/Case.lean`) is
checked against the Table 3 profile Booleans.
-/

-- ============================================================================
-- § 0: Input Correspondence Principle (Ackema-Neeleman 2004)
-- ============================================================================

/-! [ackema-neeleman-2004]'s ICP — used by AZ 2025 §5.2 as the
morphophonological factor of the MAG. Was previously in `Morphology/
Core/ICP.lean`; relocated 0.230.455 (sole consumer is this study file).

The ICP constrains the phonological realization of affixes: an affix must
take as its phonological host the head of the phrase it selects. Affixes
are always linearly adjacent to their syntactic selectee.

When the attributivizer (Attr) is realized as an affix, the ICP forces it
to be adjacent to the adjective head A — dependents of A (PPs, CPs, AdvPs)
cannot linearly intervene between A and N. When Attr is a clitic or free
word, the ICP does not apply. For null affixes, the Affix Continuity
Constraint (Ackema-Neeleman §70) extends the ICP. -/

namespace AlexeyenkoZeijlstra2025

open Morphology (MorphStatus)

/-! ## The Attr head and modification routes ([alexeyenko-zeijlstra-2025] §5)

Formerly `Syntax/Minimalist/Modification.lean` — relocated here as this paper's own
analysis (it had a single consumer, this study). The theory-neutral substrate it used
(`MAGFeatureType`/`AdjAgreementEntry`) is now `Syntax/Agreement/AdjAgreement.lean`,
imported theory-neutrally by the `Fragments/*/AdjAgreement` files. -/

/-- Morphophonological status of the attributivizer (Attr head, §5.2). Determines
    whether Attr imposes linear adjacency with the adjective. -/
inductive AttrStatus where
  | affix | clitic | freeWord | null
  deriving DecidableEq, Repr

/-- Position of attributive adjectives relative to the modified noun. -/
inductive AdjPosition where
  | prenominal | postnominal | both
  deriving DecidableEq, Repr

/-- Morphosyntactic profile of adjectives in a language — the MAG (34) factors:
    agreement identity (pred = attr), φ/κ-completeness, and the attributivizer's status. -/
structure AdjMorphProfile where
  adjPosition               : AdjPosition
  apDirection               : HeadDirection
  predAttrSameAgreement     : Bool
  agreementPhiKappaComplete : Bool
  attrStatus                : AttrStatus
  deriving DecidableEq, Repr

/-- The two routes to nominal modification (§5.1): `direct` (adjective carries
    `[N, uN]`) vs `attrMediated` (an Attr head converts features). -/
inductive ModificationRoute where
  | direct | attrMediated
  deriving DecidableEq, Repr

/-- φ/κ-complete languages modify directly; all others require an Attr head. -/
def modificationRoute (prof : AdjMorphProfile) : ModificationRoute :=
  if prof.predAttrSameAgreement && prof.agreementPhiKappaComplete then .direct
  else .attrMediated

/-- φ/κ-complete languages use direct modification. -/
theorem phiKappaComplete_implies_direct (prof : AdjMorphProfile)
    (hSame : prof.predAttrSameAgreement = true)
    (hComplete : prof.agreementPhiKappaComplete = true) :
    modificationRoute prof = .direct := by simp [modificationRoute, hSame, hComplete]

/-- Languages with pred ≠ attr require Attr. -/
theorem predNeAttr_implies_attrMediated (prof : AdjMorphProfile)
    (h : prof.predAttrSameAgreement = false) :
    modificationRoute prof = .attrMediated := by simp [modificationRoute, h]

/-- Languages with incomplete φ/κ require Attr. -/
theorem incomplete_implies_attrMediated (prof : AdjMorphProfile)
    (h : prof.agreementPhiKappaComplete = false) :
    modificationRoute prof = .attrMediated := by simp [modificationRoute, h]

/-- Map the framework-agnostic `MorphStatus` (Zwicky-Pullum clitic-affix cline) to
    the MAG's `AttrStatus`: affixes impose adjacency, clitics are independent. -/
def morphStatusToAttrStatus : MorphStatus → AttrStatus
  | .freeWord      => .freeWord
  | .simpleClitic  => .clitic
  | .specialClitic => .clitic
  | .inflAffix     => .affix
  | .derivAffix    => .affix

end AlexeyenkoZeijlstra2025

namespace Morphology.ICP

open AlexeyenkoZeijlstra2025 (AttrStatus)

/-- Does the morphophonological status of Attr impose adjacency between
    Attr and the adjective head? The ICP applies to affixes (overt and
    null); clitics and free words are not constrained. -/
def imposesAdjacency : AttrStatus → Bool
  | .affix    => true
  | .null     => true   -- null affixes: Affix Continuity Constraint (70)
  | .clitic   => false
  | .freeWord => false

/-- When adjacency is imposed, dependents of A cannot intervene between
    A and the modified N. This is the morphophonological factor of the MAG. -/
def icpBlocksIntervention (status : AttrStatus) : Bool :=
  imposesAdjacency status

theorem affix_blocks : icpBlocksIntervention .affix = true := rfl
theorem null_blocks : icpBlocksIntervention .null = true := rfl
theorem clitic_permits : icpBlocksIntervention .clitic = false := rfl
theorem freeWord_permits : icpBlocksIntervention .freeWord = false := rfl

/-- MAG condition (b) is exactly the negation of ICP adjacency. -/
theorem magCondB_is_not_icp (status : AttrStatus) :
    (match status with
     | .clitic | .freeWord => true
     | .affix  | .null     => false) = !icpBlocksIntervention status := by
  cases status <;> rfl

end Morphology.ICP

namespace AlexeyenkoZeijlstra2025

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
theorem mag_predicts_all : table3.all magCorrect = true := by decide

-- Per-language theorems: changing one profile breaks exactly one theorem.

theorem mag_greek : interventionPredicted greek = true := by decide
theorem mag_russian : interventionPredicted russian = true := by decide
theorem mag_bulgarian : interventionPredicted bulgarian = true := by decide
theorem mag_polish : interventionPredicted polish = true := by decide
theorem mag_lithuanian : interventionPredicted lithuanian = true := by decide
theorem mag_latin : interventionPredicted latin = true := by decide
theorem mag_mandarin : interventionPredicted mandarin = true := by decide
theorem mag_tagalog : interventionPredicted tagalog = true := by decide

theorem mag_german : interventionPredicted german = false := by decide
theorem mag_english : interventionPredicted english = false := by decide
theorem mag_dutch : interventionPredicted dutch = false := by decide
theorem mag_icelandic : interventionPredicted icelandic = false := by decide
theorem mag_serboCroatian : interventionPredicted serboCroatian = false := by decide
theorem mag_hungarian : interventionPredicted hungarian = false := by decide
theorem mag_georgian : interventionPredicted georgian = false := by decide
theorem mag_armenian : interventionPredicted armenian = false := by decide
theorem mag_italian : interventionPredicted italian = false := by decide
theorem mag_japanese : interventionPredicted japanese = false := by decide

theorem mag_basque : interventionPredicted basque = false := by decide
theorem mag_chacobo : interventionPredicted chacobo = false := by decide
theorem mag_easternOromo : interventionPredicted easternOromo = false := by decide

theorem mag_farsi : interventionPredicted farsi = true := by decide
theorem mag_atong : interventionPredicted atong = true := by decide
theorem mag_kalaallisut : interventionPredicted kalaallisut = true := by decide

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
    (table3.filter hffWrong).length = 11 := by decide

theorem mag_correct_count :
    (table3.filter magCorrect).length = 24 := by decide

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
-- § 9: Adjectival concord and MAG (34a)
-- ============================================================================

/-- The nominal features an adjectival form is specified for — MAG (34a)'s
    φ/κ-features — one `Finset` per dimension. Including case (κ) takes a side
    in a live debate: canonical typology confines agreement features to
    person/number/gender, with case assigned to the NP by government
    ([corbett-1998]; [corbett-2006]'s canonical-agreement hedges; the stance of
    `Syntax/Agreement/Paradigm`), while the nominal-concord literature treats
    case concord on adjectives as the same feature-sharing phenomenon.
    [alexeyenko-zeijlstra-2025] side with the latter: fn 17 has case "always
    present as a feature on DPs", and their percolation analysis carries κ
    through the extended nominal projection. -/
structure Concord where
  numbers : Finset Number := ∅
  genders : Finset Gender := ∅
  cases   : Finset Case := ∅
  deriving DecidableEq

/-- Pointwise inclusion of concord specifications. -/
instance : LE Concord where
  le a b := a.numbers ⊆ b.numbers ∧ a.genders ⊆ b.genders ∧ a.cases ⊆ b.cases

instance : DecidableLE Concord := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A language's adjectival concord data: what predicative and attributive
    forms are specified for, and what the DP carries. -/
structure AdjConcord where
  pred : Concord
  attr : Concord
  dp   : Concord

namespace AdjConcord

variable (c : AdjConcord)

/-- MAG (34a) clause 1: the agreement marker is also present on the
    predicative form. -/
def SameAgreement : Prop := c.pred = c.attr

/-- MAG (34a) clause 2: the attributive marker is specified for all
    features available in the DP. -/
def PhiKappaComplete : Prop := c.dp ≤ c.attr

instance : Decidable c.SameAgreement := inferInstanceAs (Decidable (_ = _))

instance : Decidable c.PhiKappaComplete := inferInstanceAs (Decidable (_ ≤ _))

end AdjConcord

private def russianLongForm : Concord :=
  { numbers := {.singular, .plural}
  , genders := {.masculine, .feminine, .neuter}
  , cases   := Russian.Case.caseInventory }

/-- Russian long forms: number, gender, and the full 6-case inventory
    (`Russian.Case.caseInventory`), identical in pred and attr use and covering
    the DP ((39), Table 4). Short forms (full φ, no κ) are predicative-only and
    so never bear on (34a). -/
def russianConcord : AdjConcord := ⟨russianLongForm, russianLongForm, russianLongForm⟩

private def greekForm : Concord :=
  { numbers := {.singular, .plural}
  , genders := {.masculine, .feminine, .neuter}
  , cases   := Greek.Case.caseInventory }

/-- Greek adjectives: fully inflected for gender, number, and case in both
    uses (37); 3-case inventory `Greek.Case.caseInventory`. -/
def greekConcord : AdjConcord := ⟨greekForm, greekForm, greekForm⟩

private def germanAttrForm : Concord :=
  { numbers := {.singular, .plural}
  , genders := {.masculine, .feminine, .neuter}
  , cases   := German.Case.caseInventory }

/-- German: predicative adjectives are bare (*Er ist stolz* 'He is proud');
    attributive forms carry gender/number/case endings ((38), (60)), with the
    4-case `German.Case.caseInventory`. -/
def germanConcord : AdjConcord := ⟨{}, germanAttrForm, germanAttrForm⟩

private def italianForm : Concord :=
  { numbers := {.singular, .plural}
  , genders := {.masculine, .feminine} }

/-- Italian adjectives: gender and number in both uses, never case (36); the
    DP carries κ regardless (fn 17). -/
def italianConcord : AdjConcord :=
  ⟨italianForm, italianForm, { italianForm with cases := {.nom, .acc} }⟩

-- Table 3's profile Booleans are checked against the concord data: changing
-- a concord feature set breaks exactly these theorems.

/-- Russian: long forms identical in pred and attr use. -/
theorem russian_profile_consistent_pred :
    russian.predAttrSameAgreement ↔ russianConcord.SameAgreement := by decide

/-- Russian: long forms cover the DP's φ/κ-features. -/
theorem russian_profile_consistent_phikappa :
    russian.agreementPhiKappaComplete ↔ russianConcord.PhiKappaComplete := by decide

/-- Greek: pred = attr. -/
theorem greek_profile_consistent_pred :
    greek.predAttrSameAgreement ↔ greekConcord.SameAgreement := by decide

/-- Greek: φ/κ-complete. -/
theorem greek_profile_consistent_phikappa :
    greek.agreementPhiKappaComplete ↔ greekConcord.PhiKappaComplete := by decide

/-- German: pred ≠ attr (bare predicative). -/
theorem german_profile_consistent_pred :
    german.predAttrSameAgreement ↔ germanConcord.SameAgreement := by decide

/-- German: attributive forms do cover the DP (completeness is not what
    blocks German — clause 1 is). -/
theorem german_profile_consistent_phikappa :
    german.agreementPhiKappaComplete ↔ germanConcord.PhiKappaComplete := by decide

/-- Italian: pred = attr. -/
theorem italian_profile_consistent_pred :
    italian.predAttrSameAgreement ↔ italianConcord.SameAgreement := by decide

/-- Italian: NOT φ/κ-complete (no case on adjectives). -/
theorem italian_profile_consistent_phikappa :
    italian.agreementPhiKappaComplete ↔ italianConcord.PhiKappaComplete := by decide

-- ============================================================================
-- § 10: Bridge to Modification Routes (§5.1)
-- ============================================================================

-- The MAG's two conditions correspond to the two modification routes
-- from the Theory layer. Direct modification (no Attr) = condition (a);
-- Attr-mediated modification = needs condition (b) for intervention.

/-- Greek uses direct modification (no Attr needed). -/
theorem greek_direct_mod :
    modificationRoute greek = .direct := by decide

/-- German uses Attr-mediated modification. -/
theorem german_attr_mediated :
    modificationRoute german = .attrMediated := by decide

/-- Mandarin uses Attr-mediated modification (clitic 的). -/
theorem mandarin_attr_mediated :
    modificationRoute mandarin = .attrMediated := by decide

/-- Italian uses Attr-mediated modification (null Attr for κ). -/
theorem italian_attr_mediated :
    modificationRoute italian = .attrMediated := by decide

/-- Kalaallisut uses direct modification despite affixal Attr:
    φ/κ-complete agreement means Attr is not needed structurally. -/
theorem kalaallisut_direct_mod :
    modificationRoute kalaallisut = .direct := by decide

-- ============================================================================
-- § 11: Bridge to ICP (§5.2)
-- ============================================================================

-- The ICP blocks intervention when Attr is affixal or null.
-- This is the morphophonological factor of the MAG.

/-- German: affixal Attr → ICP blocks intervention. -/
theorem german_icp_blocks :
    icpBlocksIntervention german.attrStatus = true := by decide

/-- English: null Attr → ICP blocks intervention. -/
theorem english_icp_blocks :
    icpBlocksIntervention english.attrStatus = true := by decide

/-- Mandarin: clitic 的 → ICP does NOT block. -/
theorem mandarin_icp_permits :
    icpBlocksIntervention mandarin.attrStatus = false := by decide

/-- Farsi: clitic ezafe → ICP does NOT block. -/
theorem farsi_icp_permits :
    icpBlocksIntervention farsi.attrStatus = false := by decide

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
    icpBlocksIntervention german.attrStatus = true := by decide

end AlexeyenkoZeijlstra2025
