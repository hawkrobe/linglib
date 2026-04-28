import Linglib.Phenomena.Ergativity.Basic
import Linglib.Theories.Syntax.Minimalist.Voice
import Linglib.Theories.Syntax.Minimalist.Phase
import Linglib.Theories.Syntax.Minimalist.ClauseSpine
import Linglib.Fragments.Mayan.Qanjobal.Agreement
import Linglib.Fragments.Mayan.Qanjobal.AgentFocus
import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Agreement

/-!
# Coon, Mateo Pedro & Preminger (2014) @cite{coon-mateo-pedro-preminger-2014}

The role of Case in A-bar extraction asymmetries: Evidence from Mayan.
*Linguistic Variation* 14(2), 179–242.

## Core Claim

Syntactic ergativity — the ban on A-bar extracting transitive subjects in
languages like Q'anjob'al — is not about properties of the ergative NP.
It is a **locality problem in case assignment to the absolutive object**.

In HIGH-ABS languages (ABS=NOM), Infl⁰ assigns absolutive case. The
transitive object must raise out of vP to receive this case, passing
through the single escape hatch at the vP phase edge — **trapping** the
subject. In LOW-ABS languages (ABS=DEF), v⁰ assigns absolutive locally
within vP. The escape hatch is free and the subject extracts without issue.

## The Agent Focus Construction

Q'anjob'al's AF morpheme *-on* is analyzed as a marked variant of Voice⁰
that assigns structural case to the internal argument (the transitive
object). When Voice⁰_AF assigns case, Infl⁰ is freed to assign case to
the subject. With the escape hatch unoccupied, the subject can extract.
The intransitive status suffix *-i* surfaces because AF Voice is non-phasal
(intransitive v⁰).

## The Crazy Antipassive

The same *-on* morpheme appears in Q'anjob'al non-finite embedded
transitives — environments where Infl⁰ is absent and thus cannot assign
case to objects. The *-on* provides the needed case source, further
supporting its role as a case-assigner.

## Three Factors for Syntactic Ergativity in Q'anjob'al

1. Transitive vP is phasal (constitutes a locality domain)
2. The transitive subject is generated below vP (in Spec,VoiceP)
3. There is only a single specifier available for extraction out of vP
-/

namespace CoonMateoPedroPreminger2014

open Minimalist
open Phenomena.Ergativity
open Fragments.Mayan (ABSPosition CaseLocus toCaseLocus)

-- § 1 uses `CaseLocus` and `toCaseLocus` from `Fragments.Mayan.Params`.

-- ============================================================================
-- § 2: Legate (2008) Abstract Case Decomposition
-- ============================================================================

/-- Abstract case features assigned by functional heads. Following
    @cite{legate-2008}, "absolutive" is not an abstract case but a descriptive
    cover term for the morphological form shared by transitive objects and
    intransitive subjects. The actual abstract cases are:

    - **NOM**: assigned by Infl⁰ (to intransitive subjects universally,
      and to transitive objects in ABS=NOM languages)
    - **ACC**: assigned by v⁰ (to transitive objects in ABS=DEF languages)
    - **ERG**: assigned by v⁰ (to transitive subjects universally) -/
inductive AbstractCase where
  | nom   -- from Infl⁰
  | acc   -- from v⁰ (object)
  | erg   -- from v⁰ (subject)
  deriving DecidableEq, Repr

/-- Which functional head assigns each abstract case. -/
inductive FunctionalHead where
  | infl  -- Infl⁰
  | v     -- v⁰ (transitive)
  deriving DecidableEq, Repr

def AbstractCase.assigner : AbstractCase → FunctionalHead
  | .nom => .infl
  | .acc => .v
  | .erg => .v

/-- ERG is always from v⁰, NOM is always from Infl⁰. -/
theorem erg_from_v : AbstractCase.erg.assigner = .v := rfl
theorem nom_from_infl : AbstractCase.nom.assigner = .infl := rfl

/-- The abstract case assigned to the transitive object depends on the
    case locus parameter. -/
def objectAbstractCase : CaseLocus → AbstractCase
  | .absNom => .nom   -- Infl⁰ assigns NOM to object
  | .absDef => .acc   -- v⁰ assigns ACC to object

/-- Transitive subjects always receive ERG from v⁰, regardless of
    case locus. This uniformity is the paper's key insight: the
    variation is in how *objects* are licensed, not subjects. -/
def subjectAbstractCase (_locus : CaseLocus) : AbstractCase := .erg

theorem subject_case_uniform (l1 l2 : CaseLocus) :
    subjectAbstractCase l1 = subjectAbstractCase l2 := rfl

-- ============================================================================
-- § 3: Case Assignment Configuration
-- ============================================================================

/-- Does the object need to move out of vP for case? The object must escape
    the vP phase domain to reach Infl⁰ iff case is assigned by Infl⁰. -/
def objectMustExitVP (locus : CaseLocus) : Bool :=
  match locus with
  | .absNom => true   -- Infl⁰ is outside the vP phase boundary
  | .absDef => false  -- v⁰ is inside the vP phase domain

/-- The object case assigner determines whether the object is licensed
    inside or outside vP. -/
def objectCaseIsExternal (locus : CaseLocus) : Bool :=
  (objectAbstractCase locus).assigner == .infl

-- ============================================================================
-- § 4: The Trapping Mechanism
-- ============================================================================

/-- When the transitive object exits vP through the phase edge (Spec,vP),
    it occupies the single escape hatch. The subject, base-generated in
    Spec,VoiceP (below the vP phase boundary), cannot exit the phase
    domain because the escape hatch is occupied.

    This is the paper's core contribution: the ban on extracting
    transitive subjects follows from a locality problem in how case is
    assigned to *objects*, not from any property of the ergative subject
    itself. -/
def subjectTrapped (locus : CaseLocus) (transitive : Bool) : Bool :=
  transitive && objectMustExitVP locus

/-- Syntactic ergativity: the ban on A-bar extraction of transitive
    subjects. Predicted to occur iff the language is ABS=NOM (HIGH-ABS). -/
def hasSyntacticErgativity (locus : CaseLocus) : Bool :=
  subjectTrapped locus true

theorem absNom_has_syntactic_ergativity :
    hasSyntacticErgativity .absNom = true := rfl

theorem absDef_no_syntactic_ergativity :
    hasSyntacticErgativity .absDef = false := rfl

/-- Intransitive subjects are NEVER trapped, regardless of case locus:
    there is no transitive object to occupy the escape hatch. This
    correctly predicts that intransitive subjects extract freely in
    both HIGH-ABS and LOW-ABS languages. -/
theorem intransitive_subject_never_trapped (locus : CaseLocus) :
    subjectTrapped locus false = false := by
  cases locus <;> rfl

-- ============================================================================
-- § 5: Agent Focus (Voice⁰_AF)
-- ============================================================================

/-- Agent Focus Voice: a marked variant of Voice⁰ that assigns structural
    case to the internal argument (the transitive object).

    Following @cite{ordonez-1995} on Popti', *-on* assigns case to the
    object. Unlike regular transitive Voice, AF Voice is NOT a phase head:
    its v⁰ is the intransitive variety (non-phasal), explaining why the
    intransitive status suffix *-i* surfaces rather than transitive *-V'*.

    AF is a "last-resort" strategy, akin to English *of*-insertion: the
    marked variant of Voice⁰ is merged only when the normal derivation
    (with regular transitive Voice) would crash — i.e., when the subject
    must be A-bar extracted. -/
def voiceAF : VoiceHead :=
  { flavor := .agentive
  , hasD := true
  , phaseHead := false      -- intransitive v⁰: NOT phasal
  , checksCase := true }    -- assigns case to object

/-- AF Voice assigns case to the object. -/
theorem af_assigns_case : voiceAF.checksCase = true := rfl

/-- AF Voice is NOT a phase head (intransitive v⁰). -/
theorem af_not_phase : voiceAF.phaseHead = false := rfl

/-- AF Voice still introduces an external argument (the agent). -/
theorem af_introduces_agent : voiceAF.assignsTheta = true := rfl

/-- AF Voice circumvents the trapping mechanism because it assigns case to
    the object (so the object need not move to Spec,vP) AND because AF's v⁰
    is non-phasal (so vP is not a locality domain). Either property alone
    would free the subject, but both hold simultaneously for AF Voice. -/
def afCircumventsTrapping : Bool :=
  voiceAF.checksCase && !voiceAF.phaseHead

theorem af_frees_subject : afCircumventsTrapping = true := rfl

/-- The case-assignment property alone is what frees extraction: when
    Voice checks case, the object receives case inside vP and need not
    move to the escape hatch. This is the paper's primary explanation
    for why AF circumvents the extraction ban. -/
def caseAloneFreesExtraction (v : VoiceHead) : Bool :=
  v.checksCase

theorem af_case_frees : caseAloneFreesExtraction voiceAF = true := rfl

/-- The non-phasal status explains AF's *morphology* (intransitive
    status suffix *-i*) rather than the extraction facts. Since AF's v⁰
    is intransitive, no ergative case is assigned to the subject. -/
theorem af_morphology_from_phase :
    voiceAF.phaseHead = false := rfl

/-- Contrast with regular transitive Voice: phasal, does NOT check case. -/
theorem regular_voice_traps :
    voiceAgent.phaseHead = true ∧ voiceAgent.checksCase = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Non-Finite Predictions
-- ============================================================================

/-- In non-finite embedded clauses, Infl⁰ is absent (no aspect marking).
    This makes predictions depending on the case locus:

    - **ABS=NOM**: transitive objects cannot be licensed (Infl⁰ absent).
      They require *-on* ("Crazy Antipassive") or detransitivization.
    - **ABS=DEF**: transitive objects are licensed by v⁰ (present even
      without Infl⁰). They are fine in non-finite clauses.

    Intransitive subjects lose absolutive case in BOTH types (Infl⁰ assigns
    NOM to intransitive subjects universally in Mayan). -/
def objectLicensedInNonFinite (locus : CaseLocus) : Bool :=
  match locus with
  | .absNom => false  -- Infl⁰ absent → no case source for object
  | .absDef => true   -- v⁰ present → object licensed

theorem absNom_objects_unlicensed_nonfinite :
    objectLicensedInNonFinite .absNom = false := rfl

theorem absDef_objects_licensed_nonfinite :
    objectLicensedInNonFinite .absDef = true := rfl

/-- Intransitive subjects are unlicensed in non-finite clauses regardless
    of case locus, because Infl⁰ (the universal NOM assigner for
    intransitive S) is absent. -/
def intranSLicensedInNonFinite (_locus : CaseLocus) : Bool := false

theorem intranS_unlicensed_nonfinite (locus : CaseLocus) :
    intranSLicensedInNonFinite locus = false := rfl

-- ============================================================================
-- § 7: Caseless Objects
-- ============================================================================

/-- Some objects do not require structural case: reflexive objects,
    extended reflexive objects, and bare (determinerless) NPs. These
    are licensed by pseudo-incorporation into the verb stem (§5.2).

    Extended reflexives (possessor bound by subject, e.g., *s-na?*
    '3ERG-house') are formally identical to reflexives — the possessed
    nominal has lost its independent referential meaning.

    Prediction: AF is impossible with caseless objects. Since AF exists
    precisely to assign case to the object, it is vacuous (and thus
    blocked as last-resort) when the object needs no case. -/
inductive ObjectType where
  | fullDP             -- requires structural case
  | reflexive          -- caseless (incorporated)
  | extendedReflexive  -- caseless (possessor bound by subject)
  | bareNP             -- caseless (pseudo-incorporated)
  deriving DecidableEq, Repr

def ObjectType.needsCase : ObjectType → Bool
  | .fullDP            => true
  | .reflexive         => false
  | .extendedReflexive => false
  | .bareNP            => false

/-- AF is available iff the object needs case. -/
def afAvailable (obj : ObjectType) : Bool := obj.needsCase

theorem af_available_fullDP : afAvailable .fullDP = true := rfl
theorem af_unavailable_reflexive : afAvailable .reflexive = false := rfl
theorem af_unavailable_extReflexive : afAvailable .extendedReflexive = false := rfl
theorem af_unavailable_bareNP : afAvailable .bareNP = false := rfl

/-- When the object is caseless, regular transitive Voice is used even
    for agent extraction: the object remains inside vP (no case-driven
    movement) and does not block the escape hatch. The subject is
    NOT trapped. -/
def caselessObjectFreesSubject (obj : ObjectType) : Bool :=
  !obj.needsCase

theorem reflexive_frees_subject :
    caselessObjectFreesSubject .reflexive = true := rfl

-- ============================================================================
-- § 8: Bridge to Existing Fragments
-- ============================================================================

/-- Q'anjob'al is a HIGH-ABS language with syntactic ergativity. -/
theorem qanjobal_has_syntactic_ergativity :
    hasSyntacticErgativity (.absNom) = true := rfl

/-- Chol is a LOW-ABS language without syntactic ergativity. -/
theorem chol_no_syntactic_ergativity :
    hasSyntacticErgativity (.absDef) = false := rfl

/-- Q'anjob'al's ergative alignment matches the standard pattern:
    transitive agent = ERG, transitive object = ABS. -/
theorem qanjobal_erg_alignment :
    Fragments.Mayan.Qanjobal.ArgPosition.case .A = .erg ∧
    Fragments.Mayan.Qanjobal.ArgPosition.case .P = .abs := ⟨rfl, rfl⟩

/-- Chol's ergative alignment matches the same standard pattern. -/
theorem chol_erg_alignment :
    Fragments.Mayan.Chol.ArgPosition.case .A = .erg ∧
    Fragments.Mayan.Chol.ArgPosition.case .P = .abs := ⟨rfl, rfl⟩

/-- Despite sharing ergative morphology, Q'anjob'al and Chol differ in
    whether agent extraction is banned. The difference traces to their
    distinct case loci, not to properties of the ergative NP. -/
theorem shared_morphology_different_syntax :
    -- Same ergative case on agent
    Fragments.Mayan.Qanjobal.ArgPosition.case .A =
      Fragments.Mayan.Chol.ArgPosition.case .A ∧
    -- But different syntactic ergativity predictions
    hasSyntacticErgativity .absNom ≠ hasSyntacticErgativity .absDef :=
  ⟨rfl, by decide⟩

/-- Fragment-grounded ABSPosition: Q'anjob'al is HIGH-ABS. -/
theorem qanjobal_high_abs :
    Fragments.Mayan.Qanjobal.absPosition = .high := rfl

/-- Fragment-grounded ABSPosition: Chol is LOW-ABS. -/
theorem chol_low_abs :
    Fragments.Mayan.Chol.absPosition = .low := rfl

/-- The fragment ABSPosition values derive the correct syntactic
    ergativity predictions: Q'anjob'al has it, Chol does not.
    This grounds Tada's Generalization in fragment data rather than
    hard-coded table entries. -/
theorem fragments_ground_tada :
    hasSyntacticErgativity (toCaseLocus Fragments.Mayan.Qanjobal.absPosition) = true ∧
    hasSyntacticErgativity (toCaseLocus Fragments.Mayan.Chol.absPosition) = false :=
  ⟨rfl, rfl⟩

/-- Q'anjob'al's extraction data is consistent with the prediction:
    agent extraction is banned in regular transitives. -/
theorem qanjobal_extraction_consistent :
    Fragments.Mayan.Qanjobal.ExtractionTarget.agent.extractable = false := rfl

/-- Chol's extraction data is consistent: agent extracts freely. -/
theorem chol_extraction_consistent :
    Fragments.Mayan.Chol.ExtractionTarget.agent.extractable = true := rfl

/-- Q'anjob'al's AF form carries the intransitive status suffix, matching
    the prediction that AF Voice is non-phasal (intransitive v⁰). -/
theorem qanjobal_af_itv :
    Fragments.Mayan.Qanjobal.agentFocusForm.statusSuffix = .itv := rfl

/-- The Crazy Antipassive form is identical to AF: same *-on* morpheme,
    same intransitive status suffix. Supports the unified analysis of
    *-on* as a case-assigner in environments where case is otherwise
    unavailable. -/
theorem crazy_ap_unified :
    Fragments.Mayan.Qanjobal.crazyAntipassiveForm = Fragments.Mayan.Qanjobal.agentFocusForm := rfl

/-- Non-finite absolutive asymmetry in Chol: objects are available
    (v⁰ assigns case) but intransitive subjects are not (Infl⁰ absent).
    Follows from LOW-ABS: v⁰ handles objects, Infl⁰ handles intransitives. -/
theorem chol_nonfinite_predictions :
    Fragments.Mayan.Chol.absObjectInNonFinite = true ∧
    Fragments.Mayan.Chol.absIntranSInNonFinite = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Tada's Generalization (theoretical derivation)
-- ============================================================================

/-- Tada's Generalization is now DERIVED from the case-assignment
    analysis rather than merely stated as a correlation. The observable
    parameter `ABSPosition` maps to `CaseLocus`, which determines whether
    syntactic ergativity arises. -/
theorem tada_derived_high :
    hasSyntacticErgativity (toCaseLocus .high) = true := rfl

theorem tada_derived_low :
    hasSyntacticErgativity (toCaseLocus .low) = false := rfl

/-- The morphological observation (ABSPosition) and the syntactic
    observation (extraction asymmetry) are connected through the
    case-assignment locus: for both values of the parameter, the
    predicted syntactic ergativity matches what Tada's table reports
    for the non-outlier languages. -/
theorem tada_from_case_theory (pos : ABSPosition) :
    hasSyntacticErgativity (toCaseLocus pos) =
      (pos == .high) := by
  cases pos <;> rfl

-- ============================================================================
-- § 10: Three Factors for Syntactic Ergativity
-- ============================================================================

/-- The three factors that combine to produce the ban on extracting
    transitive subjects in Q'anjob'al. All three are necessary; removing
    any one would free the subject. -/
structure SyntacticErgativityFactors where
  /-- I. Transitive vP is phasal (locality domain). -/
  vPIsPhasal : Bool
  /-- II. The transitive subject is generated below vP. -/
  subjectBelowVP : Bool
  /-- III. Only a single specifier available for extraction out of vP. -/
  singleEscapeHatch : Bool
  deriving DecidableEq, Repr

def SyntacticErgativityFactors.producesTrapping (f : SyntacticErgativityFactors) : Bool :=
  f.vPIsPhasal && f.subjectBelowVP && f.singleEscapeHatch

/-- Q'anjob'al instantiates all three factors. -/
def qanjobalFactors : SyntacticErgativityFactors :=
  { vPIsPhasal := true, subjectBelowVP := true, singleEscapeHatch := true }

theorem qanjobal_all_three : qanjobalFactors.producesTrapping = true := rfl

/-- Removing any single factor would free the subject. -/
theorem factor1_necessary :
    ({ qanjobalFactors with vPIsPhasal := false }).producesTrapping = false := rfl

theorem factor2_necessary :
    ({ qanjobalFactors with subjectBelowVP := false }).producesTrapping = false := rfl

theorem factor3_necessary :
    ({ qanjobalFactors with singleEscapeHatch := false }).producesTrapping = false := rfl

/-- Agentive Voice is a phase head — this is factor I. -/
theorem voice_phase_is_factor1 :
    voiceAgent.phaseHead = true := rfl

/-- AF removes factor I: AF Voice is not phasal. With a non-phasal vP,
    there is no locality boundary trapping the subject. -/
theorem af_removes_factor1 :
    voiceAF.phaseHead = false := rfl

-- ============================================================================
-- § 11: Morphological × Syntactic Ergativity Typology
-- ============================================================================

/-- The paper's table (10): morphological ergativity and syntactic ergativity
    are logically independent. Morphological ergativity is shared by all Mayan
    languages; syntactic ergativity (the extraction ban) arises only in
    ABS=NOM (HIGH-ABS) languages.

    |                        | +morph.erg | -morph.erg |
    |------------------------|-----------|-----------|
    | +syntactic ergativity  | Q'anjob'al | unattested |
    | -syntactic ergativity  | Chol       | English    |

    The [-morph,+syn] cell is predicted unattested: syntactic ergativity
    requires Infl⁰ to assign case to the object, which only arises in
    morphologically ergative systems. -/
structure ErgativityTypology where
  morphErg : Bool
  synErg  : Bool
  deriving DecidableEq, Repr

def qanjobalTypology : ErgativityTypology := ⟨true, true⟩
def cholTypology : ErgativityTypology := ⟨true, false⟩
def englishTypology : ErgativityTypology := ⟨false, false⟩

/-- Morphological ergativity is necessary but not sufficient for syntactic
    ergativity. Q'anjob'al and Chol are both morphologically ergative but
    differ in syntactic ergativity. -/
theorem morph_erg_necessary_not_sufficient :
    qanjobalTypology.morphErg = cholTypology.morphErg ∧
    qanjobalTypology.synErg ≠ cholTypology.synErg := ⟨rfl, by decide⟩

/-- The [-morph.erg, +syn.erg] cell is predicted unattested:
    syntactic ergativity requires HIGH-ABS (Infl⁰ licensing objects),
    which entails morphological ergativity. -/
def predictedUnattested (t : ErgativityTypology) : Bool :=
  !t.morphErg && t.synErg

theorem unattested_cell :
    predictedUnattested ⟨false, true⟩ = true := rfl

theorem attested_cells :
    predictedUnattested qanjobalTypology = false ∧
    predictedUnattested cholTypology = false ∧
    predictedUnattested englishTypology = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 12: Person-Conditioned AF (bridge)
-- ============================================================================

/-- AF is restricted to 3rd person agents in Q'anjob'al (§5.1, ex. 72).
    The fragment's `PersonRestriction` captures this. The theoretical
    explanation: 1st/2nd person pronouns may be base-generated in Spec,CP
    (following Baker 2008), so they never need to extract *through* the
    vP phase edge — the trapping problem does not arise for them.

    The Crazy Antipassive, by contrast, is NOT person-restricted: it
    applies in ALL non-finite embedded transitives regardless of the
    person of the subject, because the trigger there is the absence of
    Infl⁰ (not extraction through a phase edge). -/
theorem af_person_restriction :
    Fragments.Mayan.Qanjobal.PersonRestriction.third.requiresAF = true ∧
    Fragments.Mayan.Qanjobal.PersonRestriction.first.requiresAF = false := ⟨rfl, rfl⟩

theorem crazy_ap_no_person_restriction :
    Fragments.Mayan.Qanjobal.PersonRestriction.first.requiresCrazyAP = true ∧
    Fragments.Mayan.Qanjobal.PersonRestriction.third.requiresCrazyAP = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 13: vP-Internal Extraction Ban
-- ============================================================================

/-- The paper's §5.3 prediction: in HIGH-ABS languages, not only subjects
    but NOTHING generated inside a transitive vP (besides the object itself)
    should be able to escape. The object's movement to Spec,vP for case
    renders the single escape hatch occupied — trapping everything inside
    the phase domain.

    This distinguishes the case-based account from ergative-property
    accounts: the latter predict only subjects are banned; the former
    predicts a general vP-internal extraction restriction. -/
inductive VPInternalElement where
  | subject       -- transitive subject (in Spec,VoiceP)
  | lowAdverb     -- manner adverb (adjoined below vP)
  | secondObject  -- second object in DOC (if it existed)
  deriving DecidableEq, Repr

/-- Can this vP-internal element escape a transitive vP in a HIGH-ABS
    language? None can — the escape hatch is occupied by the object. -/
def VPInternalElement.canEscapeHighABS : VPInternalElement → Bool
  | .subject      => false
  | .lowAdverb    => false
  | .secondObject => false

/-- In a LOW-ABS language, the escape hatch is free. -/
def VPInternalElement.canEscapeLowABS : VPInternalElement → Bool
  | .subject      => true
  | .lowAdverb    => true
  | .secondObject => true

theorem vp_internal_ban_high_abs :
    VPInternalElement.subject.canEscapeHighABS = false ∧
    VPInternalElement.lowAdverb.canEscapeHighABS = false ∧
    VPInternalElement.secondObject.canEscapeHighABS = false := ⟨rfl, rfl, rfl⟩

theorem vp_internal_free_low_abs :
    VPInternalElement.subject.canEscapeLowABS = true ∧
    VPInternalElement.lowAdverb.canEscapeLowABS = true ∧
    VPInternalElement.secondObject.canEscapeLowABS = true := ⟨rfl, rfl, rfl⟩

/-- Double-object constructions are systematically absent in HIGH-ABS
    languages (Q'anjob'al, Kaqchikel) but present in LOW-ABS Chol (via
    applicative). This is consistent with the general vP-internal ban. -/
def hasDoubleObjectConstruction (locus : CaseLocus) : Bool :=
  match locus with
  | .absNom => false
  | .absDef => true

theorem doc_absent_high_abs : hasDoubleObjectConstruction .absNom = false := rfl
theorem doc_present_low_abs : hasDoubleObjectConstruction .absDef = true := rfl

-- ============================================================================
-- § 14: Reflexive → No AF → Free Extraction (end-to-end)
-- ============================================================================

/-- End-to-end argumentation chain for reflexive objects (§5.2):
    1. Reflexive objects are caseless (pseudo-incorporated)
    2. AF exists to assign case → AF is vacuous with caseless objects
    3. With no case-driven movement, the object stays in situ
    4. The escape hatch is unoccupied
    5. The subject is free to extract using regular transitive Voice
    6. Therefore: reflexive + agent extraction = regular transitive form -/
theorem reflexive_end_to_end :
    -- Reflexive needs no case
    ObjectType.reflexive.needsCase = false ∧
    -- AF unavailable (vacuous, blocked as last-resort)
    afAvailable .reflexive = false ∧
    -- Object doesn't occupy escape hatch → subject not trapped
    caselessObjectFreesSubject .reflexive = true := ⟨rfl, rfl, rfl⟩

/-- Extended reflexives (possessor bound by subject) pattern with
    reflexives: caseless, AF impossible, subject extracts freely.
    Examples (75a)–(76a) of @cite{coon-mateo-pedro-preminger-2014}. -/
theorem extReflexive_end_to_end :
    ObjectType.extendedReflexive.needsCase = false ∧
    afAvailable .extendedReflexive = false ∧
    caselessObjectFreesSubject .extendedReflexive = true := ⟨rfl, rfl, rfl⟩

/-- Contrast: full DP object requires case → AF needed → AF available. -/
theorem fullDP_end_to_end :
    ObjectType.fullDP.needsCase = true ∧
    afAvailable .fullDP = true ∧
    caselessObjectFreesSubject .fullDP = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 15: Phase Bridge
-- ============================================================================

/-- The trapping mechanism is grounded in Phase theory: regular transitive
    Voice is a phase head (v*), so vP constitutes a locality domain under
    the PIC. AF Voice is NOT a phase head, so it does not create a phase
    boundary — the complement remains accessible.

    This connects the Boolean `phaseHead` on `VoiceHead` to the Phase
    module's `isPhaseHead`. -/
theorem voice_phase_bridge :
    voiceAgent.phaseHead = true ∧ voiceAF.phaseHead = false ∧
    voicePassive.phaseHead = false ∧ voiceAnticausative.phaseHead = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Phase headedness partitions Voice into {trapping, non-trapping}: a
    Voice head traps the subject iff it is a phase head AND does not
    itself check case (freeing Infl⁰ to do so). -/
def voiceTrapsSubject (v : VoiceHead) (locus : CaseLocus) : Bool :=
  v.phaseHead && !v.checksCase && objectMustExitVP locus

theorem agent_voice_traps_absNom :
    voiceTrapsSubject voiceAgent .absNom = true := rfl

theorem agent_voice_free_absDef :
    voiceTrapsSubject voiceAgent .absDef = false := rfl

theorem af_voice_never_traps (locus : CaseLocus) :
    voiceTrapsSubject voiceAF locus = false := by
  cases locus <;> rfl

-- ============================================================================
-- § 16: Core.Case Bridge
-- ============================================================================

/-- The paper's `AbstractCase` maps to the framework's `Core.Case`. -/
def AbstractCase.toCoreCase : AbstractCase → Core.Case
  | .nom => .nom
  | .acc => .acc
  | .erg => .erg

/-- The mapping preserves the assigner structure: ERG comes from v⁰,
    NOM comes from Infl⁰, and the object case depends on the parameter. -/
theorem coreCase_bridge_object (locus : CaseLocus) :
    (objectAbstractCase locus).toCoreCase =
      match locus with
      | .absNom => .nom
      | .absDef => .acc := by
  cases locus <;> rfl

theorem coreCase_bridge_subject (locus : CaseLocus) :
    (subjectAbstractCase locus).toCoreCase = .erg := rfl

-- ============================================================================
-- § 17: Kaqchikel Voice / ClauseSpine
-- ============================================================================

/-! Theory-laden Voice/ClauseSpine apparatus for Kaqchikel, formerly in
    `Fragments/Mayan/Kaqchikel/AgentFocus.lean`. Lives here because this
    is the file that uses it (§18 cross-language bridge), and because
    Voice-flavor analysis is the @cite{coon-mateo-pedro-preminger-2014}
    side of the same author cluster's Mayan work
    (@cite{preminger-2014}'s Ch 4 covers the agreement side; CMP 2014
    covers the case/Voice side). The fragment data
    (`VerbForm.agentFocus.hasSetA`, `kaqAFType`, etc.) stays
    typology-neutral. -/

/-- Both the transitive and AF derivations project the same clausal spine
    (CP > TP > vP > VP). The difference is in the v head: transitive v
    introduces the agent in Spec,vP; AF v does not. -/
def kaqClauseSpine : ClauseSpine := ClauseSpine.cP

/-- Kaqchikel agentive Voice/v head (parallel to Mam's Voice). Present
    in the transitive derivation; absent or altered in AF.
    `phaseHead := true` is the load-bearing property for §18's
    cross-language bridge: agentive Voice is a phase head, creating the
    locality boundary that traps the subject in HIGH-ABS Mayan languages
    (CMP 2014 §4–§5). -/
def kaqVoice : VoiceHead :=
  { flavor := .agentive
  , hasD := true
  , phaseHead := true }

/-- Kaqchikel clause projects Voice. -/
theorem kaq_has_voice : kaqClauseSpine.projects .Voice = true := by
  native_decide

/-- Kaqchikel Voice is agentive. -/
theorem kaq_voice_is_agentive : kaqVoice.flavor = .agentive := rfl

-- ============================================================================
-- § 18: Cross-Language AF Bridge (Q'anjob'al vs Kaqchikel)
-- ============================================================================

/-! Different Mayan languages circumvent syntactic ergativity through
different mechanisms (@cite{coon-mateo-pedro-preminger-2014} §4.2, §5).
Q'anjob'al uses case assignment: Voice_AF assigns case to the object,
freeing the escape hatch. Kaqchikel uses an anti-locality repair: AF
structure avoids the too-local Spec,TP → Spec,CP movement step (SSAL),
at the cost of losing Set A agreement (@cite{erlewine-2016}). -/

/-- Q'anjob'al AF Voice checks case; Kaqchikel's regular Voice does NOT.
    This is the core parametric difference: Q'anjob'al's AF is a
    case-assigning repair, while Kaqchikel's AF is a locality repair. -/
theorem af_mechanism_contrast :
    voiceAF.checksCase = true ∧
    kaqVoice.checksCase = false := ⟨rfl, rfl⟩

/-- Both languages share the underlying problem: agentive Voice is a
    phase head, creating a locality boundary that traps the subject. -/
theorem shared_phase_problem :
    voiceAgent.phaseHead = true ∧
    kaqVoice.phaseHead = true := ⟨rfl, rfl⟩

/-- Both Q'anjob'al and Kaqchikel are HIGH-ABS languages with extraction
    asymmetries: agent extraction is blocked without AF in both. -/
theorem both_have_extraction_asymmetries :
    Fragments.Mayan.Qanjobal.absPosition = .high ∧
    Fragments.Mayan.Qanjobal.ExtractionTarget.agent.extractable = false ∧
    Fragments.Mayan.Kaqchikel.kaqAFType = .afLanguage := ⟨rfl, rfl, rfl⟩

/-- Kaqchikel AF loses Set A agreement (the agent never enters Spec,TP).
    Q'anjob'al AF also loses Set A agreement.
    Same surface morphological effect, different underlying mechanism. -/
theorem both_af_lose_setA :
    Fragments.Mayan.Qanjobal.agentFocusForm.hasSetA = false ∧
    Fragments.Mayan.Kaqchikel.VerbForm.agentFocus.hasSetA = false := ⟨rfl, rfl⟩

end CoonMateoPedroPreminger2014
