import Linglib.Features.Case.Basic
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine
import Linglib.Fragments.Mayan.Qanjobal.Agreement
import Linglib.Fragments.Mayan.Qanjobal.AgentFocus
import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Focus
import Linglib.Fragments.Mayan.Tseltal.Agreement
import Linglib.Fragments.Mayan.Tsotsil.Agreement
import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Kiche.Agreement

/-!
# Coon, Mateo Pedro & Preminger (2014) [coon-mateo-pedro-preminger-2014]

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

open Minimalist Minimalist.Voice
open Mayan (ABSPosition CaseLocus toCaseLocus MayanLang)

-- § 1 uses `CaseLocus` and `toCaseLocus` from `Mayan.Params`.

-- ============================================================================
-- § 2: Legate (2008) Abstract Case Decomposition
-- ============================================================================

/-- Abstract case features assigned by functional heads. Following
    [legate-2008], "absolutive" is not an abstract case but a descriptive
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

    Following [ordonez-1995] on Popti', *-on* assigns case to the
    object. Unlike regular transitive Voice, AF Voice is NOT a phase head:
    its v⁰ is the intransitive variety (non-phasal), explaining why the
    intransitive status suffix *-i* surfaces rather than transitive *-V'*.

    AF is a "last-resort" strategy, akin to English *of*-insertion: the
    marked variant of Voice⁰ is merged only when the normal derivation
    (with regular transitive Voice) would crash — i.e., when the subject
    must be A-bar extracted. -/
def voiceAF : Head :=
  { flavor := .agentive
  , hasD := true
  , phaseOverride := some false  -- intransitive v⁰: NOT phasal (Mam AF)
  , checksCase := true }         -- assigns case to object

/-- AF Voice assigns case to the object. -/
theorem af_assigns_case : voiceAF.ChecksCase := by decide

/-- AF Voice is NOT a phase head (intransitive v⁰). -/
theorem af_not_phase : ¬ voiceAF.IsPhasal := by decide

/-- AF Voice still introduces an external argument (the agent). -/
theorem af_introduces_agent : voiceAF.AssignsTheta := by decide

/-- AF Voice circumvents the trapping mechanism because it assigns case to
    the object (so the object need not move to Spec,vP) AND because AF's v⁰
    is non-phasal (so vP is not a locality domain). Either property alone
    would free the subject, but both hold simultaneously for AF Voice. -/
def AfCircumventsTrapping : Prop :=
  voiceAF.ChecksCase ∧ ¬ voiceAF.IsPhasal

instance : Decidable AfCircumventsTrapping := by
  unfold AfCircumventsTrapping; infer_instance

theorem af_frees_subject : AfCircumventsTrapping := by decide

/-- The case-assignment property alone is what frees extraction: when
    Voice checks case, the object receives case inside vP and need not
    move to the escape hatch. This is the paper's primary explanation
    for why AF circumvents the extraction ban. -/
def CaseAloneFreesExtraction (v : Head) : Prop :=
  v.ChecksCase

instance (v : Head) : Decidable (CaseAloneFreesExtraction v) := by
  unfold CaseAloneFreesExtraction; infer_instance

theorem af_case_frees : CaseAloneFreesExtraction voiceAF := by decide

/-- The non-phasal status explains AF's *morphology* (intransitive
    status suffix *-i*) rather than the extraction facts. Since AF's v⁰
    is intransitive, no ergative case is assigned to the subject. -/
theorem af_morphology_from_phase :
    ¬ voiceAF.IsPhasal := by decide

/-- Contrast with regular transitive Voice: phasal, does NOT check case. -/
theorem regular_voice_traps :
    agentive.IsPhasal ∧ ¬ agentive.ChecksCase := by decide

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
    Qanjobal.ArgPosition.case .A = .erg ∧
    Qanjobal.ArgPosition.case .P = .abs := ⟨rfl, rfl⟩

/-- Chol's ergative alignment matches the same standard pattern. -/
theorem chol_erg_alignment :
    Chol.ArgPosition.case .A = .erg ∧
    Chol.ArgPosition.case .P = .abs := ⟨rfl, rfl⟩

/-- Despite sharing ergative morphology, Q'anjob'al and Chol differ in
    whether agent extraction is banned. The difference traces to their
    distinct case loci, not to properties of the ergative NP. -/
theorem shared_morphology_different_syntax :
    -- Same ergative case on agent
    Qanjobal.ArgPosition.case .A =
      Chol.ArgPosition.case .A ∧
    -- But different syntactic ergativity predictions
    hasSyntacticErgativity .absNom ≠ hasSyntacticErgativity .absDef :=
  ⟨rfl, by decide⟩

/-- Fragment-grounded ABSPosition: Q'anjob'al is HIGH-ABS. -/
theorem qanjobal_high_abs :
    Qanjobal.absPosition = .high := rfl

/-- Fragment-grounded ABSPosition: Chol is LOW-ABS. -/
theorem chol_low_abs :
    Chol.absPosition = .low := rfl

/-- The fragment ABSPosition values derive the correct syntactic
    ergativity predictions: Q'anjob'al has it, Chol does not.
    This grounds Tada's Generalization in fragment data rather than
    hard-coded table entries. -/
theorem fragments_ground_tada :
    hasSyntacticErgativity (toCaseLocus Qanjobal.absPosition) = true ∧
    hasSyntacticErgativity (toCaseLocus Chol.absPosition) = false :=
  ⟨rfl, rfl⟩

/-- Absolutive structural position (HIGH-ABS / LOW-ABS) indexed by Mayan
    language, routed to the per-language Fragment value. The substantive
    parameter for Tada's Generalization. -/
def absPositionOf : MayanLang → ABSPosition
  | .Chol      => Chol.absPosition
  | .Qanjobal  => Qanjobal.absPosition
  | .Kaqchikel => Kaqchikel.absPosition
  | .Tseltal   => Tseltal.absPosition
  | .Tsotsil   => Tsotsil.absPosition
  | .Mam       => Mam.absPosition
  | .Kiche     => Kiche.absPosition

/-- **Tada's Generalization, parameterized form**: a Mayan language
    exhibits syntactic ergativity (the analytical predicate from §4)
    **iff** it is HIGH-ABS. Quantified over `Mayan.MayanLang`
    via the Fragment-routed `absPositionOf` dispatcher.

    Replaces the per-language enumeration in `fragments_ground_tada`
    with a single quantified theorem that scales as the `MayanLang`
    registry grows. -/
theorem mayan_tada (lang : MayanLang) :
    hasSyntacticErgativity (toCaseLocus (absPositionOf lang)) = true ↔
      absPositionOf lang = ABSPosition.high := by
  cases lang <;> decide

/-- Q'anjob'al's extraction data is consistent with the prediction:
    agent extraction is marked (requires AF morphology in regular
    transitives). The substantive claim lives at `extractionProfile`'s
    `markedPositions := [.subject]` field. -/
theorem qanjobal_extraction_consistent :
    Extraction.Marks Qanjobal.extractionMarkedPositions .subject := by decide

/-- Chol's extraction data is consistent: no Agent Focus morphology
    required (every argument extracts freely under the absent strategy). -/
theorem chol_extraction_consistent :
    Chol.extractionStrategy = .unmarked := rfl

/-- Q'anjob'al's AF form carries the intransitive status suffix, matching
    the prediction that AF Voice is non-phasal (intransitive v⁰). -/
theorem qanjobal_af_itv :
    Qanjobal.agentFocusForm.statusSuffix = .itv := rfl

/-- The Crazy Antipassive form is identical to AF: same *-on* morpheme,
    same intransitive status suffix. Supports the unified analysis of
    *-on* as a case-assigner in environments where case is otherwise
    unavailable. -/
theorem crazy_ap_unified :
    Qanjobal.crazyAntipassiveForm = Qanjobal.agentFocusForm := rfl

/-- Non-finite absolutive asymmetry in Chol: objects are available
    (v⁰ assigns case) but intransitive subjects are not (Infl⁰ absent).
    Follows from LOW-ABS: v⁰ handles objects, Infl⁰ handles intransitives. -/
theorem chol_nonfinite_predictions :
    Chol.absObjectInNonFinite = true ∧
    Chol.absIntranSInNonFinite = false := ⟨rfl, rfl⟩

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
-- § 9a: Tada's Generalization (empirical table)
-- ============================================================================

/-- A Mayan language's observable extraction behavior. -/
structure MayanExtractionDatum where
  name : String
  absPosition : ABSPosition
  /-- Does the language ban A-bar extraction of transitive subjects? -/
  hasExtractionAsymmetry : Bool
  deriving DecidableEq, Repr

/-- Tada's Generalization data (table (19) of [coon-mateo-pedro-preminger-2014],
    extending [tada-1993]).

    For the seven languages with linglib Fragments, `absPosition` and the
    extraction-asymmetry flag are routed through the Fragment values
    (`absPosition`, `extractionProfile`) rather than duplicated here.

    The two noted outliers are Yucatec and Ixil (LOW-ABS with extraction
    asymmetries). Yucatec's AF differs significantly from other Mayan AF;
    Ixil's absolutive morphemes behave like full pronominal forms. -/
def tadasTable : List MayanExtractionDatum :=
  -- HIGH-ABS, +extraction asymmetries
  [ ⟨"Q'anjob'al",  Qanjobal.absPosition,
      decide (Extraction.Marks Qanjobal.extractionMarkedPositions .subject)⟩
  , ⟨"Akatek",      .high, true⟩
  , ⟨"Popti'",      .high, true⟩
  , ⟨"Chuj",        .high, true⟩
  , ⟨"Q'eqchi'",    .high, true⟩
  , ⟨"Uspantek",    .high, true⟩
  , ⟨"Poqomchi'",   .high, true⟩
  , ⟨"Poqomam",     .high, true⟩
  , ⟨"K'ichee'",    Kiche.absPosition,
      decide (Extraction.Marks Kiche.extractionMarkedPositions .subject)⟩
  , ⟨"Kaqchikel",   Kaqchikel.absPosition,
      decide (Extraction.Marks Kaqchikel.extractionMarkedPositions .subject)⟩
  , ⟨"Tz'utujil",   .high, true⟩
  , ⟨"Sakapultek",  .high, true⟩
  , ⟨"Sipakapense", .high, true⟩
  , ⟨"Mam",         Mam.absPosition,
      decide (Extraction.Marks Mam.extractionMarkedPositions .subject)⟩
  , ⟨"Awakatek",    .high, true⟩
  -- LOW-ABS, +extraction asymmetries (outliers)
  , ⟨"Yucatec",     .low,  true⟩
  , ⟨"Ixil",        .low,  true⟩
  -- LOW-ABS, -extraction asymmetries
  , ⟨"Lakantun",    .low,  false⟩
  , ⟨"Mopan",       .low,  false⟩
  , ⟨"Itzaj",       .low,  false⟩
  , ⟨"Chol",        Chol.absPosition,
      decide (Extraction.Marks Chol.extractionMarkedPositions .subject)⟩
  , ⟨"Chontal",     .low,  false⟩
  , ⟨"Tseltal",     Tseltal.absPosition,
      decide (Extraction.Marks Tseltal.extractionMarkedPositions .subject)⟩
  , ⟨"Tsotsil",     Tsotsil.absPosition,
      decide (Extraction.Marks Tsotsil.extractionMarkedPositions .subject)⟩
  , ⟨"Tojol-ab'al", .low,  false⟩ ]

/-- All HIGH-ABS languages in the sample exhibit extraction asymmetries. -/
theorem high_abs_all_have_asymmetries :
    (tadasTable.filter (fun l => l.absPosition == .high)).all
      (fun l => l.hasExtractionAsymmetry) = true := by decide

/-- All LOW-ABS languages except the two noted outliers lack
    extraction asymmetries. -/
theorem low_abs_mostly_lack_asymmetries :
    (tadasTable.filter (fun l => l.absPosition == .low &&
      l.name != "Yucatec" && l.name != "Ixil")).all
      (fun l => !l.hasExtractionAsymmetry) = true := by decide

/-- No HIGH-ABS language lacks extraction asymmetries (unattested cell). -/
theorem high_abs_none_lack_asymmetries :
    (tadasTable.filter (fun l => l.absPosition == .high &&
      !l.hasExtractionAsymmetry)).length = 0 := by decide

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
    agentive.IsPhasal := by decide

/-- AF removes factor I: AF Voice is not phasal. With a non-phasal vP,
    there is no locality boundary trapping the subject. -/
theorem af_removes_factor1 :
    ¬ voiceAF.IsPhasal := by decide

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

/-- The +morph.erg column of table (10), grounded in Fragment data:
    every formalised Mayan language with the standard ergative-absolutive
    base assigns case canonically ergatively (A → ERG, S/P → ABS) in the
    perfective. The `isStandard` hypothesis scopes around San Juan Atitán
    Mam, whose perfective is morphologically tripartite (see
    `Mayan.MayanLang.isStandard` and `Studies/Scott2023.lean`). -/
theorem mayan_perfective_ergative
    (lang : MayanLang) (h : lang.isStandard = true)
    (r : Features.Prominence.ArgumentRole) :
    Mayan.caseAt lang .Perf r = Alignment.ergative.assignCase r := by
  cases lang <;> first | rfl | (simp [Mayan.MayanLang.isStandard] at h)

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
    Qanjobal.PersonRestriction.third.requiresAF = true ∧
    Qanjobal.PersonRestriction.first.requiresAF = false := ⟨rfl, rfl⟩

theorem crazy_ap_no_person_restriction :
    Qanjobal.PersonRestriction.first.requiresCrazyAP = true ∧
    Qanjobal.PersonRestriction.third.requiresCrazyAP = true := ⟨rfl, rfl⟩

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
    Examples (75a)–(76a) of [coon-mateo-pedro-preminger-2014]. -/
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

    This connects `IsPhasal` on `Head` to the Phase module's
    `isPhaseHeadOf .C`/`isPhaseHeadOf .Voice` selectors. -/
theorem voice_phase_bridge :
    agentive.IsPhasal ∧ ¬ voiceAF.IsPhasal ∧
    ¬ passive.IsPhasal ∧ ¬ anticausative.IsPhasal := by decide

/-- Phase headedness partitions Voice into {trapping, non-trapping}: a
    Voice head traps the subject iff it is a phase head AND does not
    itself check case (freeing Infl⁰ to do so). -/
def VoiceTrapsSubject (v : Head) (locus : CaseLocus) : Prop :=
  v.IsPhasal ∧ ¬ v.ChecksCase ∧ objectMustExitVP locus = true

instance (v : Head) (locus : CaseLocus) :
    Decidable (VoiceTrapsSubject v locus) := by
  unfold VoiceTrapsSubject; infer_instance

theorem agent_voice_traps_absNom :
    VoiceTrapsSubject agentive .absNom := by decide

theorem agent_voice_free_absDef :
    ¬ VoiceTrapsSubject agentive .absDef := by decide

theorem af_voice_never_traps (locus : CaseLocus) :
    ¬ VoiceTrapsSubject voiceAF locus := by
  cases locus <;> decide

-- ============================================================================
-- § 16: Case Bridge
-- ============================================================================

/-- The paper's `AbstractCase` maps to the framework's `Case`. -/
def AbstractCase.toCoreCase : AbstractCase → Case
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

/-! Theory-laden Voice/ClauseSpine apparatus for Kaqchikel, graduated out
    of the Kaqchikel fragment. Voice-flavor analysis is
    the [coon-mateo-pedro-preminger-2014] side of the same author
    cluster's Mayan work ([preminger-2014]'s Ch 4 covers the agreement
    side; CMP 2014 covers the case/Voice side). The Q'anjob'al-vs-Kaqchikel
    mechanism comparison consuming these heads lives in
    `Studies/Erlewine2016.lean` — the chronologically later paper, for
    which the case-based account is the principal foil. -/

/-- Both the transitive and AF derivations project the same clausal spine
    (CP > TP > vP > VP). The difference is in the v head: transitive v
    introduces the agent in Spec,vP; AF v does not. -/
def kaqClauseSpine : ClauseSpine := ClauseSpine.cP

/-- Kaqchikel agentive Voice/v head (parallel to Mam's Voice). Present
    in the transitive derivation; absent or altered in AF.
    Phasehood is the load-bearing property for §18's cross-language bridge:
    agentive Voice is a phase head (flavor default), creating the locality
    boundary that traps the subject in HIGH-ABS Mayan languages
    (CMP 2014 §4–§5). -/
def kaqVoice : Head :=
  { flavor := .agentive
  , hasD := true }

/-- Kaqchikel clause projects Voice. -/
theorem kaq_has_voice : kaqClauseSpine.projects .Voice = true := by
  decide

/-- Kaqchikel Voice is agentive. -/
theorem kaq_voice_is_agentive : kaqVoice.flavor = .agentive := rfl

end CoonMateoPedroPreminger2014
