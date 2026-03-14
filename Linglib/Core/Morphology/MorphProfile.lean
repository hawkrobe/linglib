import Linglib.Core.WALS.Features.F20A
import Linglib.Core.WALS.Features.F21A
import Linglib.Core.WALS.Features.F22A
import Linglib.Core.WALS.Features.F23A
import Linglib.Core.WALS.Features.F24A
import Linglib.Core.WALS.Features.F25A
import Linglib.Core.WALS.Features.F25B
import Linglib.Core.WALS.Features.F26A
import Linglib.Core.WALS.Features.F27A
import Linglib.Core.WALS.Features.F28A
import Linglib.Core.WALS.Features.F29A
import Linglib.Core.WALS.Features.F21B
import Linglib.Core.WALS.Features.F62A
import Linglib.Core.WALS.Features.F79A
import Linglib.Core.WALS.Features.F79B
import Linglib.Core.WALS.Features.F80A

/-!
# Morphological Profile Types

Framework-agnostic types for cross-linguistic morphological typology,
grounding functions from WALS data, and the `MorphProfile` structure.

Types correspond to WALS chapters 20--29 plus supplementary chapters
(21B, 62A, 79A/B, 80A). Grounding functions map WALS auto-generated
data to these coarser local classifications.
-/

namespace Core.Morphology

-- ============================================================================
-- §1. Typological Classification Types
-- ============================================================================

/-- WALS Ch 20: How inflectional formatives are attached to stems. -/
inductive Fusion where
  | isolating
  | concatenative
  | nonlinear
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 21: How many grammatical categories a single case formative expresses. -/
inductive Exponence where
  | monoexponential
  | polyexponential
  | noCase
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 22: How many inflectional categories are expressed on the verb. -/
inductive VerbSynthesis where
  | low       -- 0--3 categories per verb word
  | moderate  -- 4--7 categories per verb word
  | high      -- 8+ categories per verb word
  deriving DecidableEq, BEq, Repr

/-- Locus of marking: where grammatical relations are marked.
    Derived from WALS Ch 25A @cite{nichols-bickel-2013a}. -/
inductive LocusOfMarking where
  | headMarking
  | dependentMarking
  | doubleMarking
  | zeroMarking
  | inconsistentOrOther
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 26: Whether a language predominantly uses prefixes or suffixes. -/
inductive PrefixSuffix where
  | stronglySuffixing
  | weaklySuffixing
  | equalPrefixSuffix
  | weaklyPrefixing
  | stronglyPrefixing
  | littleAffixation
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 27: Whether the language has productive reduplication. -/
inductive Reduplication where
  | productiveFull
  | fullOnly
  | noProductive
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 23: Where grammatical relations are marked in clausal syntax.
    @cite{nichols-bickel-2013b} -/
inductive LocusClause where
  | headMarking
  | dependentMarking
  | doubleMarking
  | noMarking
  | other
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 24: Where grammatical relations are marked in possessive NPs.
    @cite{nichols-bickel-2013c} -/
inductive LocusPossessive where
  | headMarking
  | dependentMarking
  | doubleMarking
  | noMarking
  | other
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 25A: Whole-language locus-of-marking classification.
    @cite{nichols-bickel-2013a} -/
inductive WholeLanguageMarking where
  | headMarking
  | dependentMarking
  | doubleMarking
  | zeroMarking
  | inconsistentOrOther
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 25B: Whether A and P arguments are zero-marked.
    @cite{nichols-bickel-2013d} -/
inductive ZeroMarkingAP where
  | zeroMarking
  | nonZeroMarking
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 28: Whether a language exhibits case syncretism. -/
inductive CaseSyncretism where
  | noCaseMarking
  | coreCasesOnly
  | coreAndNonCore
  | noSyncretism
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 29: Whether a language exhibits syncretism in verbal person/number. -/
inductive VerbalSyncretism where
  | noSubjectMarking
  | syncretic
  | notSyncretic
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 21B: What categories co-occur with TAM in a single formative. -/
inductive TAMExponence where
  | monoexponential
  | tamAgreement
  | tamAgreementDiathesis
  | tamAgreementConstruct
  | tamPolarity
  | noTam
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 62: How a language constructs action nominals. -/
inductive ActionNominal where
  | sentential
  | possessiveAccusative
  | ergativePossessive
  | doublePossessive
  | other
  | mixed
  | restricted
  | noActionNominals
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 79A: Whether suppletion is conditioned by tense, aspect, or both. -/
inductive SuppletionTA where
  | tense
  | aspect
  | tenseAndAspect
  | none
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 79B: Whether a language has suppletive imperatives/hortatives. -/
inductive SuppletionImperative where
  | alternating
  | imperative
  | hortative
  | imperativeAndHortative
  | none
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 80A: Whether a language has verbal number marking. -/
inductive VerbalNumber where
  | none
  | pairsNoSuppletion
  | pairsSuppletion
  | triplesNoSuppletion
  | triplesSuppletion
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2. MorphProfile Structure
-- ============================================================================

/-- A language's morphological profile, combining dimensions from WALS
    Chapters 20--29 plus supplementary chapters. Required fields are derived
    from WALS where possible; optional fields are populated when the language
    appears in the relevant WALS chapter. -/
structure MorphProfile where
  language : String
  iso : String
  /-- Ch 20: Fusion type -/
  fusion : Fusion
  /-- Ch 21: Exponence type -/
  exponence : Exponence
  /-- Ch 22: Inflectional synthesis of the verb -/
  verbSynthesis : VerbSynthesis
  /-- Locus of marking (derived from Ch 23 clause-level; fallback for absent languages) -/
  locus : LocusOfMarking
  /-- Ch 26: Prefixing vs suffixing -/
  prefixSuffix : PrefixSuffix
  /-- Ch 27: Productive reduplication -/
  reduplication : Reduplication
  /-- Ch 23: Locus of marking in the clause (optional) -/
  locusClause : Option LocusClause := none
  /-- Ch 24: Locus of marking in possessive NP (optional) -/
  locusPossessive : Option LocusPossessive := none
  /-- Ch 25A: Whole-language marking typology (optional) -/
  wholeLanguageMarking : Option WholeLanguageMarking := none
  /-- Ch 25B: Zero marking of A and P arguments (optional) -/
  zeroMarkingAP : Option ZeroMarkingAP := none
  /-- Ch 28: Case syncretism (optional) -/
  caseSyncretism : Option CaseSyncretism := none
  /-- Ch 29: Syncretism in verbal person/number marking (optional) -/
  verbalSyncretism : Option VerbalSyncretism := none
  /-- Ch 21B: Exponence of TAM inflection (optional) -/
  tamExponence : Option TAMExponence := none
  /-- Ch 62A: Action nominal constructions (optional) -/
  actionNominal : Option ActionNominal := none
  /-- Ch 79A: Suppletion according to tense and aspect (optional) -/
  suppletionTA : Option SuppletionTA := none
  /-- Ch 79B: Suppletion in imperatives and hortatives (optional) -/
  suppletionImperative : Option SuppletionImperative := none
  /-- Ch 80A: Verbal number and suppletion (optional) -/
  verbalNumber : Option VerbalNumber := none
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- §3. WALS Converter Functions
-- ============================================================================

/-- Convert WALS 20A fusion type to the local three-way `Fusion` classification.
    Returns `none` for mixed categories that do not map cleanly. -/
def fromWALS20A : Core.WALS.F20A.FusionType → Option Fusion
  | .exclusivelyConcatenative => some .concatenative
  | .exclusivelyIsolating     => some .isolating
  | .exclusivelyTonal         => some .nonlinear
  | .ablautConcatenative      => some .nonlinear
  | .tonalIsolating           => none
  | .tonalConcatenative       => none
  | .isolatingConcatenative   => none

/-- Convert WALS 21A exponence type to the local `Exponence` classification.
    Returns `none` for `noCase` (no information about overall exponence). -/
def fromWALS21A : Core.WALS.F21A.ExponenceType → Option Exponence
  | .monoexponentialCase  => some .monoexponential
  | .caseNumber           => some .polyexponential
  | .caseReferentiality   => some .polyexponential
  | .caseTam              => some .polyexponential
  | .noCase               => none

/-- Convert WALS 22A inflectional synthesis to the local three-way classification. -/
def fromWALS22A : Core.WALS.F22A.InflectionalSynthesis → VerbSynthesis
  | .categoryPerWord0_1    => .low
  | .categoriesPerWord2_3  => .low
  | .categoriesPerWord4_5  => .moderate
  | .categoriesPerWord6_7  => .moderate
  | .categoriesPerWord8_9  => .high
  | .categoriesPerWord10_11 => .high
  | .categoriesPerWord12_13 => .high

def fromWALS26A : Core.WALS.F26A.PrefixSuffixPreference → PrefixSuffix
  | .littleAffixation             => .littleAffixation
  | .stronglySuffixing            => .stronglySuffixing
  | .weaklySuffixing              => .weaklySuffixing
  | .equalPrefixingAndSuffixing   => .equalPrefixSuffix
  | .weaklyPrefixing              => .weaklyPrefixing
  | .strongPrefixing              => .stronglyPrefixing

def fromWALS27A : Core.WALS.F27A.ReduplicationType → Reduplication
  | .productiveFullAndPartialReduplication => .productiveFull
  | .fullReduplicationOnly                => .fullOnly
  | .noProductiveReduplication            => .noProductive

def fromWALS23A : Core.WALS.F23A.LocusOfMarkingInTheClause → LocusClause
  | .headMarking      => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking    => .doubleMarking
  | .noMarking        => .noMarking
  | .other            => .other

def fromWALS24A :
    Core.WALS.F24A.LocusOfMarkingInPossessiveNounPhrases → LocusPossessive
  | .headMarking      => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking    => .doubleMarking
  | .noMarking        => .noMarking
  | .other            => .other

def fromWALS25A :
    Core.WALS.F25A.LocusOfMarkingWholeLanguageTypology → WholeLanguageMarking
  | .headMarking         => .headMarking
  | .dependentMarking    => .dependentMarking
  | .doubleMarking       => .doubleMarking
  | .zeroMarking         => .zeroMarking
  | .inconsistentOrOther => .inconsistentOrOther

def fromWALS25B :
    Core.WALS.F25B.ZeroMarkingOfAAndPArguments → ZeroMarkingAP
  | .zeroMarking    => .zeroMarking
  | .nonZeroMarking => .nonZeroMarking

def fromWALS28A : Core.WALS.F28A.CaseSyncretism → CaseSyncretism
  | .noCaseMarking  => .noCaseMarking
  | .coreCasesOnly  => .coreCasesOnly
  | .coreAndNonCore => .coreAndNonCore
  | .noSyncretism   => .noSyncretism

def fromWALS29A :
    Core.WALS.F29A.SyncretismInVerbalPersonNumberMarking → VerbalSyncretism
  | .noSubjectPersonNumberMarking => .noSubjectMarking
  | .syncretic                    => .syncretic
  | .notSyncretic                 => .notSyncretic

def fromWALS21B :
    Core.WALS.F21B.ExponenceOfTenseAspectMoodInflection → TAMExponence
  | .monoexponentialTam      => .monoexponential
  | .tamAgreement            => .tamAgreement
  | .tamAgreementDiathesis   => .tamAgreementDiathesis
  | .tamAgreementConstruct   => .tamAgreementConstruct
  | .tamPolarity             => .tamPolarity
  | .noTam                   => .noTam

def fromWALS62A :
    Core.WALS.F62A.ActionNominalConstructions → ActionNominal
  | .sentential           => .sentential
  | .possessiveAccusative => .possessiveAccusative
  | .ergativePossessive   => .ergativePossessive
  | .doublePossessive     => .doublePossessive
  | .other                => .other
  | .mixed                => .mixed
  | .restricted           => .restricted
  | .noActionNominals     => .noActionNominals

def fromWALS79A :
    Core.WALS.F79A.SuppletionAccordingToTenseAndAspect → SuppletionTA
  | .tense          => .tense
  | .aspect         => .aspect
  | .tenseAndAspect => .tenseAndAspect
  | .none           => .none

def fromWALS79B :
    Core.WALS.F79B.SuppletionInImperativesAndHortatives → SuppletionImperative
  | .aRegularAndASuppletiveFormAlternate => .alternating
  | .imperative                          => .imperative
  | .hortative                           => .hortative
  | .imperativeAndHortative              => .imperativeAndHortative
  | .none                                => .none

def fromWALS80A :
    Core.WALS.F80A.VerbalNumberAndSuppletion → VerbalNumber
  | .none                                    => .none
  | .singularPluralPairsNoSuppletion         => .pairsNoSuppletion
  | .singularPluralPairsSuppletion           => .pairsSuppletion
  | .singularDualPluralTriplesNoSuppletion   => .triplesNoSuppletion
  | .singularDualPluralTriplesSuppletion     => .triplesSuppletion

-- ============================================================================
-- §4. WALS Lookup Helpers
-- ============================================================================

/-- Map clause-level locus (F23A) to the 5-way whole-language classification. -/
def locusClauseToLocus : LocusClause → LocusOfMarking
  | .headMarking      => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking    => .doubleMarking
  | .noMarking        => .zeroMarking
  | .other            => .inconsistentOrOther

/-! WALS lookup helpers derive MorphProfile field values from auto-generated
    WALS data. Each returns `Option`, yielding `none` when the language is
    absent from that chapter or the grounding function is uninformative.
    Profile definitions use `.getD fallback` so the fallback is only reached
    when WALS cannot help. -/

def walsFusion (iso : String) : Option Fusion :=
  (Core.WALS.F20A.lookupISO iso).bind (fromWALS20A ·.value)

def walsExponence (iso : String) : Option Exponence :=
  (Core.WALS.F21A.lookupISO iso).bind (fromWALS21A ·.value)

def walsVerbSynthesis (iso : String) : Option VerbSynthesis :=
  (Core.WALS.F22A.lookupISO iso).map (fromWALS22A ·.value)

def walsLocus (iso : String) : Option LocusOfMarking :=
  (Core.WALS.F23A.lookupISO iso).map (λ e => locusClauseToLocus (fromWALS23A e.value))

def walsPrefixSuffix (iso : String) : Option PrefixSuffix :=
  (Core.WALS.F26A.lookupISO iso).map (fromWALS26A ·.value)

def walsReduplication (iso : String) : Option Reduplication :=
  (Core.WALS.F27A.lookupISO iso).map (fromWALS27A ·.value)

def walsLocusClause (iso : String) : Option LocusClause :=
  (Core.WALS.F23A.lookupISO iso).map (fromWALS23A ·.value)

def walsLocusPossessive (iso : String) : Option LocusPossessive :=
  (Core.WALS.F24A.lookupISO iso).map (fromWALS24A ·.value)

def walsWholeLanguageMarking (iso : String) : Option WholeLanguageMarking :=
  (Core.WALS.F25A.lookupISO iso).map (fromWALS25A ·.value)

def walsZeroMarkingAP (iso : String) : Option ZeroMarkingAP :=
  (Core.WALS.F25B.lookupISO iso).map (fromWALS25B ·.value)

def walsCaseSyncretism (iso : String) : Option CaseSyncretism :=
  (Core.WALS.F28A.lookupISO iso).map (fromWALS28A ·.value)

def walsVerbalSyncretism (iso : String) : Option VerbalSyncretism :=
  (Core.WALS.F29A.lookupISO iso).map (fromWALS29A ·.value)

def walsTAMExponence (iso : String) : Option TAMExponence :=
  (Core.WALS.F21B.lookupISO iso).map (fromWALS21B ·.value)

def walsActionNominal (iso : String) : Option ActionNominal :=
  (Core.WALS.F62A.lookupISO iso).map (fromWALS62A ·.value)

def walsSuppletionTA (iso : String) : Option SuppletionTA :=
  (Core.WALS.F79A.lookupISO iso).map (fromWALS79A ·.value)

def walsSuppletionImperative (iso : String) : Option SuppletionImperative :=
  (Core.WALS.F79B.lookupISO iso).map (fromWALS79B ·.value)

def walsVerbalNumber (iso : String) : Option VerbalNumber :=
  (Core.WALS.F80A.lookupISO iso).map (fromWALS80A ·.value)

-- ============================================================================
-- §5. Helper Predicates
-- ============================================================================

def MorphProfile.isConcatenative (p : MorphProfile) : Bool :=
  p.fusion == .concatenative

def MorphProfile.isIsolating (p : MorphProfile) : Bool :=
  p.fusion == .isolating

def MorphProfile.isNonlinear (p : MorphProfile) : Bool :=
  p.fusion == .nonlinear

def MorphProfile.isMono (p : MorphProfile) : Bool :=
  p.exponence == .monoexponential

def MorphProfile.isPoly (p : MorphProfile) : Bool :=
  p.exponence == .polyexponential

def MorphProfile.hasRedup (p : MorphProfile) : Bool :=
  p.reduplication == .productiveFull || p.reduplication == .fullOnly

def MorphProfile.isSuffixing (p : MorphProfile) : Bool :=
  p.prefixSuffix == .stronglySuffixing || p.prefixSuffix == .weaklySuffixing

def MorphProfile.isPrefixing (p : MorphProfile) : Bool :=
  p.prefixSuffix == .stronglyPrefixing || p.prefixSuffix == .weaklyPrefixing

def MorphProfile.isLowSynthesis (p : MorphProfile) : Bool :=
  p.verbSynthesis == .low

def MorphProfile.isHighSynthesis (p : MorphProfile) : Bool :=
  p.verbSynthesis == .high

end Core.Morphology
