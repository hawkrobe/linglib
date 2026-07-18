import Linglib.Data.WALS.Features.F20A
import Linglib.Data.WALS.Features.F21A
import Linglib.Data.WALS.Features.F22A
import Linglib.Data.WALS.Features.F23A
import Linglib.Data.WALS.Features.F24A
import Linglib.Data.WALS.Features.F25A
import Linglib.Data.WALS.Features.F25B
import Linglib.Data.WALS.Features.F26A
import Linglib.Data.WALS.Features.F27A
import Linglib.Data.WALS.Features.F28A
import Linglib.Data.WALS.Features.F29A
import Linglib.Data.WALS.Features.F21B
import Linglib.Data.WALS.Features.F62A
import Linglib.Data.WALS.Features.F79A
import Linglib.Data.WALS.Features.F79B
import Linglib.Data.WALS.Features.F80A

/-!
# Morphological Profile Types

Framework-agnostic types for cross-linguistic morphological typology,
grounding functions from WALS data, and the `MorphProfile` structure.

Types correspond to WALS chapters 20--29 plus supplementary chapters
(21B, 62A, 79A/B, 80A). Grounding functions map WALS auto-generated
data to these coarser local classifications.
-/

namespace Morphology

-- ============================================================================
-- §1. Typological Classification Types
-- ============================================================================

/-- WALS Ch 20: How inflectional formatives are attached to stems.

    Note: this captures *fusion* only — the degree of phonological
    boundedness between formative and stem. The traditional labels
    "agglutinating" and "fusional" conflate fusion with *flexivity*
    (see `Flexivity` below). Both `concatenative + nonflexive` (Turkish)
    and `concatenative + flexive` (Russian) map to `.concatenative` here.
    [bickel-nichols-2001] -/
inductive Fusion where
  | isolating
  | concatenative
  | nonlinear
  deriving DecidableEq, Repr

/-- Whether inflectional formatives show item-based allomorphic variation.

    [bickel-nichols-2001] argue this is the crucial parameter that
    the traditional typology conflates with fusion:
    - **nonflexive** ("agglutinating"): formatives have invariant or
      rule-governed shape (Turkish *-ler* ~ *-lar* is vowel-harmony,
      not item-based allomorphy)
    - **flexive** ("fusional"): formatives vary unpredictably by
      inflectional class (Latin *-ī* ~ *-ae* ~ *-ūs* for genitive
      singular depending on declension class)

    Orthogonal to `Fusion`: a language can be concatenative + nonflexive
    (Turkish), concatenative + flexive (Russian), nonlinear + flexive
    (Arabic), or isolating (flexivity N/A). -/
inductive Flexivity where
  | nonflexive   -- formatives phonologically invariant / rule-governed
  | flexive      -- formatives show item-based (class-conditioned) allomorphy
  deriving DecidableEq, Repr

/-- WALS Ch 21: How many grammatical categories a single case formative
    expresses. Specifically about *case* formatives and whether they
    bundle number, TAM, etc.

    Distinct from `ExponenceScope` (B&N's broader cumulative/separative
    parameter which applies to all morphological categories, not just case).
    [bickel-nichols-2001] -/
inductive CaseExponence where
  | monoexponential
  | polyexponential
  | noCase
  deriving DecidableEq, Repr

/-- Whether a single formative expresses multiple grammatical categories
    simultaneously (cumulative) or each formative expresses exactly one
    category (separative).

    [bickel-nichols-2001]: this is a general morphological parameter
    applying across all category pairs, not limited to case+number (cf.
    WALS Ch 21 `Exponence`). Latin *-ō* (1sg.pres.act.ind) is cumulative;
    Turkish verb suffixes are separative (each suffix = one category). -/
inductive ExponenceScope where
  | cumulative    -- one formative, multiple categories
  | separative    -- one formative per category
  deriving DecidableEq, Repr

/-- WALS Ch 22: How many inflectional categories are expressed on the verb. -/
inductive VerbSynthesis where
  | low       -- 0--3 categories per verb word
  | moderate  -- 4--7 categories per verb word
  | high      -- 8+ categories per verb word
  deriving DecidableEq, Repr

/-- Locus of marking: where grammatical relations are marked.
    Derived from WALS Ch 25A [nichols-bickel-2013a]. -/
inductive LocusOfMarking where
  | headMarking
  | dependentMarking
  | doubleMarking
  | zeroMarking
  | inconsistentOrOther
  deriving DecidableEq, Repr

/-- WALS Ch 26: Whether a language predominantly uses prefixes or suffixes. -/
inductive PrefixSuffix where
  | stronglySuffixing
  | weaklySuffixing
  | equalPrefixSuffix
  | weaklyPrefixing
  | stronglyPrefixing
  | littleAffixation
  deriving DecidableEq, Repr

/-- WALS Ch 27: Whether the language has productive reduplication. -/
inductive Reduplication where
  | productiveFull
  | fullOnly
  | noProductive
  deriving DecidableEq, Repr

/-- WALS Ch 23: Where grammatical relations are marked in clausal syntax.
    [nichols-bickel-2013b] -/
inductive LocusClause where
  | headMarking
  | dependentMarking
  | doubleMarking
  | noMarking
  | other
  deriving DecidableEq, Repr

/-- WALS Ch 24: Where grammatical relations are marked in possessive NPs.
    [nichols-bickel-2013c] -/
inductive LocusPossessive where
  | headMarking
  | dependentMarking
  | doubleMarking
  | noMarking
  | other
  deriving DecidableEq, Repr

/-- WALS Ch 25A: Whole-language locus-of-marking classification.
    [nichols-bickel-2013a] -/
inductive WholeLanguageMarking where
  | headMarking
  | dependentMarking
  | doubleMarking
  | zeroMarking
  | inconsistentOrOther
  deriving DecidableEq, Repr

/-- WALS Ch 25B: Whether A and P arguments are zero-marked.
    [nichols-bickel-2013d] -/
inductive ZeroMarkingAP where
  | zeroMarking
  | nonZeroMarking
  deriving DecidableEq, Repr

/-- WALS Ch 28: Whether a language exhibits case syncretism. -/
inductive CaseSyncretism where
  | noCaseMarking
  | coreCasesOnly
  | coreAndNonCore
  | noSyncretism
  deriving DecidableEq, Repr

/-- WALS Ch 29: Whether a language exhibits syncretism in verbal person/number. -/
inductive VerbalSyncretism where
  | noSubjectMarking
  | syncretic
  | notSyncretic
  deriving DecidableEq, Repr

/-- WALS Ch 21B: What categories co-occur with TAM in a single formative. -/
inductive TAMExponence where
  | monoexponential
  | tamAgreement
  | tamAgreementDiathesis
  | tamAgreementConstruct
  | tamPolarity
  | noTam
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- WALS Ch 79A: Whether suppletion is conditioned by tense, aspect, or both. -/
inductive SuppletionTA where
  | tense
  | aspect
  | tenseAndAspect
  | none
  deriving DecidableEq, Repr

/-- WALS Ch 79B: Whether a language has suppletive imperatives/hortatives. -/
inductive SuppletionImperative where
  | alternating
  | imperative
  | hortative
  | imperativeAndHortative
  | none
  deriving DecidableEq, Repr

/-- WALS Ch 80A: Whether a language has verbal number marking. -/
inductive VerbalNumber where
  | none
  | pairsNoSuppletion
  | pairsSuppletion
  | triplesNoSuppletion
  | triplesSuppletion
  deriving DecidableEq, Repr

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
  exponence : CaseExponence
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
  /-- [bickel-nichols-2001]: Flexivity — whether inflectional formatives
      show item-based allomorphic variation (flexive) or are phonologically
      invariant (nonflexive). Orthogonal to `fusion`. Not derivable from WALS. -/
  flexivity : Option Flexivity := none
  /-- [bickel-nichols-2001]: Exponence scope — whether single formatives
      bundle multiple categories (cumulative) or each expresses one (separative).
      Broader than WALS Ch 21 `exponence` (which is case-specific). -/
  bnExponence : Option ExponenceScope := none
  deriving Repr, DecidableEq

-- ============================================================================
-- §3. WALS Converter Functions
-- ============================================================================

/-- Convert WALS 20A fusion type to the local three-way `Fusion` classification.
    Returns `none` for mixed categories that do not map cleanly. -/
def fromWALS20A : Data.WALS.F20A.FusionType → Option Fusion
  | .exclusivelyConcatenative => some .concatenative
  | .exclusivelyIsolating     => some .isolating
  | .exclusivelyTonal         => some .nonlinear
  | .ablautConcatenative      => some .nonlinear
  | .tonalIsolating           => none
  | .tonalConcatenative       => none
  | .isolatingConcatenative   => none

/-- Convert WALS 21A exponence type to the local `Exponence` classification.
    Returns `none` for `noCase` (no information about overall exponence). -/
def fromWALS21A : Data.WALS.F21A.ExponenceType → Option CaseExponence
  | .monoexponentialCase  => some .monoexponential
  | .caseNumber           => some .polyexponential
  | .caseReferentiality   => some .polyexponential
  | .caseTam              => some .polyexponential
  | .noCase               => none

/-- Convert WALS 22A inflectional synthesis to the local three-way classification. -/
def fromWALS22A : Data.WALS.F22A.InflectionalSynthesis → VerbSynthesis
  | .categoryPerWord0_1    => .low
  | .categoriesPerWord2_3  => .low
  | .categoriesPerWord4_5  => .moderate
  | .categoriesPerWord6_7  => .moderate
  | .categoriesPerWord8_9  => .high
  | .categoriesPerWord10_11 => .high
  | .categoriesPerWord12_13 => .high

def fromWALS26A : Data.WALS.F26A.PrefixSuffixPreference → PrefixSuffix
  | .littleAffixation             => .littleAffixation
  | .stronglySuffixing            => .stronglySuffixing
  | .weaklySuffixing              => .weaklySuffixing
  | .equalPrefixingAndSuffixing   => .equalPrefixSuffix
  | .weaklyPrefixing              => .weaklyPrefixing
  | .strongPrefixing              => .stronglyPrefixing

def fromWALS27A : Data.WALS.F27A.ReduplicationType → Reduplication
  | .productiveFullAndPartialReduplication => .productiveFull
  | .fullReduplicationOnly                => .fullOnly
  | .noProductiveReduplication            => .noProductive

def fromWALS23A : Data.WALS.F23A.LocusOfMarkingInTheClause → LocusClause
  | .headMarking      => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking    => .doubleMarking
  | .noMarking        => .noMarking
  | .other            => .other

def fromWALS24A :
    Data.WALS.F24A.LocusOfMarkingInPossessiveNounPhrases → LocusPossessive
  | .headMarking      => .headMarking
  | .dependentMarking => .dependentMarking
  | .doubleMarking    => .doubleMarking
  | .noMarking        => .noMarking
  | .other            => .other

def fromWALS25A :
    Data.WALS.F25A.LocusOfMarkingWholeLanguageTypology → WholeLanguageMarking
  | .headMarking         => .headMarking
  | .dependentMarking    => .dependentMarking
  | .doubleMarking       => .doubleMarking
  | .zeroMarking         => .zeroMarking
  | .inconsistentOrOther => .inconsistentOrOther

def fromWALS25B :
    Data.WALS.F25B.ZeroMarkingOfAAndPArguments → ZeroMarkingAP
  | .zeroMarking    => .zeroMarking
  | .nonZeroMarking => .nonZeroMarking

def fromWALS28A : Data.WALS.F28A.CaseSyncretism → CaseSyncretism
  | .noCaseMarking  => .noCaseMarking
  | .coreCasesOnly  => .coreCasesOnly
  | .coreAndNonCore => .coreAndNonCore
  | .noSyncretism   => .noSyncretism

def fromWALS29A :
    Data.WALS.F29A.SyncretismInVerbalPersonNumberMarking → VerbalSyncretism
  | .noSubjectPersonNumberMarking => .noSubjectMarking
  | .syncretic                    => .syncretic
  | .notSyncretic                 => .notSyncretic

def fromWALS21B :
    Data.WALS.F21B.ExponenceOfTenseAspectMoodInflection → TAMExponence
  | .monoexponentialTam      => .monoexponential
  | .tamAgreement            => .tamAgreement
  | .tamAgreementDiathesis   => .tamAgreementDiathesis
  | .tamAgreementConstruct   => .tamAgreementConstruct
  | .tamPolarity             => .tamPolarity
  | .noTam                   => .noTam

def fromWALS62A :
    Data.WALS.F62A.ActionNominalConstructions → ActionNominal
  | .sentential           => .sentential
  | .possessiveAccusative => .possessiveAccusative
  | .ergativePossessive   => .ergativePossessive
  | .doublePossessive     => .doublePossessive
  | .other                => .other
  | .mixed                => .mixed
  | .restricted           => .restricted
  | .noActionNominals     => .noActionNominals

def fromWALS79A :
    Data.WALS.F79A.SuppletionAccordingToTenseAndAspect → SuppletionTA
  | .tense          => .tense
  | .aspect         => .aspect
  | .tenseAndAspect => .tenseAndAspect
  | .none           => .none

def fromWALS79B :
    Data.WALS.F79B.SuppletionInImperativesAndHortatives → SuppletionImperative
  | .aRegularAndASuppletiveFormAlternate => .alternating
  | .imperative                          => .imperative
  | .hortative                           => .hortative
  | .imperativeAndHortative              => .imperativeAndHortative
  | .none                                => .none

def fromWALS80A :
    Data.WALS.F80A.VerbalNumberAndSuppletion → VerbalNumber
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
  (Data.WALS.F20A.lookupISO iso).bind (fromWALS20A ·.value)

def walsExponence (iso : String) : Option CaseExponence :=
  (Data.WALS.F21A.lookupISO iso).bind (fromWALS21A ·.value)

def walsVerbSynthesis (iso : String) : Option VerbSynthesis :=
  (Data.WALS.F22A.lookupISO iso).map (fromWALS22A ·.value)

def walsLocus (iso : String) : Option LocusOfMarking :=
  (Data.WALS.F23A.lookupISO iso).map (λ e => locusClauseToLocus (fromWALS23A e.value))

def walsPrefixSuffix (iso : String) : Option PrefixSuffix :=
  (Data.WALS.F26A.lookupISO iso).map (fromWALS26A ·.value)

def walsReduplication (iso : String) : Option Reduplication :=
  (Data.WALS.F27A.lookupISO iso).map (fromWALS27A ·.value)

def walsLocusClause (iso : String) : Option LocusClause :=
  (Data.WALS.F23A.lookupISO iso).map (fromWALS23A ·.value)

def walsLocusPossessive (iso : String) : Option LocusPossessive :=
  (Data.WALS.F24A.lookupISO iso).map (fromWALS24A ·.value)

def walsWholeLanguageMarking (iso : String) : Option WholeLanguageMarking :=
  (Data.WALS.F25A.lookupISO iso).map (fromWALS25A ·.value)

def walsZeroMarkingAP (iso : String) : Option ZeroMarkingAP :=
  (Data.WALS.F25B.lookupISO iso).map (fromWALS25B ·.value)

def walsCaseSyncretism (iso : String) : Option CaseSyncretism :=
  (Data.WALS.F28A.lookupISO iso).map (fromWALS28A ·.value)

def walsVerbalSyncretism (iso : String) : Option VerbalSyncretism :=
  (Data.WALS.F29A.lookupISO iso).map (fromWALS29A ·.value)

def walsTAMExponence (iso : String) : Option TAMExponence :=
  (Data.WALS.F21B.lookupISO iso).map (fromWALS21B ·.value)

def walsActionNominal (iso : String) : Option ActionNominal :=
  (Data.WALS.F62A.lookupISO iso).map (fromWALS62A ·.value)

def walsSuppletionTA (iso : String) : Option SuppletionTA :=
  (Data.WALS.F79A.lookupISO iso).map (fromWALS79A ·.value)

def walsSuppletionImperative (iso : String) : Option SuppletionImperative :=
  (Data.WALS.F79B.lookupISO iso).map (fromWALS79B ·.value)

def walsVerbalNumber (iso : String) : Option VerbalNumber :=
  (Data.WALS.F80A.lookupISO iso).map (fromWALS80A ·.value)

-- ============================================================================
-- §4½. Smart Constructor
-- ============================================================================

/-- Build a `MorphProfile` from an ISO 639-3 code via WALS lookups.

    Required-field fallbacks (`fusionFb`, `exponenceFb`, …) must be supplied
    for the six WALS chapters where the lookup may return `none` (language
    absent from chapter, or grounding function uninformative — e.g. WALS 20A
    `isolatingConcatenative` does not map cleanly to the local 3-way `Fusion`
    enum and yields `none`). When WALS has data the lookup wins; the fallback
    is exercised only when WALS is silent.

    Optional WALS fields (`locusClause`, `locusPossessive`, …) auto-populate
    from their lookup helpers and remain `none` if absent.

    The B&N 2001 parameters `flexivity` and `bnExponence` are NOT derivable
    from any WALS chapter — they are paper-stipulated per
    [bickel-nichols-2001] and must be passed explicitly when known. -/
def MorphProfile.fromWALS
    (language iso : String)
    (fusionFb : Fusion)
    (exponenceFb : CaseExponence)
    (verbSynthesisFb : VerbSynthesis)
    (locusFb : LocusOfMarking)
    (prefixSuffixFb : PrefixSuffix)
    (reduplicationFb : Reduplication)
    (flexivity : Option Flexivity := none)
    (bnExponence : Option ExponenceScope := none) : MorphProfile :=
  { language, iso
  , fusion := (walsFusion iso).getD fusionFb
  , exponence := (walsExponence iso).getD exponenceFb
  , verbSynthesis := (walsVerbSynthesis iso).getD verbSynthesisFb
  , locus := (walsLocus iso).getD locusFb
  , prefixSuffix := (walsPrefixSuffix iso).getD prefixSuffixFb
  , reduplication := (walsReduplication iso).getD reduplicationFb
  , locusClause := walsLocusClause iso
  , locusPossessive := walsLocusPossessive iso
  , wholeLanguageMarking := walsWholeLanguageMarking iso
  , zeroMarkingAP := walsZeroMarkingAP iso
  , caseSyncretism := walsCaseSyncretism iso
  , verbalSyncretism := walsVerbalSyncretism iso
  , tamExponence := walsTAMExponence iso
  , actionNominal := walsActionNominal iso
  , suppletionTA := walsSuppletionTA iso
  , suppletionImperative := walsSuppletionImperative iso
  , verbalNumber := walsVerbalNumber iso
  , flexivity, bnExponence
  }

-- ============================================================================
-- §5. Helper Predicates
-- ============================================================================

namespace MorphProfile

/-! Mathlib-style `Prop`-typed predicates with `Decidable` instances and
    `@[simp] _iff` lemmas. Filter sites that need `Bool` should call
    `decide` at the boundary. The `_iff` lemmas are `Iff.rfl` (unfolding-
    only) but make the decomposition visible to `simp` and to mathlib-
    pattern `decidable_of_iff` derivations. -/

def IsConcatenative (p : MorphProfile) : Prop := p.fusion = .concatenative
@[simp] theorem isConcatenative_iff (p : MorphProfile) :
    p.IsConcatenative ↔ p.fusion = .concatenative := Iff.rfl
instance : DecidablePred IsConcatenative :=
  fun p => decidable_of_iff _ (isConcatenative_iff p).symm

def IsIsolating (p : MorphProfile) : Prop := p.fusion = .isolating
@[simp] theorem isIsolating_iff (p : MorphProfile) :
    p.IsIsolating ↔ p.fusion = .isolating := Iff.rfl
instance : DecidablePred IsIsolating :=
  fun p => decidable_of_iff _ (isIsolating_iff p).symm

def IsNonlinear (p : MorphProfile) : Prop := p.fusion = .nonlinear
@[simp] theorem isNonlinear_iff (p : MorphProfile) :
    p.IsNonlinear ↔ p.fusion = .nonlinear := Iff.rfl
instance : DecidablePred IsNonlinear :=
  fun p => decidable_of_iff _ (isNonlinear_iff p).symm

def IsMono (p : MorphProfile) : Prop := p.exponence = .monoexponential
@[simp] theorem isMono_iff (p : MorphProfile) :
    p.IsMono ↔ p.exponence = .monoexponential := Iff.rfl
instance : DecidablePred IsMono :=
  fun p => decidable_of_iff _ (isMono_iff p).symm

def IsPoly (p : MorphProfile) : Prop := p.exponence = .polyexponential
@[simp] theorem isPoly_iff (p : MorphProfile) :
    p.IsPoly ↔ p.exponence = .polyexponential := Iff.rfl
instance : DecidablePred IsPoly :=
  fun p => decidable_of_iff _ (isPoly_iff p).symm

def HasRedup (p : MorphProfile) : Prop :=
  p.reduplication = .productiveFull ∨ p.reduplication = .fullOnly
@[simp] theorem hasRedup_iff (p : MorphProfile) :
    p.HasRedup ↔ p.reduplication = .productiveFull ∨ p.reduplication = .fullOnly :=
  Iff.rfl
instance : DecidablePred HasRedup :=
  fun p => decidable_of_iff _ (hasRedup_iff p).symm

def IsSuffixing (p : MorphProfile) : Prop :=
  p.prefixSuffix = .stronglySuffixing ∨ p.prefixSuffix = .weaklySuffixing
@[simp] theorem isSuffixing_iff (p : MorphProfile) :
    p.IsSuffixing ↔
      p.prefixSuffix = .stronglySuffixing ∨ p.prefixSuffix = .weaklySuffixing :=
  Iff.rfl
instance : DecidablePred IsSuffixing :=
  fun p => decidable_of_iff _ (isSuffixing_iff p).symm

def IsPrefixing (p : MorphProfile) : Prop :=
  p.prefixSuffix = .stronglyPrefixing ∨ p.prefixSuffix = .weaklyPrefixing
@[simp] theorem isPrefixing_iff (p : MorphProfile) :
    p.IsPrefixing ↔
      p.prefixSuffix = .stronglyPrefixing ∨ p.prefixSuffix = .weaklyPrefixing :=
  Iff.rfl
instance : DecidablePred IsPrefixing :=
  fun p => decidable_of_iff _ (isPrefixing_iff p).symm

def IsLowSynthesis (p : MorphProfile) : Prop := p.verbSynthesis = .low
@[simp] theorem isLowSynthesis_iff (p : MorphProfile) :
    p.IsLowSynthesis ↔ p.verbSynthesis = .low := Iff.rfl
instance : DecidablePred IsLowSynthesis :=
  fun p => decidable_of_iff _ (isLowSynthesis_iff p).symm

def IsHighSynthesis (p : MorphProfile) : Prop := p.verbSynthesis = .high
@[simp] theorem isHighSynthesis_iff (p : MorphProfile) :
    p.IsHighSynthesis ↔ p.verbSynthesis = .high := Iff.rfl
instance : DecidablePred IsHighSynthesis :=
  fun p => decidable_of_iff _ (isHighSynthesis_iff p).symm

def IsFlexive (p : MorphProfile) : Prop := p.flexivity = some .flexive
@[simp] theorem isFlexive_iff (p : MorphProfile) :
    p.IsFlexive ↔ p.flexivity = some .flexive := Iff.rfl
instance : DecidablePred IsFlexive :=
  fun p => decidable_of_iff _ (isFlexive_iff p).symm

def IsNonflexive (p : MorphProfile) : Prop := p.flexivity = some .nonflexive
@[simp] theorem isNonflexive_iff (p : MorphProfile) :
    p.IsNonflexive ↔ p.flexivity = some .nonflexive := Iff.rfl
instance : DecidablePred IsNonflexive :=
  fun p => decidable_of_iff _ (isNonflexive_iff p).symm

def IsCumulative (p : MorphProfile) : Prop := p.bnExponence = some .cumulative
@[simp] theorem isCumulative_iff (p : MorphProfile) :
    p.IsCumulative ↔ p.bnExponence = some .cumulative := Iff.rfl
instance : DecidablePred IsCumulative :=
  fun p => decidable_of_iff _ (isCumulative_iff p).symm

def IsSeparative (p : MorphProfile) : Prop := p.bnExponence = some .separative
@[simp] theorem isSeparative_iff (p : MorphProfile) :
    p.IsSeparative ↔ p.bnExponence = some .separative := Iff.rfl
instance : DecidablePred IsSeparative :=
  fun p => decidable_of_iff _ (isSeparative_iff p).symm

/-- Traditional "agglutinating" = concatenative + nonflexive + separative.
    [bickel-nichols-2001] decomposition of the traditional typology. -/
def IsAgglutinating (p : MorphProfile) : Prop :=
  p.IsConcatenative ∧ p.IsNonflexive ∧ p.IsSeparative
@[simp] theorem isAgglutinating_iff (p : MorphProfile) :
    p.IsAgglutinating ↔ p.IsConcatenative ∧ p.IsNonflexive ∧ p.IsSeparative :=
  Iff.rfl
instance : DecidablePred IsAgglutinating :=
  fun p => decidable_of_iff _ (isAgglutinating_iff p).symm

/-- Traditional "fusional" = concatenative + flexive + cumulative.
    [bickel-nichols-2001] decomposition of the traditional typology. -/
def IsFusional (p : MorphProfile) : Prop :=
  p.IsConcatenative ∧ p.IsFlexive ∧ p.IsCumulative
@[simp] theorem isFusional_iff (p : MorphProfile) :
    p.IsFusional ↔ p.IsConcatenative ∧ p.IsFlexive ∧ p.IsCumulative := Iff.rfl
instance : DecidablePred IsFusional :=
  fun p => decidable_of_iff _ (isFusional_iff p).symm

end MorphProfile

-- ============================================================================
-- §6. Structural Theorems on the B&N Parameter Space
-- ============================================================================

namespace MorphProfile

/-! ### Mutual exclusion

The traditional types "agglutinating" and "fusional" are mutually exclusive
because they require contradictory values on the flexivity dimension
(nonflexive vs flexive). This follows from the B&N decomposition — it is
not an empirical observation but a structural consequence of the definitions. -/

/-- Nonflexive and flexive are contradictory: a language cannot be both. -/
theorem nonflexive_flexive_exclusive (p : MorphProfile) :
    ¬(p.IsNonflexive ∧ p.IsFlexive) := by
  rintro ⟨h1, h2⟩
  exact absurd (h1.symm.trans h2) (by decide)

/-- Cumulative and separative are contradictory: a language cannot be both. -/
theorem cumulative_separative_exclusive (p : MorphProfile) :
    ¬(p.IsCumulative ∧ p.IsSeparative) := by
  rintro ⟨h1, h2⟩
  exact absurd (h1.symm.trans h2) (by decide)

/-- Agglutinating and fusional are mutually exclusive: they require opposite
    flexivity values (nonflexive vs flexive). Follows from the B&N
    decomposition; not an empirical observation. -/
theorem agglutinating_fusional_exclusive (p : MorphProfile) :
    ¬(p.IsAgglutinating ∧ p.IsFusional) := fun ⟨⟨_, hnf, _⟩, _, hf, _⟩ =>
  nonflexive_flexive_exclusive p ⟨hnf, hf⟩

end MorphProfile

end Morphology
