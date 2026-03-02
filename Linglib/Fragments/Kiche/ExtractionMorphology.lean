import Linglib.Core.Interfaces.ExtractionMorphology

/-!
# K'iche' Extraction Morphology Fragment
@cite{elkins-imanishi-coon-2026} @cite{henderson-2008} @cite{imanishi-2020} @cite{mondloch-2017}

Theory-neutral data on the extraction particle *wi* in K'iche' (and more
broadly K'ichean Mayan), contrasted with SJO Mam's =(y)a' (Elkins,
Imanishi & Coon 2026, §8).

## The Phenomenon

When an oblique or PP undergoes Ā-movement in K'ichean languages, the
particle *wi* appears after the verb in the position from which the
phrase moved. Its distribution differs from Mam =(y)a' in several
key respects:

1. **Locus**: *wi* appears at the extraction site (foot of the Ā-chain),
   while =(y)a' appears on the probe head (Voice⁰/Dir⁰).
2. **Analysis**: *wi* is copy spellout (Mondloch & Romero 2022),
   while =(y)a' is an Agree reflex.
3. **Reason obliques**: *wi* does NOT appear with reason ('why')
   extraction; =(y)a' DOES.
4. **Fronting Particle Generalization** (Henderson 2008, Imanishi 2020):
   *wi* occurs with phrasal (XP) movement but not head (X⁰) movement.
   This generalization does not hold for =(y)a', which is conditioned
   by clause size and oblique status, not movement type.

-/

namespace Fragments.Kiche

-- ============================================================================
-- § 1: Extracted Argument Types
-- ============================================================================

/-- Types of extracted arguments relevant for *wi* distribution. -/
inductive ExtractedArgType where
  | obliqueSpatial       -- 'where', 'from where' (locative/source PPs)
  | obliqueTemporal      -- 'when'
  | obliqueReason        -- 'why'
  | obliqueInstrumental  -- 'with what'
  | subject              -- 'who' (agent — triggers Agent Focus, not *wi*)
  | object               -- 'what' (patient)
  deriving DecidableEq, BEq, Repr

/-- Is this argument type an oblique? -/
def ExtractedArgType.isOblique : ExtractedArgType → Bool
  | .obliqueSpatial | .obliqueTemporal | .obliqueReason | .obliqueInstrumental => true
  | .subject | .object => false

-- ============================================================================
-- § 2: *wi* Distribution Data
-- ============================================================================

/-- A K'iche' extraction data point: what is extracted and whether *wi*
    appears after the verb. -/
structure KicheExtractionDatum where
  label : String
  reference : String
  extractedType : ExtractedArgType
  wiLicensed : Bool
  deriving Repr

/-- Spatial oblique extraction: *wi* licensed.
    "Where did you buy it?" — *wi* appears at extraction site.
    Romero 2012; Mondloch 2017. -/
def spatialOblExtraction : KicheExtractionDatum :=
  { label := "Spatial oblique extraction (wi)"
  , reference := "Romero 2012; Elkins et al. §2, §8"
  , extractedType := .obliqueSpatial
  , wiLicensed := true }

/-- Instrumental oblique extraction: *wi* licensed.
    "With what did you hit it?" — *wi* at extraction site.
    Mondloch 2017. -/
def instrumentalOblExtraction : KicheExtractionDatum :=
  { label := "Instrumental oblique extraction (wi)"
  , reference := "Mondloch 2017; Elkins et al. §8"
  , extractedType := .obliqueInstrumental
  , wiLicensed := true }

/-- Temporal oblique extraction: *wi* NOT licensed.
    "When did you buy it?" — no *wi*. Parallel to Mam: temporal
    obliques are exempt in both language groups.
    Elkins et al. §8.1. -/
def temporalOblExtraction : KicheExtractionDatum :=
  { label := "Temporal oblique extraction (no wi)"
  , reference := "Elkins et al. §8.1"
  , extractedType := .obliqueTemporal
  , wiLicensed := false }

/-- Reason oblique extraction: *wi* NOT licensed.
    "Why did you buy it?" — no *wi*. KEY CONTRAST with Mam: SJO
    =(y)a' IS licensed with reason extraction.
    Elkins et al. §8.1. -/
def reasonOblExtraction : KicheExtractionDatum :=
  { label := "Reason oblique extraction (no wi)"
  , reference := "Elkins et al. §8.1"
  , extractedType := .obliqueReason
  , wiLicensed := false }

/-- Subject extraction: *wi* NOT licensed (Agent Focus instead).
    "Who bought it?" — AF morphology *-Vk* instead of *wi*.
    Henderson 2008; Imanishi 2020. -/
def subjectExtraction : KicheExtractionDatum :=
  { label := "Subject extraction (AF, no wi)"
  , reference := "Henderson 2008; Imanishi 2020"
  , extractedType := .subject
  , wiLicensed := false }

/-- Object extraction: *wi* NOT licensed.
    "What did you buy?" — no *wi*.
    Romero 2012. -/
def objectExtraction : KicheExtractionDatum :=
  { label := "Object extraction (no wi)"
  , reference := "Romero 2012"
  , extractedType := .object
  , wiLicensed := false }

/-- All K'iche' extraction data points. -/
def allData : List KicheExtractionDatum :=
  [ spatialOblExtraction
  , instrumentalOblExtraction
  , temporalOblExtraction
  , reasonOblExtraction
  , subjectExtraction
  , objectExtraction ]

-- ============================================================================
-- § 3: Generalizations
-- ============================================================================

/-- *wi* is licensed only with spatial and instrumental obliques —
    a proper subset of the oblique types that trigger Mam =(y)a'.
    Specifically, *wi* excludes temporal AND reason obliques, while
    =(y)a' excludes only temporal obliques. -/
theorem wi_subset_of_obliques :
    allData.all (λ d =>
      d.wiLicensed == (d.extractedType == .obliqueSpatial ||
                       d.extractedType == .obliqueInstrumental)) = true := by
  native_decide

/-- *wi* does not appear with subject or object extraction. -/
theorem wi_not_core_args :
    subjectExtraction.wiLicensed = false ∧
    objectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Temporal exemption is shared across Mayan: neither *wi* (K'ichean)
    nor =(y)a' (Mam) appears with temporal oblique extraction. -/
theorem temporal_exempt : temporalOblExtraction.wiLicensed = false := rfl

-- ============================================================================
-- § 4: The Fronting Particle Generalization (Henderson 2008; Imanishi 2020)
-- ============================================================================

/-- The Fronting Particle Generalization: *wi* occurs in clauses where
    phrasal (XP) movement has occurred, but NOT in clauses involving
    only head (X⁰) movement.

    This generalization holds for K'ichean but NOT for Mam =(y)a':
    =(y)a' is conditioned by clause size (Voice projection) and
    oblique status, not by movement type (phrasal vs. head).

    Elkins et al. §8.2 argue this difference follows from the locus:
    *wi* is copy spellout (sensitive to what moved), while =(y)a' is
    Agree on Voice (sensitive to what Voice probes for). -/
def frontingParticleGeneralization : Bool := true

-- ============================================================================
-- § 5: Extraction Profile
-- ============================================================================

/-- K'ichean extraction profile: *wi* marks oblique extraction via
    copy spellout at the foot of the Ā-chain. -/
def kicheanExtractionProfile : Interfaces.ExtractionProfile :=
  { language := "K'ichean (K'iche', Kaqchikel, Tz'utujil)"
  , strategy := .dedicatedMorpheme
  , markedPositions := [.oblique]
  , distinguishesPosition := true
  , notes := "Particle wi at extraction site (copy spellout); " ++
             "spatial/instrumental only; temporal and reason exempt; " ++
             "Fronting Particle Generalization (Henderson 2008): " ++
             "XP-movement only, not X⁰-movement" }

theorem kichean_marks_oblique :
    kicheanExtractionProfile.marks .oblique = true := by native_decide

end Fragments.Kiche
