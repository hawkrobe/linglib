import Linglib.Core.Interfaces.ExtractionMorphology

/-!
# K'iche' Extraction Morphology Fragment
@cite{mendes-ranero-2021} @cite{elkins-torrence-brown-2026} @cite{mondloch-2017}

Theory-neutral data on the extraction particle *wi* in K'iche' (and more
broadly K'ichean Mayan), contrasted with SJO Mam's =(y)a'.

## The Phenomenon

When an oblique or PP undergoes Ā-movement in K'ichean languages, the
particle *wi* appears after the verb in the position from which the
phrase moved. Its distribution differs from Mam =(y)a' in several
key respects:

1. **Locus**: *wi* appears at the extraction site (foot of the Ā-chain),
   while =(y)a' appears on the probe head (Voice⁰/Dir⁰).
2. **Analysis**: *wi* is copy spellout,
   while =(y)a' is an Agree reflex.
3. **Reason obliques**: *wi* does NOT appear with reason ('why')
   extraction; =(y)a' DOES.
4. **Fronting Particle Generalization**:
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
    "Where did you go yesterday?" — *wi* appears at extraction site.
    @cite{mondloch-2017} Lesson 14; @cite{mendes-ranero-2021} §2, ex. (9a). -/
def spatialOblExtraction : KicheExtractionDatum :=
  { label := "Spatial oblique extraction (wi)"
  , reference := "Mondloch 2017, Lesson 14; Mendes & Ranero 2021, §2, ex. (9a)"
  , extractedType := .obliqueSpatial
  , wiLicensed := true }

/-- Instrumental oblique extraction: *wi* licensed.
    "With what did they eat their food?" — *wi* at extraction site.
    @cite{mendes-ranero-2021} §2, ex. (9b). -/
def instrumentalOblExtraction : KicheExtractionDatum :=
  { label := "Instrumental oblique extraction (wi)"
  , reference := "Mendes & Ranero 2021, §2, ex. (9b)"
  , extractedType := .obliqueInstrumental
  , wiLicensed := true }

/-- Temporal oblique extraction: *wi* NOT licensed.
    "When did you eat beans?" — no *wi*. Parallel to Mam: temporal
    obliques are exempt in both language groups.
    @cite{mendes-ranero-2021} §2, ex. (12c). -/
def temporalOblExtraction : KicheExtractionDatum :=
  { label := "Temporal oblique extraction (no wi)"
  , reference := "Mendes & Ranero 2021, §2, ex. (12c)"
  , extractedType := .obliqueTemporal
  , wiLicensed := false }

/-- Reason oblique extraction: *wi* NOT licensed.
    "Why did Juan work?" — no *wi*. KEY CONTRAST with Mam: SJO
    =(y)a' IS licensed with reason extraction.
    @cite{mendes-ranero-2021} §2 (adapted from Elkins et al. Table 3). -/
def reasonOblExtraction : KicheExtractionDatum :=
  { label := "Reason oblique extraction (no wi)"
  , reference := "Mendes & Ranero 2021, §2; Elkins et al. Table 3"
  , extractedType := .obliqueReason
  , wiLicensed := false }

/-- Subject extraction: *wi* NOT licensed (Agent Focus instead).
    "Who bought it?" — AF morphology *-Vk* instead of *wi*.
    @cite{mendes-ranero-2021} §2, item (6c). -/
def subjectExtraction : KicheExtractionDatum :=
  { label := "Subject extraction (AF, no wi)"
  , reference := "Mendes & Ranero 2021, §2, item (6c)"
  , extractedType := .subject
  , wiLicensed := false }

/-- Object extraction: *wi* NOT licensed.
    "What did you buy?" — no *wi*.
    @cite{elkins-torrence-brown-2026}. -/
def objectExtraction : KicheExtractionDatum :=
  { label := "Object extraction (no wi)"
  , reference := "Elkins et al. 2026"
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
-- § 4: The Fronting Particle Generalization (@cite{mendes-ranero-2021})
-- ============================================================================

/-- The Fronting Particle Generalization: *wi* occurs in clauses where
    phrasal (XP) movement has occurred, but NOT in clauses involving
    only head (X⁰) movement.

    This generalization holds for K'ichean but NOT for Mam =(y)a':
    =(y)a' is conditioned by clause size (Voice projection) and
    oblique status, not by movement type (phrasal vs. head).

    First discussed by Can Pixabaj (2015); formalized in
    @cite{mendes-ranero-2021}, definition (5). -/
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
             "Fronting Particle Generalization (Mendes & Ranero 2021): " ++
             "XP-movement only, not X⁰-movement" }

theorem kichean_marks_oblique :
    kicheanExtractionProfile.marks .oblique = true := by native_decide

end Fragments.Kiche
