import Linglib.Core.Interfaces.ExtractionMorphology

/-!
# K'iche' Extraction Morphology Fragment
@cite{mendes-ranero-2021} @cite{elkins-torrence-brown-2026} @cite{mondloch-2017}

Theory-neutral data on the extraction particle *wi* (the "fronting
particle") in K'iche' and Kaqchikel (K'ichean Mayan).

## The Phenomenon

When a low adjunct (locative, instrumental, comitative, indirect object)
undergoes Ā-extraction in K'ichean languages, the particle *wi* appears
as a verbal enclitic. M&R analyze *wi* as the result of Chain Reduction
via Substitution: the lower copy of the moved adjunct (bearing [APPL])
is substituted by *wi* rather than being deleted.

## Key Properties

1. **Trigger**: Low adjuncts only — those introduced in Spec,ApplP
   (instrumentals, locatives, comitatives, indirect objects).
   Temporal and reason adjuncts do NOT trigger *wi*.
2. **Obligatoriness**: Obligatory in K'iche', optional in Patzún
   Kaqchikel, absent in some Kaqchikel dialects (e.g. Tecpán).
3. **Fronting Particle Generalization** (definition 5 of M&R, first
   observed by Can Pixabaj 2015): In long-distance extraction from a
   single embedded clause, the presence of *wi* in the matrix clause
   is contingent on the presence of an overt complementizer in the
   embedded clause. Embedded CPs yield *wi* on both predicates;
   embedded AspPs yield *wi* only on the embedded predicate.
4. **Not a pronoun, applicative head, movement trigger, or AF morpheme**
   (M&R §4 rejects all four alternative analyses).

-/

namespace Fragments.Mayan.Kiche

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

/-- Among the formalized data points, *wi* is licensed exactly for
    spatial and instrumental obliques. The full set of *wi*-triggering
    obliques includes comitatives and indirect objects as well
    (@cite{mendes-ranero-2021} §2; @cite{elkins-torrence-brown-2026}
    Table 3), but those are not yet formalized here. -/
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
-- § 4: Embedded Clause Types and the Fronting Particle Generalization
--      (@cite{mendes-ranero-2021}, definition (5); Can Pixabaj 2015)
-- ============================================================================

/-- Embedded clause types relevant for long-distance *wi* distribution.
    The crucial distinction is whether the embedded clause has an overt
    complementizer (= CP) or not (= AspP, a structurally reduced clause).
    @cite{mendes-ranero-2021} §2, exx. (17)–(20), (34)–(37). -/
inductive KicheEmbeddedClauseType where
  /-- Full CP with overt complementizer *chi*. -/
  | cp
  /-- Reduced AspP without complementizer. -/
  | aspP
  deriving DecidableEq, BEq, Repr

/-- Does this clause type have an overt complementizer? -/
def KicheEmbeddedClauseType.hasComp : KicheEmbeddedClauseType → Bool
  | .cp => true
  | .aspP => false

/-- Long-distance extraction datum for K'ichean *wi*. -/
structure KicheLongDistanceDatum where
  label : String
  reference : String
  embeddedType : KicheEmbeddedClauseType
  /-- Does *wi* appear on the matrix predicate? -/
  wiOnMatrix : Bool
  /-- Does *wi* appear on the embedded predicate? -/
  wiOnEmbedded : Bool
  deriving Repr

/-- LD from embedded CP: *wi* on BOTH matrix and embedded predicates.
    @cite{mendes-ranero-2021} §3, ex. (34); adapted from Can Pixabaj 2015: 166–167. -/
def ldFromCP : KicheLongDistanceDatum :=
  { label := "LD extraction from embedded CP (wi on both)"
  , reference := "Mendes & Ranero 2021, §3, ex. (34)"
  , embeddedType := .cp
  , wiOnMatrix := true
  , wiOnEmbedded := true }

/-- LD from embedded AspP: *wi* only on embedded predicate, NOT matrix.
    @cite{mendes-ranero-2021} §3, ex. (35); adapted from Can Pixabaj 2015: 163. -/
def ldFromAspP : KicheLongDistanceDatum :=
  { label := "LD extraction from embedded AspP (wi on embedded only)"
  , reference := "Mendes & Ranero 2021, §3, ex. (35)"
  , embeddedType := .aspP
  , wiOnMatrix := false
  , wiOnEmbedded := true }

def ldData : List KicheLongDistanceDatum := [ldFromCP, ldFromAspP]

/-- **The Fronting Particle Generalization** (@cite{mendes-ranero-2021},
    definition (5); first discussed by Can Pixabaj 2015):

    In long-distance A'-extraction of low adjuncts from a single
    embedded clause, the presence of *wi* in the matrix clause is
    contingent on the presence of an overt complementizer in the
    embedded clause.

    Structural explanation (M&R §3): C⁰ is a phase head, so when the
    embedded clause is a CP, the extracted adjunct must stop over in
    the embedded Spec,CP. Chain Reduction via Substitution applies to
    this intermediate copy, yielding *wi* on the matrix predicate. When
    the embedded clause is an AspP (no C⁰, no phase boundary), the
    adjunct moves directly to the matrix Spec,CP — no intermediate copy,
    no matrix *wi*. -/
theorem fronting_particle_generalization :
    ldData.all (λ d => d.embeddedType.hasComp == d.wiOnMatrix) = true := by
  native_decide

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
  , notes := "Fronting particle wi (Chain Reduction via Substitution); " ++
             "triggered by low adjuncts (spatial, instrumental, etc.); " ++
             "temporal and reason exempt; obligatory in K'iche', " ++
             "optional in Patzún Kaqchikel; FPG: matrix wi contingent " ++
             "on overt complementizer in embedded clause" }

theorem kichean_marks_oblique :
    kicheanExtractionProfile.marks .oblique = true := by native_decide

end Fragments.Mayan.Kiche
