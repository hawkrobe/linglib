import Linglib.Morphology.Reflex
import Linglib.Syntax.Extraction

/-!
# K'iche' Extraction Morphology

Theory-neutral data on the extraction particle *wi* (the "fronting
particle") in K'iche' and Kaqchikel (K'ichean Mayan), following
[mendes-ranero-2021], [elkins-torrence-brown-2026], and [mondloch-2017].
When a low adjunct (locative, instrumental, comitative, indirect object)
undergoes Ā-extraction, *wi* appears as a verbal enclitic;
[mendes-ranero-2021] analyze it as Chain Reduction via Substitution,
with the lower copy of the moved adjunct (bearing [APPL]) substituted by
*wi* rather than deleted.

## Main declarations

* `Kiche.KicheExtractionDatum`, `Kiche.allData`: the *wi*-distribution
  data points.
* `Kiche.KicheLongDistanceDatum`, `Kiche.ldData`: long-distance
  extraction data across embedded CP vs AspP.
* `Kiche.fronting_particle_generalization`: matrix *wi* is contingent on
  an overt embedded complementizer.
* `Kiche.Extraction.realize`: the AF- and *wi*-based extraction marking,
  with `Kiche.Extraction.strategy` as the WALS-style label.

## Implementation notes

*wi* triggers only on low adjuncts introduced in Spec,ApplP
(instrumentals, locatives, comitatives, indirect objects); temporal and
reason adjuncts do not trigger it. It is obligatory in K'iche', optional
in Patzún Kaqchikel, and absent in some Kaqchikel dialects (e.g.
Tecpán). [mendes-ranero-2021] §4 argues *wi* is not a pronoun,
applicative head, movement trigger, or AF morpheme. The Fronting
Particle Generalization ([mendes-ranero-2021] definition (5), first
observed by Can Pixabaj 2015) is stated and checked at
`fronting_particle_generalization`.
-/

open Extraction (ExtractionTarget ExtractionMarkingStrategy Marked)

namespace Kiche

/-! ### Extracted argument types -/

/-- Types of extracted arguments relevant for *wi* distribution. -/
inductive ExtractedArgType where
  | obliqueSpatial       -- 'where', 'from where' (locative/source PPs)
  | obliqueTemporal      -- 'when'
  | obliqueReason        -- 'why'
  | obliqueInstrumental  -- 'with what'
  | subject              -- 'who' (agent — triggers Agent Focus, not *wi*)
  | object               -- 'what' (patient)
  deriving DecidableEq, Repr

/-- Is this argument type an oblique? -/
def ExtractedArgType.isOblique : ExtractedArgType → Bool
  | .obliqueSpatial | .obliqueTemporal | .obliqueReason | .obliqueInstrumental => true
  | .subject | .object => false

/-! ### *wi* distribution data -/

/-- A K'iche' extraction data point: what is extracted and whether *wi*
    appears after the verb. -/
structure KicheExtractionDatum where
  label : String
  reference : String
  extractedType : ExtractedArgType
  wiLicensed : Bool
  deriving Repr

/-- Spatial oblique extraction ("Where did you go yesterday?"): *wi* licensed.
    [mondloch-2017] Lesson 14; [mendes-ranero-2021] §2, ex. (9a). -/
def spatialOblExtraction : KicheExtractionDatum :=
  { label := "Spatial oblique extraction (wi)"
  , reference := "Mondloch 2017, Lesson 14; Mendes & Ranero 2021, §2, ex. (9a)"
  , extractedType := .obliqueSpatial
  , wiLicensed := true }

/-- Instrumental oblique extraction ("With what did they eat their food?"):
    *wi* licensed. [mendes-ranero-2021] §2, ex. (9b). -/
def instrumentalOblExtraction : KicheExtractionDatum :=
  { label := "Instrumental oblique extraction (wi)"
  , reference := "Mendes & Ranero 2021, §2, ex. (9b)"
  , extractedType := .obliqueInstrumental
  , wiLicensed := true }

/-- Temporal oblique extraction ("When did you eat beans?"): *wi* NOT
    licensed — parallel to Mam, where temporal obliques are also exempt.
    [mendes-ranero-2021] §2, ex. (12c). -/
def temporalOblExtraction : KicheExtractionDatum :=
  { label := "Temporal oblique extraction (no wi)"
  , reference := "Mendes & Ranero 2021, §2, ex. (12c)"
  , extractedType := .obliqueTemporal
  , wiLicensed := false }

/-- Reason oblique extraction ("Why did Juan work?"): *wi* NOT licensed —
    key contrast with Mam, where SJO =(y)a' IS licensed with reason
    extraction. [mendes-ranero-2021] §2 (adapted from Elkins et al. Table 3). -/
def reasonOblExtraction : KicheExtractionDatum :=
  { label := "Reason oblique extraction (no wi)"
  , reference := "Mendes & Ranero 2021, §2; Elkins et al. Table 3"
  , extractedType := .obliqueReason
  , wiLicensed := false }

/-- Subject extraction ("Who bought it?"): *wi* NOT licensed — Agent Focus
    morphology *-Vk* appears instead. [mendes-ranero-2021] §2, item (6c). -/
def subjectExtraction : KicheExtractionDatum :=
  { label := "Subject extraction (AF, no wi)"
  , reference := "Mendes & Ranero 2021, §2, item (6c)"
  , extractedType := .subject
  , wiLicensed := false }

/-- Object extraction ("What did you buy?"): *wi* NOT licensed.
    [elkins-torrence-brown-2026]. -/
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

/-! ### Generalizations -/

/-- Among the formalized data points, *wi* is licensed exactly for
    spatial and instrumental obliques; the full trigger set also includes
    comitatives and indirect objects ([mendes-ranero-2021] §2;
    [elkins-torrence-brown-2026] Table 3), not yet formalized here. -/
theorem wi_subset_of_obliques :
    allData.all (λ d =>
      d.wiLicensed == (d.extractedType == .obliqueSpatial ||
                       d.extractedType == .obliqueInstrumental)) = true := by
  decide

/-- *wi* does not appear with subject or object extraction. -/
theorem wi_not_core_args :
    subjectExtraction.wiLicensed = false ∧
    objectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Temporal exemption is shared across Mayan: neither *wi* (K'ichean)
    nor =(y)a' (Mam) appears with temporal oblique extraction. -/
theorem temporal_exempt : temporalOblExtraction.wiLicensed = false := rfl

/-! ### Embedded clause types and the Fronting Particle Generalization -/

/-- Embedded clause types for long-distance *wi* distribution: whether the
    embedded clause has an overt complementizer (CP) or not (a structurally
    reduced AspP). [mendes-ranero-2021] §2, exx. (17)–(20), (34)–(37). -/
inductive KicheEmbeddedClauseType where
  /-- Full CP with overt complementizer *chi*. -/
  | cp
  /-- Reduced AspP without complementizer. -/
  | aspP
  deriving DecidableEq, Repr

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
    [mendes-ranero-2021] §3, ex. (34); adapted from Can Pixabaj 2015: 166–167. -/
def ldFromCP : KicheLongDistanceDatum :=
  { label := "LD extraction from embedded CP (wi on both)"
  , reference := "Mendes & Ranero 2021, §3, ex. (34)"
  , embeddedType := .cp
  , wiOnMatrix := true
  , wiOnEmbedded := true }

/-- LD from embedded AspP: *wi* only on embedded predicate, NOT matrix.
    [mendes-ranero-2021] §3, ex. (35); adapted from Can Pixabaj 2015: 163. -/
def ldFromAspP : KicheLongDistanceDatum :=
  { label := "LD extraction from embedded AspP (wi on embedded only)"
  , reference := "Mendes & Ranero 2021, §3, ex. (35)"
  , embeddedType := .aspP
  , wiOnMatrix := false
  , wiOnEmbedded := true }

def ldData : List KicheLongDistanceDatum := [ldFromCP, ldFromAspP]

/-- The Fronting Particle Generalization ([mendes-ranero-2021] definition
    (5); first discussed by Can Pixabaj 2015): in long-distance
    Ā-extraction of a low adjunct from a single embedded clause, matrix
    *wi* is contingent on an overt complementizer in the embedded clause.
    Structurally ([mendes-ranero-2021] §3), C⁰ is a phase head — an
    embedded CP forces a stopover in embedded Spec,CP whose intermediate
    copy undergoes Chain Reduction via Substitution (matrix *wi*), while an
    embedded AspP has no phase boundary and the adjunct moves directly to
    matrix Spec,CP (no matrix *wi*). -/
theorem fronting_particle_generalization :
    ldData.all (λ d => d.embeddedType.hasComp == d.wiOnMatrix) = true := by
  decide

/-! ### Extraction marking -/

namespace Extraction

/-- Reflex hosts for K'iche' extraction marking. -/
inductive Site where
  | verb
  deriving DecidableEq, Repr

/-- K'iche' marks two extraction cells on the verb: subject extraction
    switches it to AF (the voice marker *-n*, [mondloch-2017] Lesson 22;
    Lessons 30, 33 for radical transitives and perfect aspect; shared
    with the Absolutive Antipassive of Lesson 21, from which AF differs
    syntactically, not morphologically), and oblique extraction adds
    *wi* via copy spellout at the foot of the Ā-chain
    ([mendes-ranero-2021]). Core-object extraction is unmarked. -/
def realize : ExtractionTarget → List (Morphology.Reflex Site)
  | .subject => [.morpheme .verb]
  | .oblique => [.morpheme .verb]
  | _ => []

/-- WALS-style label: dedicated morphemes mark extraction. -/
def strategy : ExtractionMarkingStrategy := .dedicatedMorpheme

theorem marks_oblique : Marked realize .oblique := by decide

end Extraction

end Kiche
