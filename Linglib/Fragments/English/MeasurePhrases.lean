import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic

/-!
# English Measure Phrase Fragment

Lexical entries for English measure terms and the preposition *per*.

This fragment provides the English-specific data layer for measurement:
- Measure term entries (gram, kilo, mile, ...) typed by `Dimension`
- The preposition *per* with its dual interpretation (Bale & Schwarz 2026)
- Context-dependent interpretation selection

## Architecture

Theory types (`Dimension`, `MeasureFn`, `MeasureTermSem`) live in
`TruthConditional.Measurement.Basic`. This file provides English lexical
entries — pure data typed by those theory types, following the
Theories → Fragments dependency discipline.

## References

- Scontras, G. (2014). *The Semantics of Measurement*. Ph.D. dissertation, Harvard.
- Bale, A. & Schwarz, B. (2026). Natural language and external conventions.
- Bale, A. & Schwarz, B. (2022). Measurements from "per" without complex dimensions.
- Coppock, E. (2022). Division vs. distributivity.
-/

namespace Fragments.English.MeasurePhrases

open TruthConditional.Measurement (Dimension QuotientDimension DimensionType)

-- ============================================================================
-- § 1. Measure Term Entries
-- ============================================================================

/-- A measure term entry: an English noun that names a specific measure function.

This is the Fragment-level data for measure terms. The Theory-level semantics
(`MeasureTermSem`) is in `TruthConditional.Measurement.Basic`. -/
structure MeasureTermEntry where
  /-- Surface form (e.g., "gram", "milliliter", "mile"). -/
  form : String
  /-- Plural form. -/
  formPlural : String
  /-- Which dimension this term measures. -/
  dimension : Dimension
  deriving Repr, BEq

def gram : MeasureTermEntry :=
  { form := "gram", formPlural := "grams", dimension := .mass }
def kilo : MeasureTermEntry :=
  { form := "kilo", formPlural := "kilos", dimension := .mass }
def pound : MeasureTermEntry :=
  { form := "pound", formPlural := "pounds", dimension := .mass }
def milliliter : MeasureTermEntry :=
  { form := "milliliter", formPlural := "milliliters", dimension := .volume }
def liter : MeasureTermEntry :=
  { form := "liter", formPlural := "liters", dimension := .volume }
def mile : MeasureTermEntry :=
  { form := "mile", formPlural := "miles", dimension := .distance }
def kilometer : MeasureTermEntry :=
  { form := "kilometer", formPlural := "kilometers", dimension := .distance }
def meter : MeasureTermEntry :=
  { form := "meter", formPlural := "meters", dimension := .distance }
def hour : MeasureTermEntry :=
  { form := "hour", formPlural := "hours", dimension := .time }
def second_ : MeasureTermEntry :=
  { form := "second", formPlural := "seconds", dimension := .time }

def allMeasureTerms : List MeasureTermEntry :=
  [gram, kilo, pound, milliliter, liter, mile, kilometer, meter, hour, second_]

-- ============================================================================
-- § 2. Quantizing Noun Entries (Scontras 2014, Ch. 3)
-- ============================================================================

open TruthConditional.Measurement (QuantizingNounClass ContainerReading)

/-- A quantizing noun entry: an English noun that turns a mass term into a
countable expression.

Scontras (2014, Ch. 3) identifies three classes, each with different
semantics:

- **Measure terms** (kilo, liter): type ⟨n, ⟨e,t⟩⟩, always quantity-uniform.
  Already covered by `MeasureTermEntry` above.
- **Container nouns** (glass, box, cup): ambiguous between a CONTAINER reading
  (individuated physical objects, NOT quantity-uniform) and a MEASURE reading
  (functions as a volume/mass unit, IS quantity-uniform).
- **Atomizers** (grain, piece, drop): impose a minimal-part structure on
  a mass noun, creating countable atoms without naming a measure function.

The Fragment entry captures the lexical form and class. The semantic
distinction (quantity-uniformity, CONTAINER vs MEASURE reading) comes
from the Theory types `QuantizingNounClass` and `ContainerReading`. -/
structure QuantizingNounEntry where
  /-- Surface form (e.g., "glass", "grain"). -/
  form : String
  /-- Plural form. -/
  formPlural : String
  /-- Which class of quantizing noun. -/
  nounClass : QuantizingNounClass
  /-- For container nouns in their MEASURE reading: which dimension they
      measure. A glass measures volume; a bag might measure volume or mass.
      Atomizers and pure containers have `none`. -/
  measureDimension : Option Dimension := none
  /-- Available readings. Measure terms and atomizers have only one reading;
      container nouns are ambiguous between CONTAINER and MEASURE. -/
  availableReadings : List ContainerReading := []
  deriving Repr, BEq

-- Container nouns (ambiguous CONTAINER/MEASURE)

/-- "glass" — prototypical container noun (Scontras §3.2).

  - CONTAINER: "three glasses of water" = three individual glasses containing water
  - MEASURE: "three glasses of water" = a quantity of water equal to three glass-volumes

The CONTAINER reading is NOT quantity-uniform: three glasses ⊕ three glasses ≠ three glasses.
The MEASURE reading IS quantity-uniform (like any measure term). -/
def glass : QuantizingNounEntry where
  form := "glass"
  formPlural := "glasses"
  nounClass := .containerNoun
  measureDimension := some .volume
  availableReadings := [.container, .measure]

def box : QuantizingNounEntry where
  form := "box"
  formPlural := "boxes"
  nounClass := .containerNoun
  measureDimension := some .volume
  availableReadings := [.container, .measure]

def cup : QuantizingNounEntry where
  form := "cup"
  formPlural := "cups"
  nounClass := .containerNoun
  measureDimension := some .volume
  availableReadings := [.container, .measure]

def bag : QuantizingNounEntry where
  form := "bag"
  formPlural := "bags"
  nounClass := .containerNoun
  measureDimension := some .volume
  availableReadings := [.container, .measure]

def bottle : QuantizingNounEntry where
  form := "bottle"
  formPlural := "bottles"
  nounClass := .containerNoun
  measureDimension := some .volume
  availableReadings := [.container, .measure]

-- Atomizers (impose minimal-part structure)

/-- "grain" — atomizer (Scontras §3.3).

  "three grains of rice" imposes a minimal-part structure on the mass
  noun "rice". Unlike measure terms, "grain" does not name a standard
  measure function — it creates contextually-determined atoms. -/
def grain : QuantizingNounEntry where
  form := "grain"
  formPlural := "grains"
  nounClass := .atomizer

def piece : QuantizingNounEntry where
  form := "piece"
  formPlural := "pieces"
  nounClass := .atomizer

def drop : QuantizingNounEntry where
  form := "drop"
  formPlural := "drops"
  nounClass := .atomizer

def slice : QuantizingNounEntry where
  form := "slice"
  formPlural := "slices"
  nounClass := .atomizer

def chunk : QuantizingNounEntry where
  form := "chunk"
  formPlural := "chunks"
  nounClass := .atomizer

def allQuantizingNouns : List QuantizingNounEntry :=
  [glass, box, cup, bag, bottle, grain, piece, drop, slice, chunk]

def allContainerNouns : List QuantizingNounEntry :=
  allQuantizingNouns.filter (·.nounClass == .containerNoun)

def allAtomizers : List QuantizingNounEntry :=
  allQuantizingNouns.filter (·.nounClass == .atomizer)

-- ============================================================================
-- § 3. Per-Phrase Interpretation
-- ============================================================================

/-- Interpretation mode for *per*-phrases (Bale & Schwarz 2026).

*Per* exhibits a dual interpretive pattern:
- **Compositional**: when saturating measure predicates that select for simplex
  dimensions (weight, distance). The grammar computes meaning via multiplication.
- **Math speak**: when describing quotient dimensions (density, speed). The phrase
  verbalizes quantity calculus notation and gets its meaning from extra-grammatical
  conventions, parallel to mixed quotation (Davidson 1979). -/
inductive PerInterpretation where
  /-- Grammatically composed: *per* interacts with a covert pronoun *pro*
      whose value is determined anaphorically (Bale & Schwarz 2022).
      ⟦per⟧ = λq. λx. λr. (μ_dim(q)(x) / q) * r -/
  | compositional
  /-- Math speak: the *per*-phrase verbalizes a quantity calculus expression.
      Not derived from the syntactic structure of English. -/
  | mathSpeak
  /-- Non-compositional, idiomatic unit (e.g., "pounds per square inch" = psi).
      Speakers know the abbreviation without knowing the underlying ratio. -/
  | idiomatic
  deriving Repr, DecidableEq, BEq

/-- Entry for the preposition *per* in measure phrases. -/
structure PerEntry where
  form : String := "per"
  /-- *Per* is ambiguous between compositional and math-speak interpretations. -/
  interpretations : List PerInterpretation := [.compositional, .mathSpeak]
  /-- Compositional *per* composes via multiplication only (No Division Hypothesis). -/
  usesMultiplicationOnly : Bool := true
  deriving Repr, BEq

def per : PerEntry := {}

/-- Which interpretation is available depends on the dimension type
of the measure predicate. Simplex dimensions license compositional
interpretation; quotient dimensions force math speak. -/
def perInterpInContext (selectsDimension : Dimension)
    (predicateDimension : Option Dimension) : PerInterpretation :=
  match predicateDimension with
  | some d => if d == selectsDimension then .compositional else .mathSpeak
  | none   => .mathSpeak  -- No simplex predicate → must be math speak

-- ============================================================================
-- § 4. Verification
-- ============================================================================

/-- All measure terms have distinct dimensions appropriately assigned. -/
theorem gram_is_mass : gram.dimension = .mass := rfl
theorem liter_is_volume : liter.dimension = .volume := rfl
theorem mile_is_distance : mile.dimension = .distance := rfl
theorem hour_is_time : hour.dimension = .time := rfl

/-- Container nouns are classified correctly. -/
theorem glass_is_container : glass.nounClass = .containerNoun := rfl
theorem box_is_container : box.nounClass = .containerNoun := rfl

/-- Atomizers are classified correctly. -/
theorem grain_is_atomizer : grain.nounClass = .atomizer := rfl
theorem piece_is_atomizer : piece.nounClass = .atomizer := rfl

/-- Container nouns have both readings available. -/
theorem glass_has_both_readings :
    glass.availableReadings = [.container, .measure] := rfl

/-- Container nouns in MEASURE reading measure volume. -/
theorem glass_measures_volume : glass.measureDimension = some .volume := rfl

/-- Atomizers have no measure dimension (they don't name a measure function). -/
theorem grain_no_dimension : grain.measureDimension = none := rfl
theorem piece_no_dimension : piece.measureDimension = none := rfl

/-- All container nouns are container nouns; all atomizers are atomizers. -/
theorem all_containers_are_containers :
    ∀ n ∈ allContainerNouns, n.nounClass = .containerNoun := by
  simp [allContainerNouns, allQuantizingNouns]; decide

theorem all_atomizers_are_atomizers :
    ∀ n ∈ allAtomizers, n.nounClass = .atomizer := by
  simp [allAtomizers, allQuantizingNouns]; decide

/-- Container nouns all have a measure dimension; atomizers never do. -/
theorem containers_have_dimension :
    ∀ n ∈ allContainerNouns, n.measureDimension.isSome = true := by
  simp [allContainerNouns, allQuantizingNouns]; decide

theorem atomizers_lack_dimension :
    ∀ n ∈ allAtomizers, n.measureDimension.isNone = true := by
  simp [allAtomizers, allQuantizingNouns]; decide

/-- Per defaults to compositional and math-speak interpretations. -/
theorem per_default_interps :
    per.interpretations = [.compositional, .mathSpeak] := rfl

/-- Compositional per uses multiplication only. -/
theorem per_multiplication_only : per.usesMultiplicationOnly = true := rfl

-- ============================================================================
-- § 5. Interpretation Selection from Verb Context
-- ============================================================================

/-- When a verb selects for the same dimension as the *per*-phrase's unit,
the interpretation is compositional. -/
theorem same_dimension_compositional (d : Dimension) :
    perInterpInContext d (some d) = .compositional := by
  cases d <;> rfl

/-- When the verb selects for a different dimension (or none), the
interpretation is math speak. -/
theorem different_dimension_mathSpeak (d₁ d₂ : Dimension) (h : d₁ ≠ d₂) :
    perInterpInContext d₁ (some d₂) = .mathSpeak := by
  cases d₁ <;> cases d₂ <;> (first | exact absurd rfl h | rfl)

/-- When no predicate dimension is available, the interpretation is math speak. -/
theorem no_dimension_mathSpeak (d : Dimension) :
    perInterpInContext d none = .mathSpeak := rfl

end Fragments.English.MeasurePhrases
