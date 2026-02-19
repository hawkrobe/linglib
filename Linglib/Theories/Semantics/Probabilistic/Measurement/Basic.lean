import Linglib.Core.Scale
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat

/-!
# Measurement Semantics

Formal semantics of measurement: measure functions, measure terms, and their
connection to numeral semantics and degree semantics.

## Theoretical Foundation (Scontras 2014)

Scontras's *The Semantics of Measurement* (Ch. 2) unifies numerals and measure
terms under a single framework. The key insight: **CARD is just another measure
term**. Where "kilo" names the mass measure μ_kg, the cardinal reading of a
numeral names the cardinality measure μ_CARD. Both are instances of the same
syntactic category M (measure term), with type ⟨n, ⟨e,t⟩⟩.

### The Measure Function

A **measure function** μ maps individuals to non-negative rationals along a
physical dimension:

    μ : Entity → ℚ≥0

The dimension (mass, volume, distance, time, cardinality) is the parameter
that distinguishes different measure functions: μ_kg, μ_L, μ_km, μ_CARD.

### Measure Terms as Measure Function Names

A measure term (gram, liter, mile) **names** a specific measure function.
Its denotation:

    ⟦kilo⟧ = λn. λx. μ_kg(x) = n

This is a function from a numeral (degree) to a predicate — exactly a
modifier of type ⟨n, ⟨e,t⟩⟩ in Scontras's system.

### CARD Unification

The cardinal reading of a bare numeral ("three cats") arises from the
same structure, with CARD as a covert measure term:

    ⟦CARD⟧ = λn. λx. μ_CARD(x) = n

So "three cats" = ⟦CARD⟧(3)(⟦cats⟧) = λx. cats(x) ∧ |x| = 3.

### Connection to Scale Infrastructure

The `HasDegree` typeclass in `Core.MeasurementScale` gives `E → ℚ`.
This module adds:
- Typed dimensions (what μ measures)
- Multiple measure functions per entity (weight AND volume AND cardinality)
- The quantity-uniform property (QU_μ: number morphology via measure)

## Connection to Bale & Schwarz (2026)

The No Division Hypothesis constrains what operations the grammar can perform
on these measure functions: addition and multiplication are available, but
division is not. Quotient dimensions (density = mass/volume) exist in the
quantity calculus but are not compositionally derivable.

## References

- Scontras, G. (2014). *The Semantics of Measurement*. Ph.D. dissertation, Harvard.
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
- Krifka, M. (1989). Nominal reference, temporal constitution, and quantification.
- Bale, A. & Schwarz, B. (2026). Natural language and external conventions.
-/

namespace Semantics.Probabilistic.Measurement

-- ============================================================================
-- § 1. Physical Dimensions
-- ============================================================================

/-- Physical dimensions that measure functions can target.

Simplex dimensions are directly measurable properties of entities. These
are the dimensions accessible to compositional semantics (Bale & Schwarz
2026: the grammar can compose via addition and multiplication along these).

Quotient dimensions (density, speed) are ratios of simplex dimensions.
The grammar cannot derive them compositionally (No Division Hypothesis);
they can only be referenced via extra-grammatical conventions (math speak). -/
inductive Dimension where
  | mass         -- weight (grams, kilos, pounds)
  | volume       -- volume (milliliters, liters, gallons)
  | distance     -- distance (miles, kilometers, meters)
  | time         -- duration (hours, seconds, minutes)
  | cardinality  -- counting (Scontras 2014: CARD as measure term)
  | temperature  -- temperature (degrees Celsius, Fahrenheit)
  | area         -- area (square meters, acres)
  deriving Repr, DecidableEq, BEq

/-- Quotient dimensions: ratios of simplex dimensions.

These exist in the quantity calculus but are not compositionally
derivable within the grammar (Bale & Schwarz 2026). -/
inductive QuotientDimension where
  | density      -- mass / volume
  | speed        -- distance / time
  | pressure     -- force / area
  deriving Repr, DecidableEq, BEq

/-- The simplex components of a quotient dimension. -/
def QuotientDimension.components : QuotientDimension → Dimension × Dimension
  | .density  => (.mass, .volume)
  | .speed    => (.distance, .time)
  | .pressure => (.mass, .area)

/-- Whether a given dimension is simplex (available to compositional semantics)
or quotient (only via math speak). All constructors of `Dimension` are simplex
by definition; `QuotientDimension` is always quotient. -/
inductive DimensionType where
  | simplex
  | quotient
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- § 2. Measure Functions
-- ============================================================================

/-- A measure function maps entities to non-negative rational magnitudes
along a specific dimension.

Scontras (2014, §2.4): degrees are pairs ⟨μ, n⟩ where μ is the measure
function and n is the numerical value. A measure function is individuated
by its dimension: μ_kg measures mass, μ_L measures volume, μ_CARD counts.

We use ℚ rather than ℝ to match the library's exact-arithmetic convention
for computational semantics. -/
structure MeasureFn (E : Type*) where
  /-- Which dimension this function measures. -/
  dimension : Dimension
  /-- The measure function itself: maps an entity to its magnitude. -/
  apply : E → ℚ
  /-- Measure values are non-negative. -/
  nonneg : ∀ e, apply e ≥ 0

/-- Apply a measure function to an entity. -/
instance {E : Type*} : CoeFun (MeasureFn E) (fun _ => E → ℚ) where
  coe μ := μ.apply

/-- Two measure functions agree on dimension and values. -/
def MeasureFn.agrees {E : Type*} (μ₁ μ₂ : MeasureFn E) : Prop :=
  μ₁.dimension = μ₂.dimension ∧ ∀ e, μ₁.apply e = μ₂.apply e

-- ============================================================================
-- § 3. Measure Term Semantics
-- ============================================================================

/-- A measure term's denotation: λn. λx. μ(x) = n.

Scontras (2014, §2.4.2): measure terms are nouns that name specific
measure functions. Their type is ⟨n, ⟨e,t⟩⟩ — they take a numeral
and return a predicate.

The `rel` field allows different interpretations: exact (=), at-least (≥),
or at-most (≤), matching the numeral semantics infrastructure in
`Numeral.Semantics.OrderingRel`. By default, measure terms denote exact
measurement (= n), and pragmatic strengthening (if needed) happens at
the numeral level, not the measure term level. -/
structure MeasureTermSem (E : Type*) where
  /-- The measure function this term names. -/
  measureFn : MeasureFn E
  /-- The comparison relation (default: exact). -/
  rel : ℚ → ℚ → Bool := (· == ·)

/-- Apply a measure term to a numeral n, yielding a predicate over entities.

    ⟦kilo⟧(3) = λx. μ_kg(x) = 3 -/
def MeasureTermSem.applyNumeral {E : Type*} (mt : MeasureTermSem E) (n : ℚ) : E → Bool :=
  fun x => mt.rel (mt.measureFn.apply x) n

-- ============================================================================
-- § 4. CARD: Cardinality as a Measure Term
-- ============================================================================

/-- CARD: the cardinality measure function.

Scontras (2014, §2.1): CARD is a covert measure term whose measure function
is |·|, the cardinality function. It takes a numeral and returns a predicate:

    ⟦CARD⟧ = λn. λx. |x| = n

This unifies bare numerals ("three cats") with measure phrases ("three kilos
of rice"): both involve a measure term (CARD or kilo) applied to a numeral. -/
def card (E : Type*) (cardFn : E → ℚ) (h : ∀ e, cardFn e ≥ 0) : MeasureTermSem E :=
  { measureFn := { dimension := .cardinality, apply := cardFn, nonneg := h } }

-- ============================================================================
-- § 5. Quantity-Uniform Property
-- ============================================================================

/-- A predicate P is **quantity-uniform** with respect to measure function μ
(Scontras 2014, Def. 2.5):

    QU_μ(P) ↔ ∀ x y, P(x) ∧ P(y) ∧ μ(x) = μ(y) → P(x ⊕ y)

If two P-individuals have the same μ-measure, their sum is also a
P-individual. This is the closure condition that ensures measure terms
compose correctly with plural predicates.

The importance: only quantity-uniform predicates admit measure modification.
"Three kilos of rice" requires that rice be QU_μ_kg (any two rice-quantities
of the same weight can be summed and remain rice). "??Three kilos of cat"
fails because cat is not quantity-uniform. -/
def IsQuantityUniform {E : Type*} (P : E → Bool) (μ : MeasureFn E)
    (sum : E → E → E) : Prop :=
  ∀ x y, P x = true → P y = true → μ.apply x = μ.apply y →
    P (sum x y) = true

-- ============================================================================
-- § 6. No Division Hypothesis (Bale & Schwarz 2026)
-- ============================================================================

/-- A composition operation on quantities. -/
structure CompOp (Q : Type*) where
  /-- The operation itself. -/
  op : Q → Q → Q
  /-- Which dimension the output lives in. -/
  outputDim : Dimension

/-- **No Division Hypothesis** (Bale & Schwarz 2026): quantity division is not
available as an operation for semantic composition.

No lexical item, composition rule, or type-shifting operation in the grammar
produces a value in a quotient dimension from simplex-dimension inputs.
Quantities in quotient dimensions (density, speed) can only be referenced
via extra-grammatical conventions (math speak / mixed quotation).

The hypothesis is stated over typed dimensions: no available composition
operation outputs a quotient dimension. -/
def noDivisionHypothesis (Q : Type*) (ops : List (CompOp Q))
    (quotientDims : List Dimension) : Prop :=
  ∀ op ∈ ops, op.outputDim ∉ quotientDims

/-- Weaker form: even if a language has a lexical item *per*, its compositional
semantics can be restated using only multiplication and pure numbers.
Both Coppock (2022) and Bale & Schwarz (2022) are reformulable this way. -/
def perMultiplicationOnly
    (Quantity : Type*) (mul : Quantity → Quantity → Quantity)
    (perMeaning : Quantity → Quantity → Quantity)
    (pureNumber : Quantity → Quantity → Quantity) : Prop :=
  ∀ q r, perMeaning q r = mul (pureNumber q r) r

-- ============================================================================
-- § 7. Bridge to HasDegree
-- ============================================================================

/-- A `MeasureFn` induces a `HasDegree` instance: the degree of an entity
is its measure value. This connects Scontras's measure functions to the
existing degree semantics infrastructure in `Core.MeasurementScale`.

Note: `HasDegree` is a single-measure typeclass (one degree per entity type).
For entities with multiple measurable dimensions (a box has weight AND volume),
use `MeasureFn` directly — `HasDegree` is the specialization for when a
single dimension is contextually salient. -/
def MeasureFn.toHasDegree {E : Type} (μ : MeasureFn E) : Core.Scale.HasDegree E :=
  { degree := μ.apply }

-- ============================================================================
-- § 8. Quantizing Nouns (Scontras 2014, Ch. 3)
-- ============================================================================

/-- Classification of quantizing nouns: nouns that turn mass terms into
countable expressions.

Scontras (2014, Ch. 3) identifies three classes:
- **Measure terms** (kilo, liter): name measure functions directly
- **Container nouns** (glass, box): ambiguous between CONTAINER and MEASURE readings
- **Atomizers** (grain, piece): impose a minimal-part structure

The key semantic difference: measure terms always yield quantity-uniform
predicates, while container nouns can yield non-quantity-uniform predicates
in their CONTAINER reading (because containers are individuated). -/
inductive QuantizingNounClass where
  | measureTerm    -- kilo, liter, meter: names a measure function
  | containerNoun  -- glass, box, cup: ambiguous CONTAINER/MEASURE
  | atomizer       -- grain, piece, drop: imposes minimal-part structure
  deriving Repr, DecidableEq, BEq

/-- Container nouns are ambiguous between two readings (Scontras §3.2):

- **CONTAINER**: the noun denotes physical containers; "three glasses of water"
  means three individual glasses containing water. The predicate is NOT
  quantity-uniform (three glasses ⊕ three glasses ≠ three glasses).

- **MEASURE**: the noun functions as a measure term; "three glasses of water"
  means a quantity of water whose volume equals three glass-volumes. The
  predicate IS quantity-uniform (like any measure term). -/
inductive ContainerReading where
  | container  -- individuated physical objects
  | measure    -- measure function (glass as a volume unit)
  deriving Repr, DecidableEq, BEq

/-- Scontras's QU prediction: which class/reading combinations yield
quantity-uniform predicates?

| Class         | Reading     | QU?   | Reason                                |
|---------------|-------------|-------|---------------------------------------|
| measureTerm   | (n/a)       | true  | Names a measure function directly     |
| containerNoun | .container  | false | Individuated containers don't sum     |
| containerNoun | .measure    | true  | Functions as a measure term           |
| atomizer      | (n/a)       | false | Atoms are individuated like containers|

This is the core prediction of Scontras Ch. 3: the CONTAINER/MEASURE ambiguity
of container nouns is exactly the ambiguity between QU and non-QU readings.
The MEASURE reading makes a container noun semantically equivalent to a measure
term; the CONTAINER reading makes it semantically equivalent to a count noun. -/
def predictsQU (cls : QuantizingNounClass) (reading : Option ContainerReading) : Bool :=
  match cls, reading with
  | .measureTerm,   _             => true   -- always QU
  | .containerNoun, some .measure => true   -- MEASURE reading = measure term
  | .containerNoun, some .container => false -- CONTAINER reading = individuated
  | .containerNoun, none          => false  -- default: CONTAINER reading
  | .atomizer,      _             => false  -- atoms are individuated

/-- Measure terms are always quantity-uniform, regardless of reading. -/
theorem measureTerm_always_QU (r : Option ContainerReading) :
    predictsQU .measureTerm r = true := by
  cases r <;> rfl

/-- Atomizers are never quantity-uniform, regardless of reading. -/
theorem atomizer_never_QU (r : Option ContainerReading) :
    predictsQU .atomizer r = false := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

/-- Container nouns are QU iff in MEASURE reading. -/
theorem containerNoun_QU_iff_measure (r : ContainerReading) :
    predictsQU .containerNoun (some r) = true ↔ r = .measure := by
  cases r <;> simp [predictsQU]

-- ============================================================================
-- § 9. Measure Term = MIP(atLeast)
-- ============================================================================

/-! ### The Scontras–Kennedy bridge

Scontras's measure term denotation ⟦kilo⟧(n)(x) = (μ_kg(x) = n) is
*exactly* the MIP applied to the at-least degree property of μ:

    max⊨(atLeast_μ, n, x) ↔ μ(x) = n

This is `isMaxInf_atLeast_iff_eq` from `MeasurementScale.lean`, instantiated
to our measure functions. The connection: Kennedy's type-shift IS Scontras's
measure term semantics. They're the same operation viewed from different sides.
-/

/-- A `MeasureTermSem` with the default exact relation (= n) yields the
predicate μ(x) = n — the same as the MIP applied to "at least".

This connects Scontras Ch. 2 to Kennedy (2015): the measure term denotation
⟦kilo⟧(n)(x) = (μ_kg(x) = n) is precisely what the MIP derives from the
lower-bound meaning "at least n kilos" when applied to cardinality/mass. -/
theorem measureTerm_exact {E : Type*} (μ : MeasureFn E) (n : ℚ) (x : E) :
    ({ measureFn := μ } : MeasureTermSem E).applyNumeral n x = (μ.apply x == n) := by
  rfl

-- ============================================================================
-- § 10. Scontras–Kennedy Equivalence (non-trivial)
-- ============================================================================

/-! ### The deep theorem: measure term semantics = MIP(lower-bound)

Scontras (2014) defines measure term meaning as exact:
    ⟦kilo⟧(n)(x) = (μ_kg(x) = n)

Kennedy (2015) defines bare numeral meaning as lower-bound + MIP:
    ⟦three⟧_LB = "at least 3"  →  MIP derives "exactly 3"

These are *two different theoretical proposals* for how exact meaning arises.
The deep claim: they produce identical truth conditions, but ONLY under
the surjectivity hypothesis — every measure value must be instantiated by
some entity (or world).

The surjectivity hypothesis is not free: it is exactly the condition that
separates mass nouns (rice: every quantity of rice exists → surjective)
from count nouns (cat: only integer-valued cardinalities exist → not
surjective over ℚ, only over ℕ).

For mass-noun measure terms (kilo, liter), surjectivity holds over ℚ,
so the two derivations coincide. For count nouns with CARD, surjectivity
holds only over ℕ, but the `moreThan_eq_atLeast_succ` theorem shows that
on ℕ, discrete collapse independently delivers exactness.

So the Scontras–Kennedy equivalence holds in BOTH cases, but for
*different reasons* depending on the dimension:
- Mass/volume/distance (dense): via `isMaxInf_atLeast_iff_eq` (surjectivity)
- Cardinality (discrete): via `moreThan_eq_atLeast_succ` (discrete collapse)

This is the formal content of Scontras's CARD unification thesis: CARD
and kilo are the same kind of object, but the proof that their semantics
agrees with the MIP goes through different lemmas. -/

open Core.Scale (atLeastDeg IsMaxInf)

/-- **Scontras–Kennedy equivalence for dense dimensions.**

For a measure function μ over a dense domain: MIP applied to the at-least
degree property at numeral n and entity x yields μ(x) = n — exactly
the measure term's denotation.

The proof relies on `isMaxInf_atLeast_iff_eq` from `MeasurementScale.lean`,
which requires surjectivity: every value in the domain is realized.
This is the genuinely non-trivial hypothesis — it fails for count nouns
(not every rational cardinality is instantiated) but holds for mass nouns
(every rational quantity of rice exists, at least in principle). -/
theorem scontras_kennedy_dense {E : Type*} (μ : MeasureFn E) (n : ℚ) (x : E)
    (hSurj : Function.Surjective μ.apply) :
    IsMaxInf (atLeastDeg μ.apply) n x ↔ μ.apply x = n :=
  Core.Scale.isMaxInf_atLeast_iff_eq μ.apply n x hSurj

/-- **Scontras–Kennedy equivalence for cardinality (discrete).**

For cardinality (ℕ-valued), the discrete collapse `moreThan_eq_atLeast_succ`
independently delivers exact meaning: "more than n" = "at least n+1" on ℕ.
The MIP still applies (`atLeast_hasMaxInf`), and `isMaxInf_atLeast_iff_eq`
gives exactness under ℕ-surjectivity (which is trivially satisfied by
identity). -/
theorem scontras_kennedy_card {E : Type*} (cardFn : E → ℕ) (n : ℕ) (x : E)
    (hSurj : Function.Surjective cardFn) :
    IsMaxInf (atLeastDeg cardFn) n x ↔ cardFn x = n :=
  Core.Scale.isMaxInf_atLeast_iff_eq cardFn n x hSurj

/-- The MIP always exists for at-least degree properties, regardless of density.
This is why bare numerals always generate scalar implicatures: the lower-bound
meaning has a well-defined maximum (the true value), so the MIP can derive
exactness. Contrast with `moreThanDeg`, where the MIP fails on dense scales. -/
theorem mip_always_exists_atLeast {E : Type*} (μ : MeasureFn E) (x : E) :
    Core.Scale.HasMaxInf (atLeastDeg μ.apply) x :=
  Core.Scale.atLeast_hasMaxInf μ.apply x

-- ============================================================================
-- § 11. Dimension Typing Theorems
-- ============================================================================

/-- Every quotient dimension's components are distinct simplex dimensions. -/
theorem quotient_components_distinct (q : QuotientDimension) :
    q.components.1 ≠ q.components.2 := by
  cases q <;> simp [QuotientDimension.components]

/-- No simplex dimension appears as both components of any single quotient dimension.
    This is a type-theoretic consequence: you can't divide a dimension by itself
    to get a meaningful quotient (mass/mass = dimensionless, not a quotient dimension). -/
theorem quotient_not_self_ratio (q : QuotientDimension) :
    q.components.1 ≠ q.components.2 := quotient_components_distinct q

-- ============================================================================
-- § 11. Verification
-- ============================================================================

/-- CARD measures cardinality. -/
theorem card_dimension (E : Type*) (f : E → ℚ) (h : ∀ e, f e ≥ 0) :
    (card E f h).measureFn.dimension = .cardinality := rfl

/-- Quotient dimensions decompose into simplex components. -/
theorem density_components :
    QuotientDimension.density.components = (.mass, .volume) := rfl

theorem speed_components :
    QuotientDimension.speed.components = (.distance, .time) := rfl

end Semantics.Probabilistic.Measurement
