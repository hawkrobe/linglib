import Linglib.Semantics.Mereology
import Linglib.Core.Order.Comparison
import Linglib.Semantics.Degree.HasMeasure
import Linglib.Semantics.Degree.Predicate
import Linglib.Semantics.Entailment.Extremum
import Linglib.Features.Dimension

/-!
# Measurement Semantics
[bale-schwarz-2026] [kennedy-2015] [krifka-1989] [scontras-2014] [zabbal-2005]

Formal semantics of measurement: measure functions, the bridge to bare numerals
via CARD, the quantity-uniform property, and the connection to existing
degree-semantics infrastructure.

## Theoretical Foundation

[scontras-2014]'s *The Semantics of Measurement* (Ch. 2) aligns measure
terms (kilo, liter) with the Num-head CARD, treating both as instances of a
single category M. The CARD primitive originates with [zabbal-2005]; its
relational shape (numerals as relations between numbers and individuals) follows
[krifka-1989]. Scontras's contribution is the unification: CARD and kilo
share the type signature of a measure term, and number marking on basic nouns
(`one boy` vs. `two boys`) is the same operation as number marking on measure
terms (`one kilo` vs. `two kilos`).

### Measure Functions

A **measure function** μ maps individuals to non-negative rationals along a
specific physical dimension:

    μ : Entity → ℚ≥0

The dimension tag (mass, volume, distance, time, cardinality, ...) lives in
`Features/Dimension.lean`; this module imports it and exposes `MeasureFn`,
which carries the tag plus the underlying `apply` function.

### Measure Terms

A measure term (gram, liter, mile) **names** a specific measure function.
Its (intransitive) denotation in [scontras-2014], eq. (33):

    ⟦kilo⟧ = λn. λx. μ_kg(x) = n

This is a function from a numeral to a predicate — a modifier of type
⟨n, ⟨e,t⟩⟩. The Lean encoding is `MeasureFn.applyNumeral`.

### CARD

Scontras (eqs. (23) / (36)) gives CARD the parallel form

    ⟦CARD⟧ = λP. λn. λx. P(x) ∧ μ_CARD(x) = n

so a bare numeral phrase composes with a kind-denoting noun via CARD,
yielding a predicate restricted to individuals of the appropriate
cardinality. The point of the alignment is that the same #-head machinery
governs both `one boy` (via CARD + μ_CARD) and `one kilo of apples`
(via μ_kg). Here we expose `μ_CARD` as a `MeasureFn` (`cardMeasure`); the
CARD Num-head itself lives at the syntactic level.

### Connection to Scale Infrastructure

The `HasMeasure` (legacy `HasMeasure`) typeclass in `Core/Scales/HasMeasure.lean`
gives `E → α`. This module adds:

- typed dimensions (what μ measures), via `Features.Dimension.Dimension`
- multiple measure functions per entity (a box has weight AND volume AND
  cardinality — `MeasureFn` is not a typeclass)
- the quantity-uniform property (Scontras's QU_μ, eq. (44) p. 43)

## Connection to [bale-schwarz-2026]

`Features/Dimension.lean` provides the typed-dimension substrate
(`Dimension`, `QuotientDimension`, `DimensionType`) used by
`Studies/BaleSchwarz2026.lean` to formulate the No Division Hypothesis
(eq. (5), p. 135): "Quantity division is not available as an operation for
semantic composition." The hypothesis itself is stated and applied in the
consuming Studies file, not here.

-/

namespace Semantics.Measurement

open Features.Dimension (Dimension)

-- ============================================================================
-- § 1. Measure Functions
-- ============================================================================

/-- A measure function maps entities to non-negative rational magnitudes
along a specific dimension.

[scontras-2014]: degrees are pairs ⟨μ, n⟩ where μ is the measure
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

-- ============================================================================
-- § 2. Measure-Term Application
-- ============================================================================

/-- Apply a measure function to a numeral n, yielding a predicate over entities:

    ⟦kilo⟧(3) = λx. μ_kg(x) = 3

[scontras-2014]: measure terms are nouns that name specific measure
functions. Their type is ⟨n, ⟨e,t⟩⟩ — they take a numeral and return a
predicate. This is the **exact (`=`) case of the shared comparison-over-a-
measure primitive** `Core.Order.Comparison.over`: `⟦kilo⟧(n)` is
`Comparison.eq.over μ_kg n`. Modified readings (`> n`, `≥ n`, …) are the other
`Comparison`s over the same `μ`. -/
def MeasureFn.applyNumeral {E : Type*} (μ : MeasureFn E) (n : ℚ) (x : E) : Prop :=
  x ∈ Core.Order.Comparison.eq.over μ.apply n

/-- `applyNumeral` is exact measure predication: `μ(x) = n` (definitionally,
    the `.eq` interval-membership). -/
@[simp] theorem MeasureFn.applyNumeral_iff {E : Type*} (μ : MeasureFn E) (n : ℚ) (x : E) :
    μ.applyNumeral n x ↔ μ.apply x = n := Iff.rfl

instance {E : Type*} (μ : MeasureFn E) (n : ℚ) (x : E) :
    Decidable (μ.applyNumeral n x) :=
  inferInstanceAs (Decidable (μ.apply x = n))

-- ============================================================================
-- § 3. CARD: Cardinality as a Measure Function
-- ============================================================================

/-- The cardinality measure: μ_CARD x = |x|.

The CARD Num-head originates with [zabbal-2005]; its relational shape
(numerals as relations between numbers and individuals) follows
[krifka-1989]. [scontras-2014] (eqs. (23), (36)) gives CARD the form

    ⟦CARD⟧ = λP. λn. λx. P(x) ∧ μ_CARD(x) = n

aligning it with measure terms whose intransitive form (eq. (33)) is
⟦kilo⟧ = λn. λx. μ_kg(x) = n. This file exposes the underlying μ_CARD as
a `MeasureFn`; the CARD Num-head itself (which composes with a kind) lives
at the syntactic level. -/
def cardMeasure (E : Type*) (cardFn : E → ℚ) (h : ∀ e, cardFn e ≥ 0) : MeasureFn E :=
  { dimension := .cardinality, apply := cardFn, nonneg := h }

-- ============================================================================
-- § 4. Quantity-Uniform Property
-- ============================================================================

/-- A predicate P is **quantity-uniform** with respect to measure function μ
([scontras-2014], eq. (44), p. 43; restated as eq. (53), p. 48):

    QU_μ(P) ↔ ∀ x y, P(x) ∧ P(y) → μ(x) = μ(y)

Every individual in P's denotation evaluates to the same μ-value. This is
a uniformity condition on the predicate, NOT closure under sum (a different
condition closer to Krifka's cumulativity). The MP `one CARD boy` is QU
under μ_CARD because every member denotes a single boy; `one kilo of apples`
is QU under μ_kg because every member weighs 1 kg.

The role in Scontras's account: `⟦SG⟧` checks that the modified predicate
is QU under some relevant μ, with that μ supplying the "1-ness" presupposition
of singular morphology (eq. (54), p. 48). Predicates fail QU when they are
not measure-modified — e.g. bare `boy` is not QU under μ_CARD because two
distinct boys can have different cardinalities (one vs. plural). -/
def IsQuantityUniform {E : Type*} (P : E → Prop) (μ : MeasureFn E) : Prop :=
  ∀ x y, P x → P y → μ.apply x = μ.apply y

-- ============================================================================
-- § 5. Bridge to HasMeasure
-- ============================================================================

/-- A `MeasureFn` induces a `HasMeasure` instance: the degree of an entity
is its measure value.

Note: `HasMeasure` (= `HasMeasure`) is a typeclass with one designated degree
per (entity, codomain) pair. For entities with multiple measurable dimensions,
use `MeasureFn` directly — the typeclass projection is the specialization for
when a single dimension is contextually salient. -/
@[reducible]
def MeasureFn.toHasDegree {E : Type*} (μ : MeasureFn E) : Degree.HasMeasure E ℚ :=
  { degree := μ.apply }

-- ============================================================================
-- § 6. Quantizing Nouns ([scontras-2014], Ch. 3)
-- ============================================================================

/-- Classification of quantizing nouns (Scontras Ch. 3): nouns that turn
substance terms into countable expressions.

[scontras-2014] identifies three classes via Rothstein-style
diagnostics (Table 3.5, p. 89):

- **Measure terms** (kilo, liter): name a measure function directly;
  always license a MEASURE reading.
- **Container nouns** (glass, box): non-relational predicates with a
  CONTAINER reading by default but ambiguous toward MEASURE when the
  container's volume can serve as a measure unit.
- **Atomizers** (grain, drop, piece): relational, partitioning nouns
  (eqs. (77), (87)) that impose a partition into self-connected atoms
  via π; they are *counted* (by CARD over the partition), not measured. -/
inductive QuantizingNounClass where
  | measureTerm    -- kilo, liter, meter
  | containerNoun  -- glass, box, cup
  | atomizer       -- grain, piece, drop
  deriving Repr, DecidableEq

/-- Container nouns are ambiguous between two readings (Scontras Ch. 3 §3.2):

- **CONTAINER**: the noun denotes physical containers; "three glasses of water"
  refers to three individual glasses containing water.

- **MEASURE**: the noun functions as a measure term; "three glasses of water"
  refers to a quantity of water whose volume equals three glass-volumes. -/
inductive ContainerReading where
  | container
  | measure
  deriving Repr, DecidableEq

/-- Whether a class/reading combination licenses a MEASURE reading (Scontras
Ch. 3, Table 3.5 p. 89).

| Class         | Reading         | MEASURE? | Reason                            |
|---------------|-----------------|----------|-----------------------------------|
| measureTerm   | (n/a)           | true     | Names a measure function directly |
| containerNoun |.measure        | true     | Container's volume = measure unit |
| containerNoun |.container/none | false    | Individuated containers           |
| atomizer      | (n/a)           | false    | Atomizers resist MEASURE (Ch. 3.3)|

The original framing of this table as a "QU prediction" was misleading.
Atomizers fail to license a MEASURE reading because their semantics is
inherently relational and partitioning (Scontras eqs. (77)/(87), pp. 89-90),
not measure-naming — they don't supply a measure function; instead they
take a substance noun and impose a partition into self-connected atoms.
The resulting predicates, after partitioning by π, are then counted by
CARD (Scontras p. 100: atomizers are nominal and get counted by CARD-formed
cardinals just like basic nouns). What's predicted here is MEASURE
licensing, not QU-status under all conceivable μ. -/
def licensesMeasureReading :
    QuantizingNounClass → Option ContainerReading → Prop
  | .measureTerm,   _                 => True
  | .containerNoun, some .measure     => True
  | .containerNoun, some .container   => False
  | .containerNoun, none              => False
  | .atomizer,      _                 => False

instance : ∀ (cls : QuantizingNounClass) (r : Option ContainerReading),
    Decidable (licensesMeasureReading cls r)
  | .measureTerm,   _                 => isTrue trivial
  | .containerNoun, some .measure     => isTrue trivial
  | .containerNoun, some .container   => isFalse id
  | .containerNoun, none              => isFalse id
  | .atomizer,      _                 => isFalse id

/-- Measure terms always license a MEASURE reading. -/
theorem measureTerm_always_licensesMeasure (r : Option ContainerReading) :
    licensesMeasureReading .measureTerm r := by
  cases r <;> trivial

/-- Atomizers never license a MEASURE reading
([scontras-2014] Ch. 3 §3.3, Table 3.5 p. 89). They impose a partition
into atoms (eq. (77)) and are counted by CARD, not measured. -/
theorem atomizer_no_MEASURE_reading (r : Option ContainerReading) :
    ¬ licensesMeasureReading .atomizer r := by
  cases r with
  | none => exact id
  | some r => cases r <;> exact id

/-- Container nouns license a MEASURE reading iff in MEASURE reading. -/
theorem containerNoun_licensesMeasure_iff_measure (r : ContainerReading) :
    licensesMeasureReading .containerNoun (some r) ↔ r = .measure := by
  cases r <;> simp [licensesMeasureReading]

-- ============================================================================
-- § 7. Measure-term exact meaning vs Kennedy's max-quantifier semantics
-- ============================================================================

/-! ### Formalization-internal observation

[scontras-2014]'s measure-term denotation gives exact meaning directly:

    ⟦kilo⟧(n)(x) = (μ_kg(x) = n)               -- eq. (33), p. 37

[kennedy-2015]'s "de-Fregean" analysis gives bare numerals a two-sided
meaning via `max`:

    ⟦three⟧ = λD. max{n | D(n)} = 3            -- eq. (29), p. 15

Kennedy explicitly **rejects** the lower-bound + exhaustification approach
(p. 19-20: the de-Fregean meaning "can only be derived [from a lower-bound
basis] through the addition of some meaning changing operation, such as
exhaustification"). Kennedy's pragmatics for ignorance implicatures with
modified numerals is neo-Gricean Quantity (Sauerland-style primary
implicatures, eq. (43) p. 22), NOT Maximize Informativity.

The two proposals are independent — different empirical domains (measure
terms vs. bare numerals) and different formal mechanisms. They nonetheless
yield equivalent truth conditions for `n μ-units of stuff` whenever n is
realized in the image of μ: under that point-realization condition, the
`max` of the at-least-degree property at n equals the exact-measure
predicate `μ(x) = n`. The theorems below state this equivalence as a
formalization-internal observation; it is not stated in either source paper.

The key infrastructure is `isMaxInf_atLeast_of_hit` in
`Semantics/Entailment/Extremum.lean`, which requires only point-
realization (`∃ e, μ(e) = n`) rather than full surjectivity. Mass nouns
realize every n ∈ ℚ≥0 (rice is uniformly divisible by hypothesis); count
nouns realize only n ∈ ℕ. -/

open Core.Order (Comparison)
open Entailment (IsMaxInf HasMaxInf)

/-- For a measure function μ on ℚ: when n is realized by some entity, the
MIP applied to the at-least degree property at n yields μ(x) = n.

*Formalization-internal observation* — not stated by Scontras or Kennedy.
Bridges Scontras's exact measure-term meaning with the `max{n | ...} = n`
form of Kennedy's de-Fregean analysis. -/
theorem scontras_kennedy_dense {E : Type*} (μ : MeasureFn E) (n : ℚ) (x : E)
    (hHit : ∃ e, μ.apply e = n) :
    IsMaxInf (Comparison.ge.over μ.apply) n x ↔ μ.apply x = n :=
  Entailment.isMaxInf_atLeast_of_hit μ.apply n x hHit

/-- For a cardinality function on ℕ: same point-realization equivalence.
*Formalization-internal observation* — see the prose above. -/
theorem scontras_kennedy_card {E : Type*} (cardFn : E → ℕ) (n : ℕ) (x : E)
    (hHit : ∃ e, cardFn e = n) :
    IsMaxInf (Comparison.ge.over cardFn) n x ↔ cardFn x = n :=
  Entailment.isMaxInf_atLeast_of_hit cardFn n x hHit

-- ============================================================================
-- § 8. Bridges to Mereology (Krifka) and admissibleMeasure (Wellwood)
-- ============================================================================

/-! `MeasureFn` is the concrete Scontras-flavored substrate (a function plus a
typed dimension and a non-negativity proof). The abstract characterizations
elsewhere in linglib — Krifka extensivity (`Mereology.ExtMeasure`),
Wellwood admissibility (`StrictMono` / `admissibleMeasure`) — are properties
that a `MeasureFn` may carry. The bridges below let consumers move between
the concrete and abstract views without re-stipulation. -/

/-- A `MeasureFn` is **extensive** in the [krifka-1998] sense (additive
over non-overlapping entities, positive, strictly monotone over the part-whole
order; the formalism traces to [krifka-1989]'s cumulative/quantized
distinction). Definitionally `Mereology.ExtMeasure E μ.apply`; declared as
`abbrev` so the underlying class instance elaborates through it without manual
unfolding. -/
abbrev MeasureFn.IsExtensive {E : Type*} [SemilatticeSup E]
    (μ : MeasureFn E) : Prop :=
  Mereology.ExtMeasure E μ.apply

/-- A `MeasureFn` is **admissible** (in [wellwood-2015]'s /
[schwarzschild-2006]'s Monotonicity Constraint sense) iff its underlying
function is `StrictMono` on the part-whole order. Definitionally equal to
`Semantics.Gradability.StatesBased.admissibleMeasure μ.apply` — both are
`StrictMono μ.apply` — so consumers can prove the equivalence by `Iff.rfl`
when both abbrevs are in scope. -/
abbrev MeasureFn.IsAdmissible {E : Type*} [Preorder E]
    (μ : MeasureFn E) : Prop :=
  StrictMono μ.apply

/-- **Scontras-Krifka bridge.** When a `MeasureFn` is extensive, applying
[krifka-1989]'s QMOD with that measure function at any positive value
produces a QUA predicate. Measure terms ("three kilos of rice") yield
quantized predicates because their measure function is extensive. -/
theorem extensive_measureFn_qmod_qua
    {E : Type*} [inst : SemilatticeSup E]
    {μ : MeasureFn E}
    (hExt : MeasureFn.IsExtensive μ)
    {R : E → Prop} {n : ℚ} (_hn : 0 < n) :
    Mereology.QUA (Mereology.QMOD R μ.apply n) := by
  haveI : @Mereology.ExtMeasure E inst μ.apply := hExt
  exact Mereology.qmod_qua R n

/-- **Bridge to QMOD.** Scontras's `applyNumeral` and Krifka's `QMOD` check the
same condition `μ(x) = n` when QMOD's restrictor is taken to be trivial. -/
theorem MeasureFn.applyNumeral_iff_qmod {E : Type*}
    (μ : MeasureFn E) (n : ℚ) (x : E) :
    μ.applyNumeral n x ↔ Mereology.QMOD (fun _ => True) μ.apply n x := by
  simp [MeasureFn.applyNumeral_iff, Mereology.QMOD]

end Semantics.Measurement
