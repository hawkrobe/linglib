module

public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Degree.Measure.Basic
public import Linglib.Semantics.Degree.Predicate
public import Linglib.Semantics.Alternatives.Extremum
public import Linglib.Semantics.Degree.Measure.Dimension

/-!
# Dimensioned measure functions

A measure function maps entities to magnitudes on a scale `D` along a dimension such as mass,
volume or cardinality, and a measure term names one: `⟦kilo⟧ = λn. λx. μ_kg(x) = n`. Scontras
aligns measure terms with the number head CARD, which counts with the cardinality measure, and
lets singular morphology check that the predicate it modifies is quantity-uniform under some
measure. Krifka's extensive measures and Wellwood's admissible measures are properties of a
measure's function; over parts with remainders, extensive measures are admissible.

## Main definitions

* `DimensionedMeasure`: a measure function tagged with its dimension.
* `DimensionedMeasure.applyNumeral`: the predicate a measure term denotes at a numeral.
* `cardMeasure`: the cardinality measure behind CARD.
* `IsQuantityUniform`: predicates whose members all have the same measure.
* `QuantizingNounClass`, `licensesMeasureReading`: measure terms, container nouns and atomizers.
* `DimensionedMeasure.IsExtensive`, `DimensionedMeasure.IsAdmissible`: extensive and admissible
  measures.

## Main results

* `DimensionedMeasure.IsExtensive.isAdmissible`: extensive measures are admissible over parts
  with remainders, so the measure phrases they build are quantized
  (`DimensionedMeasure.IsAdmissible.qmod_qua`).
* `scontras_kennedy_dense`, `scontras_kennedy_card`: at a measured value, Kennedy's maximality
  reading of a numeral agrees with exact measure predication.

## References

* [scontras-2014], [zabbal-2005], [kennedy-2015], [krifka-1989], [krifka-1998],
  [wellwood-2015], [schwarzschild-2006]
-/

@[expose] public section

namespace Degree

/-! ### Measure Functions -/

/-- A measure function maps entities to magnitudes on the scale `D` along a
specific dimension.

Following [scontras-2014], degrees are pairs ⟨μ, n⟩ where μ is the measure
function and n is the numerical value. A measure function is individuated
by its dimension, so μ_kg measures mass, μ_L measures volume, and μ_CARD counts.
Non-negativity and additivity are properties of a measure
(`DimensionedMeasure.IsExtensive`), not fields; studies that compute
instantiate the scale at `ℚ`. -/
structure DimensionedMeasure (E : Type*) (D : Type := ℝ) where
  /-- Which dimension this function measures. -/
  dimension : Dimension
  /-- The function sends an entity to its magnitude. -/
  apply : E → D

variable {D : Type}

/-- A dimensioned measure coerces to its function. -/
instance {E : Type*} : CoeFun (DimensionedMeasure E D) (fun _ => E → D) where
  coe μ := μ.apply

/-! ### Measure-Term Application -/

/-- A measure term applied to a numeral `n` denotes the entities of measure `n`, as in

    ⟦kilo⟧(3) = λx. μ_kg(x) = 3

For [scontras-2014], measure terms are nouns that name specific measure
functions. Their type is ⟨n, ⟨e,t⟩⟩ — they take a numeral and return a
predicate. It is the exact case of the comparison over a measure `Degree.Comparison.over`, so
`⟦kilo⟧(n)` is `Comparison.eq.over μ_kg n`. Modified readings (`> n`, `≥ n`, …) are the other
`Comparison`s over the same `μ`. -/
def DimensionedMeasure.applyNumeral {E : Type*} [Preorder D] (μ : DimensionedMeasure E D) (n : D)
    (x : E) : Prop :=
  x ∈ Degree.Comparison.eq.over μ.apply n

/-- A measure term predicates exact measure, `μ(x) = n`. -/
@[simp] theorem DimensionedMeasure.applyNumeral_iff {E : Type*} [Preorder D]
    (μ : DimensionedMeasure E D) (n : D) (x : E) :
    μ.applyNumeral n x ↔ μ.apply x = n := Iff.rfl

instance {E : Type*} [Preorder D] [DecidableEq D] (μ : DimensionedMeasure E D) (n : D) (x : E) :
    Decidable (μ.applyNumeral n x) :=
  inferInstanceAs (Decidable (μ.apply x = n))

/-! ### CARD: Cardinality as a Measure Function -/

/-- The cardinality measure `μ_CARD` sends an entity to its cardinality.

The CARD Num-head originates with [zabbal-2005]; its relational shape
(numerals as relations between numbers and individuals) follows
[krifka-1989]. [scontras-2014] (eqs. (23), (36)) gives CARD the form

    ⟦CARD⟧ = λP. λn. λx. P(x) ∧ μ_CARD(x) = n

aligning it with measure terms whose intransitive form (eq. (33)) is
⟦kilo⟧ = λn. λx. μ_kg(x) = n. This file exposes the underlying μ_CARD as
a `DimensionedMeasure`; the CARD Num-head itself (which composes with a kind) lives
at the syntactic level. -/
def cardMeasure (E : Type*) [NatCast D] (cardFn : E → ℕ) : DimensionedMeasure E D :=
  { dimension := .cardinality, apply := fun e => (cardFn e : D) }

/-! ### Quantity-Uniform Property -/

/-- A predicate `P` is quantity-uniform with respect to a measure function `μ`
([scontras-2014], eq. (44), p. 43; restated as eq. (53), p. 48) if every individual in its
denotation has the same `μ`-value, `QU_μ(P) ↔ ∀ x y, P(x) ∧ P(y) → μ(x) = μ(y)`. This is
a uniformity condition on the predicate, NOT closure under sum (a different
condition closer to Krifka's cumulativity). The MP `one CARD boy` is QU
under μ_CARD because every member denotes a single boy; `one kilo of apples`
is QU under μ_kg because every member weighs 1 kg.

In Scontras's account `⟦SG⟧` checks that the modified predicate
is QU under some relevant μ, with that μ supplying the "1-ness" presupposition
of singular morphology (eq. (54), p. 48). Predicates fail QU when they are
not measure-modified — e.g. bare `boy` is not QU under μ_CARD because two
distinct boys can have different cardinalities (one vs. plural). -/
def IsQuantityUniform {E : Type*} (P : E → Prop) (μ : DimensionedMeasure E D) : Prop :=
  ∀ x y, P x → P y → μ.apply x = μ.apply y

/-! ### Quantizing Nouns ([scontras-2014], Ch. 3) -/

/-- Quantizing nouns turn substance terms into countable expressions. [scontras-2014]
(Ch. 3) identifies three classes with Rothstein-style diagnostics (Table 3.5, p. 89).
Measure terms (kilo, liter) name a measure function directly and always license a MEASURE
reading. Container nouns (glass, box) are non-relational predicates with a CONTAINER reading by
default, ambiguous toward MEASURE when the container's volume can serve as a measure unit.
Atomizers (grain, drop, piece) are relational, partitioning nouns (eqs. (77), (87)) that impose a
partition into self-connected atoms via π, and they are counted by CARD over the partition, not
measured. -/
inductive QuantizingNounClass where
  | measureTerm    -- kilo, liter, meter
  | containerNoun  -- glass, box, cup
  | atomizer       -- grain, piece, drop
  deriving Repr, DecidableEq

/-- Container nouns are ambiguous between two readings (Scontras Ch. 3 §3.2). On the CONTAINER
reading the noun denotes physical containers, so "three glasses of water" refers to three glasses
containing water; on the MEASURE reading it functions as a measure term, so the phrase refers to
a quantity of water whose volume equals three glass-volumes. -/
inductive ContainerReading where
  | container
  | measure
  deriving Repr, DecidableEq

/-- `licensesMeasureReading c r` holds when a noun of class `c` on reading `r` has a MEASURE
reading ([scontras-2014], Ch. 3, Table 3.5 p. 89).

| Class         | Reading         | MEASURE? | Reason                            |
|---------------|-----------------|----------|-----------------------------------|
| measureTerm   | (n/a)           | true     | Names a measure function directly |
| containerNoun |.measure        | true     | Container's volume = measure unit |
| containerNoun |.container/none | false    | Individuated containers           |
| atomizer      | (n/a)           | false    | Atomizers resist MEASURE (Ch. 3.3)|

Atomizers fail to license a MEASURE reading because their semantics is
inherently relational and partitioning (Scontras eqs. (77)/(87), pp. 89-90),
not measure-naming — they don't supply a measure function; instead they
take a substance noun and impose a partition into self-connected atoms.
The resulting predicates, after partitioning by π, are then counted by
CARD, since atomizers are nominal and are counted by CARD-formed cardinals just like
basic nouns (Scontras p. 100). What's predicted here is MEASURE
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

/-! ### Measure-term exact meaning vs Kennedy's max-quantifier semantics -/

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

The key infrastructure is `isMaxInf_ge_over_iff` in
`Semantics/Alternatives/Extremum.lean`, which requires only point-
realization (`∃ e, μ(e) = n`) rather than full surjectivity. Mass nouns
realize every n ∈ ℚ≥0 (rice is uniformly divisible by hypothesis); count
nouns realize only n ∈ ℕ. -/

open Alternatives (IsMaxInf)

/-- For a measure function into a linear scale and a value `n` some entity has, the maximality
reading of the at-least degree property at `n` is exact measure `μ(x) = n`. Neither Scontras
nor Kennedy states this. -/
theorem scontras_kennedy_dense {E : Type*} [LinearOrder D] (μ : DimensionedMeasure E D) (n : D)
    (x : E)
    (hHit : ∃ e, μ.apply e = n) :
    IsMaxInf (Comparison.ge.over μ.apply) n x ↔ μ.apply x = n :=
  Alternatives.isMaxInf_ge_over_iff μ.apply x hHit

/-- The same equivalence holds for a cardinality function into `ℕ`. -/
theorem scontras_kennedy_card {E : Type*} (cardFn : E → ℕ) (n : ℕ) (x : E)
    (hHit : ∃ e, cardFn e = n) :
    IsMaxInf (Comparison.ge.over cardFn) n x ↔ cardFn x = n :=
  Alternatives.isMaxInf_ge_over_iff cardFn x hHit

/-! ### Bridges to Mereology (Krifka) and admissibleMeasure (Wellwood) -/

/-! Krifka's extensivity (`Mereology.IsExtensiveMeasure`) and Wellwood's admissibility
(`StrictMono`, `admissibleMeasure`) are properties of a measure's function. -/

/-- A `DimensionedMeasure` is extensive ([krifka-1989], [krifka-1998]) if its function is
additive over non-overlapping entities and positive on non-null ones. -/
abbrev DimensionedMeasure.IsExtensive {E : Type*} [SemilatticeSup E]
    [AddCommMonoid D] [PartialOrder D] (μ : DimensionedMeasure E D) : Prop :=
  Mereology.IsExtensiveMeasure μ.apply

/-- A `DimensionedMeasure` is admissible ([wellwood-2015], [schwarzschild-2006]) if its function
is strictly monotone on the part-whole order. -/
abbrev DimensionedMeasure.IsAdmissible {E : Type*} [Preorder E] [Preorder D]
    (μ : DimensionedMeasure E D) : Prop :=
  admissibleMeasure μ.apply

/-- Over parts with remainders, an extensive measure is admissible. -/
theorem DimensionedMeasure.IsExtensive.isAdmissible {E : Type*} [SemilatticeSup E]
    [Mereology.HasRemainders E] [AddCommMonoid D] [PartialOrder D] [AddLeftStrictMono D]
    {μ : DimensionedMeasure E D} (h : μ.IsExtensive) : μ.IsAdmissible :=
  haveI := h
  Mereology.IsExtensiveMeasure.strictMono μ.apply

/-- A measure phrase on an admissible measure, such as *three kilos of rice*, is quantized. -/
theorem DimensionedMeasure.IsAdmissible.qmod_qua {E : Type*} [PartialOrder E] [PartialOrder D]
    {μ : DimensionedMeasure E D} (h : μ.IsAdmissible) (R : E → Prop) (n : D) :
    Mereology.QUA (Mereology.QMOD R μ.apply n) :=
  Mereology.qmod_qua (StrictMono.strictMonoOn h _) n

/-- A measure term at a numeral is the measure phrase with the trivial restrictor. -/
theorem DimensionedMeasure.applyNumeral_iff_qmod {E : Type*} [Preorder D]
    (μ : DimensionedMeasure E D) (n : D) (x : E) :
    μ.applyNumeral n x ↔ Mereology.QMOD (fun _ => True) μ.apply n x := by
  simp [DimensionedMeasure.applyNumeral_iff, Mereology.QMOD]

end Degree
