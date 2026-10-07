module

public import Mathlib.Basic.Real.Basic
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Degree.Measure.Dimension

/-!
# Dimensioned measure functions

A measure function maps entities to magnitudes on a scale `D` along a dimension such as mass,
volume or cardinality, and a measure term names one: `⟦kilo⟧ = λn. λx. μ_kg(x) = n`. Scontras
lets singular morphology check that the predicate it modifies is quantity-uniform under some
measure, and classifies the nouns that turn substance terms into countable expressions.

## Main definitions

* `DimensionedMeasure`: a measure function tagged with its dimension.
* `DimensionedMeasure.applyNumeral`: the predicate a measure term denotes at a numeral.
* `IsQuantityUniform`: predicates whose members all have the same measure.
* `QuantizingNounClass`: measure terms, container nouns and atomizers.

## References

* [scontras-2014]
-/

@[expose] public section

namespace Degree

/-! ### Measure Functions -/

/-- A measure function maps entities to magnitudes on the scale `D` along a
specific dimension.

Following [scontras-2014], degrees are pairs ⟨μ, n⟩ where μ is the measure
function and n is the numerical value. A measure function is individuated
by its dimension, so μ_kg measures mass, μ_L measures volume, and μ_CARD counts.
Non-negativity and additivity are properties of a measure, not fields;
studies that compute instantiate the scale at `ℚ`. -/
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

end Degree
