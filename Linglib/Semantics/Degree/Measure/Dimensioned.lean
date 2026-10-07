module

public import Mathlib.Basic.Real.Basic
public import Linglib.Semantics.Degree.Measure.Dimension

/-!
# Dimensioned measure functions

A measure function maps entities to magnitudes on a scale `D` along a dimension such as mass,
volume or cardinality, and a measure term names one: `⟦kilo⟧ = λn. λx. μ_kg(x) = n`. Scontras
classifies the nouns that turn substance terms into countable expressions.

## Main definitions

* `DimensionedMeasure`: a measure function tagged with its dimension.
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
  toFun : E → D

variable {D : Type}

/-- A dimensioned measure coerces to its function. -/
instance {E : Type*} : CoeFun (DimensionedMeasure E D) (fun _ => E → D) where
  coe μ := μ.toFun

/-! ### Measure-Term Application -/

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
