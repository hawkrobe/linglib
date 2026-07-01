import Mathlib.Order.Basic
import Linglib.Core.Order.Boundedness
import Linglib.Core.Order.ComparativeScale
import Linglib.Semantics.Degree.Predicate

/-!
# Directed measurement primitive
[kennedy-2007] [kennedy-2015] [lassiter-goodman-2017] [krantz-1971]

A `DirectedMeasure D E` packages a degree type, entity type, measure function,
boundedness classification, and direction. The common algebraic core of the
degree-domain constructors and epistemic threshold semantics.

## Main declarations

- `DirectedMeasure`: the bundled measure structure.
- `DirectedMeasure.IsLicensed`: endpoint-based licensing via `Boundedness.IsLicensed`.
- `DirectedMeasure.degreeProperty`: the degree property derived from
  `direction` (`Comparison.ge.over` positive, `Comparison.le.over` negative); its
  maximal informativity is characterized in `Semantics/Entailment/Extremum.lean`.
- `DirectedMeasure.numeral`, `DirectedMeasure.adjective`: Kennedy-style
  numeral and gradable-adjective domains.

## Scale types as Mathlib typeclass combinations

For **theorems about concrete scales** — proving facts about a particular
type — use Mathlib typeclasses directly:

- **Measurement scale**: `[LinearOrder α]`
- **Dense measurement scale** ([fox-2007] UDM): `[LinearOrder α] [DenselyOrdered α]`
- **Upper-bounded scale**: `[LinearOrder α] [OrderTop α]`
- **Lower-bounded scale**: `[LinearOrder α] [OrderBot α]`
- **Open scale**: `[LinearOrder α] [NoMaxOrder α] [NoMinOrder α]`

For **lexical-data tagging**, use the `Boundedness` enum from `Defs.lean`.
Mathlib typeclass instances cannot be stored in record fields; the enum
and the typeclass system serve different roles and both are real.
-/

namespace Degree

open Core.Order

/-! ### DirectedMeasure -/

/-- A directed measurement on a bounded scale: a degree type `D` (the scale),
    an entity type `E`, a measure function `μ : E → D`, boundedness
    (from `ComparativeScale`), and a direction.

    Common algebraic core of the `numeral`/`adjective` domain constructors and
    epistemic thresholds (`epistemicAsDirectedMeasure`, on
    `DirectedMeasure ℚ (E × (W → Bool))`). The degree property
    (`Comparison.ge.over` for positive, `Comparison.le.over` for negative) is
    derived from `direction`, not stored — per [lassiter-goodman-2017], the
    binary direction choice is the fundamental parameter. -/
structure DirectedMeasure (D : Type*) [LinearOrder D] (E : Type*) extends ComparativeScale D where
  /-- Measure function: maps entities to degrees on the scale -/
  μ : E → D
  /-- Scale direction: positive (μ(x) ≥ θ) or negative (μ(x) ≤ θ).
      Determines which side of a threshold counts as satisfying the
      predicate. Positive: tall, likely, full. Negative: short,
      unlikely, empty. -/
  direction : ScalePolarity := .positive

namespace DirectedMeasure

variable {D : Type*} [LinearOrder D] {E : Type*}

/-- Licensing: licensed iff the bounded scale admits an optimum.
    See `Boundedness.IsLicensed` for the caveat — this checks
    "any endpoint exists", not [kennedy-2007]'s full
    modifier-class licensing matrix. -/
def IsLicensed (dm : DirectedMeasure D E) : Prop := dm.boundedness.IsLicensed

instance (dm : DirectedMeasure D E) : Decidable dm.IsLicensed :=
  inferInstanceAs (Decidable dm.boundedness.IsLicensed)

/-- The degree property derived from the measure's direction: `Comparison.ge.over`
    for positive scales (tall, likely), `Comparison.le.over` for negative ones
    (short, unlikely). The derivation the structure docstring promises:
    `direction` is the stored parameter, the property follows. -/
def degreeProperty (dm : DirectedMeasure D E) : D → Set E :=
  match dm.direction with
  | .positive => Comparison.ge.over dm.μ
  | .negative => Comparison.le.over dm.μ

end DirectedMeasure

/-! ### Numeral and adjective domains

Constructors for [kennedy-2015]'s numeral domains (de-Fregean type-shift
over cardinality) and [kennedy-2007]'s gradable-adjective domains. The
licensing theorems below only pin the `Boundedness → licensed` map; the
substantive maximal-informativity results (exactness of the maximally
informative degree) live in `Semantics/Entailment/Extremum.lean`
(`isMaxInf_atLeast_iff_eq`, `isMaxInf_atMost_iff_eq`) and are discharged
over real numeral meanings in `Studies/FoxHackl2006Numerals.lean`. -/

namespace DirectedMeasure

variable {α : Type*} [LinearOrder α] {W : Type*}

/-- [kennedy-2015] numeral domain: "at least n" over cardinality.
    Closed scale (ℕ well-ordered) → always licensed.
    Type-shift to exact = MIP applied to `Comparison.ge.over`. -/
def numeral (μ : W → α) : DirectedMeasure α W :=
  { boundedness := .closed, μ := μ }

/-- [kennedy-2007] gradable adjective domain.
    Boundedness varies by adjective class (tall: open, full: closed). -/
def adjective (μ : W → α) (b : Boundedness) : DirectedMeasure α W :=
  { boundedness := b, μ := μ }

/-! ### Licensing theorems -/

/-- Numeral domains are always licensed (closed scale). -/
theorem numeral_licensed (μ : W → α) :
    (numeral μ).IsLicensed := trivial

/-- Class B adjectives (closed scale) are licensed. -/
theorem classB_licensed (μ : W → α) :
    (adjective μ .closed).IsLicensed := trivial

/-- Class A adjectives (open scale) are blocked. -/
theorem classA_blocked (μ : W → α) :
    ¬ (adjective μ .open_).IsLicensed := id

end DirectedMeasure

end Degree
