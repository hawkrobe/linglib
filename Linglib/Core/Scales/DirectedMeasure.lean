import Mathlib.Order.Basic
import Linglib.Core.Scales.Defs
import Linglib.Core.Scales.Comparative

/-!
# Core/Scales/DirectedMeasure.lean — directed measurement primitive
[kennedy-2007] [lassiter-goodman-2017] [rouillard-2026] [krantz-1971] [krifka-1989] [zwarts-2005]

A `DirectedMeasure D E` packages a degree type, entity type, measure function,
boundedness classification, and direction. The common algebraic core of
`GradablePredicate`, MIP domain constructors, and epistemic threshold semantics.

The MIP domain framework operators (`numeral`, `adjective`,
`rouillardETIA`, `rouillardGTIA`) currently live in this file. Per master
plan v4 Phase B, these will move to `Semantics/Gradability/{Kennedy,Rouillard}.lean`.

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).

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

namespace Core.Scale

-- ════════════════════════════════════════════════════
-- § 1e. Directed Measure (Root Algebraic Primitive)
-- ════════════════════════════════════════════════════

/-- A directed measurement on a bounded scale: the algebraic primitive
    underlying degree semantics, modal semantics, and epistemic scales.

    A `DirectedMeasure D E` packages:
    - A degree type `D` with a linear order (the scale)
    - An entity type `E` (what gets measured)
    - A measure function `μ : E → D` (the measurement)
    - Boundedness classification (from `ComparativeScale`)
    - A direction/polarity (positive or negative)

    This is the common algebraic core of `GradablePredicate` (degree
    semantics), MIP domain constructors (maximal informativity), and
    `epistemicAsGradable` (epistemic threshold semantics). Each of
    these extends or instantiates `DirectedMeasure`:

    - `GradablePredicate E D` extends `DirectedMeasure D E` with `form`
    - `numeral`, `rouillardETIA`, etc. produce `DirectedMeasure` instances
    - Epistemic vocabulary: `DirectedMeasure ℚ (E × (W → Prop))`

    The degree property (`atLeastDeg` for positive, `atMostDeg` for
    negative) is **derived** from direction, not stored. This captures
    the insight from [lassiter-goodman-2017] that the binary direction choice
    (which side of the threshold counts as "satisfying the predicate")
    is the fundamental parameter, and the degree property follows.

    References:
    - Kennedy, C. (2007). Vagueness and grammar.
    - Lassiter, D. (2017). Graded modality. OUP.
    - Rouillard, V. (2026). Maximal informativity and temporal in-adverbials.
    - Krantz, D. et al. (1971). Foundations of measurement, Vol. 1. -/
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
    See `Boundedness.isLicensed` for the caveat — this checks
    "any endpoint exists", not [kennedy-2007]'s full
    modifier-class licensing matrix. -/
def licensed (dm : DirectedMeasure D E) : Bool := dm.boundedness.isLicensed

end DirectedMeasure

-- ════════════════════════════════════════════════════
-- § 8. MIP Domain: Kennedy–Rouillard Unification
-- ════════════════════════════════════════════════════

/-! ### The Maximal Informativity Principle as a universal mechanism

[kennedy-2015] proposes a de-Fregean type-shift that maps lower-bound numeral
meanings to exact meanings for Class B items (closed scales). [rouillard-2026]
proposes the MIP as the licensing condition for temporal *in*-adverbials.

These are the SAME mechanism: given a measure function μ and a monotone degree
property P, the maximally informative value is always μ(w) — the true value.
The MIP derives exactness from monotone degree properties regardless of domain:

| Domain              | μ             | Degree prop  | Direction | MIP result    |
|---------------------|---------------|-------------|-----------|---------------|
| Kennedy numerals    | cardinality   | atLeastDeg  | down mono | max⊨ = μ(w)  |
| Kennedy adjectives  | degree        | atLeastDeg  | down mono | max⊨ = μ(w)  |
| Rouillard E-TIAs   | runtime       | atMostDeg   | up mono   | max⊨ = μ(w)  |

The `isMaxInf_atLeast_iff_eq` and `isMaxInf_atMost_iff_eq` theorems prove this
for both monotonicity directions. The Kennedy type-shift is not a separate
mechanism — it IS the MIP applied to "at least n".

Per master plan v4, these MIP-domain operators (numeral, adjective,
rouillardETIA, rouillardGTIA) are scheduled to move to
`Semantics/Gradability/{Kennedy,Rouillard}.lean` in Phase B. -/

namespace DirectedMeasure

-- ── MIP Domain Constructors ────────────────────────

variable {α : Type*} [LinearOrder α] {W : Type*}

/-- [kennedy-2015] numeral domain: "at least n" over cardinality.
    Closed scale (ℕ well-ordered) → always licensed.
    Type-shift to exact = MIP applied to atLeastDeg. -/
def numeral (μ : W → α) : DirectedMeasure α W :=
  { boundedness := .closed, μ := μ }

/-- [kennedy-2007] gradable adjective domain.
    Boundedness varies by adjective class (tall: open, full: closed). -/
def adjective (μ : W → α) (b : Boundedness) : DirectedMeasure α W :=
  { boundedness := b, μ := μ }

-- ── Licensing Theorems ──────────────────────────────

/-- Numeral domains are always licensed (closed scale). -/
theorem numeral_licensed (μ : W → α) :
    (numeral μ).licensed = true := rfl

/-- Class B adjectives (closed scale) are licensed. -/
theorem classB_licensed (μ : W → α) :
    (adjective μ .closed).licensed = true := rfl

/-- Class A adjectives (open scale) are blocked. -/
theorem classA_blocked (μ : W → α) :
    (adjective μ .open_).licensed = false := rfl

end DirectedMeasure

/-! Rouillard 2026's E-TIA / G-TIA MIP-domain operators (negative direction)
    have moved to `Semantics/Gradability/MaximalInformativity.lean`
    per master plan v4 Phase B (idea-named: `etia`/`gtia`). The
    cross-framework licensing equivalence theorems also live there. -/

end Core.Scale
