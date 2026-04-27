import Linglib.Theories.Semantics.Degree.Abstraction
import Linglib.Theories.Semantics.Comparison.Delineation
import Linglib.Theories.Semantics.Degree.Intervals
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Framework Comparison: Where Kennedy and Heim Diverge
@cite{heim-2001} @cite{kennedy-2007} @cite{klein-1980} @cite{schwarzschild-2008}

Formal comparison of the degree semantic frameworks on shared
empirical ground. By implementing all frameworks with the same type
signatures, we can formally state where they agree and where they diverge.

## Agreement

All degree-based frameworks agree on the truth conditions of simple
comparatives: "A is taller than B" iff μ(A) > μ(B). Klein's degree-free
framework agrees under the natural correspondence between delineation
functions and measure functions.

## Divergences

| Question                    | Kennedy | Heim | Klein | Schwarzschild |
|-----------------------------|---------|------|-------|---------------|
| Degrees in ontology?        | Yes     | Yes  | No    | Yes (intervals)|
| Scope of -er                | DP      | CP   | N/A   | DP            |
| Measure phrases             | Direct  | Direct| Via ≈ | Direct       |
| Subcomparatives             | Special | Special| Special| Natural    |

-/

namespace Phenomena.Comparison.Compare

-- ════════════════════════════════════════════════════
-- § 1. Extensional Equivalence of Degree Frameworks
-- ════════════════════════════════════════════════════

/-- All degree-based frameworks agree on simple comparatives.
    Heim and Schwarzschild (intervals) both yield
    μ(A) > μ(B) for "A is taller than B" — the consensus
    `comparativeSem` at positive direction. -/
theorem heim_agrees {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) :
    Semantics.Degree.Abstraction.heimComparativeWithMeasure μ a b ↔
    Semantics.Degree.Comparative.comparativeSem μ a b .positive := by
  exact Iff.rfl

/-- Schwarzschild's interval comparative also agrees (reduces to point
    comparison on positive intervals). -/
theorem schwarzschild_agrees {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) :
    Semantics.Degree.Intervals.intervalComparative μ a b ↔
    Semantics.Degree.Comparative.comparativeSem μ a b .positive := by
  exact Iff.rfl

-- ════════════════════════════════════════════════════
-- § 2. Scope Divergence: Kennedy vs. Heim
-- ════════════════════════════════════════════════════

/-- Kennedy and Heim diverge on scope predictions. Heim's DegPs take
    scope by QR (like DPs), while Kennedy's `-er` is DP-internal.
    The scope differences are formalized in `Heim2001.lean`:
    - Monotone collapse (∀/∃ + more): `exists_more_scope_collapse`
    - Non-monotone divergence (exactly, less): `nonMonotoneData`
    - Kennedy's generalization: DegP can't cross quantificational DPs
    - Intensional verb scope: `intensionalVerbData` -/
theorem heim_extensional_scope_free {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    Semantics.Degree.Comparative.comparativeSem μ a b .positive =
    Semantics.Degree.Abstraction.heimComparativeWithMeasure μ a b :=
  rfl

-- ════════════════════════════════════════════════════
-- § 3. Klein's Divergence: No Degrees
-- ════════════════════════════════════════════════════

/-- Klein's framework diverges fundamentally: it has no degrees at all.
    We cannot directly compare truth conditions because Klein's
    `comparativeSem` takes a delineation function, not a measure function.

    However, under the natural correspondence — a delineation function
    that classifies entities as "tall in C" when they exceed some
    threshold determined by C — Klein's comparative follows from
    the degree-based analysis. If μ(a) > μ(b), then for the comparison
    class {a, b}, delineating at μ(b) puts a in the positive extension
    but not b. -/
theorem klein_correspondence {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity)
    (delineation : Set Entity → Entity → Prop)
    (hdiscrim : μ a > μ b →
      ∃ C : Set Entity, delineation C a ∧ ¬ delineation C b) :
    Semantics.Degree.Comparative.comparativeSem μ a b .positive →
    Semantics.Comparison.Delineation.comparativeSem delineation a b := by
  exact hdiscrim

/-- **Strengthened Klein correspondence**: degree comparative ↔ Klein's
    ordering via `measureDelineation`. No auxiliary hypotheses beyond
    membership. Uses `ordering_iff_degree` from the theory layer. -/
theorem klein_measure_equivalence {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (cc : Set Entity) (a b : Entity)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    Semantics.Degree.Comparative.comparativeSem μ a b .positive ↔
    Semantics.Comparison.Delineation.ordering
      (Semantics.Comparison.Delineation.measureDelineation μ) cc a b := by
  simp only [Semantics.Degree.Comparative.comparativeSem,
    Semantics.Comparison.Delineation.ordering_iff_degree μ cc a b ha hb]

end Phenomena.Comparison.Compare
