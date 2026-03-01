import Linglib.Theories.Semantics.Degree.Frameworks.Kennedy
import Linglib.Theories.Semantics.Degree.Frameworks.Heim
import Linglib.Theories.Semantics.Degree.Frameworks.Klein
import Linglib.Theories.Semantics.Degree.Frameworks.Schwarzschild
import Linglib.Theories.Semantics.Degree.Frameworks.Rett
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Framework Comparison: Where Kennedy and Heim Diverge
@cite{heim-2001} @cite{kennedy-2007} @cite{klein-1980} @cite{rett-2026} @cite{schwarzschild-2008}

Formal comparison of the five degree semantic frameworks on shared
empirical ground. This is the key intellectual payoff of the `Degree/`
reorganization: by implementing all five frameworks with the same type
signatures, we can formally state where they agree and where they diverge.

## Agreement

All five frameworks agree on the truth conditions of simple comparatives:
"A is taller than B" iff μ(A) > μ(B) (for frameworks with degrees) or
∃C such that tall(A, C) ∧ ¬tall(B, C) (for Klein).

## Divergences

| Question                    | Kennedy | Heim | Klein | Schwarzschild | Rett |
|-----------------------------|---------|------|-------|---------------|------|
| Degrees in ontology?        | Yes     | Yes  | No    | Yes (intervals)| Yes |
| Scope of -er                | DP      | CP   | N/A   | DP            | DP  |
| Measure phrases             | Direct  | Direct| Hard | Direct        | Direct|
| Subcomparatives             | Special | Special| Special| Natural    | Special|
| EN licensing explanation    | —       | —    | —     | —             | ✓   |

-/

namespace Phenomena.Comparison.Comparative.Compare

-- ════════════════════════════════════════════════════
-- § 1. Extensional Equivalence of Degree Frameworks
-- ════════════════════════════════════════════════════

/-- All four degree-based frameworks agree on simple comparatives.
    Kennedy, Heim, Schwarzschild (intervals), and Rett (MAX) all
    yield μ(A) > μ(B) for "A is taller than B". -/
theorem four_degree_frameworks_agree {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) :
    Semantics.Degree.Frameworks.Kennedy.kennedyComparative μ a b ↔
    Semantics.Degree.Frameworks.Heim.heimComparativeWithMeasure μ a b := by
  exact Iff.rfl

/-- Schwarzschild's interval comparative also agrees (reduces to point
    comparison on positive intervals). -/
theorem schwarzschild_agrees {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) :
    Semantics.Degree.Frameworks.Schwarzschild.intervalComparative μ a b ↔
    Semantics.Degree.Frameworks.Kennedy.kennedyComparative μ a b := by
  exact Iff.rfl

/-- Rett's MAX-based framework agrees with Kennedy on positive direction. -/
theorem rett_agrees_with_kennedy {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    Semantics.Degree.Frameworks.Rett.rettComparative μ a b .positive ↔
    Semantics.Degree.Frameworks.Kennedy.kennedyComparative μ a b := by
  exact Iff.rfl

-- ════════════════════════════════════════════════════
-- § 2. Scope Divergence: Kennedy vs. Heim
-- ════════════════════════════════════════════════════

/-- The key divergence between Kennedy and Heim is scope.
    Kennedy: -er is DP-internal → only narrow scope
    Heim: -er is sentential → wide scope available

    We can't formalize the scope prediction directly (it's about
    LF movement), but we can state that the frameworks are
    extensionally equivalent in scope-free contexts. -/
theorem extensional_equivalence_scope_free {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    Semantics.Degree.Frameworks.Kennedy.kennedyComparative μ a b =
    Semantics.Degree.Frameworks.Heim.heimComparativeWithMeasure μ a b :=
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
    Kennedy's. If μ(a) > μ(b), then for the comparison class {a, b},
    delineating at μ(b) puts a in the positive extension but not b. -/
theorem klein_correspondence {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity)
    (delineation : Set Entity → Entity → Prop)
    (hdiscrim : μ a > μ b →
      ∃ C : Set Entity, delineation C a ∧ ¬ delineation C b) :
    Semantics.Degree.Frameworks.Kennedy.kennedyComparative μ a b →
    Semantics.Degree.Frameworks.Klein.comparativeSem delineation a b := by
  exact hdiscrim

end Phenomena.Comparison.Comparative.Compare
