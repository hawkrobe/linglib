import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core

/-!
# Rett's Order-Sensitive MAX Framework
@cite{rett-2026} @cite{rullmann-1995} @cite{schwarzschild-2008} @cite{krifka-2010b}

@cite{rett-2026} "Semantic Ambivalence and Expletive Negation": the
comparative morpheme is an order-sensitive maximality operator MAX_R
that picks the R-maximal element of a degree set.

This framework absorbs and extends the content previously in
`Theories/Semantics/Lexical/Adjective/Comparative.lean`, providing
a unified analysis of comparatives, temporal connectives, and
expletive negation licensing.

## Key Ideas

1. **MAX_R**: A domain-general maximality operator parameterized by
   a relation R. MAX_R(X) = {x ∈ X | ∀x' ∈ X, x' ≠ x → R x x'}.
   For `<`, this gives the minimum; for `>`, the maximum.

2. **Ambidirectionality**: A construction f is ambidirectional for B iff
   f(B) ↔ f(Bᶜ). This holds when MAX picks the same boundary from both
   B and its complement.

3. **Expletive negation licensing**: EN is licensed exactly in
   ambidirectional constructions, because negating the argument is
   truth-conditionally vacuous.

4. **Manner implicature**: EN triggers evaluativity — the marked
   form signals that the comparison/temporal relation is noteworthy.

## Connections

- `maxOnScale` and `isAmbidirectional` are defined in `Core.Scale`
- The comparative morpheme `comparativeSem` is now in `Degree.Comparative`
- EN predictions are in `Phenomena/Negation/Studies/Rett2026.lean`

-/

namespace Semantics.Degree.Frameworks.Rett

open Core.Scale (maxOnScale maxOnScale_singleton maxOnScale_ge_atMost
  isAmbidirectional ScalePolarity)

-- ════════════════════════════════════════════════════
-- § 1. Scale Direction
-- ════════════════════════════════════════════════════

/-- Comparative direction reuses scale polarity from Core.
    `positive`: "taller" — MAX picks the highest degrees.
    `negative`: "shorter" — MAX picks the lowest degrees. -/
abbrev ScaleDirection := ScalePolarity

-- ════════════════════════════════════════════════════
-- § 2. MAX-Based Comparative
-- ════════════════════════════════════════════════════

/-- Rett/Schwarzschild comparative morpheme (eq. 47):
    "A is taller than B" iff MAX of A's degrees >_dir MAX of B's degrees.

    For singleton degree sets {μ(a)} and {μ(b)}, MAX is trivial
    (`maxOnScale_singleton`), so this reduces to direct comparison. -/
def rettComparative {Entity : Type*} {α : Type*} [LinearOrder α]
    (μ : Entity → α) (a b : Entity) (dir : ScaleDirection) : Prop :=
  match dir with
  | .positive => μ a > μ b
  | .negative => μ a < μ b

/-- **MAX–direct bridge**: the direct comparison `μ(a) > μ(b)` is
    equivalent to the MAX-based formulation. This makes explicit that
    `rettComparative` is a simplification of the general MAX-comparison,
    justified by `maxOnScale_singleton`. -/
theorem rettComparative_eq_MAX {Entity : Type*} {α : Type*} [LinearOrder α]
    (μ : Entity → α) (a b : Entity) :
    rettComparative μ a b .positive ↔
      ∃ m ∈ maxOnScale (· > ·) ({μ b} : Set α), μ a > m := by
  simp [rettComparative, maxOnScale_singleton]

-- ════════════════════════════════════════════════════
-- § 3. Ambidirectionality Analysis
-- ════════════════════════════════════════════════════

/-- The comparative depends only on the boundary μ_b, not on
    whether the standard is B = {d | d ≤ μ_b} or any other set
    sharing that supremum. This captures Rett's ambidirectionality
    insight: since MAX₍≥₎({d | d ≤ μ_b}) = {μ_b}, the existential
    reduces to a direct comparison. -/
theorem comparative_boundary {α : Type*} [LinearOrder α]
    (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale (· ≥ ·) {d | d ≤ μ_b}, μ_a > m) ↔ μ_a > μ_b := by
  rw [maxOnScale_ge_atMost]
  simp

/-- Equative boundary reduction:
    the equative also depends only on the boundary μ_b. -/
theorem equative_boundary {α : Type*} [LinearOrder α]
    (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale (· ≥ ·) {d | d ≤ μ_b}, μ_a ≥ m) ↔ μ_a ≥ μ_b := by
  rw [maxOnScale_ge_atMost]
  simp

-- ════════════════════════════════════════════════════
-- § 4. Manner Implicature
-- ════════════════════════════════════════════════════

/-- Manner implicature triggered by EN in an ambidirectional construction.
    `evaluative`: the relation is noteworthy (large gap / early timing).
    `atypical`: the EN form is pragmatically marked (optional, stylistic). -/
structure MannerEffect where
  /-- Does EN trigger an evaluative reading? -/
  evaluative : Bool
  /-- Is the EN form pragmatically marked (optional, stylistic)? -/
  atypical : Bool
  deriving DecidableEq, BEq, Repr

/-- EN in ambidirectional constructions (comparatives, *before*-clauses)
    triggers evaluativity but is not atypical — it's a productive pattern
    cross-linguistically. -/
def enEvaluativeEffect : MannerEffect :=
  { evaluative := true, atypical := false }

end Semantics.Degree.Frameworks.Rett
