import Linglib.Core.Scale
import Linglib.Theories.Semantics.Degree.Core

/-!
# Framework-Independent Comparative Semantics

Comparative semantics shared across all degree frameworks: the basic
`comparativeSem` and `equativeSem` functions, antonymy as scale reversal,
DE-ness of than-clauses (NPI licensing), and boundary dependence.

This module was extracted from `Theories/Semantics/Lexical/Adjective/Comparative.lean`
(which now re-exports from here). The framework-specific content (MAX,
ambidirectionality, manner implicature) is in `Degree/Frameworks/Rett.lean`.

## Key Results

1. **comparativeSem**: "A is taller than B" iff μ(A) > μ(B) (positive) or
   μ(A) < μ(B) (negative).
2. **Antonymy as scale reversal**: "A taller than B" ↔ "B shorter than A".
3. **DE-ness of than-clauses**: universal quantification over the standard
   domain is anti-monotone (Hoeksema 1983, von Stechow 1984).

## References

- Schwarzschild, R. (2008). The semantics of comparatives.
- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
- Hoeksema, J. (1983). Negative polarity and the comparative.
- von Stechow, A. (1984). Comparing semantic theories of comparison.
-/

namespace Semantics.Degree.Comparative

open Core.Scale (ScalePolarity maxOnScale maxOnScale_singleton maxOnScale_ge_atMost)

-- ════════════════════════════════════════════════════
-- § 1. Scale Direction
-- ════════════════════════════════════════════════════

/-- Comparative direction reuses scale polarity from Core.
    `positive`: "taller" — MAX picks the highest degrees.
    `negative`: "shorter" — MAX picks the lowest degrees. -/
abbrev ScaleDirection := ScalePolarity

-- ════════════════════════════════════════════════════
-- § 2. Comparative and Equative Semantics
-- ════════════════════════════════════════════════════

variable {Entity : Type*} {α : Type*} [LinearOrder α]

/-- Comparative semantics (Rett 2026 / Schwarzschild 2008):
    "A is Adj-er than B" iff μ(a) exceeds μ(b) on the directed scale. -/
def comparativeSem (μ : Entity → α) (a b : Entity) (dir : ScaleDirection) : Prop :=
  match dir with
  | .positive => μ a > μ b
  | .negative => μ a < μ b

/-- Equative semantics: "A is as Adj as B" iff μ(a) ≥ μ(b) on the
    directed scale. -/
def equativeSem (μ : Entity → α) (a b : Entity) (dir : ScaleDirection) : Prop :=
  match dir with
  | .positive => μ a ≥ μ b
  | .negative => μ a ≤ μ b

/-- **MAX–direct bridge**: the direct comparison `μ(a) > μ(b)` is
    equivalent to the MAX-based formulation. -/
theorem comparativeSem_eq_MAX (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔
      ∃ m ∈ maxOnScale (· > ·) ({μ b} : Set α), μ a > m := by
  simp [comparativeSem, maxOnScale_singleton]

-- ════════════════════════════════════════════════════
-- § 3. Antonymy as Scale Reversal
-- ════════════════════════════════════════════════════

/-- "A taller than B" ↔ "B shorter than A" — antonymy is argument swap
    plus direction reversal. -/
theorem taller_shorter_antonymy (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ comparativeSem μ b a .negative := by
  simp [comparativeSem]

/-- Equative antonymy: "A as tall as B" ↔ "B as short as A". -/
theorem equative_antonymy (μ : Entity → α) (a b : Entity) :
    equativeSem μ a b .positive ↔ equativeSem μ b a .negative := by
  simp [equativeSem]

-- ════════════════════════════════════════════════════
-- § 4. Boundary Dependence
-- ════════════════════════════════════════════════════

/-- The comparative depends only on the boundary μ_b. -/
theorem comparative_boundary {α : Type*} [LinearOrder α]
    (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale (· ≥ ·) {d | d ≤ μ_b}, μ_a > m) ↔ μ_a > μ_b := by
  rw [maxOnScale_ge_atMost]
  simp

/-- The equative depends only on the boundary μ_b. -/
theorem equative_boundary {α : Type*} [LinearOrder α]
    (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale (· ≥ ·) {d | d ≤ μ_b}, μ_a ≥ m) ↔ μ_a ≥ μ_b := by
  rw [maxOnScale_ge_atMost]
  simp

-- ════════════════════════════════════════════════════
-- § 5. NPI Licensing in Comparatives
-- ════════════════════════════════════════════════════

/-- The *than*-clause argument of a comparative is DE: universal
    quantification over a domain is anti-monotone in the domain. -/
theorem comparative_than_DE {α : Type*} (R : α → α → Prop)
    (μ_a : α) (D₁ D₂ : Set α) (h_sub : D₁ ⊆ D₂)
    (h : ∀ d ∈ D₂, R μ_a d) : ∀ d ∈ D₁, R μ_a d :=
  fun d hd => h d (h_sub hd)

-- ════════════════════════════════════════════════════
-- § 6. Manner Implicature (re-exported from Rett)
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

/-- EN in ambidirectional constructions triggers evaluativity. -/
def enEvaluativeEffect : MannerEffect :=
  { evaluative := true, atypical := false }

end Semantics.Degree.Comparative
