import Linglib.Core.Scales.Extent
import Linglib.Theories.Semantics.Degree.Core

/-!
# Framework-Independent Comparative Semantics
@cite{rett-2026} @cite{schwarzschild-2008} @cite{von-stechow-1984}

Comparative semantics shared across all degree frameworks: the basic
`comparativeSem` and `equativeSem` functions, antonymy as scale reversal,
DE-ness of than-clauses (NPI licensing), and boundary dependence.

NPI licensing in than-clauses (the @cite{hoeksema-1983} analysis: NP-comparative
as Boolean homomorphism, S-comparative as anti-additive) lives in
`Phenomena/Polarity/Studies/Hoeksema1983.lean`. The `comparative_than_DE`
lemma below is the generic universal-quantifier antitonicity result, not
the Hoeksema-specific anti-additivity result.

This module was extracted from `Theories/Semantics/Lexical/Adjective/Comparative.lean`
(which now re-exports from here). The framework-specific content (MAX,
ambidirectionality, manner implicature) is in `Degree/Frameworks/Rett.lean`.

## Key Results

1. **comparativeSem**: "A is taller than B" iff μ(A) > μ(B) (positive) or
   μ(A) < μ(B) (negative).
2. **Antonymy as scale reversal**: "A taller than B" ↔ "B shorter than A".
3. **DE-ness of than-clauses**: universal quantification over the standard
   domain is anti-monotone.

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

/-- Comparative semantics (@cite{rett-2026} / @cite{schwarzschild-2008}):
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

/-- Universal quantification over a domain is antitone in the domain.
    This is the generic monotonicity fact behind the surface observation
    that *than*-clauses are downward-entailing — not @cite{hoeksema-1983}'s
    specific anti-additivity / Boolean-homomorphism result, which is
    proved in `Phenomena/Polarity/Studies/Hoeksema1983.lean`. -/
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
  deriving DecidableEq, Repr

/-- EN in ambidirectional constructions triggers evaluativity. -/
def enEvaluativeEffect : MannerEffect :=
  { evaluative := true, atypical := false }

-- ════════════════════════════════════════════════════
-- § 7. Comparative as Extent Inclusion
-- ════════════════════════════════════════════════════

/-- Comparative via extents: "A is taller than B" iff A's positive
    extent strictly contains B's. Bridges the point comparison
    to the algebraic `posExt_ssubset_iff` from `Core.Scale`. -/
theorem comparative_iff_posExt_ssubset {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔
      Core.Scale.posExt μ b ⊂ Core.Scale.posExt μ a := by
  exact (Core.Scale.posExt_ssubset_iff μ b a).symm


-- ════════════════════════════════════════════════════
-- § 8. Antonymy from Extent Algebra
-- ════════════════════════════════════════════════════

/-- "A is taller than B" iff "B is shorter than A" — derived from
    the complementarity of positive and negative extents, not
    stipulated as a lexical property of antonym pairs.

    This is @cite{kennedy-1999}'s central result: antonymy equivalence
    follows from the algebra of extents. Delegates to
    `Core.Scale.antonymy_biconditional`. -/
theorem comparative_iff_negExt_ssubset {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔
      Core.Scale.negExt μ a ⊂ Core.Scale.negExt μ b := by
  rw [comparative_iff_posExt_ssubset, Core.Scale.antonymy_biconditional]

-- ════════════════════════════════════════════════════
-- § 9. LITTLE: Degree Negation
-- ════════════════════════════════════════════════════

/-- LITTLE: the degree negation operator (@cite{heim-2006}).
    short = LITTLE tall, less = LITTLE -er, fewer = LITTLE many.

    Semantically, LITTLE complements a degree predicate:
    ⟦LITTLE⟧(P)(d) = ¬P(d). On extents, this maps `posExt` to
    `negExt`: the degrees an entity "has" become the degrees it
    "lacks", reversing the comparison direction.

    @cite{buring-2007} uses LITTLE to analyze cross-polar nomalies:
    "the ladder was shorter than the house was high" works because
    MORE [LITTLE long] -er can be reinterpreted as LITTLE-er long
    (the "more-to-less metamorphosis"). -/
def littlePred {D : Type*} (P : D → Prop) : D → Prop :=
  fun d => ¬ P d

/-- LITTLE maps the positive extent to the negative extent:
    LITTLE({d | d ≤ μ(x)}) = {d | μ(x) < d}.

    This is the formal content of "short = LITTLE tall":
    the degree predicate for 'short' is the complement of the
    degree predicate for 'tall', which is exactly the relationship
    between `posExt` and `negExt` from @cite{kennedy-1999}. -/
theorem little_posExt_eq_negExt {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (x : Entity) (d : D) :
    littlePred (· ∈ Core.Scale.posExt μ x) d ↔
      d ∈ Core.Scale.negExt μ x := by
  simp [littlePred, Core.Scale.posExt, Core.Scale.negExt]

/-- LITTLE is an involution: LITTLE(LITTLE(P)) = P.
    Double degree negation cancels out. -/
theorem little_involution {D : Type*} (P : D → Prop) (d : D) :
    littlePred (littlePred P) d ↔ P d := by
  simp [littlePred]

/-- LITTLE reverses the comparison direction:
    "A is LITTLE-er tall than B" ↔ "B is taller than A".
    Delegates to `taller_shorter_antonymy`. -/
theorem little_reverses_comparison {Entity : Type*} {α : Type*} [LinearOrder α]
    (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ comparativeSem μ b a .negative :=
  taller_shorter_antonymy μ a b

end Semantics.Degree.Comparative
