import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Montague.Basic

/-!
# Degree Semantics: Core Infrastructure

Shared types and interfaces for degree-based analyses of gradable
expressions. This module defines the minimal `GradablePredicate`
interface that all degree semantic frameworks (Kennedy, Heim, Klein,
Schwarzschild, Rett) share, and the compositional `DegP` structure
for degree phrase composition.

## Design

Every degree framework provides a measure function μ : Entity → Degree.
They differ in how the degree argument is bound and how the standard of
comparison is introduced:

| Framework       | Degree binding           | Standard introduction  |
|-----------------|--------------------------|------------------------|
| Kennedy (2007)  | Degree quantifier -er    | Degree clause          |
| Heim (2001)     | Sentential -er operator  | λ-abstraction          |
| Klein (1980)    | No degrees               | Comparison class       |
| Schwarzschild   | Intervals on scale       | Interval semantics     |
| Rett (2026)     | Order-sensitive MAX      | Scale-directional MAX  |

All frameworks except Klein posit degrees; this module provides the
interface they share.

## Connection to Core.Scale

`Core.Scale` defines the algebraic infrastructure (boundedness, MAX,
DirectedMeasure, degree/threshold types for computation). This module adds
the linguistic interface: gradable predicates, DegP composition, and
standard-of-comparison structure.

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Heim, I. (2001). Degree operators and scope.
- Klein, E. (1980). A semantics for positive and comparative adjectives.
- Schwarzschild, R. (2008). The semantics of comparatives.
- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
-/

namespace Semantics.Degree

open Core.Scale (Boundedness ComparativeScale Degree Threshold)

-- ════════════════════════════════════════════════════
-- § 1. Gradable Predicate Interface
-- ════════════════════════════════════════════════════

/-- Minimal interface for a gradable predicate: a measure function
    mapping entities to degrees on a scale with known boundedness.

    Extends `DirectedMeasure D Entity` with a lexical `form` field.
    Every degree framework (Kennedy, Heim, Schwarzschild, Rett) provides
    an instance. Klein's delineation approach does not use degrees, so
    it does not instantiate this interface.

    The algebraic content (μ, boundedness, direction) comes from
    `DirectedMeasure`. `GradablePredicate` adds only the lexical identity.

    The `D` parameter is the degree type (e.g., `ℚ`, `Degree max`,
    or an abstract `LinearOrder`). -/
structure GradablePredicate (Entity D : Type*) [LinearOrder D]
    extends Core.Scale.DirectedMeasure D Entity where
  /-- The adjective's lexical form (for identification) -/
  form : String

-- ════════════════════════════════════════════════════
-- § 2. DegP Compositional Structure
-- ════════════════════════════════════════════════════

/-- The compositional structure of a Degree Phrase (DegP).

    In all degree frameworks, DegP is the syntactic locus where
    degree comparison happens. The internal structure varies:

    Kennedy: [DegP [Deg -er/as/est] [DegComplement than-clause]]
    Heim:    [DegP [-er d₁ d₂] ...]  (sentential operator)

    This type captures the framework-independent parts:
    what kind of comparison, and what standard type. -/
inductive DegPType where
  | comparative   -- -er / more
  | equative      -- as...as
  | superlative   -- -est / most
  | excessive     -- too
  | sufficiency   -- enough
  deriving DecidableEq, BEq, Repr

/-- The standard of comparison: what the degree is compared to. -/
inductive StandardType where
  | explicit     -- "taller than Bill" — explicit standard
  | contextual   -- "tall" — contextually determined standard
  | absolute     -- "full" — scale endpoint as standard
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Positive Form Semantics
-- ════════════════════════════════════════════════════

/-- The positive (unmarked) form of a gradable adjective:
    "Kim is tall" is true iff μ(Kim) exceeds a contextual standard θ.

    This is the common core across Kennedy and Heim:
    - Kennedy: ⟦tall⟧ = λd.λx. height(x) ≥ d, with θ = pos(tall)
    - Heim: ⟦tall⟧ = λx. height(x) ≥ θ_c

    Klein's approach is different: "tall" is true relative to a
    comparison class, with no degree parameter. -/
def positiveSem {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (θ : D) (x : Entity) : Prop :=
  μ x ≥ θ

/-- The positive form with standard derived from scale structure.
    Kennedy (2007): for closed-scale adjectives, the standard IS
    the scale endpoint (minimum or maximum); for open-scale adjectives,
    it's contextually determined. -/
def positiveFromScale {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (b : Boundedness) (x : Entity) : Prop :=
  match b with
  | .closed | .upperBounded => μ x = ⊤   -- "completely full"
  | .lowerBounded           => μ x > ⊥   -- "wet" (any amount)
  | .open_                  => True       -- needs contextual θ

end Semantics.Degree
