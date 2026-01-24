/-
# Linglib.Core.SemanticBackend

The semantic interface that connects syntax to pragmatics (RSA).

## Design Principle

This interface is MINIMAL: it only provides what the literal listener needs.
- φ : Utterance → World → Float (or Bool)

How φ is computed is an internal concern of the semantic theory:
- Could be a simple lookup table
- Could be compositional (generalized quantifiers)
- Could involve belief worlds for embedded clauses

Alternatives for pragmatic reasoning are handled separately by pragmatics
(RSA, NeoGricean), not by the semantic backend.
-/

-- ============================================================================
-- Core Semantic Backend
-- ============================================================================

/--
The semantic interface that RSA needs from a syntactic/semantic backend.

Type parameter `S` is the semantic theory/domain.

This is intentionally minimal - just what L0 needs:
- A type of utterances
- A type of worlds
- An agreement function φ

How φ is derived (lookup, composition, etc.) is internal to the implementation.
-/
class SemanticBackend (S : Type) where
  Utterance : Type
  World : Type
  /-- Agreement function: how well does utterance u describe world w? -/
  φ : Utterance → World → Float
  /-- φ is bounded (for well-defined normalization) -/
  bounded : ∃ M : Float, ∀ u w, φ u w ≤ M

-- ============================================================================
-- Specializations
-- ============================================================================

/--
A literal (Boolean) semantics: φ returns 1 if true, 0 if false.

This is the standard case for classical model-theoretic semantics.
-/
class LiteralSemantics (S : Type) extends SemanticBackend S where
  /-- The satisfaction relation (denotation) -/
  satisfies : World → Utterance → Prop
  /-- Satisfaction is decidable -/
  decSatisfies : ∀ w u, Decidable (satisfies w u)
  /-- φ is the indicator function of satisfaction -/
  φ_is_indicator : ∀ u w, φ u w = if satisfies w u then 1.0 else 0.0

/--
A graded semantics: φ can take values in [0, 1].

Useful for:
- Fuzzy/vague predicates
- Probabilistic semantics
- Degree-based approaches
-/
class GradedSemantics (S : Type) extends SemanticBackend S where
  /-- φ is normalized to [0, 1] -/
  normalized : ∀ u w, 0.0 ≤ φ u w ∧ φ u w ≤ 1.0

-- ============================================================================
-- RSA Literal Listener (L0)
-- ============================================================================

/--
Literal listener score: L₀(w | u) ∝ P(w) · φ(u, w)

The literal listener:
1. Takes the utterance at face value
2. Updates prior beliefs by φ
3. Returns posterior over worlds

Note: This is agnostic to how φ was computed.
-/
def literalListenerScore (S : Type) [SemanticBackend S]
    (prior : SemanticBackend.World S → Float)
    (u : SemanticBackend.Utterance S) (w : SemanticBackend.World S) : Float :=
  prior w * SemanticBackend.φ u w

/--
RSA speaker score (unnormalized): S(u | w) ∝ exp(α · φ(u, w) - c(u))

The speaker chooses utterances that:
1. Are true/appropriate (high φ)
2. Are not too costly (low c)

Weighted by rationality parameter α.
-/
def rsaSpeakerScore (S : Type) [SemanticBackend S]
    (α : Float) (cost : SemanticBackend.Utterance S → Float)
    (u : SemanticBackend.Utterance S) (w : SemanticBackend.World S) : Float :=
  Float.exp (α * SemanticBackend.φ u w - cost u)

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Core Interface
- `SemanticBackend`: Minimal interface (Utterance, World, φ)
- `LiteralSemantics`: Boolean specialization (φ ∈ {0, 1})
- `GradedSemantics`: Continuous specialization (φ ∈ [0, 1])

### RSA Primitives
- `literalListenerScore`: L₀(w | u) ∝ P(w) · φ(u, w)
- `rsaSpeakerScore`: S(u | w) ∝ exp(α · φ(u, w) - c(u))

### Design Principles
1. **Minimal**: Only what L0 needs
2. **Agnostic**: Doesn't care how φ is computed
3. **Flexible**: Different implementations can provide φ differently

### What's NOT Here
- Alternatives (handled by pragmatics)
- Compositional structure (internal to semantic implementations)
- Monotonicity tracking (internal to compositional semantics)

These are concerns of specific theories, not the interface.
-/
