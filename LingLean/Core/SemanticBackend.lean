/-
# LingLean.Core.SemanticBackend

The semantic interface that connects syntax to pragmatics (RSA).

This defines what computational pragmatics needs from a syntactic framework:
- A type of utterances (derivations)
- A type of worlds/models
- An agreement function φ : Utterance → World → ℝ
-/

-- ============================================================================
-- Semantic Backend Typeclass
-- ============================================================================

/--
The semantic interface that RSA needs from a syntactic backend.
Type parameter `S` is the syntactic framework.
-/
class SemanticBackend (S : Type) where
  Utterance : Type
  World : Type
  φ : Utterance → World → Float
  bounded : ∃ M : Float, ∀ u w, φ u w ≤ M

/-- A literal semantics: φ returns 1 if true, 0 if false. -/
class LiteralSemantics (S : Type) extends SemanticBackend S where
  satisfies : World → Utterance → Prop
  decSatisfies : ∀ w u, Decidable (satisfies w u)
  φ_is_indicator : ∀ u w, φ u w = if satisfies w u then 1.0 else 0.0

/-- A graded semantics: φ can take values in [0, 1]. -/
class GradedSemantics (S : Type) extends SemanticBackend S where
  normalized : ∀ u w, 0.0 ≤ φ u w ∧ φ u w ≤ 1.0

-- ============================================================================
-- RSA Speaker and Listener
-- ============================================================================

/-- RSA speaker score (unnormalized): S(u | w) ∝ exp(α · φ(u, w) - c(u)) -/
def rsaSpeakerScore (S : Type) [SemanticBackend S]
    (α : Float) (cost : SemanticBackend.Utterance S → Float)
    (u : SemanticBackend.Utterance S) (w : SemanticBackend.World S) : Float :=
  Float.exp (α * SemanticBackend.φ u w - cost u)

/-- Literal listener score: L₀(w | u) ∝ P(w) · φ(u, w) -/
def literalListenerScore (S : Type) [SemanticBackend S]
    (prior : SemanticBackend.World S → Float)
    (u : SemanticBackend.Utterance S) (w : SemanticBackend.World S) : Float :=
  prior w * SemanticBackend.φ u w
