/-!
# Epistemic Contradictions — Empirical Data
@cite{holliday-mandelkern-2024}

Theory-neutral observations about epistemic contradictions. These are the
empirical facts that any semantic theory of epistemic modals must account for.

## Three kinds of contradiction

1. **Moore sentences**: "It's raining but I don't know that it's raining."
   Pragmatically odd but embeddable (under "suppose", in conditionals, etc.).
2. **Wittgenstein sentences**: "It's raining and it might not be raining."
   Semantically contradictory — infelicitous even under embedding.
3. **Classical contradictions**: "It's raining and it's not raining."
   Logically contradictory — always infelicitous.

The key datum: Wittgenstein sentences pattern with classical contradictions
(not with Moore sentences) under embedding, suggesting they are *semantic*
contradictions, not merely pragmatic ones.
-/

namespace Phenomena.Modality.EpistemicContradictions

/-- A sentence type: how epistemic modality interacts with assertion. -/
inductive SentenceType where
  | moore          -- p ∧ ¬Kp ("It's raining but I don't know it")
  | wittgenstein   -- p ∧ ◇¬p ("It's raining and it might not be")
  | classical      -- p ∧ ¬p ("It's raining and it's not raining")
  deriving DecidableEq, BEq, Repr

/-- Embedding environments that distinguish Moore from Wittgenstein. -/
inductive EmbeddingEnv where
  | suppose        -- "Suppose it's raining and it might not be"
  | conditional    -- "If it's raining and it might not be, then..."
  | epistemic      -- "It might be that it's raining and it might not be"
  | disjunction    -- "Either ... or it's raining and it might not be"
  | attitude       -- "John thinks it's raining and it might not be"
  deriving DecidableEq, BEq, Repr

/-- Moore sentences become felicitous under embedding; Wittgenstein and
    classical contradictions remain infelicitous. This is the core
    diagnostic separating pragmatic from semantic contradiction. -/
def felicitousUnderEmbedding : SentenceType → Bool
  | .moore => true
  | .wittgenstein => false
  | .classical => false

/-- Distributivity failure intuition: the LHS is felicitous but the
    classically equivalent RHS is not. -/
structure DistribIntuition where
  lhs : String
  rhs : String
  lhsFelicitous : Bool
  rhsFelicitous : Bool

/-- "Sue might be the winner and she might not be, and either she is or
    she isn't" is fine; distributing yields two Wittgenstein sentences
    joined by "or", which is not. -/
def distribFailure : DistribIntuition :=
  { lhs := "Sue might be the winner and she might not be, and either she is the winner or she isn't"
  , rhs := "Sue might not be the winner and she is the winner, or else Sue might be the winner and she isn't the winner"
  , lhsFelicitous := true
  , rhsFelicitous := false }

/-- Disjunctive syllogism failure intuition. -/
structure DisjSyllIntuition where
  premise1 : String
  premise2 : String
  conclusion : String
  valid : Bool

/-- The argument "either the dog is inside or it must be outside; it's
    not the case that it must be outside; therefore the dog is inside"
    is intuitively invalid for epistemic modals. -/
def disjSyllFailure : DisjSyllIntuition :=
  { premise1 := "Either the dog is inside or it must be outside"
  , premise2 := "It's not the case that the dog must be outside"
  , conclusion := "The dog is inside"
  , valid := false }

end Phenomena.Modality.EpistemicContradictions
