/-
# Coordination

## The Phenomenon

Coordination allows two or more elements to be joined by a conjunction.
Key constraints:
1. Coordinated elements must have matching categories
2. Coordinated verbs must have matching argument structures

## The Data

  (1a)  John and Mary sleep           ✓  NP coordination
  (1b) *John and sleeps               ✗  category mismatch (D + V)

  (2a)  John sleeps and Mary sleeps   ✓  S coordination
  (2b) *John sleeps and Mary          ✗  incomplete second conjunct

  (3a)  John sees and hears Mary      ✓  VP coordination (shared args)
  (3b) *John sees and sleeps Mary     ✗  valence mismatch (trans + intrans)

Reference: Gibson (2025) "Syntax", MIT Press, Section 3.8
-/

import Linglib.Core.Grammar

-- ============================================================================
-- Core Coordination Data (String-Based)
-- ============================================================================

/-- NP coordination minimal pairs -/
def npCoordinationData : StringPhenomenonData := {
  name := "NP Coordination"
  generalization := "Coordinated NPs must have matching categories"
  pairs := [
    { grammatical := "John and Mary sleep"
      ungrammatical := "John and sleeps"
      clauseType := .declarative
      description := "NP coordination requires matching categories" },

    { grammatical := "the boy and the girl sleep"
      ungrammatical := "the boy and sleeps"
      clauseType := .declarative
      description := "Complex NP coordination" }
  ]
}

/-- VP coordination minimal pairs -/
def vpCoordinationData : StringPhenomenonData := {
  name := "VP Coordination"
  generalization := "Coordinated VPs must have matching argument structures"
  pairs := [
    { grammatical := "John sees and hears Mary"
      ungrammatical := "John sees and sleeps Mary"
      clauseType := .declarative
      description := "VP coordination requires matching valence (trans + trans)" },

    { grammatical := "John sleeps and snores"
      ungrammatical := "John sleeps and sees"
      clauseType := .declarative
      description := "Intransitive VP coordination" }
  ]
}

/-- S coordination minimal pairs -/
def sCoordinationData : StringPhenomenonData := {
  name := "S Coordination"
  generalization := "Coordinated sentences must each be complete"
  pairs := [
    { grammatical := "John sleeps and Mary sleeps"
      ungrammatical := "John sleeps and Mary"
      clauseType := .declarative
      description := "S coordination requires complete clauses" },

    { grammatical := "John sees Mary and Mary sees John"
      ungrammatical := "John sees Mary and sees John"
      clauseType := .declarative
      description := "Each conjunct needs a subject" }
  ]
}

-- ============================================================================
-- Non-Constituent Coordination: The Semantic Fact
-- ============================================================================

/-
## Non-Constituent Coordination

"John likes and Mary hates beans" is grammatical and has a conjunctive interpretation.

**The empirical observation** (theory-neutral):
- The sentence means: John likes beans AND Mary hates beans
- Symbolically: likes(beans, john) ∧ hates(beans, mary)

**Why this is surprising**:
In traditional phrase structure, "John likes" is NOT a constituent:
    [S [NP John] [VP likes [NP ___]]]

Yet it behaves as a unit for coordination purposes.

**What any theory must explain**:
1. The sentence is grammatical
2. The interpretation is the conjunction of two predications
3. Each predication shares the same object ("beans")

References:
- Steedman (2000) "The Syntactic Process" Ch. 3
- Dowty (1988) "Type raising, functional composition, and non-constituent conjunction"
-/

/--
**Theory-Neutral Semantic Data for Non-Constituent Coordination**

The core empirical observation is a **semantic equivalence**:

  "John likes and Mary hates beans" ≡ "John likes beans and Mary hates beans"

This is theory-neutral: we don't presuppose any logical formalism, just that
native speakers judge these sentences to have the same meaning (same truth
conditions, same entailments, intersubstitutable in any context).
-/
structure SemanticEquivalence where
  /-- The non-constituent coordination sentence -/
  sentence : List String
  /-- The semantically equivalent spelled-out version -/
  equivalentTo : List String
  /-- Both are grammatical -/
  bothGrammatical : Bool := true
  deriving Repr

/-- "John likes and Mary hates beans" ≡ "John likes beans and Mary hates beans" -/
def johnLikesAndMaryHatesBeans : SemanticEquivalence := {
  sentence := ["John", "likes", "and", "Mary", "hates", "beans"]
  equivalentTo := ["John", "likes", "beans", "and", "Mary", "hates", "beans"]
}

/-- "Warren cooked and Betsy ate the potatoes" ≡ "Warren cooked the potatoes and Betsy ate the potatoes" -/
def warrenCookedAndBetsyAte : SemanticEquivalence := {
  sentence := ["Warren", "cooked", "and", "Betsy", "ate", "the", "potatoes"]
  equivalentTo := ["Warren", "cooked", "the", "potatoes", "and", "Betsy", "ate", "the", "potatoes"]
}

/-- "I met and you saw John" ≡ "I met John and you saw John" -/
def iMetAndYouSaw : SemanticEquivalence := {
  sentence := ["I", "met", "and", "you", "saw", "John"]
  equivalentTo := ["I", "met", "John", "and", "you", "saw", "John"]
}

/-
## The Core Empirical Fact

Native speakers judge these sentence pairs **semantically equivalent**:
- Same truth conditions
- Same entailments
- Intersubstitutable in any context

This is the raw data. Any theory of coordination semantics must predict
that the two sentences in each pair receive equivalent interpretations.
-/

/-- A theory captures non-constituent coordination if it derives equivalent
    meanings for both sentences in a SemanticEquivalence pair. -/
class CapturesNonConstituentCoord (G : Type) where
  /-- Both sentences derive -/
  bothDerive : G → SemanticEquivalence → Bool
  /-- The derived meanings are equivalent -/
  meaningsEquivalent : G → SemanticEquivalence → Bool
