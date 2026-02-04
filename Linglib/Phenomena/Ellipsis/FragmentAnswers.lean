/-
# Fragment Answers: Empirical Data

Theory-neutral data on fragment answers to questions.

## The Phenomenon

Sentence fragments can communicate full propositions:

  A: "Who went to the movies?"
  B: "Bob"  →  interpreted as "Bob went to the movies"

Key observation: Fragments have NO literal truth conditions,
yet are routinely used and correctly interpreted.

## Distinction from Sluicing

Fragment answers differ from sluicing:
- **Sluicing**: "Someone left, but I don't know who __" (wh-phrase + ellipsis)
- **Fragments**: "Bob" as answer to "Who left?" (bare NP, no clause structure)

## Theoretical Approaches

1. **Noisy Channel** (Bergen & Goodman 2015): Listener infers noise deleted words
2. **Syntactic Ellipsis** (Merchant 2004): Fragments have full syntactic structure
3. **Direct Interpretation** (Stainton 2006): Fragments interpreted without ellipsis

## References

- Bergen, L. & Goodman, N.D. (2015). The Strategic Use of Noise in Pragmatic
  Reasoning. Topics in Cognitive Science 7(2): 336-350.
- Merchant, J. (2004). Fragments and ellipsis. L&P 27(6): 661-738.
- Stainton, R. (2006). Words and Thoughts. OUP.
-/

import Linglib.Phenomena.Core.Basic

/-!
## Connection to RSA Theory

This phenomenon is modeled by Bergen & Goodman (2015)'s noisy channel RSA.
See: `Theories/RSA/Implementations/BergenGoodman2015.lean`

The key insight: fragments are interpreted via noise inference.
The listener reasons that words were deleted during transmission.

Connection to unified noise theory: `Theories/RSA/Core/Noise.lean`
-/

namespace Phenomena.Ellipsis.FragmentAnswers

-- Part 1: Basic Fragment Answer Data

/-- A fragment answer datum -/
structure FragmentDatum where
  /-- The question context -/
  question : String
  /-- The fragment utterance -/
  fragment : String
  /-- The full sentence it's interpreted as -/
  interpretation : String
  /-- Syntactic category of fragment -/
  category : String := "NP"
  /-- Is this interpretation available? -/
  available : Bool := true
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Subject fragment answer -/
def fragmentSubject : FragmentDatum := {
  question := "Who went to the movies?"
  fragment := "Bob"
  interpretation := "Bob went to the movies"
  category := "NP"
  notes := "Subject NP fragment. Most common type."
  source := "Bergen & Goodman (2015)"
}

/-- Object fragment answer -/
def fragmentObject : FragmentDatum := {
  question := "What did John eat?"
  fragment := "An apple"
  interpretation := "John ate an apple"
  category := "NP"
  notes := "Object NP fragment fills direct object position."
  source := "constructed"
}

/-- Negative quantifier fragment -/
def fragmentNobody : FragmentDatum := {
  question := "Who went to the movies?"
  fragment := "Nobody"
  interpretation := "Nobody went to the movies"
  category := "NP"
  notes := "Negative quantifier as fragment answer."
  source := "Bergen & Goodman (2015)"
}

/-- PP fragment answer -/
def fragmentPP : FragmentDatum := {
  question := "Where did John go?"
  fragment := "To the store"
  interpretation := "John went to the store"
  category := "PP"
  notes := "Prepositional phrase fragment."
  source := "constructed"
}

/-- Temporal adverb fragment -/
def fragmentTemporal : FragmentDatum := {
  question := "When did Mary arrive?"
  fragment := "Yesterday"
  interpretation := "Mary arrived yesterday"
  category := "AdvP"
  notes := "Temporal adverb fragment."
  source := "constructed"
}

/-- Predicate fragment (less common) -/
def fragmentPredicate : FragmentDatum := {
  question := "What did John do?"
  fragment := "Left early"
  interpretation := "John left early"
  category := "VP"
  notes := "VP fragment. Less common than NP fragments."
  source := "constructed"
}

-- Part 2: Non-Question Contexts

/-- Fragment in non-question context (Stainton's examples) -/
structure NonQuestionFragmentDatum where
  /-- The preceding context -/
  context : String
  /-- The fragment utterance -/
  fragment : String
  /-- The interpretation -/
  interpretation : String
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Assertion context -/
def fragmentAssertion : NonQuestionFragmentDatum := {
  context := "I think I've discovered the culprit."
  fragment := "The butler!"
  interpretation := "The butler is the culprit"
  notes := "No wh-question; fragment fills contextually salient role."
  source := "Bergen & Goodman (2015), cf. Stainton (1998)"
}

/-- Topic continuation -/
def fragmentTopic : NonQuestionFragmentDatum := {
  context := "I got laughed out of the seminar again today."
  fragment := "Your pragmatic theories."
  interpretation := "Your pragmatic theories got you laughed out"
  notes := "Fragment identifies the cause/topic."
  source := "Bergen & Goodman (2015)"
}

/-- Pointing context -/
def fragmentPointing : NonQuestionFragmentDatum := {
  context := "[pointing at a dog]"
  fragment := "Fido"
  interpretation := "That is Fido"
  notes := "Naming/identifying without question context."
  source := "Stainton (2006)"
}

-- Part 3: Constraints on Fragment Answers

/-- When fragments are NOT acceptable -/
structure FragmentConstraintDatum where
  /-- The question -/
  question : String
  /-- The attempted fragment -/
  fragment : String
  /-- Is it acceptable? -/
  acceptable : Bool
  /-- Why (not) acceptable -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Category mismatch -/
def categoryMismatch : FragmentConstraintDatum := {
  question := "Who left?"
  fragment := "*Quickly"
  acceptable := false
  explanation := "Manner adverb cannot answer 'who' question"
  source := "constructed"
}

/-- Focus mismatch -/
def focusMismatch : FragmentConstraintDatum := {
  question := "WHO left?"  -- contrastive focus on 'who'
  fragment := "John left"
  acceptable := false
  explanation := "Full sentence with neutral prosody doesn't match contrastive focus"
  source := "constructed"
}

/-- Semantic mismatch -/
def semanticMismatch : FragmentConstraintDatum := {
  question := "Where did John go?"
  fragment := "*John"
  acceptable := false
  explanation := "NP cannot answer 'where' (location) question"
  source := "constructed"
}

-- Part 4: Collected Data

def basicFragments : List FragmentDatum := [
  fragmentSubject, fragmentObject, fragmentNobody,
  fragmentPP, fragmentTemporal, fragmentPredicate
]

def nonQuestionFragments : List NonQuestionFragmentDatum := [
  fragmentAssertion, fragmentTopic, fragmentPointing
]

def fragmentConstraints : List FragmentConstraintDatum := [
  categoryMismatch, focusMismatch, semanticMismatch
]

-- Part 5: Connection to Noisy Channel Model

/-!
## Noisy Channel Account (Bergen & Goodman 2015)

The noisy channel model explains fragment interpretation via:

1. **Noise assumption**: Words can be deleted in transmission
2. **Rational inference**: Listener infers what was deleted
3. **Most probable reconstruction**: "Bob" → "Bob went to the movies"

Key prediction: Fragment interpretation is **robust to noise rate**.
Even with very low actual noise, fragments work because:
- Conditional on hearing a fragment, listener knows something was deleted
- Most likely deletion recovers the correct full sentence

See: `Theories/RSA/Implementations/BergenGoodman2015.lean`

### Proven Results

```lean
theorem fragment_interpretation :
    getScore l0_bob .bobWent > getScore l0_bob .aliceWent ∧
    getScore l0_bob .bobWent > getScore l0_bob .nobodyWent
```

### Alternative Accounts

1. **Syntactic ellipsis** (Merchant): Fragments have unpronounced structure
   - Predicts island sensitivity, case matching
   - See: `Phenomena/Ellipsis/Sluicing.lean` for related data

2. **Direct interpretation** (Stainton): No hidden structure
   - Fragments are genuinely sub-sentential
   - Interpretation via pragmatic type-shifting
-/

end Phenomena.Ellipsis.FragmentAnswers
