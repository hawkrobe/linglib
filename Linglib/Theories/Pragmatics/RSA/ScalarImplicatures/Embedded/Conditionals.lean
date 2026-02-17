/-
# RSA Conditional Antecedent Embedding

Models scalar implicatures embedded in conditional antecedents.

## The Phenomenon

"If some students passed, the professor will be happy"

The antecedent of a conditional is a DOWNWARD-ENTAILING context:
- "If all students passed, P" entails "If some students passed, P"

This predicts DE-like blocking of local implicatures, similar to "no one".

## Theoretical Background

Conditional antecedents are DE because:
- Let p ⊆ q (p entails q)
- Then: "If q, r" entails "If p, r"  (contrapositive reasoning)

For scalar implicatures:
- "some" ⊆ "all" (in terms of truth conditions)
- So: "If all passed, happy" entails "If some passed, happy"

Local SI would strengthen "some" to "some-but-not-all", making:
- "If some-but-not-all passed, happy"

This is WEAKER than "If some passed, happy" (true in fewer cases).
RSA should prefer the more informative global interpretation.

## References

- Geurts (2010). Quantity Implicatures. Ch. 3.
- Chierchia (2004). Scalar implicatures, polarity phenomena.
- von Fintel (1999). NPI licensing, Strawson-entailment, and context dependency.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Mathlib.Tactic.DeriveFintype

namespace RSA.ConditionalEmbedding

-- World Structure for Conditionals

/--
Student outcome for conditional scenario.
-/
inductive StudentResult where
  | noneP   -- no students passed
  | someP   -- some but not all passed
  | allP    -- all students passed
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Professor's happiness state.
-/
inductive ProfState where
  | unhappy
  | happy
  deriving DecidableEq, Repr, BEq, Inhabited

/--
World for conditional embedding.

Tracks both the student outcome and whether the professor is happy.
-/
structure CondWorld where
  students : StudentResult
  professor : ProfState
  deriving DecidableEq, Repr, BEq, Inhabited

-- Truth Conditions for Conditionals

/--
"Some students passed" - weak (existential) reading.
-/
def somePassed (w : CondWorld) : Bool :=
  w.students == .someP || w.students == .allP

/--
"Some-but-not-all students passed" - strong (exact) reading.
-/
def someNotAllPassed (w : CondWorld) : Bool :=
  w.students == .someP

/--
"All students passed".
-/
def allPassed (w : CondWorld) : Bool :=
  w.students == .allP

/--
"No students passed".
-/
def nonePassed (w : CondWorld) : Bool :=
  w.students == .noneP

/--
"The professor is happy".
-/
def profHappy (w : CondWorld) : Bool :=
  w.professor == .happy

-- Conditional Interpretations

/--
Interpretations of "If some students passed, the professor will be happy":

1. **Global**: "some" is weak; if any student passed, prof is happy
2. **Local**: "some" is strong; if some-but-not-all passed, prof is happy
-/
inductive CondInterpretation where
  | global  -- "some" = at least one
  | local_  -- "some" = some-but-not-all
  deriving DecidableEq, Repr, BEq, Inhabited, Fintype

/--
Material conditional semantics: "If P, Q" = ¬P ∨ Q.

- **Global**: ¬(some passed) ∨ happy = (none passed) ∨ happy
- **Local**: ¬(some-not-all passed) ∨ happy = (none ∨ all passed) ∨ happy
-/
def conditionalMeaning (interp : CondInterpretation) (w : CondWorld) : Bool :=
  match interp with
  | .global => !somePassed w || profHappy w      -- ¬(≥1 passed) ∨ happy
  | .local_ => !someNotAllPassed w || profHappy w -- ¬(some-not-all) ∨ happy

-- World Space

/--
Relevant worlds for the conditional scenario.

We include worlds where the conditional's consequent may or may not hold.
-/
def condWorlds : List CondWorld := [
  -- No students passed
  ⟨.noneP, .unhappy⟩,
  ⟨.noneP, .happy⟩,
  -- Some but not all passed
  ⟨.someP, .unhappy⟩,
  ⟨.someP, .happy⟩,
  -- All passed
  ⟨.allP, .unhappy⟩,
  ⟨.allP, .happy⟩
]

instance : Fintype StudentResult where
  elems := ⟨[StudentResult.noneP, StudentResult.someP, StudentResult.allP], by decide⟩
  complete := λ x => by cases x <;> decide

instance : Fintype ProfState where
  elems := ⟨[ProfState.unhappy, ProfState.happy], by decide⟩
  complete := λ x => by cases x <;> decide

instance : Fintype CondWorld :=
  Fintype.ofEquiv (StudentResult × ProfState)
    { toFun := λ ⟨s, p⟩ => ⟨s, p⟩
      invFun := λ ⟨s, p⟩ => ⟨s, p⟩
      left_inv := λ _ => rfl
      right_inv := λ _ => rfl }

-- Key Predictions: DE-like Behavior

/--
Global interpretation: "If some passed, happy"
- False only when: some passed AND prof unhappy
- True when: none passed OR prof happy
-/
theorem global_false_when_passed_unhappy :
    conditionalMeaning .global ⟨.someP, .unhappy⟩ = false := rfl

theorem global_true_when_none_passed :
    conditionalMeaning .global ⟨.noneP, .unhappy⟩ = true := rfl

/--
Local interpretation: "If some-but-not-all passed, happy"
- False only when: some-but-not-all passed AND prof unhappy
- True when: (none OR all passed) OR prof happy
-/
theorem local_false_when_someNotAll_unhappy :
    conditionalMeaning .local_ ⟨.someP, .unhappy⟩ = false := rfl

theorem local_true_when_all_passed :
    conditionalMeaning .local_ ⟨.allP, .unhappy⟩ = true := rfl

-- DE Property: Global is Stronger

/--
The key DE property: Global ENTAILS Local.

"If some passed, happy" → "If some-but-not-all passed, happy"

This is because:
- Global is false when (some ∧ unhappy) - includes someP and allP
- Local is false only when (some-not-all ∧ unhappy) - only someP

So Global being true implies Local is true.
-/
theorem global_entails_local :
    ∀ w : CondWorld, conditionalMeaning .global w = true →
      conditionalMeaning .local_ w = true := by
  intro ⟨students, professor⟩ h
  cases students <;> cases professor
  case noneP.unhappy => native_decide
  case noneP.happy => native_decide
  case someP.unhappy => exact absurd h (by native_decide)
  case someP.happy => native_decide
  case allP.unhappy => exact absurd h (by native_decide)
  case allP.happy => native_decide

/--
Local does NOT entail Global.
When all students passed and prof is unhappy:
- Local is true (antecedent "some-not-all" is false)
- Global is false (antecedent "some" is true, consequent false)
-/
theorem local_not_entails_global :
    ∃ w : CondWorld, conditionalMeaning .local_ w = true ∧
      conditionalMeaning .global w = false := by
  use ⟨.allP, .unhappy⟩
  decide

/--
Worlds where global and local differ.
-/
def globalLocalDiffer : List CondWorld :=
  condWorlds.filter (λ w =>
    conditionalMeaning .global w != conditionalMeaning .local_ w)

#eval globalLocalDiffer  -- Should be: allP + unhappy

/--
The conditional antecedent is DE: weakening the antecedent strengthens the conditional.

"If some passed, happy" entails "If all passed, happy" because:
- some ⊇ all (some is satisfied by more worlds than all)
- So the weaker antecedent gives a stronger conditional

This is the DE property: p ⊆ q implies "If q, r" ⊆ "If p, r"
-/
theorem conditional_antecedent_is_DE :
    -- "If some passed, happy" → "If all passed, happy"
    ∀ w : CondWorld, (!somePassed w || profHappy w) = true →
      (!allPassed w || profHappy w) = true := by
  intro ⟨students, professor⟩ h
  cases students <;> cases professor
  case noneP.unhappy => native_decide
  case noneP.happy => native_decide
  case someP.unhappy => exact absurd h (by native_decide)
  case someP.happy => native_decide
  case allP.unhappy => exact absurd h (by native_decide)
  case allP.happy => native_decide

-- RSA Prediction

/-
## RSA Analysis

Since Global ENTAILS Local:
- Global is strictly more informative (rules out more worlds)
- RSA prefers more informative utterances
- Therefore: RSA predicts Global interpretation preferred

This matches the DE blocking pattern:
- Conditional antecedent = DE context
- Local SI would weaken the overall sentence
- Global interpretation is informationally stronger
- RSA derives preference for Global

## Contrast with Attitude Verbs

For attitude verbs:
- Local entails Global (opposite direction!)
- Neither is strictly more informative overall
- Both interpretations available

For conditionals (like "no one"):
- Global entails Local
- Global is more informative
- Global preferred
-/

/--
RSA predicts: in conditional antecedents, global is preferred over local.
This is the same prediction as for DE contexts under "no".
-/
theorem conditional_like_de_context :
    -- Global entails local (like DE)
    (∀ w, conditionalMeaning .global w = true → conditionalMeaning .local_ w = true) ∧
    -- But local doesn't entail global
    (∃ w, conditionalMeaning .local_ w = true ∧ conditionalMeaning .global w = false) := by
  constructor
  · exact global_entails_local
  · use ⟨.allP, .unhappy⟩
    decide

-- Summary

/-
## Results

1. **Conditional antecedents are DE**: Strengthening the antecedent weakens
   the conditional (contraposition).

2. **Global entails Local**: "If some passed, happy" → "If some-not-all passed, happy"

3. **RSA predicts Global preferred**: More informative interpretation wins.

4. **Same pattern as "no one"**: Both are DE contexts with same prediction.

## Connection to Linguistic Theory

This formalizes the observation that:
- Scalar implicatures are blocked in conditional antecedents
- "If some passed..." typically means "if any passed..."
- The "not all" inference is blocked, just like under negation

## Future Work

- Add full RSA computation with lexical uncertainty
- Compare predictions to experimental data
- Extend to other DE environments (restrictors of "every", etc.)
-/

end RSA.ConditionalEmbedding
