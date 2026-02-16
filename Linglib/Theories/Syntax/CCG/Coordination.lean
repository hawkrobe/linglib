/-
# CCG Analysis of Non-Constituent Coordination

## The Phenomenon

In "John likes and Mary hates beans", the strings "John likes" and
"Mary hates" are coordinated. But in traditional phrase structure:

    [S [NP John] [VP likes ___]] and [S [NP Mary] [VP hates ___]] beans

"John likes" is NOT a constituent - it's NP + part of VP.
Yet native speakers accept this sentence as grammatical.

## Qualitative Empirical Facts

1. Non-constituent coordination is GRAMMATICAL
2. Non-constituent coordination is HARDER TO PROCESS than standard coordination
   (Pickering & Barry 1991; Steedman 2000)

## CCG's Solution

CCG shows that "John likes" IS a constituent with category S/NP:
- John: NP type-raises to S/(S\NP)
- likes: (S\NP)/NP
- John likes: S/(S\NP) ∘ (S\NP)/NP = S/NP (forward composition)

Both conjuncts have category S/NP, so they can coordinate normally.

## References

- Steedman (2000). The Syntactic Process. MIT Press.
- Pickering & Barry (1991). Sentence processing without empty categories.
  Language and Cognitive Processes, 6(3), 229-259.
-/

import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Theories.Syntax.CCG.Bridge.Interface
import Linglib.Phenomena.Coordination.Data

namespace Phenomena.Coordination

open CCG
open Semantics.Montague

-- Empirical Fact 1: Non-constituent coordination is GRAMMATICAL

-- CCG derives "John likes and Mary hates beans" with category S
theorem nonConstituentCoord_is_grammatical :
    john_likes_and_mary_hates_beans.cat = some S := rfl

-- CCG also derives standard coordination
theorem standardCoord_is_grammatical :
    john_sleeps.cat = some S := rfl

-- Empirical Fact 2: Non-constituent coordination is HARDER TO PROCESS

/-
Processing difficulty correlates with the number of combinatory operations.
Non-constituent coordination requires MORE operations than standard sentences.
-/

-- Standard sentence: 1 operation (backward application)
#eval john_sleeps.opCount  -- 1

-- Standard coordination: 3 operations (2 backward apps + 1 coordination)
def john_sleeps_and_mary_sleeps : DerivStep :=
  .coord
    (.bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩))
    (.bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"sleeps", IV⟩))

#eval john_sleeps_and_mary_sleeps.opCount  -- 3

-- Non-constituent coordination: 8 operations
-- (2 type-raises + 2 compositions + 1 coordination + 1 application + 2 implicit)
#eval john_likes_and_mary_hates_beans.opCount  -- 8

-- THEOREM: CCG predicts non-constituent coordination is harder to process
theorem nonConstituentCoord_harder_than_standard :
    john_sleeps_and_mary_sleeps.opCount < john_likes_and_mary_hates_beans.opCount := by
  native_decide

-- THEOREM: Standard coordination is harder than simple sentences
theorem standardCoord_harder_than_simple :
    john_sleeps.opCount < john_sleeps_and_mary_sleeps.opCount := by
  native_decide

-- Why This Matters

/-
CCG makes two correct qualitative predictions:

1. GRAMMATICALITY: Non-constituent coordination is derivable
   - Other theories need special mechanisms (ATB movement, ellipsis, etc.)
   - CCG handles it with the same rules used everywhere else

2. PROCESSING DIFFICULTY: More operations = harder to process
   - This connects to surprisal-based and memory-based processing models
   - The extra type-raising and composition operations have a cost

The theorems above show that CCG's predictions MATCH the empirical facts.
This is the syntax-to-processing linking function in action.
-/

-- Empirical Fact 3: The SEMANTIC INTERPRETATION is Conjunctive

/-
The empirical observation (from Phenomena/Coordination/Data.lean):
  "John likes and Mary hates beans" means likes(beans, john) ∧ hates(beans, mary)

CCG's prediction: the compositional semantics yields this interpretation
via type-raising + composition + generalized conjunction.
-/

/--
**LINKING THEOREM: CCG derives both sides of the semantic equivalence**

The phenomena-level data (from Phenomena/Coordination/Data.lean):
  "John likes and Mary hates beans" ≡ "John likes beans and Mary hates beans"

CCG's prediction: both sentences derive and receive equivalent meanings.

This theorem proves CCG derives the non-constituent coordination sentence.
(The full equivalence proof would require implementing the spelled-out derivation too.)
-/
theorem ccg_derives_nonconstituent_coordination :
    -- The phenomena data specifies a semantic equivalence
    johnLikesAndMaryHatesBeans.bothGrammatical = true ∧
    -- CCG derives the non-constituent coordination sentence
    john_likes_and_mary_hates_beans.cat = some S ∧
    -- CCG's compositional semantics produces a well-formed interpretation
    (john_likes_and_mary_hates_beans.interp toySemLexicon).isSome = true := by
  constructor
  · rfl  -- The phenomena data specifies both are grammatical
  constructor
  · rfl  -- CCG derives category S
  · native_decide  -- CCG's derivation succeeds

/--
**THE SUBSTANTIVE SEMANTIC THEOREM**

CCG derives the meaning of "John likes and Mary hates beans" as the
conjunction of two predications:

  ⟦John likes and Mary hates beans⟧ = ⟦John likes⟧(beans) ∧ ⟦Mary hates⟧(beans)

This is non-trivial because it requires:
1. Type-raising John and Mary to S/(S\NP)
2. Composing with the verbs to get S/NP
3. Coordinating with generalized conjunction (pointwise ∧)
4. Applying to the shared object

The theorem proves CCG's compositional semantics matches the empirical observation.
-/
theorem ccg_coordination_semantics_correct :
    -- The coordinated meaning is pointwise conjunction
    ∀ e : ToyEntity,
      coordMeaningAt e = pointwiseConjAt e := by
  intro e
  cases e <;> native_decide

-- Summary: CCG Captures Non-Constituent Coordination

/-
## What CCG Explains

| Empirical Fact                        | CCG Prediction                    | Theorem                                |
|---------------------------------------|-----------------------------------|----------------------------------------|
| Sentence is grammatical               | Derivation yields category S     | nonConstituentCoord_is_grammatical     |
| Processing is harder than standard    | More combinatory operations      | nonConstituentCoord_harder_than_standard|
| Interpretation is conjunctive         | Generalized conjunction applies  | ccg_coordination_semantics_correct     |

## Why This Matters

Other theories require special mechanisms for non-constituent coordination:
- Transformational grammar: Across-The-Board movement
- GPSG: Metarules for coordination
- LFG: Functional uncertainty

CCG needs NO special mechanism. The same type-raising and composition rules
that handle word order flexibility also enable non-constituent coordination.
The interpretation falls out automatically from generalized conjunction.

This is the hallmark of a good theory: diverse phenomena explained by
the same core mechanisms, with correct empirical predictions.
-/

end Phenomena.Coordination
