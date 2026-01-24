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

import LingLean.Syntax.CCG.Basic

namespace Phenomena.Coordination

open CCG

-- ============================================================================
-- Empirical Fact 1: Non-constituent coordination is GRAMMATICAL
-- ============================================================================

-- CCG derives "John likes and Mary hates beans" with category S
theorem nonConstituentCoord_is_grammatical :
    john_likes_and_mary_hates_beans.cat = some S := rfl

-- CCG also derives standard coordination
theorem standardCoord_is_grammatical :
    john_sleeps.cat = some S := rfl

-- ============================================================================
-- Empirical Fact 2: Non-constituent coordination is HARDER TO PROCESS
-- ============================================================================

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

-- ============================================================================
-- Why This Matters
-- ============================================================================

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

end Phenomena.Coordination
