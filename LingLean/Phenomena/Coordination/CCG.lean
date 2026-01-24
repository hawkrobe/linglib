/-
# CCG Analysis of Non-Constituent Coordination

CCG's treatment of coordination is one of its most celebrated results.
Unlike phrase structure grammars, CCG can coordinate "non-constituents"
like "John likes" and "Mary hates" in "John likes and Mary hates beans".

## The Key Insight

What looks like a non-constituent in phrase structure grammar is
actually a constituent in CCG. Through type-raising and composition,
"John likes" has category S/NP - a perfectly legitimate constituent.

## Predictions

1. **Categorical**: Coordination of matching categories is grammatical
2. **Graded**: More complex derivations (more type-raising/composition) = lower acceptability
3. **Processing**: Composition operations incur incremental processing cost

## References

- Steedman (2000). The Syntactic Process. MIT Press.
- Steedman & Baldridge (2011). Combinatory Categorial Grammar.
-/

import LingLean.Syntax.CCG.Basic
import LingLean.Phenomena.EmpiricalData

namespace Phenomena.Coordination

open CCG
open Phenomena

-- ============================================================================
-- Example: Derivation Complexity Comparison
-- ============================================================================

-- "John sleeps" - simple (1 operation: backward app)
#eval john_sleeps.opCount   -- 1
#eval john_sleeps.depth     -- 2

-- "John likes and Mary hates beans" - complex (type-raising + composition + coord)
#eval john_likes_and_mary_hates_beans.opCount  -- 7
#eval john_likes_and_mary_hates_beans.depth    -- 4

-- Prediction: "John likes and Mary hates beans" should be harder to process
-- than simple SVO sentences, due to the extra combinatory operations.

-- ============================================================================
-- CCG Graded Linking: Complexity → Acceptability
-- ============================================================================

/-- Transform operation count to predicted acceptability (1-7 scale)
    Assumption: Higher complexity → lower acceptability (negative correlation)
    Using a simple linear transformation: 7 - k * opCount, clamped to [1,7] -/
def predictAcceptabilityFromOps (opCount : Nat) (k : Float := 0.5) : Float :=
  let raw := 7.0 - k * opCount.toFloat
  max 1.0 (min 7.0 raw)

#eval predictAcceptabilityFromOps 1   -- 6.5 (simple sentence)
#eval predictAcceptabilityFromOps 7   -- 3.5 (complex coordination)

-- ============================================================================
-- CCG Processing Linking: Incremental Complexity
-- ============================================================================

/-
In CCG, processing difficulty can be modeled as the cost of building
structure incrementally. Key sources of difficulty:
1. Type-raising: recognizing the need to type-raise
2. Composition: combining partial structures
3. Holding incomplete dependencies: memory cost for S/NP waiting for NP

This connects to surprisal-based models and memory-based models
like Gibson's Dependency Locality Theory (DLT).
-/

/-- Incremental state during CCG parsing -/
structure IncrementalState where
  /-- Categories waiting for arguments -/
  stack : List CCG.Cat
  /-- Number of operations performed -/
  ops : Nat
  deriving Repr

/-- Processing cost at a word: stack depth + operations needed -/
def incrementalCost (state : IncrementalState) : Float :=
  state.stack.length.toFloat + state.ops.toFloat

-- ============================================================================
-- Comparison: Standard Coordination vs Non-Constituent
-- ============================================================================

/-
Standard S coordination:
  "John sleeps and Mary sleeps"

  John:NP sleeps:S\NP  and  Mary:NP sleeps:S\NP
       └──<──┘                    └──<──┘
          S            conj          S
          └────────────Φ─────────────┘
                       S

Operations: 2 backward apps + 1 coordination = 3 ops
-/

def john_sleeps_and_mary_sleeps : DerivStep :=
  .coord
    (.bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩))
    (.bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"sleeps", IV⟩))

#eval john_sleeps_and_mary_sleeps.cat      -- some S ✓
#eval john_sleeps_and_mary_sleeps.opCount  -- 3

/-
Non-constituent coordination:
  "John likes and Mary hates beans"

  John  likes  and  Mary  hates  beans
   NP   S\NP/NP          NP    S\NP/NP   NP
   ↓>T                   ↓>T
  S/S\NP                S/S\NP
    └──>B──┘              └──>B──┘
      S/NP        conj      S/NP
      └───────────Φ─────────┘
                S/NP
                └────────>────────┘
                         S

Operations: 2 type-raises + 2 compositions + 1 coordination + 1 app = 7 ops
-/

-- Prediction: Non-constituent coordination is harder than standard coordination
example : john_sleeps_and_mary_sleeps.opCount < john_likes_and_mary_hates_beans.opCount := by
  native_decide

-- ============================================================================
-- Graded Acceptability Predictions
-- ============================================================================

/-- Predicted acceptability for simple sentence -/
def simpleSentenceAcceptability : Float :=
  predictAcceptabilityFromOps john_sleeps.opCount

/-- Predicted acceptability for standard coordination -/
def standardCoordAcceptability : Float :=
  predictAcceptabilityFromOps john_sleeps_and_mary_sleeps.opCount

/-- Predicted acceptability for non-constituent coordination -/
def nonConstituentCoordAcceptability : Float :=
  predictAcceptabilityFromOps john_likes_and_mary_hates_beans.opCount

#eval simpleSentenceAcceptability         -- 6.5
#eval standardCoordAcceptability          -- 5.5
#eval nonConstituentCoordAcceptability    -- 3.5

-- Prediction ordering: simple > standard coord > non-constituent coord
example : simpleSentenceAcceptability > standardCoordAcceptability := by native_decide
example : standardCoordAcceptability > nonConstituentCoordAcceptability := by native_decide

-- ============================================================================
-- Theoretical Insight
-- ============================================================================

/-
CCG's analysis makes several testable predictions:

1. **Categorical**: Non-constituent coordination is grammatical when
   categories match after type-raising and composition. This predicts:
   - ✓ "John likes and Mary hates beans" (S/NP coord S/NP)
   - ✗ "John likes and Mary sleeps beans" (S/NP cannot coord with S)

2. **Graded**: Acceptability correlates negatively with derivation complexity.
   Non-constituent coordination requires more operations, so it should be
   rated slightly lower than simple sentences (while still grammatical).

3. **Processing**: Reading times should be elevated at the coordination
   point and object, due to:
   - Memory cost of maintaining incomplete S/NP
   - Integration cost when the shared object is encountered

These predictions distinguish CCG from theories that treat "John likes"
as a non-constituent that requires special mechanisms to coordinate.
-/

end Phenomena.Coordination
