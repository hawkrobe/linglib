/-
# Number Word Semantics

Two competing semantic backends for number words:
1. **Lower-bound semantics** (Horn 1972): "two" means ≥2
2. **Exact semantics**: "two" means exactly 2

Both implement `FiniteSemanticBackend` so they can be used with RSA.

The empirical data from Goodman & Stuhlmüller (2013) Experiment 2
shows that lower-bound semantics is correct: interpretation varies
with speaker's knowledge state, which is only possible if there's
an implicature to cancel.
-/

import Linglib.Core.RSA

namespace Semantics.Numbers

-- ============================================================================
-- Shared Types
-- ============================================================================

/-- World states: how many (of 3) have the property -/
inductive NumWorld where
  | n0 | n1 | n2 | n3
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Number word utterances -/
inductive NumUtterance where
  | one | two | three
  deriving DecidableEq, BEq, Repr, Inhabited

def allNumWorlds : List NumWorld := [.n0, .n1, .n2, .n3]
def allNumUtterances : List NumUtterance := [.one, .two, .three]

-- ============================================================================
-- Lower-Bound Semantics Backend
-- ============================================================================

namespace LowerBound

/-- Lower-bound meaning: "n" means ≥n -/
def meaning : NumUtterance → NumWorld → Bool
  | .one, .n0 => false
  | .one, _ => true      -- ≥1
  | .two, .n0 => false
  | .two, .n1 => false
  | .two, _ => true      -- ≥2
  | .three, .n3 => true  -- ≥3 (only n3)
  | .three, _ => false

/-- Lower-bound semantics as a FiniteSemanticBackend -/
def Backend : Type := Unit

instance : RSA.FiniteSemanticBackend Backend where
  Utterance := NumUtterance
  World := NumWorld
  utterances := allNumUtterances
  worlds := allNumWorlds
  meaning := meaning
  utteranceBEq := inferInstance
  worldBEq := inferInstance

-- Key property: "two" is compatible with multiple worlds
theorem two_ambiguous :
    (allNumWorlds.filter (meaning .two)).length = 2 := by
  native_decide

theorem two_compatible_worlds :
    allNumWorlds.filter (meaning .two) = [.n2, .n3] := by
  native_decide

end LowerBound

-- ============================================================================
-- Exact Semantics Backend
-- ============================================================================

namespace Exact

/-- Exact meaning: "n" means exactly n -/
def meaning : NumUtterance → NumWorld → Bool
  | .one, .n1 => true
  | .one, _ => false     -- exactly 1
  | .two, .n2 => true
  | .two, _ => false     -- exactly 2
  | .three, .n3 => true
  | .three, _ => false   -- exactly 3

/-- Exact semantics as a FiniteSemanticBackend -/
def Backend : Type := Unit

instance : RSA.FiniteSemanticBackend Backend where
  Utterance := NumUtterance
  World := NumWorld
  utterances := allNumUtterances
  worlds := allNumWorlds
  meaning := meaning
  utteranceBEq := inferInstance
  worldBEq := inferInstance

-- Key property: "two" is compatible with only ONE world
theorem two_unambiguous :
    (allNumWorlds.filter (meaning .two)).length = 1 := by
  native_decide

theorem two_compatible_worlds :
    allNumWorlds.filter (meaning .two) = [.n2] := by
  native_decide

end Exact

-- ============================================================================
-- The Critical Difference
-- ============================================================================

/--
**Semantic Backends Differ on Ambiguity**

Lower-bound: "two" compatible with {n2, n3} - ambiguity exists
Exact: "two" compatible with {n2} only - no ambiguity

Implicature can only arise (and be canceled) if there's ambiguity.
-/
theorem backends_differ_on_ambiguity :
    (allNumWorlds.filter (LowerBound.meaning .two)).length ≠
    (allNumWorlds.filter (Exact.meaning .two)).length := by
  native_decide

/--
**Only Lower-Bound Has Ambiguity to Resolve**

If there's no literal ambiguity, RSA has nothing to do.
The "exactly 2" interpretation is built-in, not derived.
-/
theorem lowerbound_has_ambiguity_exact_doesnt :
    (allNumWorlds.filter (LowerBound.meaning .two)).length > 1 ∧
    (allNumWorlds.filter (Exact.meaning .two)).length = 1 := by
  native_decide

-- ============================================================================
-- Implications for RSA
-- ============================================================================

/-
## How This Affects RSA Predictions

**With Lower-Bound Backend:**
- L0("two") assigns uniform probability to {n2, n3}
- S1 in world n2 prefers "two" (it's informative)
- S1 in world n3 prefers "three" (more informative than "two")
- L1("two") infers n2 more likely than n3 → implicature emerges
- With partial access: speaker might not know if n3, so implicature canceled

**With Exact Backend:**
- L0("two") assigns probability 1 to n2, 0 elsewhere
- No matter what S1 does, "two" already means exactly n2
- L1("two") will always strongly prefer n2
- Partial access doesn't change anything - no implicature to cancel

The empirical data shows cancellation → Lower-bound is correct.
-/

end Semantics.Numbers
