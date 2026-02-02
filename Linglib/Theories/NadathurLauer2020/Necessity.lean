/-
# Causal Necessity

Causal necessity semantics for the verb "cause" based on
Nadathur & Lauer (2020) Definition 24.

## Key Insight

"X caused Y" asserts that X was **necessary** for Y:
- Without X, Y would not have occurred (counterfactual dependence)
- X is a but-for cause: "but for X, not Y"

## Formal Definition (Def 24)

C is **causally necessary** for E in situation s iff:
  normalDevelopment(s ⊕ {C = false}) does NOT include E = true

In other words: if we remove C (or set it false), E doesn't happen.

## Linguistic Examples

1. "The short circuit caused the fire"
   - Without the short circuit, the fire wouldn't have started
   - The short circuit was necessary (in that context)

2. "Kim's actions caused Sandy to leave"
   - If Kim hadn't acted, Sandy would have stayed
   - Kim's action was a but-for cause

## Necessity vs Sufficiency

| Verb | Semantics | Test |
|------|-----------|------|
| cause | Necessity | Would E happen without C? |
| make | Sufficiency | Does adding C guarantee E? |

These can come apart in overdetermination cases:
- Lightning AND arsonist both present
- Lightning sufficient for fire
- Lightning NOT necessary (arsonist would have caused it anyway)

## References

- Nadathur & Lauer (2020), Section 5.2
- Lewis (1973). Counterfactuals.
-/

import Linglib.Core.CausalModel
import Linglib.Theories.NadathurLauer2020.Sufficiency

namespace Theories.NadathurLauer2020.Necessity

open Core.CausalModel
open Theories.NadathurLauer2020.Sufficiency

-- ============================================================================
-- Causal Necessity (Definition 24)
-- ============================================================================

/--
**Causal Necessity** (Definition 24)

C is causally necessary for E in situation s iff:
removing C (setting it false) and developing normally does NOT produce E.

Formally: E ∉ normalDevelopment(s ⊕ {C = false})

This is the counterfactual test: "but for C, E would not have occurred."
-/
def causallyNecessary (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let sWithoutCause := s.extend cause false
  let developed := normalDevelopment dyn sWithoutCause
  -- E should NOT become true without C
  !developed.hasValue effect true

/--
Necessity with explicit background situation.
-/
def necessaryIn (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Bool :=
  causallyNecessary dyn background cause effect

-- ============================================================================
-- Semantics for "cause"
-- ============================================================================

/--
**Semantics of "cause"** (causative verb asserting necessity)

"X caused Y" is true iff:
1. Y actually occurred (effect is true in developed situation)
2. X was causally necessary for Y
3. (Implicitly) X actually occurred

The core semantic content is the counterfactual dependence.
-/
def causeSem (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) : Bool :=
  let withCause := background.extend causeEvent true
  let developed := normalDevelopment dyn withCause
  -- Effect occurred AND cause was necessary
  developed.hasValue effectEvent true &&
  causallyNecessary dyn background causeEvent effectEvent

/--
Extended cause semantics with explicit actual situation.

"X caused Y" requires:
1. X occurred
2. Y occurred (after X)
3. Y counterfactually depended on X
-/
def causeExtended (dyn : CausalDynamics) (actual background : Situation)
    (causeEvent effectEvent : Variable) : Bool :=
  actual.hasValue causeEvent true &&
  actual.hasValue effectEvent true &&
  causallyNecessary dyn background causeEvent effectEvent

-- ============================================================================
-- Properties of Necessity
-- ============================================================================

/-
Necessity is sensitive to background: the same cause may be necessary
in one background but not in another (overdetermination).
-/

/--
If there's an alternative sufficient cause in the background,
the original cause may not be necessary.
-/
theorem redundant_cause_not_necessary (dyn : CausalDynamics) (s : Situation)
    (c1 c2 effect : Variable)
    (h_c2_present : s.hasValue c2 true = true)
    (h_c2_sufficient : causallySufficient dyn (s.remove c1) c2 effect = true) :
    causallyNecessary dyn s c1 effect = false := by
  simp only [causallyNecessary, causallySufficient] at *
  -- Without c1, c2 still causes effect
  sorry  -- Requires showing c2 fires even without c1

-- ============================================================================
-- Necessity and Sufficiency Interaction
-- ============================================================================

/--
**Key theorem**: Sufficiency does NOT imply necessity.

A cause can be sufficient (adding it guarantees the effect)
without being necessary (removing it might not prevent the effect).

This is the overdetermination case.
-/
theorem sufficiency_not_implies_necessity :
    ∃ (dyn : CausalDynamics) (s : Situation) (cause effect : Variable),
      causallySufficient dyn s cause effect = true ∧
      causallyNecessary dyn s cause effect = false := by
  -- Witness: disjunctive causation with both causes present
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  let dyn := CausalDynamics.disjunctiveCausation a b c
  let s := Situation.empty.extend b true  -- b is already present
  use dyn, s, a, c
  constructor
  · -- a is sufficient (a → c)
    simp only [causallySufficient]
    sorry  -- a triggers its law
  · -- a is NOT necessary (b would cause c anyway)
    simp only [causallyNecessary]
    sorry  -- Without a, b still causes c

/--
**Key theorem**: Necessity does NOT imply sufficiency.

A cause can be necessary (removing it prevents the effect)
without being sufficient (adding it alone might not guarantee the effect).

This happens with conjunctive causes or enabling conditions.
-/
theorem necessity_not_implies_sufficiency :
    ∃ (dyn : CausalDynamics) (s : Situation) (cause effect : Variable),
      causallyNecessary dyn s cause effect = true ∧
      causallySufficient dyn Situation.empty cause effect = false := by
  -- Witness: conjunctive causation where only one conjunct is tested
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  let dyn := CausalDynamics.conjunctiveCausation a b c
  let s := Situation.empty.extend b true  -- b is present
  use dyn, s, a, c
  constructor
  · -- a is necessary (without a, the conjunctive law doesn't fire)
    simp only [causallyNecessary]
    sorry
  · -- a is NOT sufficient in empty background (needs b too)
    simp only [causallySufficient]
    sorry

-- ============================================================================
-- The INUS Condition
-- ============================================================================

/--
An **INUS cause** is:
- Insufficient but Necessary part of an
- Unnecessary but Sufficient condition

This is Mackie's analysis of causation.
C is an INUS cause of E if there exists a set of conditions X such that:
1. C ∪ X is sufficient for E
2. C is necessary within C ∪ X
3. C ∪ X is not necessary for E (there could be other sufficient sets)
-/
def isINUSCause (dyn : CausalDynamics) (cause effect : Variable)
    (enablingConditions : Situation) : Bool :=
  -- C + enabling conditions is sufficient
  causallySufficient dyn enablingConditions cause effect &&
  -- C is necessary given the enabling conditions
  causallyNecessary dyn enablingConditions cause effect &&
  -- C alone is NOT sufficient (it needs the enabling conditions)
  !causallySufficient dyn Situation.empty cause effect

-- ============================================================================
-- But-For Causation
-- ============================================================================

/--
**But-for causation**: C is a but-for cause of E in s iff
"but for C, E would not have occurred."

This is just necessity with a different framing.
-/
abbrev butForCause (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  causallyNecessary dyn s cause effect

/--
All but-for causes are necessary causes.
-/
theorem butfor_eq_necessary (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    butForCause dyn s cause effect = causallyNecessary dyn s cause effect := rfl

-- ============================================================================
-- Actual Causation
-- ============================================================================

/--
**Actual causation**: A full analysis combining necessity and actuality.

C actually caused E in situation s iff:
1. C occurred (C = true in s)
2. E occurred (E = true in developed s)
3. C was necessary for E (counterfactual dependence)
-/
def actuallyCaused (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let developed := normalDevelopment dyn s
  s.hasValue cause true &&
  developed.hasValue effect true &&
  causallyNecessary dyn s cause effect

/--
Actual causation implies the effect occurred.
-/
theorem actual_cause_effect_occurred (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect = true) :
    (normalDevelopment dyn s).hasValue effect true = true := by
  simp only [actuallyCaused, Bool.and_eq_true] at h
  exact h.1.2

/--
Actual causation implies the cause occurred.
-/
theorem actual_cause_cause_occurred (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect = true) :
    s.hasValue cause true = true := by
  simp only [actuallyCaused, Bool.and_eq_true] at h
  exact h.1.1

end Theories.NadathurLauer2020.Necessity
