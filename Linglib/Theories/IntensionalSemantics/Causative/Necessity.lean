/-
# Causal Necessity

Causal necessity semantics for the verb "cause" based on
Nadathur & Lauer (2020) Definition 24.

## Insight

"X caused Y" asserts that X was necessary for Y:
- Without X, Y would not have occurred (counterfactual dependence)
- X is a but-for cause: "but for X, not Y"

## Formal Definition (Def 24)

C is causally necessary for E in situation s iff:
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

import Linglib.Core.Causation
import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency

namespace NadathurLauer2020.Necessity

open Core.Causation
export Core.Causation (causallyNecessary)
open NadathurLauer2020.Sufficiency

/-- Semantics of "cause": effect occurred AND cause was necessary (N&L 2020 §5.2). -/
def causeSem (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) : Bool :=
  let withCause := background.extend causeEvent true
  let developed := normalDevelopment dyn withCause
  -- Effect occurred AND cause was necessary
  developed.hasValue effectEvent true &&
  causallyNecessary dyn background causeEvent effectEvent

/-- An alternative sufficient cause makes the original unnecessary. -/
theorem redundant_cause_not_necessary (dyn : CausalDynamics) (s : Situation)
    (c1 c2 effect : Variable)
    (h_c2_present : s.hasValue c2 true = true)
    (h_c2_sufficient : causallySufficient dyn (s.remove c1) c2 effect = true) :
    causallyNecessary dyn s c1 effect = false := by
  simp only [causallyNecessary, causallySufficient] at *
  -- Without c1, c2 still causes effect
  sorry  -- Requires showing c2 fires even without c1

/-- Sufficiency does NOT imply necessity (overdetermination). -/
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

/-- Necessity does NOT imply sufficiency (conjunctive causes). -/
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

/-- INUS cause (Mackie): insufficient but necessary part of an
    unnecessary but sufficient condition. -/
def isINUSCause (dyn : CausalDynamics) (cause effect : Variable)
    (enablingConditions : Situation) : Bool :=
  -- C + enabling conditions is sufficient
  causallySufficient dyn enablingConditions cause effect &&
  -- C is necessary given the enabling conditions
  causallyNecessary dyn enablingConditions cause effect &&
  -- C alone is NOT sufficient (it needs the enabling conditions)
  !causallySufficient dyn Situation.empty cause effect

/-- Actual causation: C occurred, E occurred, and C was necessary. -/
def actuallyCaused (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  factuallyDeveloped dyn s cause effect &&
  causallyNecessary dyn s cause effect

/-- Actual causation implies the effect occurred. -/
theorem actual_cause_effect_occurred (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect = true) :
    (normalDevelopment dyn s).hasValue effect true = true := by
  simp only [actuallyCaused, factuallyDeveloped, Bool.and_eq_true] at h
  exact h.1.2

/-- Actual causation implies the cause occurred. -/
theorem actual_cause_cause_occurred (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect = true) :
    s.hasValue cause true = true := by
  simp only [actuallyCaused, factuallyDeveloped, Bool.and_eq_true] at h
  exact h.1.1

end NadathurLauer2020.Necessity
