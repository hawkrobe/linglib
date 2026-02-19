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
import Linglib.Theories.Semantics.Causation.Sufficiency

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

/-- An alternative sufficient cause makes the original unnecessary.

    Requires positive dynamics (no inhibitory connections) and c1 ≠ c2: in positive
    dynamics, setting c1 = false doesn't trigger new laws, so the sufficient
    alternative c2 still fires the effect. Without positivity, a law with
    precondition (c1, false) could inhibit the effect. -/
theorem redundant_cause_not_necessary (dyn : CausalDynamics) (s : Situation)
    (c1 c2 effect : Variable)
    (hne : c1 ≠ c2)
    (hPos : isPositiveDynamics dyn = true)
    (h_c2_present : s.hasValue c2 true = true)
    (h_c2_sufficient : causallySufficient dyn (s.remove c1) c2 effect = true) :
    causallyNecessary dyn s c1 effect = false := by
  -- Suffices to show effect develops to true even without c1
  suffices h : (normalDevelopment dyn (s.extend c1 false)).hasValue effect true = true by
    show (!(normalDevelopment dyn (s.extend c1 false)).hasValue effect true) = false
    rw [h]; rfl
  simp only [causallySufficient] at h_c2_sufficient
  -- Key: trueLE ((s.remove c1).extend c2 true) (s.extend c1 false)
  -- In positive dynamics, c1=false vs c1=none makes no difference (no inhibitory laws),
  -- and c2 is true in both situations.
  have hLE : Situation.trueLE ((s.remove c1).extend c2 true) (s.extend c1 false) := by
    intro v hv
    by_cases hvc1 : v = c1
    · -- v = c1: after remove, c1 is none → hasValue c1 true = false, contradiction
      rw [hvc1] at hv
      rw [Situation.extend_hasValue_diff hne] at hv
      simp [Situation.hasValue, Situation.remove] at hv
    · by_cases hvc2 : v = c2
      · rw [hvc2]
        rw [Situation.extend_hasValue_diff (Ne.symm hne)]
        exact h_c2_present
      · -- v ≠ c1, v ≠ c2: remove c1 doesn't affect v
        rw [Situation.extend_hasValue_diff hvc2] at hv
        rw [Situation.extend_hasValue_diff hvc1]
        have hbeq : (v == c1) = false := by
          rw [show (v == c1) = decide (v = c1) from rfl]
          exact decide_eq_false hvc1
        simp only [Situation.hasValue, Situation.remove, hbeq] at hv ⊢
        exact hv
  exact normalDevelopment_trueLE_positive dyn _ _ 100 hPos hLE effect h_c2_sufficient

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
  exact ⟨by native_decide, by native_decide⟩

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
  exact ⟨by native_decide, by native_decide⟩

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
