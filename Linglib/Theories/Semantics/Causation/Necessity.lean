import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Core.Causal.SEM.Monotonicity
import Mathlib.Tactic.Use

/-!
# Causal Necessity
@cite{nadathur-2024} @cite{nadathur-lauer-2020}

Causal necessity semantics for the verb "cause." The core definition
`causallyNecessary` implements @cite{nadathur-2024} Definition 10b
(supersituation necessity with precondition + achievability + but-for),
superseding the simple but-for test from @cite{nadathur-lauer-2020}
Definition 24.

## Insight

"X caused Y" asserts that X was necessary for Y:
- Without X, Y would not have occurred (counterfactual dependence)
- X is a but-for cause: "but for X, not Y"

## Formal Definition (@cite{nadathur-2024} Def 10b)

⟨C, true⟩ is causally necessary for ⟨E, true⟩ relative to situation s iff:
- **Precondition**: s ⊭_D ⟨C, true⟩ and s ⊭_D ⟨E, true⟩
- **(i) Achievability**: ∃ consistent supersituation s' of s[C↦true]
  with E ∉ dom(s') where s' ⊨_D ⟨E, true⟩
- **(ii) But-for**: ¬∃ consistent supersituation s' of s with
  E ∉ dom(s') satisfying s' ⊨_D ⟨E, true⟩ while s' ⊭_D ⟨C, true⟩

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
| cause | Necessity (Def 10b) | No consistent supersituation achieves E without C |
| make | Sufficiency (Def 23) | Does adding C guarantee E? |

These can come apart in overdetermination cases:
- Lightning AND arsonist both present
- Lightning sufficient for fire
- Lightning NOT necessary (arsonist would have caused it anyway)

-/

namespace Semantics.Causation.Necessity

open Core.Causal
export Core.Causal (causallyNecessary)

/-- Semantics of "cause": effect occurred AND cause was necessary.
    Necessity uses @cite{nadathur-2024} Def 10b (supersituation test). -/
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
    precondition (c1, false) could inhibit the effect.

    Under Def 10b, this follows from the **precondition check**: if c2 is
    sufficient and present in s, then the effect is already causally entailed
    by s (via monotonicity), so the precondition `s ⊭_D ⟨effect, true⟩` fails. -/
theorem redundant_cause_not_necessary (dyn : CausalDynamics) (s : Situation)
    (c1 c2 effect : Variable)
    (hne : c1 ≠ c2)
    (hPos : isPositiveDynamics dyn = true)
    (h_c2_present : s.hasValue c2 true = true)
    (h_c2_sufficient : causallySufficient dyn (s.remove c1) c2 effect = true) :
    causallyNecessary dyn s c1 effect = false := by
  -- The effect is already causally entailed by s (via c2 + monotonicity)
  have h_effect_entailed : (normalDevelopment dyn s).hasValue effect true = true := by
    simp only [causallySufficient] at h_c2_sufficient
    have hLE : Situation.trueLE ((s.remove c1).extend c2 true) s := by
      intro v hv
      by_cases hvc1 : v = c1
      · subst hvc1
        rw [Situation.extend_hasValue_diff hne] at hv
        simp [Situation.hasValue, Situation.remove] at hv
      · by_cases hvc2 : v = c2
        · subst hvc2; exact h_c2_present
        · rw [Situation.extend_hasValue_diff hvc2] at hv
          have hbeq : (v == c1) = false := by
            rw [show (v == c1) = decide (v = c1) from rfl]
            exact decide_eq_false hvc1
          simp only [Situation.hasValue, Situation.remove, hbeq] at hv ⊢
          exact hv
    exact normalDevelopment_trueLE_positive dyn _ _ 100 hPos hLE effect h_c2_sufficient
  -- Def 10b returns false when effect is already entailed by s
  unfold causallyNecessary
  simp only [h_effect_entailed, Bool.or_true, ↓reduceIte]

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

-- ============================================================
-- § Actual Causation
-- ============================================================

/-- **Actual causation**: C factually occurred, E factually occurred, and
    C was causally necessary for E.

    Under @cite{nadathur-2024} Definition 10b, necessity must be tested
    against a background that does NOT contain the cause (the precondition
    rejects situations where cause is already entailed). We strip the cause
    from `s` via `s.remove cause` before passing to `causeSem`.

    This is the retrospective causal judgment: "did C actually cause E
    in situation s?" -/
def actuallyCaused (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  s.hasValue cause true &&
  causeSem dyn (s.remove cause) cause effect

/-- `actuallyCaused` is `causeSem` applied to the actual situation with
    the cause stripped from the background. -/
theorem actuallyCaused_eq_causeSem (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    actuallyCaused dyn s cause effect =
      (s.hasValue cause true && causeSem dyn (s.remove cause) cause effect) := rfl

/-- Actual causation implies the cause occurred. -/
theorem actual_cause_cause_occurred (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect = true) :
    s.hasValue cause true = true := by
  simp only [actuallyCaused, Bool.and_eq_true] at h; exact h.1

/-- Actual causation implies the effect occurred. -/
theorem actual_cause_effect_occurred (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect = true) :
    (normalDevelopment dyn ((s.remove cause).extend cause true)).hasValue effect true = true := by
  simp only [actuallyCaused, causeSem, Bool.and_eq_true] at h
  exact h.2.1

/-- Actual causation implies causal necessity. -/
theorem actual_cause_necessary (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect = true) :
    causallyNecessary dyn (s.remove cause) cause effect = true := by
  simp only [actuallyCaused, causeSem, Bool.and_eq_true] at h
  exact h.2.2

end Semantics.Causation.Necessity
