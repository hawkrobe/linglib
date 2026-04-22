import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Core.Causal.SEM.Monotonicity
import Mathlib.Tactic.Use

/-!
# Causal Necessity
@cite{nadathur-2024} @cite{nadathur-lauer-2020} @cite{schulz-2011}

Causal necessity semantics for the verb "cause." The core definition
`causallyNecessary` implements @cite{nadathur-2024} Definition 10b
(supersituation necessity with precondition + achievability + but-for),
superseding the simple but-for test from @cite{nadathur-lauer-2020}
Definition 24.

## Insight

"X caused Y" asserts that X was necessary for Y:
- Without X, Y would not have occurred (counterfactual dependence)
- X is a but-for cause: "but for X, not Y"

## Necessity vs Sufficiency

| Verb | Semantics | Test |
|------|-----------|------|
| cause | Necessity (Def 10b) | No consistent supersituation achieves E without C |
| make | Sufficiency (Def 23) | Does adding C guarantee E? |
-/

namespace Semantics.Causation.Necessity

open Core.Causal
export Core.Causal (causallyNecessary)

/-- Semantics of "cause": effect occurred AND cause was necessary.
    Necessity uses @cite{nadathur-2024} Def 10b (supersituation test). -/
def causeSem (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) : Prop :=
  (normalDevelopment dyn (background.extend causeEvent true)).hasValue effectEvent true ∧
  causallyNecessary dyn background causeEvent effectEvent

instance (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) :
    Decidable (causeSem dyn background causeEvent effectEvent) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Sufficiency does NOT imply necessity (overdetermination). -/
theorem sufficiency_not_implies_necessity :
    ∃ (dyn : CausalDynamics) (s : Situation) (cause effect : Variable),
      causallySufficient dyn s cause effect ∧
      ¬ (causallyNecessary dyn s cause effect) := by
  refine ⟨CausalDynamics.disjunctiveCausation (mkVar "a") (mkVar "b") (mkVar "c"),
          Situation.empty.extend (mkVar "b") true,
          mkVar "a", mkVar "c", ?_, ?_⟩
  · native_decide
  · native_decide

/-- Necessity does NOT imply sufficiency (conjunctive causes). -/
theorem necessity_not_implies_sufficiency :
    ∃ (dyn : CausalDynamics) (s : Situation) (cause effect : Variable),
      causallyNecessary dyn s cause effect ∧
      ¬ (causallySufficient dyn Situation.empty cause effect) := by
  refine ⟨CausalDynamics.conjunctiveCausation (mkVar "a") (mkVar "b") (mkVar "c"),
          Situation.empty.extend (mkVar "b") true,
          mkVar "a", mkVar "c", ?_, ?_⟩
  · native_decide
  · native_decide

/-- INUS cause (Mackie): insufficient but necessary part of an
    unnecessary but sufficient condition. -/
def isINUSCause (dyn : CausalDynamics) (cause effect : Variable)
    (enablingConditions : Situation) : Prop :=
  causallySufficient dyn enablingConditions cause effect ∧
  causallyNecessary dyn enablingConditions cause effect ∧
  ¬ causallySufficient dyn Situation.empty cause effect

instance (dyn : CausalDynamics) (cause effect : Variable) (enablingConditions : Situation) :
    Decidable (isINUSCause dyn cause effect enablingConditions) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

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
    (cause effect : Variable) : Prop :=
  s.hasValue cause true ∧
  causeSem dyn (s.remove cause) cause effect

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (actuallyCaused dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `actuallyCaused` is `causeSem` applied to the actual situation with
    the cause stripped from the background. -/
theorem actuallyCaused_iff_causeSem (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    actuallyCaused dyn s cause effect ↔
      (s.hasValue cause true ∧ causeSem dyn (s.remove cause) cause effect) :=
  Iff.rfl

/-- Actual causation implies the cause occurred. -/
theorem actual_cause_cause_occurred (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect) :
    s.hasValue cause true := h.1

/-- Actual causation implies the effect occurred. -/
theorem actual_cause_effect_occurred (dyn : CausalDynamics)
    (s : Situation) (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect) :
    (normalDevelopment dyn ((s.remove cause).extend cause true)).hasValue effect true :=
  h.2.1

/-- Actual causation implies causal necessity. -/
theorem actual_cause_necessary (dyn : CausalDynamics)
    (s : Situation) (cause effect : Variable)
    (h : actuallyCaused dyn s cause effect) :
    causallyNecessary dyn (s.remove cause) cause effect :=
  h.2.2

end Semantics.Causation.Necessity
