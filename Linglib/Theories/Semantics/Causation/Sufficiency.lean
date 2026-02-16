/-
# Causal Sufficiency

Causal sufficiency semantics for the verb "make" based on
Nadathur & Lauer (2020) Definition 23.

## Insight

"X made Y happen" asserts that X was **sufficient** for Y:
- Given the background situation, adding X guarantees Y
- The effect is inevitable once the cause is in place

## Formal Definition (Def 23)

C is **causally sufficient** for E in situation s iff:
  normalDevelopment(s ⊕ {C = true}) includes E = true

In other words: if we add C to the background, E necessarily follows.

## Linguistic Examples

1. "Kim made Sandy leave"
   - Kim's action (persuasion, coercion, etc.) was sufficient for Sandy leaving
   - Once Kim acted, Sandy's departure was guaranteed

2. "The short circuit made the fire start"
   - The short circuit alone was enough to cause the fire
   - No other conditions needed (beyond background)

## References

- Nadathur & Lauer (2020), Section 5.1
-/

import Linglib.Core.Causation

namespace NadathurLauer2020.Sufficiency

open Core.Causation
export Core.Causation (causallySufficient)

/-- Semantics of "make": X was causally sufficient for Y (N&L 2020 §5.1). -/
def makeSem (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) : Bool :=
  causallySufficient dyn background causeEvent effectEvent

/-- Adding another cause doesn't change C's sufficiency. -/
theorem sufficiency_monotone_cause (dyn : CausalDynamics) (s : Situation)
    (c1 c2 effect : Variable) (h : causallySufficient dyn s c1 effect = true) :
    causallySufficient dyn (s.extend c2 true) c1 effect = true := by
  simp only [causallySufficient, Situation.extend, Situation.hasValue] at *
  -- The developed situation with both c1 and c2 should still have effect=true
  -- since c1 alone was sufficient
  sorry  -- Requires showing that adding c2 doesn't block c1's effect

/-- Sufficiency implies effect occurrence (after cause). -/
theorem sufficient_implies_effect (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : causallySufficient dyn s cause effect = true) :
    developsToTrue dyn (s.extend cause true) effect = true := by
  simp only [causallySufficient, developsToTrue, developsToBe] at *
  exact h

/-- In disjunctive causation (A ∨ B → C), each disjunct is sufficient. -/
theorem disjunctive_each_sufficient (a b c : Variable) (_ha : a ≠ b) :
    let dyn := CausalDynamics.disjunctiveCausation a b c
    causallySufficient dyn Situation.empty a c = true := by
  -- The first law (a → c) fires immediately, setting c=true. The result is a fixpoint.
  -- TODO: Prove using normalDevelopment_fixpoint_after_one + applyLawsOnce unfolding
  sorry

/-- In conjunctive causation (A ∧ B → C), neither alone is sufficient. -/
theorem conjunctive_neither_sufficient_alone (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    let dyn := CausalDynamics.conjunctiveCausation a b c
    causallySufficient dyn Situation.empty a c = false := by
  -- a alone doesn't trigger the conjunctive law
  sorry  -- Requires showing the law doesn't fire without b

/-- In conjunctive causation, A is sufficient when B is in the background. -/
theorem conjunctive_sufficient_with_other (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    let dyn := CausalDynamics.conjunctiveCausation a b c
    let background := Situation.empty.extend b true
    causallySufficient dyn background a c = true := by
  -- With b=true in background, adding a triggers the law
  sorry  -- Requires showing the conjunctive law fires

end NadathurLauer2020.Sufficiency
