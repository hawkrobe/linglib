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

import Linglib.Core.CausalModel

namespace Theories.NadathurLauer2020.Sufficiency

open Core.CausalModel

-- Causal Sufficiency (Definition 23)

/--
**Causal Sufficiency** (Definition 23)

C is causally sufficient for E in situation s iff:
adding C to s and developing normally produces E.

Formally: E ∈ normalDevelopment(s ⊕ {C = true})

This captures the intuition that C *guarantees* E in the given background.
-/
def causallySufficient (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let sWithCause := s.extend cause true
  let developed := normalDevelopment dyn sWithCause
  developed.hasValue effect true

/--
Sufficiency with explicit background situation.
-/
def sufficientIn (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Bool :=
  causallySufficient dyn background cause effect

-- Semantics for "make"

/--
**Semantics of "make"** (causative verb asserting sufficiency)

"X made Y happen" is true iff:
1. X actually occurred (cause is true in developed situation)
2. X was causally sufficient for Y

The second condition is the core semantic content.
The first is typically presupposed/entailed by the assertion context.
-/
def makeSem (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) : Bool :=
  causallySufficient dyn background causeEvent effectEvent

/--
Extended semantics: make with explicit cause occurrence.

"X made Y happen" requires both:
1. X occurred (in the actual situation)
2. X was sufficient for Y
-/
def makeExtended (dyn : CausalDynamics) (actual background : Situation)
    (causeEvent effectEvent : Variable) : Bool :=
  actual.hasValue causeEvent true &&
  causallySufficient dyn background causeEvent effectEvent

-- Properties of Sufficiency

/-
Sufficiency is preserved under weaker backgrounds.

If C is sufficient for E in background s, and s' ⊆ s (s' has fewer determined values),
then C might still be sufficient in s' (but not guaranteed).

This captures: more specific backgrounds can only make sufficiency easier to achieve.
Note: The converse is more interesting for linguistic analysis.
-/

/--
Sufficiency with redundant causes: if C is sufficient, adding another cause D
doesn't change the sufficiency of C.
-/
theorem sufficiency_monotone_cause (dyn : CausalDynamics) (s : Situation)
    (c1 c2 effect : Variable) (h : causallySufficient dyn s c1 effect = true) :
    causallySufficient dyn (s.extend c2 true) c1 effect = true := by
  simp only [causallySufficient, Situation.extend, Situation.hasValue] at *
  -- The developed situation with both c1 and c2 should still have effect=true
  -- since c1 alone was sufficient
  sorry  -- Requires showing that adding c2 doesn't block c1's effect

/--
If nothing is sufficient for E in empty background, E cannot be caused.
-/
def uncausable (dyn : CausalDynamics) (effect : Variable) : Prop :=
  ∀ cause, causallySufficient dyn Situation.empty cause effect = false

-- Sufficiency and Effect Occurrence

/--
Sufficiency implies effect occurrence (after cause).

If C is sufficient for E, then adding C and developing produces E.
-/
theorem sufficient_implies_effect (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : causallySufficient dyn s cause effect = true) :
    developsToTrue dyn (s.extend cause true) effect = true := by
  simp only [causallySufficient, developsToTrue, developsToBe] at *
  exact h

/-
Sufficiency is about the counterfactual guarantee, not actual occurrence.

C can be sufficient for E even if:
- C hasn't occurred yet
- E has already occurred (from another cause)
-/

-- Weak vs Strong Sufficiency

/--
**Weak sufficiency**: C is sufficient for E in *some* compatible background.

This is a weaker notion: there exists a situation where C → E.
-/
def weaklySufficient (dyn : CausalDynamics) (cause effect : Variable) : Bool :=
  causallySufficient dyn Situation.empty cause effect

/--
**Strong sufficiency**: C is sufficient for E in *all* backgrounds.

This requires C → E regardless of other facts.
Rarely true in practice (usually background matters).
-/
def stronglySufficient (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  ∀ s, causallySufficient dyn s cause effect = true

/--
Strong sufficiency implies weak sufficiency.
-/
theorem strong_implies_weak (dyn : CausalDynamics) (cause effect : Variable)
    (h : stronglySufficient dyn cause effect) :
    weaklySufficient dyn cause effect = true := by
  simp only [weaklySufficient]
  exact h Situation.empty

-- Sufficiency in Different Causal Structures

/--
In disjunctive causation (A ∨ B → C), each disjunct is sufficient.
-/
theorem disjunctive_each_sufficient (a b c : Variable) (_ha : a ≠ b) :
    let dyn := CausalDynamics.disjunctiveCausation a b c
    causallySufficient dyn Situation.empty a c = true := by
  -- The first law (a → c) fires immediately, setting c=true. The result is a fixpoint.
  -- TODO: Prove using normalDevelopment_fixpoint_after_one + applyLawsOnce unfolding
  sorry

/--
In conjunctive causation (A ∧ B → C), neither alone is sufficient (in empty background).
-/
theorem conjunctive_neither_sufficient_alone (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    let dyn := CausalDynamics.conjunctiveCausation a b c
    causallySufficient dyn Situation.empty a c = false := by
  -- a alone doesn't trigger the conjunctive law
  sorry  -- Requires showing the law doesn't fire without b

/--
In conjunctive causation, A is sufficient when B is already in the background.
-/
theorem conjunctive_sufficient_with_other (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    let dyn := CausalDynamics.conjunctiveCausation a b c
    let background := Situation.empty.extend b true
    causallySufficient dyn background a c = true := by
  -- With b=true in background, adding a triggers the law
  sorry  -- Requires showing the conjunctive law fires

end Theories.NadathurLauer2020.Sufficiency
