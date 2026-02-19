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

-- ============================================================
-- § Positive Dynamics: monotonicity condition
-- ============================================================

/-- Standard constructors produce positive dynamics. -/
theorem simple_isPositive (a b : Variable) :
    isPositiveDynamics ⟨[CausalLaw.simple a b]⟩ = true := rfl

theorem conjunctive_isPositive (a b c : Variable) :
    isPositiveDynamics ⟨[CausalLaw.conjunctive a b c]⟩ = true := rfl

theorem disjunctive_isPositive (a b c : Variable) :
    isPositiveDynamics (CausalDynamics.disjunctiveCausation a b c) = true := rfl

theorem chain_isPositive (a b c : Variable) :
    isPositiveDynamics (CausalDynamics.causalChain a b c) = true := rfl

-- ============================================================
-- § True-subset ordering on situations
-- ============================================================

-- trueLE, Situation.trueLE_refl, Situation.trueLE_trans, Situation.extend_hasValue_same/diff
-- are defined in Core.Causation

/-- Local abbreviation for readability. -/
private abbrev trueLE := Situation.trueLE

private theorem extend_trueLE_extend (s : Situation) (c1 c2 : Variable) :
    trueLE (s.extend c1 true) ((s.extend c2 true).extend c1 true) := by
  intro v hv
  by_cases h1 : v = c1
  · subst h1; simp
  · by_cases h2 : v = c2
    · subst h2; simp [h1]
    · simp [h1, h2] at hv ⊢; exact hv

/-- **Sufficiency is monotone for positive dynamics.**

    In causal models with no inhibitory connections (all preconditions require
    `true`, all effects set variables to `true`), adding `c2 = true` to the
    background preserves causal sufficiency.

    Proof: Define `trueLE s₁ s₂` ("every variable true in s₁ is true in s₂").
    Show that positive dynamics preserve `trueLE` through `applyLawsOnce`
    (induction on the law list) and `normalDevelopment` (induction on fuel,
    with a fixpoint absorption lemma for the asymmetric case). -/
theorem sufficiency_monotone_positive (dyn : CausalDynamics) (s : Situation)
    (c1 c2 effect : Variable)
    (hPos : isPositiveDynamics dyn = true)
    (h : causallySufficient dyn s c1 effect = true) :
    causallySufficient dyn (s.extend c2 true) c1 effect = true := by
  simp only [causallySufficient] at *
  exact normalDevelopment_trueLE_positive dyn _ _ 100 hPos
    (extend_trueLE_extend s c1 c2) effect h

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
  show (normalDevelopment _ (Situation.empty.extend a true)).hasValue c true = true
  set dyn := CausalDynamics.disjunctiveCausation a b c
  set s := Situation.empty.extend a true
  have hfix : isFixpoint dyn (applyLawsOnce dyn s) = true := by
    simp only [dyn, s, isFixpoint, applyLawsOnce, CausalDynamics.disjunctiveCausation,
      CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
      Situation.empty, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    split_ifs <;> simp_all
  change (normalDevelopment dyn s 100).hasValue c true = true
  rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_fixpoint_after_one _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.disjunctiveCausation,
    CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
    Situation.empty]
  split_ifs <;> simp_all

/-- In conjunctive causation (A ∧ B → C), neither alone is sufficient. -/
theorem conjunctive_neither_sufficient_alone (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    let dyn := CausalDynamics.conjunctiveCausation a b c
    causallySufficient dyn Situation.empty a c = false := by
  show (normalDevelopment _ (Situation.empty.extend a true)).hasValue c true = false
  set dyn := CausalDynamics.conjunctiveCausation a b c
  set s := Situation.empty.extend a true
  have hfix : isFixpoint dyn (applyLawsOnce dyn s) = true := by
    simp only [dyn, s, isFixpoint, applyLawsOnce, CausalDynamics.conjunctiveCausation,
      CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
      Situation.empty, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    split_ifs <;> simp_all [Ne.symm _ha, Ne.symm _hac]
  change (normalDevelopment dyn s 100).hasValue c true = false
  rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_fixpoint_after_one _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.conjunctiveCausation,
    CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
    Situation.empty]
  split_ifs <;> simp_all [Ne.symm _ha, Ne.symm _hac]

/-- In conjunctive causation, A is sufficient when B is in the background. -/
theorem conjunctive_sufficient_with_other (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    let dyn := CausalDynamics.conjunctiveCausation a b c
    let background := Situation.empty.extend b true
    causallySufficient dyn background a c = true := by
  show (normalDevelopment _ ((Situation.empty.extend b true).extend a true)).hasValue c true = true
  set dyn := CausalDynamics.conjunctiveCausation a b c
  set s := (Situation.empty.extend b true).extend a true
  have hfix : isFixpoint dyn (applyLawsOnce dyn s) = true := by
    simp only [dyn, s, isFixpoint, applyLawsOnce, CausalDynamics.conjunctiveCausation,
      CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
      Situation.empty, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    split_ifs <;> simp_all [Ne.symm _ha]
  change (normalDevelopment dyn s 100).hasValue c true = true
  rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_fixpoint_after_one _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.conjunctiveCausation,
    CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
    Situation.empty]
  split_ifs <;> simp_all [Ne.symm _ha]

end NadathurLauer2020.Sufficiency
