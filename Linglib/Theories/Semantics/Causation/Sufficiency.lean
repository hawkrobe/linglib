import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Core.Causal.SEM.Monotonicity
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-!
# Causal Sufficiency

Causal sufficiency semantics for the verb "make" based on
@cite{nadathur-lauer-2020} Definition 23.

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

-/

namespace Semantics.Causation.Sufficiency

open Core.Causal
export Core.Causal (causallySufficient)

/-- Semantics of "make": X was causally sufficient for Y (@cite{nadathur-lauer-2020}). -/
def makeSem (dyn : CausalDynamics) [IsPositive dyn] (background : Situation)
    (causeEvent effectEvent : Variable) : Prop :=
  causallySufficient dyn background causeEvent effectEvent

instance (dyn : CausalDynamics) [IsPositive dyn] (background : Situation)
    (causeEvent effectEvent : Variable) :
    Decidable (makeSem dyn background causeEvent effectEvent) :=
  inferInstanceAs (Decidable (causallySufficient ..))

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
-- are defined in Core.Causal

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
theorem sufficiency_monotone_positive (dyn : CausalDynamics) [hPos : IsPositive dyn]
    (s : Situation) (c1 c2 effect : Variable)
    (h : causallySufficient dyn s c1 effect) :
    causallySufficient dyn (s.extend c2 true) c1 effect := by
  simp only [causallySufficient] at *
  exact normalDevelopmentPositive_trueLE dyn hPos.positive _ _
    (extend_trueLE_extend s c1 c2) effect h

/-- Sufficiency implies effect occurrence (after cause). -/
theorem sufficient_implies_effect (dyn : CausalDynamics) [IsPositive dyn]
    (s : Situation) (cause effect : Variable)
    (h : causallySufficient dyn s cause effect) :
    developsToTrue dyn (s.extend cause true) effect := h

/-- In disjunctive causation (A ∨ B → C), each disjunct is sufficient. -/
theorem disjunctive_each_sufficient (a b c : Variable) (_ha : a ≠ b) :
    causallySufficient (CausalDynamics.disjunctiveCausation a b c) Situation.empty a c := by
  show (normalDevelopmentPositive _ _ (Situation.empty.extend a true)).hasValue c true = true
  set dyn := CausalDynamics.disjunctiveCausation a b c
  set s := Situation.empty.extend a true
  have hfix : isFixpoint dyn (applyLawsOnce dyn s) = true := by
    simp only [dyn, s, isFixpoint, applyLawsOnce, CausalDynamics.disjunctiveCausation,
      CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
      Situation.empty, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    split_ifs <;> simp_all
  rw [normalDevelopmentPositive_eq_applyLawsOnce_of_fixpoint _ _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.disjunctiveCausation,
    CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
    Situation.empty]
  split_ifs <;> simp_all

/-- In conjunctive causation (A ∧ B → C), neither alone is sufficient. -/
theorem conjunctive_neither_sufficient_alone (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    ¬ (causallySufficient (CausalDynamics.conjunctiveCausation a b c)
        Situation.empty a c) := by
  show ¬ (normalDevelopmentPositive _ _ (Situation.empty.extend a true)).hasValue c true = true
  set dyn := CausalDynamics.conjunctiveCausation a b c
  set s := Situation.empty.extend a true
  have hfix : isFixpoint dyn (applyLawsOnce dyn s) = true := by
    simp only [dyn, s, isFixpoint, applyLawsOnce, CausalDynamics.conjunctiveCausation,
      CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
      Situation.empty, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    split_ifs <;> simp_all [Ne.symm _ha, Ne.symm _hac]
  suffices hfalse : (normalDevelopmentPositive dyn (IsPositive.positive (dyn := dyn)) s).hasValue
      c true = false by
    intro htrue; rw [hfalse] at htrue; exact Bool.false_ne_true htrue
  rw [normalDevelopmentPositive_eq_applyLawsOnce_of_fixpoint _ _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.conjunctiveCausation,
    CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
    Situation.empty]
  split_ifs <;> simp_all [Ne.symm _ha, Ne.symm _hac]

/-- In conjunctive causation, A is sufficient when B is in the background. -/
theorem conjunctive_sufficient_with_other (a b c : Variable)
    (_ha : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) :
    causallySufficient (CausalDynamics.conjunctiveCausation a b c)
      (Situation.empty.extend b true) a c := by
  show (normalDevelopmentPositive _ _
    ((Situation.empty.extend b true).extend a true)).hasValue c true = true
  set dyn := CausalDynamics.conjunctiveCausation a b c
  set s := (Situation.empty.extend b true).extend a true
  have hfix : isFixpoint dyn (applyLawsOnce dyn s) = true := by
    simp only [dyn, s, isFixpoint, applyLawsOnce, CausalDynamics.conjunctiveCausation,
      CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
      Situation.empty, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    split_ifs <;> simp_all [Ne.symm _ha]
  rw [normalDevelopmentPositive_eq_applyLawsOnce_of_fixpoint _ _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.conjunctiveCausation,
    CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet, List.all, Situation.hasValue, Situation.extend,
    Situation.empty]
  split_ifs <;> simp_all [Ne.symm _ha]

end Semantics.Causation.Sufficiency
