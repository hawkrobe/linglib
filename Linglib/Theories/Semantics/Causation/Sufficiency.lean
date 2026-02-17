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

/-- A dynamics is **positive** if all preconditions require `true` and all
    effect values are `true`. Positive dynamics have no inhibitory connections:
    causes can only enable effects, never block them.

    This is the necessary condition for sufficiency monotonicity. Without it,
    adding a variable set to `true` can break sufficiency via:
    - Negative preconditions (`v = false`): the new value blocks a law
    - Inhibitory effects (`effectValue = false`): the new value activates
      a law that overrides the effect with `false` -/
def isPositiveDynamics (dyn : CausalDynamics) : Bool :=
  dyn.laws.all (fun law => law.preconditions.all (·.2) && law.effectValue)

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

/-- s₁ ⊑ s₂: every variable `true` in s₁ is also `true` in s₂. -/
private def trueLE (s₁ s₂ : Situation) : Prop :=
  ∀ v, s₁.hasValue v true = true → s₂.hasValue v true = true

private theorem trueLE_refl (s : Situation) : trueLE s s := fun _ hv => hv

private theorem trueLE_trans {s₁ s₂ s₃ : Situation}
    (h₁₂ : trueLE s₁ s₂) (h₂₃ : trueLE s₂ s₃) : trueLE s₁ s₃ :=
  fun v hv => h₂₃ v (h₁₂ v hv)

private theorem extend_trueLE_extend (s : Situation) (c1 c2 : Variable) :
    trueLE (s.extend c1 true) ((s.extend c2 true).extend c1 true) := by
  intro v hv
  simp only [Situation.hasValue, Situation.extend, Variable.beq_def, decide_eq_true_eq] at *
  split_ifs at hv ⊢ <;> simp_all

-- ============================================================
-- § Helper lemmas for extend/hasValue interaction
-- ============================================================

private theorem extend_hasValue_same (s : Situation) (v : Variable) (val bval : Bool) :
    (s.extend v val).hasValue v bval = (val == bval) := by
  simp [Situation.hasValue, Situation.extend, Variable.beq_def, decide_eq_true_eq]

private theorem extend_hasValue_diff (s : Situation) (v w : Variable) (val bval : Bool)
    (h : w ≠ v) : (s.extend v val).hasValue w bval = s.hasValue w bval := by
  simp [Situation.hasValue, Situation.extend, Variable.beq_def, decide_eq_true_eq, h]

-- ============================================================
-- § Per-law monotonicity lemmas
-- ============================================================

private theorem positive_preconditions_monotone
    (law : CausalLaw) (s₁ s₂ : Situation)
    (hPosPrec : law.preconditions.all (·.2) = true)
    (hLE : trueLE s₁ s₂)
    (hMet : law.preconditionsMet s₁ = true) :
    law.preconditionsMet s₂ = true := by
  simp only [CausalLaw.preconditionsMet, List.all_eq_true] at *
  intro p hmem
  have hval : p.2 = true := hPosPrec p hmem
  exact hval ▸ hLE p.1 (hval ▸ hMet p hmem)

private theorem positive_law_apply_trueLE
    (law : CausalLaw) (s₁ s₂ : Situation)
    (hPosPrec : law.preconditions.all (·.2) = true)
    (hPosEff : law.effectValue = true)
    (hLE : trueLE s₁ s₂) :
    trueLE (law.apply s₁) (law.apply s₂) := by
  intro v hv
  simp only [CausalLaw.apply] at hv ⊢
  by_cases hMet₁ : law.preconditionsMet s₁ = true
  · have hMet₂ := positive_preconditions_monotone law s₁ s₂ hPosPrec hLE hMet₁
    simp only [hMet₁, ↓reduceIte] at hv; simp only [hMet₂, ↓reduceIte]
    by_cases he : v = law.effect
    · subst he; rw [extend_hasValue_same]; simp [hPosEff]
    · rw [extend_hasValue_diff _ _ _ _ _ he] at hv ⊢
      exact hLE v hv
  · have h₁ : law.preconditionsMet s₁ = false := by
      cases h : law.preconditionsMet s₁ <;> simp_all
    simp only [h₁] at hv
    by_cases hMet₂ : law.preconditionsMet s₂ = true
    · simp only [hMet₂, ↓reduceIte]
      by_cases he : v = law.effect
      · subst he; rw [extend_hasValue_same]; simp [hPosEff]
      · rw [extend_hasValue_diff _ _ _ _ _ he]; exact hLE v hv
    · have h₂ : law.preconditionsMet s₂ = false := by
        cases h : law.preconditionsMet s₂ <;> simp_all
      simp only [h₂]; exact hLE v hv

private theorem positive_law_apply_grows
    (law : CausalLaw) (s : Situation) (hPosEff : law.effectValue = true) :
    trueLE s (law.apply s) := by
  intro v hv
  simp only [CausalLaw.apply]
  by_cases hMet : law.preconditionsMet s = true
  · simp only [hMet, ↓reduceIte]
    by_cases he : v = law.effect
    · subst he; rw [extend_hasValue_same]; simp [hPosEff]
    · rw [extend_hasValue_diff _ _ _ _ _ he]; exact hv
  · have : law.preconditionsMet s = false := by
      cases h : law.preconditionsMet s <;> simp_all
    simp only [this]; exact hv

private theorem positive_law_apply_absorbed
    (law : CausalLaw) (s₁ s₂ : Situation)
    (hPosPrec : law.preconditions.all (·.2) = true)
    (hPosEff : law.effectValue = true)
    (hLE : trueLE s₁ s₂)
    (hFixLaw : (!law.preconditionsMet s₂ || s₂.hasValue law.effect law.effectValue) = true) :
    trueLE (law.apply s₁) s₂ := by
  intro v hv
  simp only [CausalLaw.apply] at hv
  by_cases hMet₁ : law.preconditionsMet s₁ = true
  · simp only [hMet₁, ↓reduceIte] at hv
    by_cases he : v = law.effect
    · subst he
      have hMet₂ := positive_preconditions_monotone law s₁ s₂ hPosPrec hLE hMet₁
      simp only [hMet₂, Bool.not_true, Bool.false_or] at hFixLaw
      rw [hPosEff] at hFixLaw; exact hFixLaw
    · rw [extend_hasValue_diff _ _ _ _ _ he] at hv; exact hLE v hv
  · have : law.preconditionsMet s₁ = false := by
      cases h : law.preconditionsMet s₁ <;> simp_all
    simp only [this] at hv; exact hLE v hv

-- ============================================================
-- § Foldl (law-list) monotonicity
-- ============================================================

private theorem positive_foldl_trueLE
    (laws : List CausalLaw) (s₁ s₂ : Situation)
    (hPos : laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true)
    (hLE : trueLE s₁ s₂) :
    trueLE (laws.foldl (fun s' law => law.apply s') s₁)
           (laws.foldl (fun s' law => law.apply s') s₂) := by
  induction laws generalizing s₁ s₂ with
  | nil => exact hLE
  | cons law rest ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    exact ih (law.apply s₁) (law.apply s₂) hPos.2
      (positive_law_apply_trueLE law s₁ s₂ hPos.1.1 hPos.1.2 hLE)

private theorem positive_foldl_grows
    (laws : List CausalLaw) (s : Situation)
    (hPos : laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true) :
    trueLE s (laws.foldl (fun s' law => law.apply s') s) := by
  induction laws generalizing s with
  | nil => exact trueLE_refl s
  | cons law rest ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    exact trueLE_trans
      (positive_law_apply_grows law s hPos.1.2) (ih (law.apply s) hPos.2)

private theorem positive_foldl_absorbed
    (laws : List CausalLaw) (s₁ s₂ : Situation)
    (hPos : laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true)
    (hLE : trueLE s₁ s₂)
    (hFix : laws.all (fun law => !law.preconditionsMet s₂ ||
            s₂.hasValue law.effect law.effectValue) = true) :
    trueLE (laws.foldl (fun s' law => law.apply s') s₁) s₂ := by
  induction laws generalizing s₁ with
  | nil => exact hLE
  | cons law rest ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    exact ih (law.apply s₁) hPos.2
      (positive_law_apply_absorbed law s₁ s₂ hPos.1.1 hPos.1.2 hLE hFix.1) hFix.2

-- ============================================================
-- § applyLawsOnce / normalDevelopment monotonicity
-- ============================================================

private theorem positive_applyLawsOnce_trueLE
    (dyn : CausalDynamics) (s₁ s₂ : Situation)
    (hPos : isPositiveDynamics dyn = true) (hLE : trueLE s₁ s₂) :
    trueLE (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) :=
  positive_foldl_trueLE dyn.laws s₁ s₂ hPos hLE

private theorem positive_applyLawsOnce_grows
    (dyn : CausalDynamics) (s : Situation)
    (hPos : isPositiveDynamics dyn = true) :
    trueLE s (applyLawsOnce dyn s) :=
  positive_foldl_grows dyn.laws s hPos

private theorem positive_applyLawsOnce_absorbed
    (dyn : CausalDynamics) (s₁ s₂ : Situation)
    (hPos : isPositiveDynamics dyn = true)
    (hLE : trueLE s₁ s₂) (hFix : isFixpoint dyn s₂ = true) :
    trueLE (applyLawsOnce dyn s₁) s₂ :=
  positive_foldl_absorbed dyn.laws s₁ s₂ hPos hLE hFix

private theorem positive_normalDevelopment_grows
    (dyn : CausalDynamics) (s : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true) :
    trueLE s (normalDevelopment dyn s fuel) := by
  induction fuel generalizing s with
  | zero => exact trueLE_refl s
  | succ n ih =>
    simp only [normalDevelopment]
    have hGrow := positive_applyLawsOnce_grows dyn s hPos
    by_cases hFix : isFixpoint dyn (applyLawsOnce dyn s) = true
    · simp only [hFix, ↓reduceIte]; exact hGrow
    · have : isFixpoint dyn (applyLawsOnce dyn s) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s) <;> simp_all
      simp only [this]; exact trueLE_trans hGrow (ih (applyLawsOnce dyn s))

private theorem fixpoint_absorbs
    (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true)
    (hLE : trueLE s₁ s₂) (hFix : isFixpoint dyn s₂ = true) :
    trueLE (normalDevelopment dyn s₁ fuel) s₂ := by
  induction fuel generalizing s₁ with
  | zero => exact hLE
  | succ n ih =>
    simp only [normalDevelopment]
    have hLE' := positive_applyLawsOnce_absorbed dyn s₁ s₂ hPos hLE hFix
    by_cases hFixS₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = true
    · simp only [hFixS₁, ↓reduceIte]; exact hLE'
    · have : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      simp only [this]; exact ih (applyLawsOnce dyn s₁) hLE'

private theorem positive_normalDevelopment_trueLE
    (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true) (hLE : trueLE s₁ s₂) :
    trueLE (normalDevelopment dyn s₁ fuel) (normalDevelopment dyn s₂ fuel) := by
  induction fuel generalizing s₁ s₂ with
  | zero => exact hLE
  | succ n ih =>
    simp only [normalDevelopment]
    have hLE' := positive_applyLawsOnce_trueLE dyn s₁ s₂ hPos hLE
    by_cases hFix₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = true <;>
    by_cases hFix₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = true
    · simp only [hFix₁, hFix₂, ↓reduceIte]; exact hLE'
    · have h₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₂) <;> simp_all
      simp only [hFix₁, h₂, ↓reduceIte]
      exact trueLE_trans hLE'
        (positive_normalDevelopment_grows dyn (applyLawsOnce dyn s₂) n hPos)
    · have h₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      simp only [h₁, hFix₂, ↓reduceIte]
      exact fixpoint_absorbs dyn (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) n hPos
        hLE' hFix₂
    · have h₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      have h₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₂) <;> simp_all
      simp only [h₁, h₂]
      exact ih (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) hLE'

-- ============================================================
-- § Main monotonicity theorem
-- ============================================================

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
  exact positive_normalDevelopment_trueLE dyn _ _ 100 hPos
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
      CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
      List.all, Situation.hasValue, Situation.extend, Situation.empty,
      Variable.beq_def, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true]
    split_ifs <;> simp_all
  change (normalDevelopment dyn s 100).hasValue c true = true
  rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_fixpoint_after_one _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.disjunctiveCausation,
    CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
    List.all, Situation.hasValue, Situation.extend, Situation.empty,
    Variable.beq_def, decide_eq_true_eq]
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
      CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
      List.all, Situation.hasValue, Situation.extend, Situation.empty,
      Variable.beq_def, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true]
    split_ifs <;> simp_all [Ne.symm _ha, Ne.symm _hac]
  change (normalDevelopment dyn s 100).hasValue c true = false
  rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_fixpoint_after_one _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.conjunctiveCausation,
    CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
    List.all, Situation.hasValue, Situation.extend, Situation.empty,
    Variable.beq_def, decide_eq_true_eq]
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
      CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
      List.all, Situation.hasValue, Situation.extend, Situation.empty,
      Variable.beq_def, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true]
    split_ifs <;> simp_all [Ne.symm _ha]
  change (normalDevelopment dyn s 100).hasValue c true = true
  rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_fixpoint_after_one _ _ hfix]
  simp only [dyn, s, applyLawsOnce, CausalDynamics.conjunctiveCausation,
    CausalLaw.conjunctive, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
    List.all, Situation.hasValue, Situation.extend, Situation.empty,
    Variable.beq_def, decide_eq_true_eq]
  split_ifs <;> simp_all [Ne.symm _ha]

end NadathurLauer2020.Sufficiency
