import Linglib.Core.Causal.SEM.Defs

/-!
# Structural Equation Model: Monotonicity for Positive Dynamics
@cite{nadathur-lauer-2020}

For *positive* dynamics (no inhibitory connections), `normalDevelopment`
is monotone in the `trueLE` preorder. This is the key technical
machinery that lets `Theories/Semantics/Causation/Closure.lean` build a
mathlib `ClosureOperator` instance from `normalDevelopment` and exposes
the inflationary closure-operator axiom as `positive_normalDevelopment_grows`.
-/

namespace Core.Causal

-- ============================================================
-- § Positive Dynamics: Monotonicity
-- ============================================================

private abbrev trueLE := Situation.trueLE

-- § Per-law monotonicity lemmas

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
  by_cases hMet₁ : law.preconditionsMet s₁ = true
  · have hMet₂ := positive_preconditions_monotone law s₁ s₂ hPosPrec hLE hMet₁
    rw [CausalLaw.apply_of_met hMet₁] at hv; rw [CausalLaw.apply_of_met hMet₂]
    by_cases he : v = law.effect
    · subst he; rw [Situation.extend_hasValue_same]; simp [hPosEff]
    · rw [Situation.extend_hasValue_diff he] at hv ⊢
      exact hLE v hv
  · have h₁ : law.preconditionsMet s₁ = false := by
      cases h : law.preconditionsMet s₁ <;> simp_all
    rw [CausalLaw.apply_of_not_met h₁] at hv
    by_cases hMet₂ : law.preconditionsMet s₂ = true
    · rw [CausalLaw.apply_of_met hMet₂]
      by_cases he : v = law.effect
      · subst he; rw [Situation.extend_hasValue_same]; simp [hPosEff]
      · rw [Situation.extend_hasValue_diff he]; exact hLE v hv
    · have h₂ : law.preconditionsMet s₂ = false := by
        cases h : law.preconditionsMet s₂ <;> simp_all
      rw [CausalLaw.apply_of_not_met h₂]; exact hLE v hv

private theorem positive_law_apply_grows
    (law : CausalLaw) (s : Situation) (hPosEff : law.effectValue = true) :
    trueLE s (law.apply s) := by
  intro v hv
  by_cases hMet : law.preconditionsMet s = true
  · rw [CausalLaw.apply_of_met hMet]
    by_cases he : v = law.effect
    · subst he; rw [Situation.extend_hasValue_same]; simp [hPosEff]
    · rw [Situation.extend_hasValue_diff he]; exact hv
  · have : law.preconditionsMet s = false := by
      cases h : law.preconditionsMet s <;> simp_all
    rw [CausalLaw.apply_of_not_met this]; exact hv

private theorem positive_law_apply_absorbed
    (law : CausalLaw) (s₁ s₂ : Situation)
    (hPosPrec : law.preconditions.all (·.2) = true)
    (hPosEff : law.effectValue = true)
    (hLE : trueLE s₁ s₂)
    (hFixLaw : (!law.preconditionsMet s₂ || s₂.hasValue law.effect law.effectValue) = true) :
    trueLE (law.apply s₁) s₂ := by
  intro v hv
  by_cases hMet₁ : law.preconditionsMet s₁ = true
  · rw [CausalLaw.apply_of_met hMet₁] at hv
    by_cases he : v = law.effect
    · subst he
      have hMet₂ := positive_preconditions_monotone law s₁ s₂ hPosPrec hLE hMet₁
      simp only [hMet₂, Bool.not_true, Bool.false_or] at hFixLaw
      rw [hPosEff] at hFixLaw; exact hFixLaw
    · rw [Situation.extend_hasValue_diff he] at hv; exact hLE v hv
  · have : law.preconditionsMet s₁ = false := by
      cases h : law.preconditionsMet s₁ <;> simp_all
    rw [CausalLaw.apply_of_not_met this] at hv; exact hLE v hv

-- § Foldl (law-list) monotonicity

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
  | nil => exact Situation.trueLE_refl s
  | cons law rest ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    exact Situation.trueLE_trans
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

-- § Foldl sets witness effect (for convergence)

/-- If a law `l` is in the list and its preconditions are met in `s`,
    then after folding all positive laws, `l`'s effect is set.
    Key helper for proving normalDevelopment convergence. -/
private theorem foldl_sets_witness_effect :
    ∀ (laws : List CausalLaw) (s : Situation) (l : CausalLaw),
    laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true →
    l ∈ laws →
    l.effectValue = true →
    l.preconditionsMet s = true →
    (laws.foldl (fun s' law => law.apply s') s).hasValue l.effect true = true
  | [], _, _, _, hMem, _, _ => by simp at hMem
  | hd :: tl, s, l, hPos, hMem, hPosEff, hMet => by
    simp only [List.foldl_cons]
    have hPosAll := hPos
    simp only [List.all_cons, Bool.and_eq_true] at hPos
    cases List.mem_cons.mp hMem with
    | inl heq =>
      subst heq
      rw [CausalLaw.apply_of_met hMet]
      have hSet : (s.extend l.effect l.effectValue).hasValue l.effect true = true := by
        simp [Situation.hasValue, Situation.extend, hPosEff]
      exact positive_foldl_grows tl (s.extend l.effect l.effectValue) hPos.2
        l.effect hSet
    | inr hmem =>
      have hLE := positive_law_apply_grows hd s hPos.1.2
      have hLPos := List.all_eq_true.mp hPos.2 l hmem
      simp only [Bool.and_eq_true] at hLPos
      have hMet' := positive_preconditions_monotone l s (hd.apply s) hLPos.1 hLE hMet
      exact foldl_sets_witness_effect tl (hd.apply s) l hPos.2 hmem hPosEff hMet'

-- § applyLawsOnce / normalDevelopment monotonicity

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

/-- For positive dynamics, normal development is **inflationary** (extensive):
    every truth in `s` is preserved. This is one of the three closure-operator
    axioms. Used by `CausalClosure.lean` to build the `ClosureOperator` instance. -/
theorem positive_normalDevelopment_grows
    (dyn : CausalDynamics) (s : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true) :
    trueLE s (normalDevelopment dyn s fuel) := by
  induction fuel generalizing s with
  | zero => exact Situation.trueLE_refl s
  | succ n ih =>
    have hGrow := positive_applyLawsOnce_grows dyn s hPos
    by_cases hFix : isFixpoint dyn (applyLawsOnce dyn s) = true
    · rw [normalDevelopment_succ_fix hFix]; exact hGrow
    · have : isFixpoint dyn (applyLawsOnce dyn s) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s) <;> simp_all
      rw [normalDevelopment_succ_step this]
      exact Situation.trueLE_trans hGrow (ih (applyLawsOnce dyn s))

private theorem fixpoint_absorbs
    (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true)
    (hLE : trueLE s₁ s₂) (hFix : isFixpoint dyn s₂ = true) :
    trueLE (normalDevelopment dyn s₁ fuel) s₂ := by
  induction fuel generalizing s₁ with
  | zero => exact hLE
  | succ n ih =>
    have hLE' := positive_applyLawsOnce_absorbed dyn s₁ s₂ hPos hLE hFix
    by_cases hFixS₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = true
    · rw [normalDevelopment_succ_fix hFixS₁]; exact hLE'
    · have : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      rw [normalDevelopment_succ_step this]; exact ih (applyLawsOnce dyn s₁) hLE'

private theorem positive_normalDevelopment_trueLE
    (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true) (hLE : trueLE s₁ s₂) :
    trueLE (normalDevelopment dyn s₁ fuel) (normalDevelopment dyn s₂ fuel) := by
  induction fuel generalizing s₁ s₂ with
  | zero => exact hLE
  | succ n ih =>
    have hLE' := positive_applyLawsOnce_trueLE dyn s₁ s₂ hPos hLE
    by_cases hFix₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = true <;>
    by_cases hFix₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = true
    · rw [normalDevelopment_succ_fix hFix₁, normalDevelopment_succ_fix hFix₂]; exact hLE'
    · have h₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₂) <;> simp_all
      rw [normalDevelopment_succ_fix hFix₁, normalDevelopment_succ_step h₂]
      exact Situation.trueLE_trans hLE'
        (positive_normalDevelopment_grows dyn (applyLawsOnce dyn s₂) n hPos)
    · have h₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      rw [normalDevelopment_succ_step h₁, normalDevelopment_succ_fix hFix₂]
      exact fixpoint_absorbs dyn (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) n hPos
        hLE' hFix₂
    · have h₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      have h₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₂) <;> simp_all
      rw [normalDevelopment_succ_step h₁, normalDevelopment_succ_step h₂]
      exact ih (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) hLE'

-- § Main monotonicity theorem

/-- For positive dynamics, normalDevelopment is monotone in the trueLE ordering.
    If s₁ ⊑ s₂ (every true in s₁ is true in s₂), then
    normalDevelopment(s₁) ⊑ normalDevelopment(s₂). -/
theorem normalDevelopment_trueLE_positive (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true)
    (hLE : Situation.trueLE s₁ s₂) :
    Situation.trueLE (normalDevelopment dyn s₁ fuel) (normalDevelopment dyn s₂ fuel) :=
  positive_normalDevelopment_trueLE dyn s₁ s₂ fuel hPos hLE

end Core.Causal
