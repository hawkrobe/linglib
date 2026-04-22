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

/-- Default-fuel form of `normalDevelopment_trueLE_positive`: when both
    `normalDevelopment` calls use the default fuel, monotonicity holds without
    needing to thread an explicit fuel argument. -/
theorem normalDevelopment_trueLE_positive_default {dyn : CausalDynamics} {s₁ s₂ : Situation}
    (hPos : isPositiveDynamics dyn = true)
    (hLE : Situation.trueLE s₁ s₂) :
    Situation.trueLE (normalDevelopment dyn s₁) (normalDevelopment dyn s₂) :=
  normalDevelopment_trueLE_positive dyn s₁ s₂ defaultFuel hPos hLE

-- ============================================================
-- § Termination measure & well-founded normalDevelopment
-- ============================================================

/-! For positive dynamics, the count of inner variables not yet `some true`
    strictly decreases on every non-fixpoint step. This gives a well-founded
    recursion measure, eliminating the fuel parameter. -/

/-- List counting: if `P` implies `Q` pointwise, then `countP P ≤ countP Q`. -/
private theorem countP_le_of_imp {α : Type*}
    {P Q : α → Bool} (hMono : ∀ x, P x = true → Q x = true) :
    ∀ (l : List α), l.countP P ≤ l.countP Q
  | [] => Nat.le_refl _
  | hd :: tl => by
    cases hPhd : P hd
    · cases hQhd : Q hd
      · simp [List.countP_cons, hPhd, hQhd]
        exact countP_le_of_imp hMono tl
      · simp [List.countP_cons, hPhd, hQhd]
        exact Nat.le_succ_of_le (countP_le_of_imp hMono tl)
    · have hQhd : Q hd = true := hMono hd hPhd
      simp [List.countP_cons, hPhd, hQhd]
      exact countP_le_of_imp hMono tl

/-- List counting: pointwise implication plus a witness `x ∈ l` with `Q x` and
    `¬ P x` gives strict inequality `countP P < countP Q`. -/
private theorem countP_lt_of_imp_of_witness {α : Type*}
    {P Q : α → Bool} (hMono : ∀ x, P x = true → Q x = true)
    {l : List α} {x : α} (hx : x ∈ l) (hQx : Q x = true) (hPx : P x = false) :
    l.countP P < l.countP Q := by
  induction l with
  | nil => cases hx
  | cons hd tl ih =>
    rw [List.mem_cons] at hx
    rcases hx with rfl | hxtl
    · -- hd = x: P false, Q true at this position, count diverges by 1 + monotone tail
      simp [List.countP_cons, hPx, hQx]
      exact Nat.lt_succ_of_le (countP_le_of_imp hMono tl)
    · cases hPhd : P hd
      · cases hQhd : Q hd
        · simp [List.countP_cons, hPhd, hQhd]
          exact ih hxtl
        · simp [List.countP_cons, hPhd, hQhd]
          exact Nat.lt_succ_of_lt (ih hxtl)
      · have hQhd : Q hd = true := hMono hd hPhd
        simp [List.countP_cons, hPhd, hQhd]
        exact ih hxtl

/-- **Strict-decrease lemma**: for positive dynamics, if `s` is not a fixpoint
    then `applyLawsOnce` strictly decreases the count of inner variables not
    yet `some true`. The witness is the law whose preconditions are met but
    effect not yet at value: `foldl_sets_witness_effect` ensures the law's
    effect transitions to `some true` after applying. -/
theorem positive_applyLawsOnce_strict_decrease
    (dyn : CausalDynamics) (s : Situation)
    (hPos : isPositiveDynamics dyn = true)
    (hNotFix : isFixpoint dyn s = false) :
    (innerVariables dyn).countP (fun v => !(applyLawsOnce dyn s).hasValue v true) <
    (innerVariables dyn).countP (fun v => !s.hasValue v true) := by
  -- Step 1: extract witness law L₀ from non-fixpoint
  unfold isFixpoint at hNotFix
  rw [List.all_eq_false] at hNotFix
  obtain ⟨L₀, hL₀mem, hL₀_bad⟩ := hNotFix
  -- hL₀_bad : ¬(!L₀.preconditionsMet s || s.hasValue L₀.effect L₀.effectValue) = true
  -- Convert to Bool form: the disjunction = false
  have hL₀_or_false : (!L₀.preconditionsMet s || s.hasValue L₀.effect L₀.effectValue) = false := by
    cases h : (!L₀.preconditionsMet s || s.hasValue L₀.effect L₀.effectValue)
    · rfl
    · exact absurd h hL₀_bad
  rw [Bool.or_eq_false_iff] at hL₀_or_false
  obtain ⟨hPrecBool, hValueBool⟩ := hL₀_or_false
  have hPrec : L₀.preconditionsMet s = true := by
    cases hp : L₀.preconditionsMet s
    · rw [hp] at hPrecBool; simp at hPrecBool
    · rfl
  -- Step 2: positivity for L₀
  unfold isPositiveDynamics at hPos
  have hL₀Pos := List.all_eq_true.mp hPos L₀ hL₀mem
  rw [Bool.and_eq_true] at hL₀Pos
  obtain ⟨_hPrecPos, hEffPos⟩ := hL₀Pos
  -- Step 3: s.hasValue L₀.effect true = false (from hValueBool + hEffPos)
  rw [hEffPos] at hValueBool
  -- Step 4: (applyLawsOnce dyn s).hasValue L₀.effect true = true
  have hValAfter : (applyLawsOnce dyn s).hasValue L₀.effect true = true := by
    show (dyn.laws.foldl _ s).hasValue L₀.effect true = true
    have hPos' : dyn.laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true :=
      hPos
    exact foldl_sets_witness_effect dyn.laws s L₀ hPos' hL₀mem hEffPos hPrec
  -- Step 5: L₀.effect ∈ innerVariables
  have hMem : L₀.effect ∈ innerVariables dyn := effect_mem_innerVariables dyn L₀ hL₀mem
  -- Step 6: apply countP_lt_of_imp_of_witness
  refine countP_lt_of_imp_of_witness ?_ hMem ?_ ?_
  · -- monotonicity: !(applyLawsOnce dyn s).hasValue v true → !s.hasValue v true
    intro v hAfter
    cases hSb : s.hasValue v true
    · rfl
    · -- s.hasValue v true = true → mono → applyLawsOnce.hasValue v true = true
      -- → !true = false ≠ true, contradicting hAfter
      have hMono : trueLE s (applyLawsOnce dyn s) := positive_applyLawsOnce_grows dyn s hPos
      have hAfterTrue := hMono v hSb
      rw [hAfterTrue] at hAfter
      exact hAfter
  · rw [hValueBool]; rfl
  · rw [hValAfter]; rfl

/-- **Termination-proven `normalDevelopment` for positive dynamics.**

    Iterates `applyLawsOnce` until reaching a fixpoint, with no fuel parameter.
    Termination is via well-founded recursion on the count of inner variables
    not yet `some true` (decreased by `positive_applyLawsOnce_strict_decrease`
    on every non-fixpoint step). -/
def normalDevelopmentPositive (dyn : CausalDynamics)
    (hPos : isPositiveDynamics dyn = true) (s : Situation) : Situation :=
  if hFix : isFixpoint dyn s = true then s
  else normalDevelopmentPositive dyn hPos (applyLawsOnce dyn s)
termination_by (innerVariables dyn).countP (fun v => !s.hasValue v true)
decreasing_by
  simp_wf
  have hNotFix : isFixpoint dyn s = false := by
    cases hf : isFixpoint dyn s
    · rfl
    · exact absurd hf hFix
  exact positive_applyLawsOnce_strict_decrease dyn s hPos hNotFix

/-- Fixpoint case unfolds. -/
theorem normalDevelopmentPositive_of_fixpoint
    {dyn : CausalDynamics} {hPos : isPositiveDynamics dyn = true} {s : Situation}
    (h : isFixpoint dyn s = true) :
    normalDevelopmentPositive dyn hPos s = s := by
  rw [normalDevelopmentPositive, dif_pos h]

/-- Step case unfolds. -/
theorem normalDevelopmentPositive_of_not_fixpoint
    {dyn : CausalDynamics} {hPos : isPositiveDynamics dyn = true} {s : Situation}
    (h : isFixpoint dyn s = false) :
    normalDevelopmentPositive dyn hPos s =
      normalDevelopmentPositive dyn hPos (applyLawsOnce dyn s) := by
  rw [normalDevelopmentPositive]
  have hne : ¬ (isFixpoint dyn s = true) := by rw [h]; decide
  rw [dif_neg hne]

/-- One-step convergence: if `applyLawsOnce dyn s` is a fixpoint, then
    `normalDevelopmentPositive dyn hPos s = applyLawsOnce dyn s` (no fuel
    appears anywhere). Handles both the case where `s` is itself a fixpoint
    (in which case `applyLawsOnce` is the identity) and the case where it
    takes one step. -/
theorem normalDevelopmentPositive_eq_applyLawsOnce_of_fixpoint
    (dyn : CausalDynamics) (hPos : isPositiveDynamics dyn = true) (s : Situation)
    (hFix : isFixpoint dyn (applyLawsOnce dyn s) = true) :
    normalDevelopmentPositive dyn hPos s = applyLawsOnce dyn s := by
  by_cases hSFix : isFixpoint dyn s = true
  · -- s is itself a fixpoint; both sides equal s
    rw [normalDevelopmentPositive_of_fixpoint hSFix, applyLawsOnce_of_fixpoint hSFix]
  · have hSNotFix : isFixpoint dyn s = false := by
      cases h : isFixpoint dyn s
      · rfl
      · exact absurd h hSFix
    rw [normalDevelopmentPositive_of_not_fixpoint hSNotFix,
        normalDevelopmentPositive_of_fixpoint hFix]

/-- **Agreement with the fuel-based version.** With sufficient fuel
    (at least the count of undetermined inner variables), the two agree. -/
theorem normalDevelopment_eq_normalDevelopmentPositive
    (dyn : CausalDynamics) (hPos : isPositiveDynamics dyn = true) (s : Situation)
    (fuel : Nat)
    (hFuel : (innerVariables dyn).countP (fun v => !s.hasValue v true) ≤ fuel) :
    normalDevelopment dyn s fuel = normalDevelopmentPositive dyn hPos s := by
  induction fuel generalizing s with
  | zero =>
    -- Fuel = 0 means measure s = 0, so s has no undetermined inner variables
    -- and is therefore a fixpoint (every law's effect is already at value).
    rw [Nat.le_zero] at hFuel
    have hSFix : isFixpoint dyn s = true := by
      by_contra hNotFix
      have hf : isFixpoint dyn s = false := by
        cases hh : isFixpoint dyn s
        · rfl
        · exact absurd hh hNotFix
      have hStrict := positive_applyLawsOnce_strict_decrease dyn s hPos hf
      rw [hFuel] at hStrict
      exact Nat.not_lt_zero _ hStrict
    rw [normalDevelopmentPositive_of_fixpoint hSFix]
    rfl
  | succ n ih =>
    by_cases hFix : isFixpoint dyn s = true
    · -- s is a fixpoint
      rw [normalDevelopment_of_fixpoint hFix, normalDevelopmentPositive_of_fixpoint hFix]
    · -- s is not a fixpoint
      have hNotFix : isFixpoint dyn s = false := by
        cases hh : isFixpoint dyn s
        · rfl
        · exact absurd hh hFix
      have hStrict := positive_applyLawsOnce_strict_decrease dyn s hPos hNotFix
      have hFuel' : (innerVariables dyn).countP
          (fun v => !(applyLawsOnce dyn s).hasValue v true) ≤ n := by omega
      rw [normalDevelopmentPositive_of_not_fixpoint hNotFix]
      -- Need to relate normalDevelopment dyn s (n+1) to normalDevelopment dyn (applyLawsOnce dyn s) n
      by_cases hFix' : isFixpoint dyn (applyLawsOnce dyn s) = true
      · rw [normalDevelopment_succ_fix hFix', normalDevelopmentPositive_of_fixpoint hFix']
      · have hNotFix' : isFixpoint dyn (applyLawsOnce dyn s) = false := by
          cases hh : isFixpoint dyn (applyLawsOnce dyn s)
          · rfl
          · exact absurd hh hFix'
        rw [normalDevelopment_succ_step hNotFix']
        exact ih (applyLawsOnce dyn s) hFuel'

/-- Monotonicity for `normalDevelopmentPositive` (no fuel). Derived from
    `normalDevelopment_trueLE_positive` via the agreement theorem. -/
theorem normalDevelopmentPositive_trueLE (dyn : CausalDynamics)
    (hPos : isPositiveDynamics dyn = true) (s₁ s₂ : Situation)
    (hLE : Situation.trueLE s₁ s₂) :
    Situation.trueLE (normalDevelopmentPositive dyn hPos s₁)
                     (normalDevelopmentPositive dyn hPos s₂) := by
  -- Pick fuel large enough for both measures, then bridge via agreement
  let m₁ := (innerVariables dyn).countP (fun v => !s₁.hasValue v true)
  let m₂ := (innerVariables dyn).countP (fun v => !s₂.hasValue v true)
  have h₁ : normalDevelopment dyn s₁ (m₁ + m₂) = normalDevelopmentPositive dyn hPos s₁ :=
    normalDevelopment_eq_normalDevelopmentPositive dyn hPos s₁ (m₁ + m₂) (Nat.le_add_right _ _)
  have h₂ : normalDevelopment dyn s₂ (m₁ + m₂) = normalDevelopmentPositive dyn hPos s₂ :=
    normalDevelopment_eq_normalDevelopmentPositive dyn hPos s₂ (m₁ + m₂) (Nat.le_add_left _ _)
  rw [← h₁, ← h₂]
  exact normalDevelopment_trueLE_positive dyn s₁ s₂ (m₁ + m₂) hPos hLE

end Core.Causal
