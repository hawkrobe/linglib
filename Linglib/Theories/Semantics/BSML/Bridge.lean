import Linglib.Theories.Semantics.BSML.Defs
import Linglib.Core.IntensionalLogic.RestrictedModality

/-!
# BSML–CML Bridge
@cite{aloni-2022}

For NE-free formulas, BSML reduces to classical modal logic (CML) on
singleton teams (Fact 15 from @cite{aloni-2022}). This module defines
a classical evaluation function and proves the correspondence.

## Key Result

| Result | Statement |
|--------|-----------|
| Classical Collapse (Fact 15) | For NE-free φ, {w} ⊨⁺ φ iff φ is classically true at w |

## Architecture

`classicalEval` evaluates BSML formulas as standard Kripke modal logic
formulas: ∨ is pointwise (not split), ◇ is existential over accessible
worlds, □ is universal. For NE-free formulas, this agrees with BSML's
team semantics restricted to singleton teams.
-/

namespace Semantics.BSML

variable {W : Type*} [DecidableEq W] [Fintype W]

-- ============================================================================
-- §1: Classical Evaluation
-- ============================================================================

/-- Classical (Kripke) evaluation of a BSML formula at a single world.
    ∨ is pointwise, ◇ is existential, □ is universal — no team splitting.
    NE evaluates to true (singletons are non-empty). -/
def classicalEval (M : BSMLModel W) (φ : BSMLFormula) (w : W) : Bool :=
  match φ with
  | .atom p => M.val p w
  | .ne => true
  | .neg ψ => !classicalEval M ψ w
  | .conj ψ₁ ψ₂ => classicalEval M ψ₁ w && classicalEval M ψ₂ w
  | .disj ψ₁ ψ₂ => classicalEval M ψ₁ w || classicalEval M ψ₂ w
  | .poss ψ => decide (∃ v ∈ M.access w, classicalEval M ψ v = true)

-- ============================================================================
-- §2: NE-free Flatness Equation
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- For NE-free formulas, support and anti-support decompose pointwise over
    team members in terms of classical evaluation. -/
private theorem neFree_flat_eq (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hNE : φ.isNEFree = true) :
    (support M φ t ↔ ∀ w ∈ t, classicalEval M φ w = true) ∧
    (antiSupport M φ t ↔ ∀ w ∈ t, classicalEval M φ w = false) := by
  induction φ generalizing t with
  | atom p => exact ⟨Iff.rfl, Iff.rfl⟩
  | ne => simp [BSMLFormula.isNEFree] at hNE
  | neg ψ ih =>
    have hNE' := by simp [BSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ih_s, ih_a⟩ := ih t hNE'
    constructor
    · -- support of ¬ψ = antiSupport of ψ
      simp only [classicalEval, Bool.not_eq_true']
      exact ih_a
    · -- antiSupport of ¬ψ = support of ψ
      simp only [classicalEval, Bool.not_eq_false']
      exact ih_s
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ := by simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have hψ₂ := by simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    constructor
    · -- support of ψ₁ ∧ ψ₂ = ∀ w ∈ t, classicalEval (ψ₁ ∧ ψ₂) w
      simp only [classicalEval, Bool.and_eq_true]
      exact ⟨fun ⟨h₁, h₂⟩ w hw => ⟨(ih₁ t hψ₁).1.mp h₁ w hw, (ih₂ t hψ₂).1.mp h₂ w hw⟩,
             fun h => ⟨(ih₁ t hψ₁).1.mpr (fun w hw => (h w hw).1),
                       (ih₂ t hψ₂).1.mpr (fun w hw => (h w hw).2)⟩⟩
    · -- antiSupport of ψ₁ ∧ ψ₂ (SPLIT) = ∀ w ∈ t, ¬(ce ψ₁ w ∧ ce ψ₂ w)
      simp only [classicalEval, Bool.and_eq_false_iff]
      constructor
      · -- Forward: from SPLIT, for each world w ∈ t, w is in one part
        intro ⟨s₁, s₂, hunion, h₁, h₂⟩ w hw
        have hw_union := hunion ▸ hw
        rcases Finset.mem_union.mp hw_union with h | h
        · exact Or.inl ((ih₁ s₁ hψ₁).2.mp h₁ w h)
        · exact Or.inr ((ih₂ s₂ hψ₂).2.mp h₂ w h)
      · -- Backward: split t into {w | ce ψ₁ w = false} and the rest
        intro h
        refine ⟨t.filter (fun w => classicalEval M ψ₁ w = false),
                t.filter (fun w => classicalEval M ψ₁ w = true), ?_, ?_, ?_⟩
        · apply Finset.Subset.antisymm
          · intro w hw
            rcases Finset.mem_union.mp hw with h | h <;>
              exact (Finset.mem_filter.mp h).1
          · intro w hw
            cases hb : classicalEval M ψ₁ w with
            | false => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hb⟩)
            | true => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, hb⟩)
        · exact (ih₁ _ hψ₁).2.mpr (fun w hw => (Finset.mem_filter.mp hw).2)
        · exact (ih₂ _ hψ₂).2.mpr (fun w hw => by
            have hmem := (Finset.mem_filter.mp hw).1
            have hce := (Finset.mem_filter.mp hw).2
            have := h w hmem
            cases this with
            | inl h => simp [hce] at h
            | inr h => exact h)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ := by simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have hψ₂ := by simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    constructor
    · -- support of ψ₁ ∨ ψ₂ (SPLIT) = ∀ w ∈ t, ce ψ₁ w ∨ ce ψ₂ w
      simp only [classicalEval, Bool.or_eq_true]
      constructor
      · rintro ⟨s₁, s₂, hunion, h₁, h₂⟩ w hw
        have hw_union := hunion ▸ hw
        rcases Finset.mem_union.mp hw_union with h | h
        · exact Or.inl ((ih₁ s₁ hψ₁).1.mp h₁ w h)
        · exact Or.inr ((ih₂ s₂ hψ₂).1.mp h₂ w h)
      · intro h
        refine ⟨t.filter (fun w => classicalEval M ψ₁ w = true),
                t.filter (fun w => classicalEval M ψ₁ w = false), ?_, ?_, ?_⟩
        · apply Finset.Subset.antisymm
          · intro w hw
            rcases Finset.mem_union.mp hw with h | h <;>
              exact (Finset.mem_filter.mp h).1
          · intro w hw
            cases hb : classicalEval M ψ₁ w with
            | true => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hb⟩)
            | false => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, hb⟩)
        · exact (ih₁ _ hψ₁).1.mpr (fun w hw => (Finset.mem_filter.mp hw).2)
        · exact (ih₂ _ hψ₂).1.mpr (fun w hw => by
            have hmem := (Finset.mem_filter.mp hw).1
            have hce := (Finset.mem_filter.mp hw).2
            have := h w hmem
            cases this with
            | inl h => simp [hce] at h
            | inr h => exact h)
    · -- antiSupport of ψ₁ ∨ ψ₂ = ∀ w ∈ t, ¬(ce ψ₁ w ∨ ce ψ₂ w)
      simp only [classicalEval, Bool.or_eq_false_iff]
      exact ⟨fun ⟨h₁, h₂⟩ w hw => ⟨(ih₁ t hψ₁).2.mp h₁ w hw, (ih₂ t hψ₂).2.mp h₂ w hw⟩,
             fun h => ⟨(ih₁ t hψ₁).2.mpr (fun w hw => (h w hw).1),
                       (ih₂ t hψ₂).2.mpr (fun w hw => (h w hw).2)⟩⟩
  | poss ψ ih =>
    have hNE' := by simp [BSMLFormula.isNEFree] at hNE; exact hNE
    constructor
    · -- support of ◇ψ ↔ ∀ w ∈ t, ∃ v ∈ R[w], ce ψ v = true
      simp only [classicalEval]
      constructor
      · intro h w hw
        obtain ⟨s, hs_sub, hs_ne, hs_supp⟩ := h w hw
        obtain ⟨v, hv⟩ := hs_ne
        have hv_acc := hs_sub (Finset.mem_coe.mpr hv)
        have hv_ce := (ih s hNE').1.mp hs_supp v hv
        exact decide_eq_true ⟨v, hv_acc, hv_ce⟩
      · intro h w hw
        obtain ⟨v, hv_acc, hv_ce⟩ := of_decide_eq_true (h w hw)
        exact ⟨{v}, Finset.singleton_subset_iff.mpr hv_acc,
               ⟨v, Finset.mem_singleton.mpr rfl⟩,
               (ih {v} hNE').1.mpr (fun u hu => by
                 rw [Finset.mem_singleton.mp hu]; exact hv_ce)⟩
    · -- antiSupport of ◇ψ ↔ ∀ w ∈ t, classicalEval ◇ψ w = false
      -- classicalEval ◇ψ w = false means ¬∃ v ∈ R[w], ce ψ v = true
      -- antiSupport ◇ψ t means ∀ w ∈ t, antiSupport ψ (R[w])
      -- By IH: ↔ ∀ w ∈ t, ∀ v ∈ R[w], ce ψ v = false
      simp only [classicalEval]
      constructor
      · intro h w hw
        have h_all := (ih (M.access w) hNE').2.mp (h w hw)
        simp only [decide_eq_false_iff_not, not_exists]
        intro v ⟨hv_acc, hv_ce⟩; rw [h_all v hv_acc] at hv_ce; exact Bool.false_ne_true hv_ce
      · intro h w hw
        simp only [decide_eq_false_iff_not, not_exists] at h
        exact (ih (M.access w) hNE').2.mpr (fun v hv =>
          Bool.eq_false_iff.mpr (fun hce => h w hw v ⟨hv, hce⟩))

-- ============================================================================
-- §3: Classical Collapse (Fact 15)
-- ============================================================================

/--
Classical Collapse (Fact 15 from @cite{aloni-2022}).

For NE-free formulas, BSML support on a singleton team equals classical
Kripke evaluation.
-/
theorem classicalCollapse (M : BSMLModel W)
    (φ : BSMLFormula) (w : W)
    (hNE : φ.isNEFree = true) :
    support M φ {w} ↔ classicalEval M φ w = true := by
  rw [(neFree_flat_eq M φ {w} hNE).1]
  simp [Finset.mem_singleton]

/-- Anti-support collapse: singleton anti-support equals negation of
    classical evaluation. -/
theorem classicalCollapseAnti (M : BSMLModel W)
    (φ : BSMLFormula) (w : W)
    (hNE : φ.isNEFree = true) :
    antiSupport M φ {w} ↔ classicalEval M φ w = false := by
  rw [(neFree_flat_eq M φ {w} hNE).2]
  simp [Finset.mem_singleton]

-- ============================================================================
-- §4: NE-free Formulas are Flat (Corollary of Fact 15)
-- ============================================================================

/-- NE-free formulas have flat support: team support = pointwise classical
    evaluation on all members. -/
theorem neFree_flat (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hNE : φ.isNEFree = true) :
    support M φ t ↔ ∀ w ∈ t, classicalEval M φ w = true :=
  (neFree_flat_eq M φ t hNE).1

-- ============================================================================
-- §5: BSML–CML Type Bridge
-- ============================================================================

open Core.IntensionalLogic.RestrictedModality (BAccessRel kripkeEval)
open Core.Proposition (FiniteWorlds)

/-!
### Accessibility Type Bridge

`BSMLModel.access : W → Finset W` can be converted to `BAccessRel W = W → W → Bool`
via `fun w v => decide (v ∈ M.access w)`.
-/

/-- Convert BSML accessibility to a classical accessibility relation. -/
def BSMLModel.toAccessRel (M : BSMLModel W) : BAccessRel W :=
  fun w v => decide (v ∈ M.access w)

/-- `classicalEval` of ◇φ agrees with `kripkeEval` at `.possibility`,
    connecting BSML's classical evaluation to the shared modal logic
    infrastructure from `Core.IntensionalLogic.RestrictedModality`. -/
theorem classicalEval_agrees_kripkeEval_poss
    [fw : FiniteWorlds W]
    (M : BSMLModel W) (φ : BSMLFormula) (w : W)
    (hworlds : ∀ v, v ∈ fw.worlds) :
    classicalEval M (.poss φ) w =
    kripkeEval M.toAccessRel .possibility (classicalEval M φ) w := by
  simp only [classicalEval, kripkeEval]
  cases h : decide (∃ v ∈ M.access w, classicalEval M φ v = true)
  · -- No accessible world satisfies φ
    symm; apply Bool.eq_false_iff.mpr; intro hany
    obtain ⟨v, hv_mem, hvboth⟩ := List.any_eq_true.mp hany
    simp only [List.mem_filter, BSMLModel.toAccessRel, decide_eq_true_eq] at hv_mem
    rw [decide_eq_false_iff_not] at h
    exact absurd ⟨v, hv_mem.2, hvboth⟩ h
  · -- Some accessible world satisfies φ
    obtain ⟨v, hv, hce⟩ := of_decide_eq_true h
    symm; apply List.any_eq_true.mpr
    exact ⟨v, List.mem_filter.mpr ⟨hworlds v, by
      simp only [BSMLModel.toAccessRel, decide_eq_true_eq]; exact hv⟩, hce⟩

end Semantics.BSML
