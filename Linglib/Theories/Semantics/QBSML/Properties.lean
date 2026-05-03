import Linglib.Theories.Semantics.QBSML.Defs
import Linglib.Core.Logic.Team.Properties

/-!
# QBSML formula properties — Anttila 2021 Proposition 2.2.8 (substrate test)

@cite{aloni-vanormondt-2023} @cite{anttila-2021}

**Substrate test**: prove the three structural properties from Anttila 2021
Proposition 2.2.8 for QBSML's `support` relation, using the SAME
`Core.Logic.Team.flat_iff_downwardClosed_unionClosed_emptyTeam` template that
BSML uses (via `Theories/Semantics/BSML/Properties.lean`).

The substrate composes for first-order team semantics: the bilateral mutual
induction pattern from BSML carries over directly, with additional cases for
quantifiers `exi` and `univ` using
`State.extendUniversal_union_distrib`, `State.extendUniversal_subset_mono`,
`State.extendFunctional_union_distrib`, `State.extendFunctional_subset_mono`
from `Defs.lean`.

## Why one big joint induction (not two)

BSML splits the proof into separate joint inductions per property
(unionClosed standalone, downwardClosed standalone, emptyTeam standalone).
That works because BSML's `unionClosed` is unconditional — no operator in
BSML needs `downwardClosed` of its subformula to establish union closure.

QBSML's `exi` (and dually antiSupport `univ`) is different. The union case
of support `exi x ψ` constructs a witness `h_st` from the witnesses on `s`
and `t`, leaving an `(t \ s).extendFunctional x h_t` term that has to be
weakened to `t.extendFunctional x h_t` via `State.extendFunctional_subset_mono`
plus downward closure of ψ. So the proof of UC needs DC of ψ as IH —
which only works if both properties are proved in a single joint induction.

This narrows the result: QBSML's `unionClosed` requires NE-free (BSML's
doesn't). The flat corollary still composes, since flat consumers use
NE-free anyway.

## Status

- `emptyTeam_support_of_isNEFree`: **fully proved** (joint bilateral induction
  over all 8 QBSMLFormula constructors).
- `unionClosed_support_of_isNEFree`, `downwardClosed_support_of_isNEFree`:
  **fully proved** via single 4-property joint bilateral induction.
- `flat_support_of_isNEFree` corollary: derives via
  `Core.Logic.Team.flat_of_downwardClosed_unionClosed_emptyTeam`.
-/

namespace Semantics.QBSML

open Core.Logic.Team

variable {W Var Domain Pred : Type*}
variable [DecidableEq W] [Fintype W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

-- ============================================================================
-- §1 Joint empty-team property — bilateral induction
-- ============================================================================

/-- Joint empty-team property: NE-free QBSML formulas have BOTH support and
    anti-support on the empty team. The bilateral mutual induction handles
    the negation case (where support flips to antiSupport). All quantifier
    cases use `State.extendUniversal_empty` and `State.extendFunctional_empty`. -/
private theorem support_and_antiSupport_empty_of_isNEFree
    (φ : QBSMLFormula Var Pred) (hNE : φ.isNEFree = true)
    (M : QBSMLModel W Domain Pred) :
    support M φ (∅ : Finset (Index W Var Domain)) ∧
    antiSupport M φ (∅ : Finset (Index W Var Domain)) := by
  induction φ with
  | pred P x =>
    refine ⟨?_, ?_⟩
    · intro i hi; exact absurd hi (by simp)
    · intro i hi; exact absurd hi (by simp)
  | ne => simp [QBSMLFormula.isNEFree] at hNE
  | neg ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨hs, ha⟩ := ih hψ
    -- support (¬ψ) = antiSupport ψ; antiSupport (¬ψ) = support ψ
    exact ⟨ha, hs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨hs₁, ha₁⟩ := ih₁ h₁
    have ⟨hs₂, ha₂⟩ := ih₂ h₂
    refine ⟨⟨hs₁, hs₂⟩, ?_⟩
    -- antiSupport (φ₁ ∧ φ₂) ∅: split (∅, ∅)
    refine ⟨∅, ∅, ?_, ha₁, ha₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨hs₁, ha₁⟩ := ih₁ h₁
    have ⟨hs₂, ha₂⟩ := ih₂ h₂
    refine ⟨?_, ⟨ha₁, ha₂⟩⟩
    refine ⟨∅, ∅, ?_, hs₁, hs₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | poss ψ _ih =>
    refine ⟨?_, ?_⟩
    · intro i hi; exact absurd hi (by simp)
    · intro i hi; exact absurd hi (by simp)
  | exi x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨hs, ha⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · -- support (∃x ψ) ∅: take h := fun _ => Finset.univ; vacuous nonempty
      -- Note: this requires Domain to be nonempty for h to be nonempty,
      -- but vacuously holds since there are no i ∈ ∅.
      refine ⟨fun _ => ∅, fun i hi => absurd hi (by simp), ?_⟩
      -- support ψ (∅.extendFunctional x (fun _ => ∅)) = support ψ ∅
      rw [State.extendFunctional_empty]
      exact hs
    · -- antiSupport (∃x ψ) ∅ = antiSupport ψ (∅.extendUniversal x) = antiSupport ψ ∅
      show antiSupport M ψ (State.extendUniversal (∅ : Finset (Index W Var Domain)) x)
      rw [State.extendUniversal_empty]
      exact ha
  | univ x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨hs, ha⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · -- support (∀x ψ) ∅ = support ψ (∅.extendUniversal x) = support ψ ∅
      show support M ψ (State.extendUniversal (∅ : Finset (Index W Var Domain)) x)
      rw [State.extendUniversal_empty]
      exact hs
    · -- antiSupport (∀x ψ) ∅: take h := fun _ => ∅; vacuous nonempty
      refine ⟨fun _ => ∅, fun i hi => absurd hi (by simp), ?_⟩
      rw [State.extendFunctional_empty]
      exact ha

/-- NE-free QBSML formulas are supported on the empty team. -/
theorem emptyTeam_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.emptyTeam (support (W := W) (Domain := Domain)) φ :=
  fun M => (support_and_antiSupport_empty_of_isNEFree φ hNE M).1

-- ============================================================================
-- §2 Joint downward + union closure for NE-free QBSML formulas
-- ============================================================================

/-- Joint statement of all four closure properties for both polarities of an
    NE-free QBSML formula. The union case of `exi` (and antiSupport `univ`)
    needs the IH's downward closure for ψ to weaken
    `t.extendFunctional x h_t` to `(t \ s).extendFunctional x h_t`, so all
    four properties have to live inside one induction. -/
private theorem support_and_antiSupport_dc_uc_of_isNEFree
    (φ : QBSMLFormula Var Pred) (hNE : φ.isNEFree = true)
    (M : QBSMLModel W Domain Pred) :
    -- (1) DC support
    (∀ s t : Finset (Index W Var Domain), t ⊆ s → support M φ s → support M φ t) ∧
    -- (2) UC support
    (∀ s t : Finset (Index W Var Domain),
      support M φ s → support M φ t → support M φ (s ∪ t)) ∧
    -- (3) DC antiSupport
    (∀ s t : Finset (Index W Var Domain),
      t ⊆ s → antiSupport M φ s → antiSupport M φ t) ∧
    -- (4) UC antiSupport
    (∀ s t : Finset (Index W Var Domain),
      antiSupport M φ s → antiSupport M φ t → antiSupport M φ (s ∪ t)) := by
  induction φ with
  | pred P x =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s t hsub hsupp i hi; exact hsupp i (hsub hi)
    · intro s t hs ht i hi; simp [Finset.mem_union] at hi
      cases hi with
      | inl h => exact hs i h
      | inr h => exact ht i h
    · intro s t hsub hsupp i hi; exact hsupp i (hsub hi)
    · intro s t hs ht i hi; simp [Finset.mem_union] at hi
      cases hi with
      | inl h => exact hs i h
      | inr h => exact ht i h
  | ne => simp [QBSMLFormula.isNEFree] at hNE
  | neg ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ihdc_s, ihuc_s, ihdc_a, ihuc_a⟩ := ih hψ
    -- support (¬ψ) = antiSupport ψ; antiSupport (¬ψ) = support ψ
    exact ⟨ihdc_a, ihuc_a, ihdc_s, ihuc_s⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ihdc_s₁, ihuc_s₁, ihdc_a₁, ihuc_a₁⟩ := ih₁ h₁
    have ⟨ihdc_s₂, ihuc_s₂, ihdc_a₂, ihuc_a₂⟩ := ih₂ h₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- DC support: conj of two supports
      intro s t hsub ⟨hs₁, hs₂⟩
      exact ⟨ihdc_s₁ s t hsub hs₁, ihdc_s₂ s t hsub hs₂⟩
    · -- UC support: conj of two supports
      intro s t ⟨hs₁, hs₂⟩ ⟨ht₁, ht₂⟩
      exact ⟨ihuc_s₁ s t hs₁ ht₁, ihuc_s₂ s t hs₂ ht₂⟩
    · -- DC antiSupport: ∃ split (t₁,t₂) of s; intersect with t
      intro s t hsub ⟨t₁, t₂, hsplit, ha₁, ha₂⟩
      refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, ?_, ?_⟩
      · unfold Core.Logic.Team.splitsAs
        rw [show (t₁ ∩ t) ∪ (t₂ ∩ t) = (t₁ ∪ t₂) ∩ t from by
          ext x; simp [Finset.mem_inter, Finset.mem_union]; tauto]
        have heq : t₁ ∪ t₂ = s := hsplit
        rw [heq]
        exact Finset.inter_eq_right.mpr hsub
      · exact ihdc_a₁ t₁ (t₁ ∩ t) Finset.inter_subset_left ha₁
      · exact ihdc_a₂ t₂ (t₂ ∩ t) Finset.inter_subset_left ha₂
    · -- UC antiSupport: combine splits
      intro s t ⟨s₁, s₂, hsplit_s, ha_s₁, ha_s₂⟩ ⟨t₁, t₂, hsplit_t, ha_t₁, ha_t₂⟩
      refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, ?_, ?_⟩
      · unfold Core.Logic.Team.splitsAs
        have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
          ext x; simp [Finset.mem_union]; tauto]
        rw [h1, h2]
      · exact ihuc_a₁ s₁ t₁ ha_s₁ ha_t₁
      · exact ihuc_a₂ s₂ t₂ ha_s₂ ha_t₂
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ihdc_s₁, ihuc_s₁, ihdc_a₁, ihuc_a₁⟩ := ih₁ h₁
    have ⟨ihdc_s₂, ihuc_s₂, ihdc_a₂, ihuc_a₂⟩ := ih₂ h₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- DC support: ∃ split (t₁,t₂) of s; intersect with t
      intro s t hsub ⟨t₁, t₂, hsplit, hs₁, hs₂⟩
      refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, ?_, ?_⟩
      · unfold Core.Logic.Team.splitsAs
        rw [show (t₁ ∩ t) ∪ (t₂ ∩ t) = (t₁ ∪ t₂) ∩ t from by
          ext x; simp [Finset.mem_inter, Finset.mem_union]; tauto]
        have heq : t₁ ∪ t₂ = s := hsplit
        rw [heq]
        exact Finset.inter_eq_right.mpr hsub
      · exact ihdc_s₁ t₁ (t₁ ∩ t) Finset.inter_subset_left hs₁
      · exact ihdc_s₂ t₂ (t₂ ∩ t) Finset.inter_subset_left hs₂
    · -- UC support: combine splits
      intro s t ⟨s₁, s₂, hsplit_s, hs_s₁, hs_s₂⟩ ⟨t₁, t₂, hsplit_t, hs_t₁, hs_t₂⟩
      refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, ?_, ?_⟩
      · unfold Core.Logic.Team.splitsAs
        have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
          ext x; simp [Finset.mem_union]; tauto]
        rw [h1, h2]
      · exact ihuc_s₁ s₁ t₁ hs_s₁ hs_t₁
      · exact ihuc_s₂ s₂ t₂ hs_s₂ hs_t₂
    · -- DC antiSupport: conj of two antiSupports
      intro s t hsub ⟨ha₁, ha₂⟩
      exact ⟨ihdc_a₁ s t hsub ha₁, ihdc_a₂ s t hsub ha₂⟩
    · -- UC antiSupport: conj of two antiSupports
      intro s t ⟨ha₁, ha₂⟩ ⟨ht₁, ht₂⟩
      exact ⟨ihuc_a₁ s t ha₁ ht₁, ihuc_a₂ s t ha₂ ht₂⟩
  | poss ψ _ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s t hsub hsupp i hi; exact hsupp i (hsub hi)
    · intro s t hs ht i hi; simp [Finset.mem_union] at hi
      cases hi with
      | inl h => exact hs i h
      | inr h => exact ht i h
    · intro s t hsub hsupp i hi; exact hsupp i (hsub hi)
    · intro s t hs ht i hi; simp [Finset.mem_union] at hi
      cases hi with
      | inl h => exact hs i h
      | inr h => exact ht i h
  | exi x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ihdc_s, ihuc_s, ihdc_a, ihuc_a⟩ := ih hψ
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- DC support exi: same h works on subteam (via extendFunctional_subset_mono + IH DC)
      intro s t hsub ⟨h, hne, hsupp⟩
      refine ⟨h, fun i hi => hne i (hsub hi), ?_⟩
      exact ihdc_s _ _
        (State.extendFunctional_subset_mono x h hsub) hsupp
    · -- UC support exi: combine h_s, h_t into h_st via if-then-else
      intro s t ⟨h_s, hne_s, hsupp_s⟩ ⟨h_t, hne_t, hsupp_t⟩
      classical
      refine ⟨fun i => if i ∈ s then h_s i else h_t i, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with hs | ht
        · simp [hs]; exact hne_s i hs
        · by_cases his : i ∈ s
          · simp [his]; exact hne_s i his
          · simp [his]; exact hne_t i ht
      · -- Goal: support ψ (extendFunctional (s ∪ t) x h_st)
        --      = extendFunctional s x h_s ∪ extendFunctional (t \ s) x h_t
        have eq1 : State.extendFunctional (s ∪ t) x
                     (fun i => if i ∈ s then h_s i else h_t i)
                 = State.extendFunctional s x h_s ∪
                     State.extendFunctional (t \ s) x h_t := by
          have decomp : s ∪ t = s ∪ (t \ s) := by
            ext y; simp [Finset.mem_union]
          rw [decomp, State.extendFunctional_union_distrib]
          congr 1
          · unfold State.extendFunctional
            apply Finset.biUnion_congr rfl
            intro i hi; simp [hi]
          · unfold State.extendFunctional
            apply Finset.biUnion_congr rfl
            intro i hi
            have : i ∉ s := (Finset.mem_sdiff.mp hi).2
            simp [this]
        rw [eq1]
        -- support ψ on extendFunctional s x h_s — given by hsupp_s
        -- support ψ on extendFunctional (t \ s) x h_t — by IH DC of ψ
        have h_ext : support M ψ (State.extendFunctional (t \ s) x h_t) :=
          ihdc_s _ _
            (State.extendFunctional_subset_mono x h_t Finset.sdiff_subset) hsupp_t
        exact ihuc_s _ _ hsupp_s h_ext
    · -- DC antiSupport exi: extendUniversal t x ⊆ extendUniversal s x + IH DC
      intro s t hsub hsupp
      show antiSupport M ψ (State.extendUniversal t x)
      exact ihdc_a _ _ (State.extendUniversal_subset_mono x hsub) hsupp
    · -- UC antiSupport exi: extendUniversal distributes + IH UC
      intro s t hs ht
      show antiSupport M ψ (State.extendUniversal (s ∪ t) x)
      rw [State.extendUniversal_union_distrib]
      exact ihuc_a _ _ hs ht
  | univ x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ihdc_s, ihuc_s, ihdc_a, ihuc_a⟩ := ih hψ
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- DC support univ: extendUniversal t x ⊆ extendUniversal s x + IH DC
      intro s t hsub hsupp
      show support M ψ (State.extendUniversal t x)
      exact ihdc_s _ _ (State.extendUniversal_subset_mono x hsub) hsupp
    · -- UC support univ: extendUniversal distributes + IH UC
      intro s t hs ht
      show support M ψ (State.extendUniversal (s ∪ t) x)
      rw [State.extendUniversal_union_distrib]
      exact ihuc_s _ _ hs ht
    · -- DC antiSupport univ: same h works on subteam (mirror of DC support exi)
      intro s t hsub ⟨h, hne, hsupp⟩
      refine ⟨h, fun i hi => hne i (hsub hi), ?_⟩
      exact ihdc_a _ _
        (State.extendFunctional_subset_mono x h hsub) hsupp
    · -- UC antiSupport univ: combine h_s, h_t (mirror of UC support exi)
      intro s t ⟨h_s, hne_s, hsupp_s⟩ ⟨h_t, hne_t, hsupp_t⟩
      classical
      refine ⟨fun i => if i ∈ s then h_s i else h_t i, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with hs | ht
        · simp [hs]; exact hne_s i hs
        · by_cases his : i ∈ s
          · simp [his]; exact hne_s i his
          · simp [his]; exact hne_t i ht
      · have eq1 : State.extendFunctional (s ∪ t) x
                     (fun i => if i ∈ s then h_s i else h_t i)
                 = State.extendFunctional s x h_s ∪
                     State.extendFunctional (t \ s) x h_t := by
          have decomp : s ∪ t = s ∪ (t \ s) := by
            ext y; simp [Finset.mem_union]
          rw [decomp, State.extendFunctional_union_distrib]
          congr 1
          · unfold State.extendFunctional
            apply Finset.biUnion_congr rfl
            intro i hi; simp [hi]
          · unfold State.extendFunctional
            apply Finset.biUnion_congr rfl
            intro i hi
            have : i ∉ s := (Finset.mem_sdiff.mp hi).2
            simp [this]
        rw [eq1]
        have h_ext : antiSupport M ψ (State.extendFunctional (t \ s) x h_t) :=
          ihdc_a _ _
            (State.extendFunctional_subset_mono x h_t Finset.sdiff_subset) hsupp_t
        exact ihuc_a _ _ hsupp_s h_ext

/-- NE-free QBSML formulas are downward-closed (Anttila 2.2.8 part 1
    extended to first-order). -/
theorem downwardClosed_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.downwardClosed (support (W := W) (Domain := Domain)) φ :=
  fun M s t hsub hsupp =>
    (support_and_antiSupport_dc_uc_of_isNEFree φ hNE M).1 s t hsub hsupp

/-- NE-free QBSML formulas are union-closed.

    NB: Stronger than BSML's `unionClosed_support` requires no NE-free
    hypothesis, but QBSML's `exi` UC needs DC of ψ as IH (see file
    docstring), so we narrow to NE-free. The downstream flat corollary
    consumes NE-free anyway. -/
theorem unionClosed_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.unionClosed (support (W := W) (Domain := Domain)) φ :=
  fun M s t hs ht =>
    (support_and_antiSupport_dc_uc_of_isNEFree φ hNE M).2.1 s t hs ht

-- ============================================================================
-- §3 Corollary: NE-free QBSML formulas are flat
-- ============================================================================

/-- **Anttila Proposition 2.2.16 (QBSML specialization)**: NE-free QBSML
    formulas are flat. Same call structure as BSML's `flat_support_of_isNEFree`
    — substrate validates. -/
theorem flat_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.flat (support (W := W) (Domain := Domain)) φ :=
  Core.Logic.Team.flat_of_downwardClosed_unionClosed_emptyTeam
    (downwardClosed_support_of_isNEFree hNE)
    (unionClosed_support_of_isNEFree hNE)
    (emptyTeam_support_of_isNEFree hNE)

end Semantics.QBSML
