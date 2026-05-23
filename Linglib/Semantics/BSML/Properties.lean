import Linglib.Semantics.BSML.Defs
import Linglib.Core.Logic.Team.Closure

/-!
# BSML formula closure properties (Anttila 2021 Proposition 2.2.8)

@cite{anttila-2021} @cite{aloni-2022}

For BSML's `support` relation, this file proves the three constituent
properties from Anttila 2021 Proposition 2.2.8 (specialised to a logic
without global disjunction ⨼) plus the flatness corollary from Anttila
2.2.16 / @cite{aloni-2022} Fact 15.

## Main declarations

* `supClosed_support` — every BSML formula has sup-closed support
  (Anttila 2.2.8 part 2; BSML's connective set has no ⨼, so the
  union-closure obstruction is absent).
* `support_empty_of_isNEFree` — NE-free BSML formulas are supported on
  the empty team (Anttila 2.2.8 part 1).
* `isLowerSet_support_of_isNEFree` — NE-free BSML formulas are
  downward-closed (Anttila 2.2.8 part 1).
* `isFlat_support_of_isNEFree` — NE-free BSML formulas are flat
  (Anttila 2.2.16 / @cite{aloni-2022} Fact 15), derived via Anttila
  Proposition 2.2.2 from the three properties above.

## Implementation notes

The negation case needs bilateral mutual induction (support of `¬φ` is
anti-support of `φ`), so each property is proved as a *joint* statement
over support + anti-support via a `private` helper, then the public form
projects the support component.

A direct flatness proof is also available in `Bridge.lean` as
`neFree_flat_eq`, which proves the stronger statement `support t ↔ ∀ w ∈ t,
classicalEval w` (flatness + classical-evaluation bridge). This file's
proof routes through the foundational decomposition; `neFree_flat_eq`
provides the additional bridge to classical Kripke semantics.

The decomposition through Anttila 2.2.8 + 2.2.2 is reusable: any future
team-semantic logic in linglib (QBSML, inquisitive, dependence logic)
needs the same structural argument — proving the three closure properties
separately and composing them via `Core.Logic.Team.isFlat_iff`.
-/

namespace Semantics.BSML

open Core.Logic.Team

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

/-! ### Sup-closure (Anttila 2.2.8 part 2) -/

/-- Joint union closure for both polarities. The conj-anti-support and
    disj-support cases need mutual induction on partitions; the neg case
    needs the polarity flip. -/
private theorem support_and_antiSupport_unionClosed
    (φ : BSMLFormula Atom) (M : BSMLModel W Atom) :
    (∀ s t : Finset W, support M φ s → support M φ t → support M φ (s ∪ t)) ∧
    (∀ s t : Finset W, antiSupport M φ s → antiSupport M φ t → antiSupport M φ (s ∪ t)) := by
  induction φ with
  | atom p =>
    refine ⟨?_, ?_⟩
    · intro s t hs ht w hw; simp [Finset.mem_union] at hw
      cases hw with
      | inl h => exact hs w h
      | inr h => exact ht w h
    · intro s t hs ht w hw; simp [Finset.mem_union] at hw
      cases hw with
      | inl h => exact hs w h
      | inr h => exact ht w h
  | ne =>
    refine ⟨?_, ?_⟩
    · -- support NE s = s.Nonempty; union of nonempty is nonempty
      intro s t hs _ht
      exact hs.mono (Finset.subset_union_left)
    · -- antiSupport NE s = (s = ∅); union of two empties is empty
      intro s t hs ht
      show s ∪ t = ∅
      rw [hs, ht]; simp
  | neg ψ ih =>
    have ⟨ihs, iha⟩ := ih
    -- support (¬ψ) = antiSupport ψ; antiSupport (¬ψ) = support ψ
    exact ⟨iha, ihs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨ihs₁, iha₁⟩ := ih₁
    have ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · -- support: conjunction of supports; both halves union-close by IH
      intro s t ⟨hs₁, hs₂⟩ ⟨ht₁, ht₂⟩
      exact ⟨ihs₁ s t hs₁ ht₁, ihs₂ s t hs₂ ht₂⟩
    · -- antiSupport: split (s₁, s₂) of s and (t₁, t₂) of t; combine into
      -- (s₁ ∪ t₁, s₂ ∪ t₂) of s ∪ t. By IH for antiSupport.
      intro s t ⟨s₁, s₂, hsplit_s, ha_s₁, ha_s₂⟩ ⟨t₁, t₂, hsplit_t, ha_t₁, ha_t₂⟩
      refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, ?_, ?_⟩
      · have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
        rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
          ext x; simp [Finset.mem_union]; tauto]
        rw [h1, h2]
      · exact iha₁ s₁ t₁ ha_s₁ ha_t₁
      · exact iha₂ s₂ t₂ ha_s₂ ha_t₂
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨ihs₁, iha₁⟩ := ih₁
    have ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · -- support: split (s₁, s₂) of s and (t₁, t₂) of t; combine.
      intro s t ⟨s₁, s₂, hsplit_s, hs_s₁, hs_s₂⟩ ⟨t₁, t₂, hsplit_t, hs_t₁, hs_t₂⟩
      refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, ?_, ?_⟩
      · have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
        rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
          ext x; simp [Finset.mem_union]; tauto]
        rw [h1, h2]
      · exact ihs₁ s₁ t₁ hs_s₁ hs_t₁
      · exact ihs₂ s₂ t₂ hs_s₂ hs_t₂
    · -- antiSupport: conjunction of antiSupports.
      intro s t ⟨ha_s₁, ha_s₂⟩ ⟨ha_t₁, ha_t₂⟩
      exact ⟨iha₁ s t ha_s₁ ha_t₁, iha₂ s t ha_s₂ ha_t₂⟩
  | poss ψ _ih =>
    refine ⟨?_, ?_⟩
    · -- support (◇ψ) s = ∀ w ∈ s, ∃ subteam. For w ∈ s ∪ t, case split.
      intro s t hs ht w hw
      simp [Finset.mem_union] at hw
      cases hw with
      | inl h => exact hs w h
      | inr h => exact ht w h
    · -- antiSupport (◇ψ) s = ∀ w ∈ s, antiSupport ψ R[w]. Same per-w argument.
      intro s t hs ht w hw
      simp [Finset.mem_union] at hw
      cases hw with
      | inl h => exact hs w h
      | inr h => exact ht w h

/-- BSML support is sup-closed (Anttila Proposition 2.2.8 part 2). BSML's
    connective set lacks the global disjunction ⨼, so the union-closure
    obstruction is absent and all formulas satisfy the property. -/
theorem supClosed_support (M : BSMLModel W Atom) (φ : BSMLFormula Atom) :
    SupClosed { t : Finset W | support M φ t } :=
  fun _ ha _ hb => (support_and_antiSupport_unionClosed φ M).1 _ _ ha hb

/-! ### Empty-team property for NE-free formulas (Anttila 2.2.8 part 1) -/

/-- Joint empty-team property: NE-free formulas have BOTH support and
    anti-support on the empty team. Used as the engine for the bilateral
    mutual induction needed by the negation case. -/
private theorem support_and_antiSupport_empty_of_isNEFree
    (φ : BSMLFormula Atom) (hNE : φ.isNEFree = true) (M : BSMLModel W Atom) :
    support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p =>
    refine ⟨?_, ?_⟩
    · intro w hw; exact absurd hw (by simp)
    · intro w hw; exact absurd hw (by simp)
  | ne => simp [BSMLFormula.isNEFree] at hNE
  | neg ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [BSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨hs, ha⟩ := ih hψ
    -- support (¬ψ) ∅ = antiSupport ψ ∅; antiSupport (¬ψ) ∅ = support ψ ∅
    exact ⟨ha, hs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨hs₁, ha₁⟩ := ih₁ h₁
    have ⟨hs₂, ha₂⟩ := ih₂ h₂
    refine ⟨⟨hs₁, hs₂⟩, ?_⟩
    -- antiSupport (φ₁ ∧ φ₂) ∅ = ∃ t₁ t₂ : Finset W, splitsAs ∅ t₁ t₂ ∧ antiSupport φ₁ t₁ ∧ antiSupport φ₂ t₂
    -- Take t₁ = ∅, t₂ = ∅
    refine ⟨∅, ∅, ?_, ha₁, ha₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨hs₁, ha₁⟩ := ih₁ h₁
    have ⟨hs₂, ha₂⟩ := ih₂ h₂
    refine ⟨?_, ⟨ha₁, ha₂⟩⟩
    -- support (φ₁ ∨ φ₂) ∅ = ∃ t₁ t₂ : Finset W, splitsAs ∅ t₁ t₂ ∧ support φ₁ t₁ ∧ support φ₂ t₂
    refine ⟨∅, ∅, ?_, hs₁, hs₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | poss ψ _ih =>
    refine ⟨?_, ?_⟩
    · intro w hw; exact absurd hw (by simp)
    · intro w hw; exact absurd hw (by simp)

/-- NE-free BSML formulas are supported on the empty team. The only
    obstruction is NE itself, which fails on ∅ by definition. -/
theorem support_empty_of_isNEFree {φ : BSMLFormula Atom}
    (hNE : φ.isNEFree = true) (M : BSMLModel W Atom) : support M φ ∅ :=
  (support_and_antiSupport_empty_of_isNEFree φ hNE M).1

/-! ### Downward closure for NE-free formulas (Anttila 2.2.8 part 1) -/

/-- Joint downward closure: NE-free formulas have BOTH support and
    anti-support downward-closed. The bilateral mutual induction handles
    the negation case (where support flips to antiSupport). -/
private theorem support_and_antiSupport_downward_of_isNEFree
    (φ : BSMLFormula Atom) (hNE : φ.isNEFree = true)
    (M : BSMLModel W Atom) :
    (∀ s t : Finset W, t ⊆ s → support M φ s → support M φ t) ∧
    (∀ s t : Finset W, t ⊆ s → antiSupport M φ s → antiSupport M φ t) := by
  induction φ with
  | atom p =>
    refine ⟨?_, ?_⟩
    · intro s t hsub hsupp w hw; exact hsupp w (hsub hw)
    · intro s t hsub hsupp w hw; exact hsupp w (hsub hw)
  | ne => simp [BSMLFormula.isNEFree] at hNE
  | neg ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [BSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ihs, iha⟩ := ih hψ
    -- support (¬ψ) = antiSupport ψ; antiSupport (¬ψ) = support ψ
    exact ⟨iha, ihs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ihs₁, iha₁⟩ := ih₁ h₁
    have ⟨ihs₂, iha₂⟩ := ih₂ h₂
    refine ⟨?_, ?_⟩
    · -- support: conjunction of two supports survives ⊆
      intro s t hsub ⟨hs₁, hs₂⟩
      exact ⟨ihs₁ s t hsub hs₁, ihs₂ s t hsub hs₂⟩
    · -- antiSupport: split into (t₁, t₂); for t ⊆ s, intersect
      intro s t hsub ⟨t₁, t₂, hsplit, ha₁, ha₂⟩
      refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, ?_, ?_⟩
      · -- splitsAs t (t₁∩t) (t₂∩t) := (t₁∩t) ∪ (t₂∩t) = t
        show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
        rw [show (t₁ ∩ t) ∪ (t₂ ∩ t) = (t₁ ∪ t₂) ∩ t from by
          ext x; simp [Finset.mem_inter, Finset.mem_union]; tauto]
        have heq : t₁ ∪ t₂ = s := hsplit
        rw [heq]
        exact Finset.inter_eq_right.mpr hsub
      · exact iha₁ t₁ (t₁ ∩ t) (Finset.inter_subset_left) ha₁
      · exact iha₂ t₂ (t₂ ∩ t) (Finset.inter_subset_left) ha₂
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ihs₁, iha₁⟩ := ih₁ h₁
    have ⟨ihs₂, iha₂⟩ := ih₂ h₂
    refine ⟨?_, ?_⟩
    · -- support: split into (t₁, t₂); for t ⊆ s, intersect
      intro s t hsub ⟨t₁, t₂, hsplit, hs₁, hs₂⟩
      refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, ?_, ?_⟩
      · show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
        rw [show (t₁ ∩ t) ∪ (t₂ ∩ t) = (t₁ ∪ t₂) ∩ t from by
          ext x; simp [Finset.mem_inter, Finset.mem_union]; tauto]
        have heq : t₁ ∪ t₂ = s := hsplit
        rw [heq]
        exact Finset.inter_eq_right.mpr hsub
      · exact ihs₁ t₁ (t₁ ∩ t) (Finset.inter_subset_left) hs₁
      · exact ihs₂ t₂ (t₂ ∩ t) (Finset.inter_subset_left) hs₂
    · -- antiSupport: conjunction of two antiSupports survives ⊆
      intro s t hsub ⟨ha₁, ha₂⟩
      exact ⟨iha₁ s t hsub ha₁, iha₂ s t hsub ha₂⟩
  | poss ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [BSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨_, _⟩ := ih hψ  -- IHs not used directly; the modal cases hold from per-w structure
    refine ⟨?_, ?_⟩
    · -- support (◇ψ) s = ∀ w ∈ s, ∃ subteam ⊆ R[w], nonempty, support ψ subteam.
      -- For t ⊆ s, ∀ w ∈ t, w ∈ s, so the per-w property holds.
      intro s t hsub hsupp w hw
      exact hsupp w (hsub hw)
    · -- antiSupport (◇ψ) s = ∀ w ∈ s, antiSupport ψ R[w]. Same per-w argument.
      intro s t hsub hasupp w hw
      exact hasupp w (hsub hw)

/-- NE-free BSML formulas are downward-closed: support survives under
    taking subsets of the team. -/
theorem isLowerSet_support_of_isNEFree {φ : BSMLFormula Atom}
    (hNE : φ.isNEFree = true) (M : BSMLModel W Atom) :
    IsLowerSet { t : Finset W | support M φ t } :=
  fun _ _ hab hb =>
    (support_and_antiSupport_downward_of_isNEFree φ hNE M).1 _ _ hab hb

/-! ### Flatness corollary (Anttila 2.2.16) -/

/-- **Anttila Proposition 2.2.16** (BSML specialisation of Fact 15 from
    @cite{aloni-2022}): NE-free BSML formulas are flat — team support
    equals pointwise support at each world in the team.

    Derived from Anttila 2.2.2 (`Core.Logic.Team.isFlat_iff`) applied to
    the three closure properties proved above. The same conclusion has a
    direct classical-evaluation-bridge proof in `Bridge.lean` as
    `neFree_flat_eq`. -/
theorem isFlat_support_of_isNEFree {φ : BSMLFormula Atom}
    (hNE : φ.isNEFree = true) (M : BSMLModel W Atom) :
    IsFlat { t : Finset W | support M φ t } :=
  isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_support_of_isNEFree hNE M)
    (supClosed_support M φ)
    (support_empty_of_isNEFree hNE M)

end Semantics.BSML
