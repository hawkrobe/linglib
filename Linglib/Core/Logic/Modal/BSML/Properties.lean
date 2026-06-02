import Linglib.Core.Logic.Modal.BSML.Defs
import Linglib.Core.Logic.Team.Closure
import Linglib.Core.Logic.Team.Definability

/-!
# BSML formula closure properties (Anttila 2021 Proposition 2.2.8)

[anttila-2021] [aloni-2022]

For BSML's `support` relation, this file proves the three constituent
properties from Anttila 2021 Proposition 2.2.8 (specialised to a logic
without global disjunction ⨼) plus the flatness corollary from Anttila
2.2.16 / [aloni-2022] Fact 15.

## Main declarations

* `supClosed_support` — every BSML formula has sup-closed support
  (Anttila 2.2.8 part 2; BSML's connective set has no ⨼, so the
  union-closure obstruction is absent).
* `support_empty_of_isNEFree` — NE-free BSML formulas are supported on
  the empty team (Anttila 2.2.8 part 1).
* `isLowerSet_support_of_isNEFree` — NE-free BSML formulas are
  downward-closed (Anttila 2.2.8 part 1).
* `isFlat_support_of_isNEFree` — NE-free BSML formulas are flat
  (Anttila 2.2.16 / [aloni-2022] Fact 15), derived via Anttila
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

namespace Core.Logic.Modal.BSML

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

/-! ### Convexity for all formulas (Anttila 2025, Proposition 3.3.1) -/

/-- Joint order-convexity for both polarities. The split cases (`disj`-support,
    `conj`-antisupport) are the crux: given a lower split `s₁ ∪ s₂` and an upper
    split `u₁ ∪ u₂`, the middle team `t` is split as `(sᵢ ∪ uᵢ) ∩ t`, and each
    part satisfies its subformula by convexity (IH) between `sᵢ` and `sᵢ ∪ uᵢ`,
    the upper endpoint holding by **union closure**
    (`support_and_antiSupport_unionClosed`). This is exactly why split
    disjunction preserves convexity only in a union-closed setting
    ([anttila-2025] Fact 3.2.7 vs Proposition 3.3.1). The other cases use a
    single endpoint: the upper (downward-closed-style) for atom, poss and the
    negative polarities; the lower for `ne` (nonemptiness is upward closed). -/
private theorem support_and_antiSupport_ordConnected
    (φ : BSMLFormula Atom) (M : BSMLModel W Atom) :
    (∀ s t u : Finset W, s ⊆ t → t ⊆ u →
      support M φ s → support M φ u → support M φ t) ∧
    (∀ s t u : Finset W, s ⊆ t → t ⊆ u →
      antiSupport M φ s → antiSupport M φ u → antiSupport M φ t) := by
  induction φ with
  | atom p =>
    refine ⟨?_, ?_⟩
    · intro s t u _hst htu _hs hu w hw; exact hu w (htu hw)
    · intro s t u _hst htu _hs hu w hw; exact hu w (htu hw)
  | ne =>
    refine ⟨?_, ?_⟩
    · intro s t u hst _htu hs _hu; exact hs.mono hst
    · intro s t u _hst htu _hs hu; rw [hu] at htu; exact Finset.subset_empty.mp htu
  | neg ψ ih =>
    obtain ⟨ihs, iha⟩ := ih
    exact ⟨iha, ihs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁
    obtain ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s t u hst htu hs hu
      obtain ⟨hs₁, hs₂⟩ := hs
      obtain ⟨hu₁, hu₂⟩ := hu
      exact ⟨ihs₁ s t u hst htu hs₁ hu₁, ihs₂ s t u hst htu hs₂ hu₂⟩
    · intro s t u hst htu hs hu
      obtain ⟨s₁, s₂, hsplit_s, ha_s₁, ha_s₂⟩ := hs
      obtain ⟨u₁, u₂, hsplit_u, ha_u₁, ha_u₂⟩ := hu
      have es : s₁ ∪ s₂ = s := hsplit_s
      have eu : u₁ ∪ u₂ = u := hsplit_u
      refine ⟨(s₁ ∪ u₁) ∩ t, (s₂ ∪ u₂) ∩ t, ?_, ?_, ?_⟩
      · show ((s₁ ∪ u₁) ∩ t) ∪ ((s₂ ∪ u₂) ∩ t) = t
        ext x
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (⟨_, hxt⟩ | ⟨_, hxt⟩) <;> exact hxt
        · intro hxt
          have hxu : x ∈ u := htu hxt
          rw [← eu, Finset.mem_union] at hxu
          rcases hxu with h | h
          · exact Or.inl ⟨Or.inr h, hxt⟩
          · exact Or.inr ⟨Or.inr h, hxt⟩
      · have hs1t : s₁ ⊆ t := by
          intro x hx; apply hst; rw [← es]; exact Finset.mem_union_left _ hx
        exact iha₁ s₁ ((s₁ ∪ u₁) ∩ t) (s₁ ∪ u₁)
          (Finset.subset_inter Finset.subset_union_left hs1t)
          Finset.inter_subset_left ha_s₁
          ((support_and_antiSupport_unionClosed ψ₁ M).2 s₁ u₁ ha_s₁ ha_u₁)
      · have hs2t : s₂ ⊆ t := by
          intro x hx; apply hst; rw [← es]; exact Finset.mem_union_right _ hx
        exact iha₂ s₂ ((s₂ ∪ u₂) ∩ t) (s₂ ∪ u₂)
          (Finset.subset_inter Finset.subset_union_left hs2t)
          Finset.inter_subset_left ha_s₂
          ((support_and_antiSupport_unionClosed ψ₂ M).2 s₂ u₂ ha_s₂ ha_u₂)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁
    obtain ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s t u hst htu hs hu
      obtain ⟨s₁, s₂, hsplit_s, hs₁, hs₂⟩ := hs
      obtain ⟨u₁, u₂, hsplit_u, hu₁, hu₂⟩ := hu
      have es : s₁ ∪ s₂ = s := hsplit_s
      have eu : u₁ ∪ u₂ = u := hsplit_u
      refine ⟨(s₁ ∪ u₁) ∩ t, (s₂ ∪ u₂) ∩ t, ?_, ?_, ?_⟩
      · show ((s₁ ∪ u₁) ∩ t) ∪ ((s₂ ∪ u₂) ∩ t) = t
        ext x
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (⟨_, hxt⟩ | ⟨_, hxt⟩) <;> exact hxt
        · intro hxt
          have hxu : x ∈ u := htu hxt
          rw [← eu, Finset.mem_union] at hxu
          rcases hxu with h | h
          · exact Or.inl ⟨Or.inr h, hxt⟩
          · exact Or.inr ⟨Or.inr h, hxt⟩
      · have hs1t : s₁ ⊆ t := by
          intro x hx; apply hst; rw [← es]; exact Finset.mem_union_left _ hx
        exact ihs₁ s₁ ((s₁ ∪ u₁) ∩ t) (s₁ ∪ u₁)
          (Finset.subset_inter Finset.subset_union_left hs1t)
          Finset.inter_subset_left hs₁
          ((support_and_antiSupport_unionClosed ψ₁ M).1 s₁ u₁ hs₁ hu₁)
      · have hs2t : s₂ ⊆ t := by
          intro x hx; apply hst; rw [← es]; exact Finset.mem_union_right _ hx
        exact ihs₂ s₂ ((s₂ ∪ u₂) ∩ t) (s₂ ∪ u₂)
          (Finset.subset_inter Finset.subset_union_left hs2t)
          Finset.inter_subset_left hs₂
          ((support_and_antiSupport_unionClosed ψ₂ M).1 s₂ u₂ hs₂ hu₂)
    · intro s t u hst htu hs hu
      obtain ⟨ha₁, ha₂⟩ := hs
      obtain ⟨ha₁', ha₂'⟩ := hu
      exact ⟨iha₁ s t u hst htu ha₁ ha₁', iha₂ s t u hst htu ha₂ ha₂'⟩
  | poss ψ ih =>
    refine ⟨?_, ?_⟩
    · intro s t u _hst htu _hs hu w hw; exact hu w (htu hw)
    · intro s t u _hst htu _hs hu w hw; exact hu w (htu hw)

/-- **BSML support is order-convex** for every formula — NE-bearing included
    ([anttila-2025] Proposition 3.3.1): `{ t | support M φ t }` is
    `Set.OrdConnected`, i.e. `s ⊆ t ⊆ u` with `support M φ s` and
    `support M φ u` forces `support M φ t`.

    Generalizes `isLowerSet_support_of_isNEFree`: for NE-free `φ` the empty-team
    property holds, and `Core.Logic.Team.isLowerSet_iff_ordConnected_of_empty`
    recovers downward closure from convexity. Together with `supClosed_support`,
    this is the convex-and-union-closed property for which BSML is expressively
    complete ([anttila-2025]). -/
theorem ordConnected_support (M : BSMLModel W Atom) (φ : BSMLFormula Atom) :
    Set.OrdConnected { t : Finset W | support M φ t } := by
  refine ⟨?_⟩
  intro s hs u hu t ht
  rw [Set.mem_Icc] at ht
  exact (support_and_antiSupport_ordConnected φ M).1 s t u ht.1 ht.2 hs hu

/-! ### Flatness corollary (Anttila 2.2.16) -/

/-- **Anttila Proposition 2.2.16** (BSML specialisation of Fact 15 from
    [aloni-2022]): NE-free BSML formulas are flat — team support
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

/-! ### Soundness for the closure cell (Definability bridge) -/

open Core.Logic.Team in
/-- **BSML is sound for its closure cell**: every BSML-definable team property is
    convex and union-closed — the soundness half of BSML's expressive
    completeness ([anttila-2025] Proposition 3.3.1: BSML is complete for the
    convex, union-closed modal properties, modulo bounded bisimulation).

    Composes `ordConnected_support` and `supClosed_support` through the
    `Team/Definability.lean` bridge. The converse (every such property is
    BSML-definable) is the open half. -/
theorem soundFor_convex_inter_unionClosed (M : BSMLModel W Atom) :
    SoundFor (support M) (convexProperties ∩ unionClosedProperties) := by
  unfold SoundFor
  apply Set.subset_inter
  · intro P hP
    simp only [mem_definableClass] at hP
    obtain ⟨φ, rfl⟩ := hP
    show Set.OrdConnected (definedBy (support M) φ)
    exact ordConnected_support M φ
  · intro P hP
    simp only [mem_definableClass] at hP
    obtain ⟨φ, rfl⟩ := hP
    show SupClosed (definedBy (support M) φ)
    exact supClosed_support M φ

open Core.Logic.Team in
/-- **The NE-free fragment of BSML is sound for the flat cell** (Anttila
    Proposition 2.2.16 / [aloni-2022] Fact 15): NE-free BSML formulas define
    flat properties. Companion to `soundFor_convex_inter_unionClosed`: NE is
    exactly what moves a formula off the `flat` cell into the strictly larger
    convex, union-closed cell. -/
theorem soundFor_flat_neFree (M : BSMLModel W Atom) :
    definableClassWhere (support M) (fun φ => φ.isNEFree = true) ⊆ flatProperties := by
  unfold flatProperties
  exact definableClassWhere_subset (C := IsFlat)
    fun _φ hφ => isFlat_support_of_isNEFree hφ M

end Core.Logic.Modal.BSML
