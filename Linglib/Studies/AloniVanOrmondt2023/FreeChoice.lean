import Linglib.Core.Logic.Modal.QBSML.Enrichment

/-!
# QBSML free-choice theorems — Aloni & van Ormondt 2023 §5

[aloni-vanormondt-2023] [aloni-2022]

The first-order analogues of `BSML/FreeChoice.lean`'s theorems. Pragmatic
enrichment (Aloni & van Ormondt 2023 Definition 4.13) combined with split
disjunction (§3.1) and bilateral evaluation (§4) derives ignorance,
free-choice, distribution, obviation, and behaviour-under-negation
inferences as universal substrate facts — applicable to any QBSML model
satisfying the relevant frame conditions.

## Status

This file currently lands the **negation fact (Fact 10)** as a universal
substrate theorem, plus the `enrichment_strengthens_*` engine that powers
the rest of the §5 facts. Future additions:
- `narrowScopeFC_Q` (Fact 8) — needs world-projection lemmas for
  `State.modalLift`
- `universalFC_Q` (Fact 9) — needs `State.extendUniversal` lemmas + the
  modal pattern from `narrowScopeFC_Q`
- `modalDisjunction_Q` (Fact 3) — needs state-based frame condition handling
- The wide-scope variants

The negation fact is the cleanest standalone result — it requires no frame
condition on `R` (Aloni & van Ormondt 2023 page 564 proof: "We assume that
M, s ⊨ [¬(Pa ∨ Pb)]⁺. This means that s ≠ ∅ and M, s ⊧ [Pa ∨ Pb]⁺. ..."
— frame conditions on `R` are not invoked).

## Proof architecture (mirrors `BSML/FreeChoice.lean`)

1. **Joint enrichment-strengthens** (`enrichment_strengthens_both`):
   simultaneous induction on QBSMLFormula proving both
   `support enrich φ → support φ` and `antiSupport enrich φ → antiSupport φ`
   for NE-free `φ`. The mutual structure handles negation: `support (¬ψ) =
   antiSupport ψ`, so the two directions interleave.

2. **Negation strip** (`negationStrip_Q`): for NE-free α, β,
   `[¬(α ∨ β)]⁺ ⊨ ¬α ∧ ¬β`. Composes `antiSupport_strip_ne` (in
   `Enrichment.lean`) with the antiSupport-disj clause and
   `enrichment_strengthens_antiSupport`.
-/

namespace AloniVanOrmondt2023

open Core.Logic.Modal.QBSML

variable {W Var Domain Pred : Type*}
variable [DecidableEq W] [Fintype W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

-- ============================================================================
-- §1 Enrichment strengthens (joint bilateral induction)
-- ============================================================================

/-- Both directions of "enrichment strengthens" (Fact 1 of [aloni-2022]
    extended to QBSML). For NE-free `φ`:
    - `support M (enrich φ) s → support M φ s`
    - `antiSupport M (enrich φ) s → antiSupport M φ s`

    Joint bilateral induction over `QBSMLFormula`. The negation case
    interleaves the two directions (support of `¬ψ` is anti-support of `ψ`).
    All quantifier cases use `antiSupport_strip_ne` to peel the `NE`
    conjunct, then `extendUniversal` / `extendFunctional` to apply the IH
    on the extended state. -/
private theorem enrichment_strengthens_both (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (hNE : φ.isNEFree = true) :
    (∀ s : Finset (Index W Var Domain), support M φ.enrich s → support M φ s) ∧
    (∀ s : Finset (Index W Var Domain),
        antiSupport M φ.enrich s → antiSupport M φ s) := by
  induction φ with
  | ne => simp [QBSMLFormula.isNEFree] at hNE
  | pred P x =>
    refine ⟨?_, ?_⟩
    · intro s h; exact h.1
    · intro s h; exact antiSupport_strip_ne M (.pred P x) s h
  | neg ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ih_s, ih_a⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · -- support (¬ψ).enrich s = support ((¬ψ.enrich) ∧ NE) s = antiSupport ψ.enrich s ∧ NE
      intro s h
      show antiSupport M ψ s
      exact ih_a s h.1
    · -- antiSupport (¬ψ).enrich s; strip the outer NE; reduces to support ψ.enrich s
      intro s h
      have h' := antiSupport_strip_ne M (.neg ψ.enrich) s h
      -- h' : antiSupport M (.neg ψ.enrich) s = support M ψ.enrich s
      show support M ψ s
      exact ih_s s h'
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have hψ₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ih₁_s, ih₁_a⟩ := ih₁ hψ₁
    have ⟨ih₂_s, ih₂_a⟩ := ih₂ hψ₂
    refine ⟨?_, ?_⟩
    · intro s h; exact ⟨ih₁_s s h.1.1, ih₂_s s h.1.2⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.conj ψ₁.enrich ψ₂.enrich) s h
      obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h'
      exact ⟨t₁, t₂, hunion, ih₁_a t₁ h₁, ih₂_a t₂ h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have hψ₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ih₁_s, ih₁_a⟩ := ih₁ hψ₁
    have ⟨ih₂_s, ih₂_a⟩ := ih₂ hψ₂
    refine ⟨?_, ?_⟩
    · intro s h
      obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1
      exact ⟨t₁, t₂, hunion, ih₁_s t₁ h₁, ih₂_s t₂ h₂⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.disj ψ₁.enrich ψ₂.enrich) s h
      exact ⟨ih₁_a s h'.1, ih₂_a s h'.2⟩
  | poss ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ih_s, ih_a⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · intro s h i hi
      obtain ⟨X, hX, hne, hsupp⟩ := h.1 i hi
      exact ⟨X, hX, hne, ih_s _ hsupp⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.poss ψ.enrich) s h
      exact fun i hi => ih_a _ (h' i hi)
  | exi x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ih_s, ih_a⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · -- support (.exi x ψ).enrich s = (∃ h, ... support ψ.enrich (s.extendFunctional x h)) ∧ NE
      intro s h
      obtain ⟨h_fn, hne, hsupp⟩ := h.1
      exact ⟨h_fn, hne, ih_s _ hsupp⟩
    · -- antiSupport (.exi x ψ).enrich s; strip NE; reduces to antiSupport ψ.enrich (s.extendUniversal x)
      intro s h
      have h' := antiSupport_strip_ne M (.exi x ψ.enrich) s h
      show antiSupport M ψ (State.extendUniversal s x)
      exact ih_a _ h'
  | univ x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨ih_s, ih_a⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · -- support (.univ x ψ).enrich s = support ψ.enrich (s.extendUniversal x) ∧ NE
      intro s h
      show support M ψ (State.extendUniversal s x)
      exact ih_s _ h.1
    · -- antiSupport (.univ x ψ).enrich s; strip NE; reduces to functional
      intro s h
      have h' := antiSupport_strip_ne M (.univ x ψ.enrich) s h
      obtain ⟨h_fn, hne, hsupp⟩ := h'
      exact ⟨h_fn, hne, ih_a _ hsupp⟩

/-- **Enrichment strengthens (support direction)** — Aloni 2022 Fact 1
    extended to QBSML. For NE-free `φ`, supporting the enriched form implies
    supporting the original. -/
theorem enrichment_strengthens_support (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.isNEFree = true)
    (h : support M φ.enrich s) :
    support M φ s :=
  (enrichment_strengthens_both M φ hNE).1 s h

/-- **Enrichment strengthens (anti-support direction)**. -/
theorem enrichment_strengthens_antiSupport (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.isNEFree = true)
    (h : antiSupport M φ.enrich s) :
    antiSupport M φ s :=
  (enrichment_strengthens_both M φ hNE).2 s h

-- ============================================================================
-- §2 Helper: modalLift world-projection (for narrow-scope FC)
-- ============================================================================

/-- For any state `s` contained in `State.modalLift X g`, the world-projection
    of `s` lifted back via `modalLift` recovers `s` exactly. The key fact:
    `modalLift X g` produces only indices of the form `(v, g)` for `v ∈ X`,
    so every index in `s` has assignment `g`, and projecting-then-lifting
    is the identity. -/
private lemma modalLift_image_fst_subset {s : Finset (Index W Var Domain)}
    {X : Finset W} {g : Assignment Var Domain}
    (h : s ⊆ State.modalLift X g) :
    State.modalLift (s.image Prod.fst) g = s := by
  -- Every i ∈ s has snd = g (since s ⊆ modalLift X g and modalLift produces (?, g)).
  have hsnd : ∀ i ∈ s, i.snd = g := by
    intro i hi
    have himodal : i ∈ State.modalLift X g := h hi
    simp only [State.modalLift, Finset.mem_image] at himodal
    obtain ⟨w, _, hw⟩ := himodal
    rw [← hw]
  ext i
  simp only [State.modalLift, Finset.mem_image]
  constructor
  · rintro ⟨v, ⟨j, hjs, hjv⟩, hvi⟩
    -- j ∈ s, j.fst = v, (v, g) = i. Show i = j.
    have hjeq : j = (v, g) := Prod.ext hjv (hsnd j hjs)
    -- (v, g) = i, j = (v, g) → j = i
    rwa [hjeq, hvi] at hjs
  · intro hi
    -- i ∈ s. Witness v = i.fst; (i.fst, g) = i because i.snd = g (by hsnd).
    refine ⟨i.fst, ⟨i, hi, rfl⟩, ?_⟩
    -- Goal: (i.fst, g) = i. Use Prod.ext: fst trivial, snd = g via hsnd.
    exact Prod.ext rfl (hsnd i hi).symm

/-- The world projection of `modalLift X g` is `X` itself. -/
private lemma modalLift_image_fst (X : Finset W) (g : Assignment Var Domain) :
    (State.modalLift X g).image Prod.fst = X := by
  unfold State.modalLift
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨w, hwX, hw⟩, hwv⟩
    rw [← hw] at hwv
    simp at hwv
    rwa [← hwv]
  · intro hvX
    exact ⟨(v, g), ⟨v, hvX, rfl⟩, rfl⟩

/-- World-projection of a subset of `modalLift X g` is itself a subset of `X`. -/
private lemma image_fst_subset_of_subset_modalLift
    {s : Finset (Index W Var Domain)} {X : Finset W}
    {g : Assignment Var Domain}
    (h : s ⊆ State.modalLift X g) :
    s.image Prod.fst ⊆ X := by
  intro v hv
  obtain ⟨j, hjs, hjv⟩ := Finset.mem_image.mp hv
  have hjmodal := h hjs
  obtain ⟨w, hwX, hw⟩ := by
    simp only [State.modalLift, Finset.mem_image] at hjmodal
    exact hjmodal
  rw [← hw] at hjv
  simp at hjv
  rwa [← hjv]

-- ============================================================================
-- §3 Negation behaviour (Fact 10)
-- ============================================================================

/-- **Fact 10 (negation behaviour)** of [aloni-vanormondt-2023]:

    `[¬(α ∨ β)]⁺ ⊨ ¬α ∧ ¬β` for NE-free `α`, `β`.

    Three NE-strips compose: outer `(¬enrich(α ∨ β)) ∧ NE`, then disj-anti
    splits to `(antiSupport enrich α) ∧ (antiSupport enrich β)`, then
    `enrichment_strengthens_antiSupport` for each disjunct.

    No frame condition on `R` — the proof goes through for every model.
    Negation cancels ignorance (paper §5.5): the `Nonempty` hypothesis is
    discharged by the three NE-strips, leaving classical anti-support on
    each disjunct. -/
theorem negationStrip_Q (M : QBSMLModel W Domain Pred)
    (α β : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hα : α.isNEFree = true) (hβ : β.isNEFree = true)
    (h : support M (QBSMLFormula.enrich (.neg (.disj α β))) s) :
    support M (.neg α) s ∧ support M (.neg β) s := by
  -- Outer: enrich (¬(α ∨ β)) = (¬enrich (α ∨ β)) ∧ NE; project outer NE.
  have hNeg : antiSupport M (QBSMLFormula.enrich (.disj α β)) s := h.1
  -- enrich (α ∨ β) = (enrich α ∨ enrich β) ∧ NE; strip NE.
  have hDisj : antiSupport M (.disj α.enrich β.enrich) s :=
    antiSupport_strip_ne M (.disj α.enrich β.enrich) s hNeg
  -- antiSupport-disj is conj of antiSupports.
  have ⟨hL, hR⟩ := hDisj
  -- Apply enrichment_strengthens_antiSupport to each disjunct.
  exact ⟨enrichment_strengthens_antiSupport M α s hα hL,
         enrichment_strengthens_antiSupport M β s hβ hR⟩

-- ============================================================================
-- §4 Narrow-scope free choice (Fact 8)
-- ============================================================================

/-- **Fact 8 (◇-free choice / narrow-scope FC)** of [aloni-vanormondt-2023]
    (the first-order analogue of [aloni-2022] Fact 4):

    `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for NE-free `α`, `β`.

    Per-index `i ∈ s`: the enriched `◇` provides a non-empty `X ⊆ R(i.world)`
    with split `t₁ ∪ t₂ = modalLift X i.assign`, each part supporting the
    enriched disjunct on its piece. Project each piece's worlds back via
    `s.image Prod.fst` and use `modalLift_image_fst_subset` to recover
    a Finset W witness. `enrichment_strengthens_support` discharges the
    enrichment to plain support of α, β. -/
theorem narrowScopeFC_Q (M : QBSMLModel W Domain Pred)
    (α β : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hα : α.isNEFree = true) (hβ : β.isNEFree = true)
    (h : support M (QBSMLFormula.enrich (.poss (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  -- Outer: enrich (◇φ) = (◇enrich φ) ∧ NE; project the diamond clause.
  have hPoss : support M (.poss (QBSMLFormula.disj α β).enrich) s := h.1
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨X, hX, _, hsupp⟩ := hPoss i hi
    -- hsupp : support M ((.disj α β).enrich) (modalLift X i.assign)
    --        = support M (.conj (.disj α.enrich β.enrich) .ne) (modalLift X i.assign)
    -- Project: support of the inner disj on modalLift X i.assign
    obtain ⟨t₁, t₂, hunion, h₁, _h₂⟩ := hsupp.1
    -- h₁ : support α.enrich t₁; need ◇α at i with witness t₁'s world projection.
    have ht₁_sub : t₁ ⊆ State.modalLift X i.assign :=
      hunion ▸ Finset.subset_union_left
    have ht₁_modal : State.modalLift (t₁.image Prod.fst) i.assign = t₁ :=
      modalLift_image_fst_subset ht₁_sub
    have ht₁_subX : t₁.image Prod.fst ⊆ X :=
      image_fst_subset_of_subset_modalLift ht₁_sub
    refine ⟨t₁.image Prod.fst, ht₁_subX.trans hX, ?_, ?_⟩
    · -- t₁.image Prod.fst is nonempty: t₁ is nonempty (by enrichment NE) so its image is.
      have ht₁_ne : t₁.Nonempty :=
        enriched_support_implies_nonempty M α t₁ h₁
      exact ht₁_ne.image _
    · -- support α (modalLift (t₁.image Prod.fst) i.assign) = support α t₁
      rw [ht₁_modal]
      exact enrichment_strengthens_support M α t₁ hα h₁
  · intro i hi
    obtain ⟨X, hX, _, hsupp⟩ := hPoss i hi
    obtain ⟨t₁, t₂, hunion, _h₁, h₂⟩ := hsupp.1
    have ht₂_sub : t₂ ⊆ State.modalLift X i.assign :=
      hunion ▸ Finset.subset_union_right
    have ht₂_modal : State.modalLift (t₂.image Prod.fst) i.assign = t₂ :=
      modalLift_image_fst_subset ht₂_sub
    have ht₂_subX : t₂.image Prod.fst ⊆ X :=
      image_fst_subset_of_subset_modalLift ht₂_sub
    refine ⟨t₂.image Prod.fst, ht₂_subX.trans hX, ?_, ?_⟩
    · have ht₂_ne : t₂.Nonempty :=
        enriched_support_implies_nonempty M β t₂ h₂
      exact ht₂_ne.image _
    · rw [ht₂_modal]
      exact enrichment_strengthens_support M β t₂ hβ h₂

end AloniVanOrmondt2023
