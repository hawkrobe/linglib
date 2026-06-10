import Linglib.Core.Logic.Modal.QBSML.Enrichment

/-!
# QBSML free-choice theorems — Aloni & van Ormondt 2023 §5

[aloni-vanormondt-2023] [aloni-2022]

The first-order analogues of `BSML/FreeChoice.lean`'s theorems. Pragmatic
enrichment ([aloni-vanormondt-2023] Definition 4.13) combined with split
disjunction and bilateral evaluation derives ignorance, free-choice,
distribution, obviation, and behaviour-under-negation inferences as
universal substrate facts — applicable to any QBSML model satisfying the
relevant frame conditions.

## Status

Lands **Fact 10 (negation)** and **Fact 8 (narrow-scope FC)** as universal
substrate theorems, plus the `enrichment_strengthens_*` engine that powers
the rest of the §5 facts. Future additions: `universalFC_Q` (Fact 9, needs
the modal pattern over `State.extendUniversal`), `modalDisjunction_Q`
(Fact 3, needs state-based frame condition handling), and the wide-scope
variants.

The negation fact requires no frame condition on `R` ([aloni-vanormondt-2023]
page 564 proof: "We assume that M, s ⊨ [¬(Pa ∨ Pb)]⁺. This means that s ≠ ∅
and M, s ⊧ [Pa ∨ Pb]⁺. ..." — frame conditions on `R` are not invoked).

## Proof architecture (mirrors `BSML/FreeChoice.lean`)

1. **Joint enrichment-strengthens** (`enrichment_strengthens_both`):
   simultaneous induction on the NE-free derivation proving both
   `support enrich φ → support φ` and `antiSupport enrich φ → antiSupport φ`.
   The mutual structure handles negation: `support (¬ψ) = antiSupport ψ`, so
   the two directions interleave.

2. **Negation strip** (`negationStrip_Q`): for NE-free α, β,
   `[¬(α ∨ β)]⁺ ⊨ ¬α ∧ ¬β`. Composes `antiSupport_strip_ne` (in
   `Enrichment.lean`) with the antiSupport-disj clause and
   `enrichment_strengthens_antiSupport`.
-/

namespace AloniVanOrmondt2023

open Core.Logic.Modal.QBSML

variable {W Var Domain Pred : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-! ### Enrichment strengthens (joint bilateral induction) -/

/-- Both directions of "enrichment strengthens" (Fact 1 of [aloni-2022]
    extended to QBSML). For NE-free `φ`:
    - `support M (enrich φ) s → support M φ s`
    - `antiSupport M (enrich φ) s → antiSupport M φ s`

    Joint bilateral induction over the NE-free derivation. The negation case
    interleaves the two directions (support of `¬ψ` is anti-support of `ψ`).
    All quantifier cases use `antiSupport_strip_ne` to peel the `NE`
    conjunct, then `extendUniversal` / `extendFunctional` to apply the IH
    on the extended state. -/
private theorem enrichment_strengthens_both (M : QBSMLModel W Domain Pred)
    {φ : QBSMLFormula Var Pred} (hNE : φ.IsNEFree) :
    (∀ s : Finset (Index W Var Domain), support M φ.enrich s → support M φ s) ∧
    (∀ s : Finset (Index W Var Domain),
        antiSupport M φ.enrich s → antiSupport M φ s) := by
  induction hNE with
  | pred P x =>
    refine ⟨?_, ?_⟩
    · intro s h; exact h.1
    · intro s h; exact antiSupport_strip_ne M (.pred P x) s h
  | @neg ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
    refine ⟨?_, ?_⟩
    · -- support (¬ψ).enrich s = support ((¬ψ.enrich) ∧ NE) s = antiSupport ψ.enrich s ∧ NE
      intro s h
      show antiSupport M ψ s
      exact ih_a s h.1
    · -- antiSupport (¬ψ).enrich s; strip the outer NE; reduces to support ψ.enrich s
      intro s h
      have h' := antiSupport_strip_ne M (.neg ψ.enrich) s h
      show support M ψ s
      exact ih_s s h'
  | @conj ψ₁ ψ₂ _ _ ih₁ ih₂ =>
    obtain ⟨ih₁_s, ih₁_a⟩ := ih₁
    obtain ⟨ih₂_s, ih₂_a⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s h; exact ⟨ih₁_s s h.1.1, ih₂_s s h.1.2⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.conj ψ₁.enrich ψ₂.enrich) s h
      obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h'
      exact ⟨t₁, t₂, hunion, ih₁_a t₁ h₁, ih₂_a t₂ h₂⟩
  | @disj ψ₁ ψ₂ _ _ ih₁ ih₂ =>
    obtain ⟨ih₁_s, ih₁_a⟩ := ih₁
    obtain ⟨ih₂_s, ih₂_a⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s h
      obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1
      exact ⟨t₁, t₂, hunion, ih₁_s t₁ h₁, ih₂_s t₂ h₂⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.disj ψ₁.enrich ψ₂.enrich) s h
      exact ⟨ih₁_a s h'.1, ih₂_a s h'.2⟩
  | @poss ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
    refine ⟨?_, ?_⟩
    · intro s h i hi
      obtain ⟨X, hX, hne, hsupp⟩ := h.1 i hi
      exact ⟨X, hX, hne, ih_s _ hsupp⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.poss ψ.enrich) s h
      exact fun i hi => ih_a _ (h' i hi)
  | @exi x ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
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
  | @univ x ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
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

/-- **Enrichment strengthens (support direction)** — [aloni-2022] Fact 1
    extended to QBSML. For NE-free `φ`, supporting the enriched form implies
    supporting the original. -/
theorem enrichment_strengthens_support (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.IsNEFree)
    (h : support M φ.enrich s) :
    support M φ s :=
  (enrichment_strengthens_both M hNE).1 s h

/-- **Enrichment strengthens (anti-support direction)**. -/
theorem enrichment_strengthens_antiSupport (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.IsNEFree)
    (h : antiSupport M φ.enrich s) :
    antiSupport M φ s :=
  (enrichment_strengthens_both M hNE).2 s h

/-! ### Negation behaviour (Fact 10) -/

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
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
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

/-! ### Narrow-scope free choice (Fact 8) -/

/-- **Fact 8 (◇-free choice / narrow-scope FC)** of [aloni-vanormondt-2023]
    (the first-order analogue of [aloni-2022] Fact 4):

    `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for NE-free `α`, `β`.

    Per-index `i ∈ s`: the enriched `◇` provides a non-empty `X ⊆ R(i.world)`
    with split `t₁ ∪ t₂ = modalLift X i.assign`, each part supporting the
    enriched disjunct on its piece. `State.modalLift_worldProj_of_subset`
    recovers each piece from its world projection, which serves as the
    `Finset W` witness; `enrichment_strengthens_support` discharges the
    enrichment to plain support of α, β. -/
theorem narrowScopeFC_Q (M : QBSMLModel W Domain Pred)
    (α β : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (QBSMLFormula.enrich (.poss (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  -- Outer: enrich (◇φ) = (◇enrich φ) ∧ NE; project the diamond clause.
  have hPoss : support M (.poss (QBSMLFormula.disj α β).enrich) s := h.1
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨X, hX, _, hsupp⟩ := hPoss i hi
    -- hsupp : support of the enriched disjunction on modalLift X i.assign;
    -- project its split and keep the α piece t₁.
    obtain ⟨t₁, t₂, hunion, h₁, _h₂⟩ := hsupp.1
    have ht₁_sub : t₁ ⊆ State.modalLift X i.assign :=
      hunion ▸ Finset.subset_union_left
    refine ⟨State.worldProj t₁,
      (State.worldProj_subset_of_subset_modalLift ht₁_sub).trans hX,
      State.worldProj_nonempty (enriched_support_implies_nonempty M α t₁ h₁),
      ?_⟩
    rw [State.modalLift_worldProj_of_subset ht₁_sub]
    exact enrichment_strengthens_support M α t₁ hα h₁
  · intro i hi
    obtain ⟨X, hX, _, hsupp⟩ := hPoss i hi
    obtain ⟨t₁, t₂, hunion, _h₁, h₂⟩ := hsupp.1
    have ht₂_sub : t₂ ⊆ State.modalLift X i.assign :=
      hunion ▸ Finset.subset_union_right
    refine ⟨State.worldProj t₂,
      (State.worldProj_subset_of_subset_modalLift ht₂_sub).trans hX,
      State.worldProj_nonempty (enriched_support_implies_nonempty M β t₂ h₂),
      ?_⟩
    rw [State.modalLift_worldProj_of_subset ht₂_sub]
    exact enrichment_strengthens_support M β t₂ hβ h₂

end AloniVanOrmondt2023
