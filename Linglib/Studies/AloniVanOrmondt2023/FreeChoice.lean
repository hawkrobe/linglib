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

Lands **Fact 10 (negation)**, **Fact 8 (narrow-scope FC)**, **Fact 9
(universal FC)**, **Fact 5 (distribution at maximal information)**, and
**Fact 6 (distribution° under state-based access)** as universal substrate
theorems, plus the `enrichment_strengthens_*` engine. Facts 8 and 9 share
the per-index core `possFC_on`. Still missing:

- **Fact 3 (ignorance)**: its proof evaluates the closed atoms `Pa`, `Pb`
  across indices carrying *different* assignments, which the constant-free
  monadic language cannot express (with a free variable in place of `a`
  the statement is false); needs individual constants in the term language.
- **Fact 4 (obviation)**: a non-entailment; the paper's Fig. 14
  counterexample needs hand-proved non-support or a `Decidable` instance
  for `eval`.
- **Fact 7 (□-free choice)**: `□` is derived as `¬◇¬` here, so
  `QBSMLFormula.enrich` gives `□φ` the negation-clause enrichment rather
  than [aloni-vanormondt-2023] Definition 4.13's primitive
  `[□φ]⁺ = □[φ]⁺ ∧ NE`; Fact 7 needs a primitive `□` or a bridge between
  the two enrichments.

The negation fact requires no frame condition on `R` ([aloni-vanormondt-2023]
page 564 proof of Fact 10: "Assume M, s ⊨ [¬(Pa ∨ Pb)]⁺. It follows that
s ≠ ∅ and M, s ⫤ [Pa ∨ Pb]⁺" — frame conditions on `R` are not invoked).

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

/-! ### Free choice (Facts 8 and 9) -/

/-- The shared per-index core of the ◇-free-choice facts: a state whose
    every index sees an enriched split disjunction supports both diamonds.

    Per-index `i ∈ t`: the enriched `◇` provides a non-empty `X ⊆ R(i.world)`
    with split `t₁ ∪ t₂ = modalLift X i.assign`, each part supporting the
    enriched disjunct on its piece. `State.modalLift_worldProj_of_subset`
    recovers each piece from its world projection, which serves as the
    `Finset W` witness; `enrichment_strengthens_support` discharges the
    enrichment to plain support of α, β. -/
private theorem possFC_on (M : QBSMLModel W Domain Pred)
    {α β : QBSMLFormula Var Pred} (hα : α.IsNEFree) (hβ : β.IsNEFree)
    {t : Finset (Index W Var Domain)}
    (h : support M (.poss (QBSMLFormula.disj α β).enrich) t) :
    support M (.poss α) t ∧ support M (.poss β) t := by
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨X, hX, _, hsupp⟩ := h i hi
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
    obtain ⟨X, hX, _, hsupp⟩ := h i hi
    obtain ⟨t₁, t₂, hunion, _h₁, h₂⟩ := hsupp.1
    have ht₂_sub : t₂ ⊆ State.modalLift X i.assign :=
      hunion ▸ Finset.subset_union_right
    refine ⟨State.worldProj t₂,
      (State.worldProj_subset_of_subset_modalLift ht₂_sub).trans hX,
      State.worldProj_nonempty (enriched_support_implies_nonempty M β t₂ h₂),
      ?_⟩
    rw [State.modalLift_worldProj_of_subset ht₂_sub]
    exact enrichment_strengthens_support M β t₂ hβ h₂

/-- **Fact 8 (◇-free choice / narrow-scope FC)** of [aloni-vanormondt-2023]
    (the first-order analogue of [aloni-2022] Fact 4):

    `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for NE-free `α`, `β`.

    Projects the diamond clause of the enrichment and applies the per-index
    core `possFC_on` at `s`. -/
theorem narrowScopeFC_Q (M : QBSMLModel W Domain Pred)
    (α β : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (QBSMLFormula.enrich (.poss (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s :=
  possFC_on M hα hβ h.1

/-- **Fact 9 (universal free choice)** of [aloni-vanormondt-2023], the
    pattern attested experimentally by [chemla-2009]:

    `[∀x◇(α ∨ β)]⁺ ⊨ ∀x◇α ∧ ∀x◇β` for NE-free `α`, `β`.

    The enriched premise evaluates the enriched diamond at the universal
    extension `s[x]`, so the conclusion is `possFC_on` at `s[x]` — the same
    per-index argument as Fact 8, one extension up. -/
theorem universalFC_Q (M : QBSMLModel W Domain Pred)
    (α β : QBSMLFormula Var Pred) (x : Var) (s : Finset (Index W Var Domain))
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (QBSMLFormula.enrich (.univ x (.poss (.disj α β)))) s) :
    support M (.univ x (.poss α)) s ∧ support M (.univ x (.poss β)) s :=
  possFC_on M hα hβ h.1.1

/-! ### Distribution (Facts 5 and 6) -/

/-- A non-empty subset `t` of the universal extension of a singleton state
    that supports `γ` yields an existential witness on the singleton: the
    functional `h` sending the (unique) index to the domain values whose
    extensions land in `t` reconstructs `t` exactly. The engine of Fact 5. -/
private lemma exi_of_subset_extendUniversal_singleton
    (M : QBSMLModel W Domain Pred) {γ : QBSMLFormula Var Pred}
    {i : Index W Var Domain} {x : Var} {t : Finset (Index W Var Domain)}
    (htsub : t ⊆ State.extendUniversal {i} x) (htne : t.Nonempty)
    (hsupp : support M γ t) :
    support M (.exi x γ) {i} := by
  classical
  refine ⟨fun j => Finset.univ.filter (fun d => j.update x d ∈ t), ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    obtain ⟨j₀, hj₀⟩ := htne
    obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp (htsub hj₀)
    rw [Finset.mem_singleton] at hi'
    subst hi'
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, by rwa [hupd]⟩⟩
  · have ht : State.extendFunctional {i} x
        (fun j => Finset.univ.filter (fun d => j.update x d ∈ t)) = t := by
      ext j
      rw [State.mem_extendFunctional]
      constructor
      · rintro ⟨i', hi', d, hd, rfl⟩
        rw [Finset.mem_singleton] at hi'
        subst hi'
        exact (Finset.mem_filter.mp hd).2
      · intro hj
        obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp (htsub hj)
        rw [Finset.mem_singleton] at hi'
        subst hi'
        exact ⟨i', Finset.mem_singleton_self i', d,
          Finset.mem_filter.mpr ⟨Finset.mem_univ d, by rwa [hupd]⟩, hupd⟩
    rw [ht]
    exact hsupp

/-- **Fact 5 (distribution at maximal information)** of
    [aloni-vanormondt-2023]: on a state of maximal information
    (`card s = 1`, here `s = {i}`),

    `[∀x(α ∨ β)]⁺ ⊨ ∃xα ∧ ∃xβ` for NE-free `α`, `β`.

    The enriched premise splits the universal extension `{i}[x]` into
    non-empty parts supporting the enriched disjuncts; because the state is
    a singleton, every part extends the *same* index, so each part is the
    image of a functional extension witnessing the existential. -/
theorem distribution_Q (M : QBSMLModel W Domain Pred)
    (α β : QBSMLFormula Var Pred) (x : Var) (i : Index W Var Domain)
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (QBSMLFormula.enrich (.univ x (.disj α β))) {i}) :
    support M (.exi x α) {i} ∧ support M (.exi x β) {i} := by
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1.1
  exact ⟨exi_of_subset_extendUniversal_singleton M
      (hunion ▸ Finset.subset_union_left)
      (enriched_support_implies_nonempty M α t₁ h₁)
      (enrichment_strengthens_support M α t₁ hα h₁),
    exi_of_subset_extendUniversal_singleton M
      (hunion ▸ Finset.subset_union_right)
      (enriched_support_implies_nonempty M β t₂ h₂)
      (enrichment_strengthens_support M β t₂ hβ h₂)⟩

/-- A non-empty subset `t` of `s[x]` supporting the atom `Px` yields
    `∃x◇Px` on `s` when `R` is state-based: some index of `t` is `i₀[x/d]`
    with `d ∈ I(i₀.world)(P)`, the individual extension `s[x/d]` (as the
    constant functional) witnesses the existential, and state-basedness puts
    `i₀.world` in every index's accessible set, so the singleton
    `{i₀.world}` witnesses each diamond. The engine of Fact 6. -/
private lemma exi_poss_atom_of_subset_extendUniversal
    (M : QBSMLModel W Domain Pred) {P : Pred} {x : Var}
    {s t : Finset (Index W Var Domain)}
    (hSB : M.IsStateBased s)
    (htsub : t ⊆ State.extendUniversal s x) (htne : t.Nonempty)
    (hsupp : support M (.pred P x) t) :
    support M (.exi x (.poss (.pred P x))) s := by
  classical
  have hSB' : ∀ w ∈ State.worldProj s, M.access w = State.worldProj s := hSB
  obtain ⟨j₀, hj₀⟩ := htne
  obtain ⟨d, i₀, hi₀s, hupd⟩ := State.mem_extendUniversal.mp (htsub hj₀)
  obtain ⟨d', hassign, hmem⟩ := hsupp j₀ hj₀
  rw [← hupd] at hassign hmem
  simp only [Index.assign_update, Function.update_self,
    Option.some.injEq] at hassign
  rw [← hassign] at hmem
  rw [Index.world_update] at hmem
  -- hmem : d ∈ M.pInterp P i₀.world
  refine ⟨fun _ => {d}, fun j _ => Finset.singleton_nonempty d, ?_⟩
  intro j hj
  obtain ⟨i, his, d'', hd'', hupd'⟩ := State.mem_extendFunctional.mp hj
  rw [Finset.mem_singleton] at hd''
  subst hd''
  refine ⟨{i₀.world}, ?_, Finset.singleton_nonempty _, ?_⟩
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    have hjw : j.world ∈ State.worldProj s :=
      State.mem_worldProj.mpr ⟨i, his, by rw [← hupd', Index.world_update]⟩
    rw [hSB' j.world hjw]
    exact State.mem_worldProj.mpr ⟨i₀, hi₀s, rfl⟩
  · intro k hk
    obtain ⟨hkw, hka⟩ := State.mem_modalLift.mp hk
    rw [Finset.mem_singleton] at hkw
    refine ⟨d'', ?_, ?_⟩
    · rw [hka, ← hupd']
      simp only [Index.assign_update, Function.update_self]
    · rw [hkw]
      exact hmem

/-- **Fact 6 (distribution°)** of [aloni-vanormondt-2023]: on epistemic
    models (state-based `R`),

    `[∀x(Px ∨ Qx)]⁺ ⊨ ∃x◇Px ∧ ∃x◇Qx`.

    Stated for atoms, as in the paper (the proof evaluates the atom
    pointwise at a single transplanted world; the paper notes the result
    "can easily be generalised", which for arbitrary NE-free formulas would
    route through flatness). -/
theorem distributionEpi_Q (M : QBSMLModel W Domain Pred)
    (P Q : Pred) (x : Var) (s : Finset (Index W Var Domain))
    (hSB : M.IsStateBased s)
    (h : support M
      (QBSMLFormula.enrich (.univ x (.disj (.pred P x) (.pred Q x)))) s) :
    support M (.exi x (.poss (.pred P x))) s ∧
    support M (.exi x (.poss (.pred Q x))) s := by
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1.1
  exact ⟨exi_poss_atom_of_subset_extendUniversal M hSB
      (hunion ▸ Finset.subset_union_left)
      (enriched_support_implies_nonempty M (.pred P x) t₁ h₁) h₁.1,
    exi_poss_atom_of_subset_extendUniversal M hSB
      (hunion ▸ Finset.subset_union_right)
      (enriched_support_implies_nonempty M (.pred Q x) t₂ h₂) h₂.1⟩

end AloniVanOrmondt2023
