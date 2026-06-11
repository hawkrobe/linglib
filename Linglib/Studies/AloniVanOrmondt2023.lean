import Linglib.Core.Logic.Modal.QBSML.Enrichment
import Linglib.Core.Logic.Modal.QBSML.StandardTranslation
import Linglib.Core.Logic.Modal.QBSML.Properties
import Linglib.Phenomena.FreeChoice.Atoms
import Linglib.Phenomena.FreeChoice.Worlds

/-!
# [aloni-vanormondt-2023]: QBSML applied to modified numerals + split disjunction

[aloni-vanormondt-2023] [aloni-2022]

Aloni & van Ormondt 2023 introduces QBSML, the first-order extension of
Aloni 2022's BSML, and applies it to a battery of inferences arising from
modified numerals analysed as disjunctions:
  `at least n φ ↦ n ∨ more`,  `at most n φ ↦ n ∨ less`.

The framework's central facts (paper §5):

| Fact | Statement |
|------|-----------|
| 3   | `[Pa ∨ Pb]⁺ ⊨_epi ◇Pa ∧ ◇Pb` (ignorance, R state-based) |
| 4   | `[∀xPx ∨ Qx]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)` (obviation; counterexample on paper Fig. 14) |
| 5   | `card(s)=1 ⇒ M, s ⊨ [∀x(Px ∨ Qx)]⁺ ⇒ M, s ⊨ ∃xPx ∧ ∃xQx` (distribution under full information) |
| 6   | `[∀x(Px ∨ Qx)]⁺ ⊨_epi ∃x◇Px ∧ ∃x◇Qx` (distribution° on epistemic models) |
| 7   | `[□(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (□-free choice) |
| 8   | `[◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (◇-free choice; ≡ Aloni 2022 NS FC at first-order) |
| 9   | `[∀x◇(Px ∨ Qx)]⁺ ⊨ ∀x◇Px ∧ ∀x◇Qx` (universal FC; [chemla-2009]) |
| 10  | `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb` (negation behaviour; ignorance disappears) |

Facts 3 and 5–10 are proved here as universal substrate theorems over
arbitrary QBSML models, the unconditional ones instantiated at a concrete
model (`avoModel`); Fact 4 is the paper's Fig. 14 countermodel; Facts 1–2
and Proposition 4.1 live with the framework substrate in
`Core/Logic/Modal/QBSML/Properties.lean` (the modal-free Proposition 4.1
against mathlib `Formula.Realize` is instantiated here at `avoModel`, the
translation discharged by `rfl`). Fact 3 needs the individual constants of
[aloni-vanormondt-2023] Definition 4.1 — `QBSMLFormula.predc` atoms,
interpreted world-relatively via `QBSMLModel.cInterp`.

## Proof architecture (mirrors `BSML/FreeChoice.lean`)

1. **Joint enrichment-strengthens** (`enrichment_strengthens_both`):
   simultaneous induction on the NE-free derivation proving both
   `support enrich φ → support φ` and `antiSupport enrich φ → antiSupport φ`.
   The mutual structure handles negation: `support (¬ψ) = antiSupport ψ`, so
   the two directions interleave.
2. **Diamond split** (`diamond_split`): an enriched split disjunction
   supported on a modal pairing yields a non-empty world-set witness for
   each disjunct — the shared core of Facts 7, 8, 9.
3. **NE strips**: `antiSupport_strip_ne` (in `QBSML/Enrichment.lean`)
   peels the `NE` conjuncts that pragmatic enrichment inserts.

The negation fact requires no frame condition on `R` ([aloni-vanormondt-2023]
page 564 proof of Fact 10: "Assume M, s ⊨ [¬(Pa ∨ Pb)]⁺. It follows that
s ≠ ∅ and M, s ⫤ [Pa ∨ Pb]⁺" — frame conditions on `R` are not invoked);
Fact 7 holds with the *derived* `□` even though its enrichment differs from
the paper's primitive `[□φ]⁺ = □[φ]⁺ ∧ NE`.

## What is deferred

- **`Decidable` instance for `QBSML.eval`**: well-defined, but of limited
  use — the split-disjunction clauses quantify over pairs of subteams of
  the index space (`2^12 × 2^12` already at this file's model sizes), so
  kernel `decide` is infeasible for the interesting claims; the Fact 4
  countermodel is therefore proved by hand.

## Atoms and worlds

The concrete model reuses `Phenomena.FreeChoice.{FCAtom, PowerSet2World}`
from the existing FreeChoice substrate, ensuring AvO 2023 + Aloni 2022 both
target the same world space.
-/

namespace AloniVanOrmondt2023

open Core.Logic.Modal.QBSML
open FirstOrder Language
open Phenomena.FreeChoice (FCAtom PowerSet2World)

variable {W Var Domain Const Pred : Type*}
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
private theorem enrichment_strengthens_both (M : QBSMLModel W Domain Const Pred)
    {φ : QBSMLFormula Var Const Pred} (hNE : φ.IsNEFree) :
    (∀ s : Finset (Index W Var Domain), support M φ.enrich s → support M φ s) ∧
    (∀ s : Finset (Index W Var Domain),
        antiSupport M φ.enrich s → antiSupport M φ s) := by
  induction hNE with
  | pred P x =>
    refine ⟨?_, ?_⟩
    · intro s h; exact h.1
    · intro s h; exact antiSupport_strip_ne M (.pred P x) s h
  | predc P c =>
    refine ⟨?_, ?_⟩
    · intro s h; exact h.1
    · intro s h; exact antiSupport_strip_ne M (.predc P c) s h
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
theorem enrichment_strengthens_support (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.IsNEFree)
    (h : support M φ.enrich s) :
    support M φ s :=
  (enrichment_strengthens_both M hNE).1 s h

/-- **Enrichment strengthens (anti-support direction)**. -/
theorem enrichment_strengthens_antiSupport (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.IsNEFree)
    (h : antiSupport M φ.enrich s) :
    antiSupport M φ s :=
  (enrichment_strengthens_both M hNE).2 s h

/-- **Fact 3 (ignorance)** of [aloni-vanormondt-2023]: on epistemic models
    (state-based `R`),

    `[Pc₁ ∨ Qc₂]⁺ ⊨_epi ◇Pc₁ ∧ ◇Qc₂`.

    Stated for constant atoms, as in the paper's `Pa ∨ Pb`: the proof
    transplants each split-half's worlds to every index via state-basedness,
    which is sound only because constant atoms are *assignment-invariant* —
    with a free variable in place of the constant the statement is false
    (the transplanted indices carry the wrong assignments). -/
theorem ignorance_Q (M : QBSMLModel W Domain Const Pred)
    (P Q : Pred) (c₁ c₂ : Const) (s : Finset (Index W Var Domain))
    (hSB : M.IsStateBased s)
    (h : support M
      (QBSMLFormula.enrich (.disj (.predc P c₁) (.predc Q c₂))) s) :
    support M (.poss (.predc P c₁)) s ∧
    support M (.poss (.predc Q c₂)) s := by
  have hSB' : ∀ w ∈ State.worldProj s, M.access w = State.worldProj s := hSB
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1
  have ht₁s : t₁ ⊆ s := hunion ▸ Finset.subset_union_left
  have ht₂s : t₂ ⊆ s := hunion ▸ Finset.subset_union_right
  constructor
  · intro i hi
    refine ⟨State.worldProj t₁, ?_, State.worldProj_nonempty h₁.2, ?_⟩
    · rw [hSB' i.world (State.mem_worldProj.mpr ⟨i, hi, rfl⟩)]
      exact State.worldProj_mono ht₁s
    · intro k hk
      obtain ⟨hkw, -⟩ := State.mem_modalLift.mp hk
      obtain ⟨j, hj, hjw⟩ := State.mem_worldProj.mp hkw
      rw [← hjw]
      exact h₁.1 j hj
  · intro i hi
    refine ⟨State.worldProj t₂, ?_, State.worldProj_nonempty h₂.2, ?_⟩
    · rw [hSB' i.world (State.mem_worldProj.mpr ⟨i, hi, rfl⟩)]
      exact State.worldProj_mono ht₂s
    · intro k hk
      obtain ⟨hkw, -⟩ := State.mem_modalLift.mp hk
      obtain ⟨j, hj, hjw⟩ := State.mem_worldProj.mp hkw
      rw [← hjw]
      exact h₂.1 j hj

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
theorem negationStrip_Q (M : QBSMLModel W Domain Const Pred)
    (α β : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
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

/-- The shared core of the free-choice facts: an enriched split disjunction
    supported on a modal pairing yields a non-empty world-set witness for
    each disjunct. The split `t₁ ∪ t₂ = modalLift X g` supports the enriched
    disjuncts on its pieces; `State.modalLift_worldProj_of_subset` recovers
    each piece from its world projection, which serves as the `Finset W`
    witness, and `enrichment_strengthens_support` discharges the enrichment
    to plain support of α, β. -/
private theorem diamond_split (M : QBSMLModel W Domain Const Pred)
    {α β : QBSMLFormula Var Const Pred} (hα : α.IsNEFree) (hβ : β.IsNEFree)
    {X : Finset W} {g : Assignment Var Domain}
    (hsupp : support M (QBSMLFormula.disj α β).enrich (State.modalLift X g)) :
    (∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M α (State.modalLift Y g)) ∧
    (∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M β (State.modalLift Y g)) := by
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := hsupp.1
  constructor
  · have ht₁_sub : t₁ ⊆ State.modalLift X g :=
      hunion ▸ Finset.subset_union_left
    refine ⟨State.worldProj t₁,
      State.worldProj_subset_of_subset_modalLift ht₁_sub,
      State.worldProj_nonempty (enriched_support_implies_nonempty M α t₁ h₁),
      ?_⟩
    rw [State.modalLift_worldProj_of_subset ht₁_sub]
    exact enrichment_strengthens_support M α t₁ hα h₁
  · have ht₂_sub : t₂ ⊆ State.modalLift X g :=
      hunion ▸ Finset.subset_union_right
    refine ⟨State.worldProj t₂,
      State.worldProj_subset_of_subset_modalLift ht₂_sub,
      State.worldProj_nonempty (enriched_support_implies_nonempty M β t₂ h₂),
      ?_⟩
    rw [State.modalLift_worldProj_of_subset ht₂_sub]
    exact enrichment_strengthens_support M β t₂ hβ h₂

/-- Per-index form of the core: a state whose every index sees an enriched
    split disjunction supports both diamonds (shared by Facts 8 and 9). -/
private theorem possFC_on (M : QBSMLModel W Domain Const Pred)
    {α β : QBSMLFormula Var Const Pred} (hα : α.IsNEFree) (hβ : β.IsNEFree)
    {t : Finset (Index W Var Domain)}
    (h : support M (.poss (QBSMLFormula.disj α β).enrich) t) :
    support M (.poss α) t ∧ support M (.poss β) t := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨X, hX, _, hsupp⟩ := h i hi
    obtain ⟨⟨Y, hYX, hYne, hY⟩, -⟩ := diamond_split M hα hβ hsupp
    exact ⟨Y, hYX.trans hX, hYne, hY⟩
  · obtain ⟨X, hX, _, hsupp⟩ := h i hi
    obtain ⟨-, ⟨Y, hYX, hYne, hY⟩⟩ := diamond_split M hα hβ hsupp
    exact ⟨Y, hYX.trans hX, hYne, hY⟩

/-- **Fact 8 (◇-free choice / narrow-scope FC)** of [aloni-vanormondt-2023]
    (the first-order analogue of [aloni-2022] Fact 4):

    `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for NE-free `α`, `β`.

    Projects the diamond clause of the enrichment and applies the per-index
    core `possFC_on` at `s`. -/
theorem narrowScopeFC_Q (M : QBSMLModel W Domain Const Pred)
    (α β : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
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
theorem universalFC_Q (M : QBSMLModel W Domain Const Pred)
    (α β : QBSMLFormula Var Const Pred) (x : Var) (s : Finset (Index W Var Domain))
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (QBSMLFormula.enrich (.univ x (.poss (.disj α β)))) s) :
    support M (.univ x (.poss α)) s ∧ support M (.univ x (.poss β)) s :=
  possFC_on M hα hβ h.1.1

/-- **Fact 7 (□-free choice)** of [aloni-vanormondt-2023]:

    `[□(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for NE-free `α`, `β`.

    `□` is derived (`QBSMLFormula.nec`), so the enrichment here is the
    negation-clause enrichment of `¬◇¬(α ∨ β)` rather than the paper's
    primitive `[□φ]⁺ = □[φ]⁺ ∧ NE` — but the fact holds all the same: two
    NE-strips flip the doubly-negated diamond into support of the enriched
    disjunction on each index's full accessible lift `R(wᵢ)[gᵢ]`, and
    `diamond_split` produces the witnesses. -/
theorem boxFC_Q (M : QBSMLModel W Domain Const Pred)
    (α β : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (QBSMLFormula.enrich (QBSMLFormula.nec (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  -- enrich (¬◇¬(α∨β)) = (¬[◇¬(α∨β)]⁺) ∧ NE; project, strip the ◇-clause's NE.
  have hPossAnti : antiSupport M
      (.poss (QBSMLFormula.neg (.disj α β)).enrich) s :=
    antiSupport_strip_ne M _ s h.1
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hsupp : support M (QBSMLFormula.disj α β).enrich
        (State.modalLift (M.access i.world) i.assign) :=
      antiSupport_strip_ne M _ _ (hPossAnti i hi)
    obtain ⟨⟨Y, hYX, hYne, hY⟩, -⟩ := diamond_split M hα hβ hsupp
    exact ⟨Y, hYX, hYne, hY⟩
  · have hsupp : support M (QBSMLFormula.disj α β).enrich
        (State.modalLift (M.access i.world) i.assign) :=
      antiSupport_strip_ne M _ _ (hPossAnti i hi)
    obtain ⟨-, ⟨Y, hYX, hYne, hY⟩⟩ := diamond_split M hα hβ hsupp
    exact ⟨Y, hYX, hYne, hY⟩

/-! ### Distribution (Facts 5 and 6) -/

/-- A non-empty subset `t` of the universal extension of a singleton state
    that supports `γ` yields an existential witness on the singleton: the
    functional `h` sending the (unique) index to the domain values whose
    extensions land in `t` reconstructs `t` exactly. The engine of Fact 5. -/
private lemma exi_of_subset_extendUniversal_singleton
    (M : QBSMLModel W Domain Const Pred) {γ : QBSMLFormula Var Const Pred}
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
theorem distribution_Q (M : QBSMLModel W Domain Const Pred)
    (α β : QBSMLFormula Var Const Pred) (x : Var) (i : Index W Var Domain)
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
    (M : QBSMLModel W Domain Const Pred) {P : Pred} {x : Var}
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
theorem distributionEpi_Q (M : QBSMLModel W Domain Const Pred)
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

/-! ### Predicates and variables -/

/-- Two unary predicates `P` and `Q`: provides the non-degenerate disjunction
    `Pa ∨ Qa` matching the paper's `Pa ∨ Pb` schema (where the `a, b` are
    domain elements rather than predicate-instances). With monadic predicates
    over a 2-element domain, `Pa ∨ Qa` and `Pa ∨ Pb` are equally non-trivial
    instantiations of split disjunction. -/
inductive QPred | P | Q
  deriving DecidableEq, Repr

instance : Fintype QPred where
  elems := {.P, .Q}
  complete := by intro p; cases p <;> simp

/-- Single variable `x`. -/
inductive QVar | x
  deriving DecidableEq, Repr

instance : Fintype QVar where
  elems := {.x}
  complete := by intro v; cases v; simp

/-! ### The concrete model -/

/-- Universal-access deontic-style model on `PowerSet2World`.

    The interpretation is the `monadicStructure` of the valuation
    `V w P d := w.holds d`: both predicates hold of `d` at `w` iff `w`
    models the atom `d`. The disjunction `Px ∨ Qx` is non-degenerate at the
    *formula* level even though at this model the two interpretations
    coincide. A model with divergent P and Q extensions would discriminate
    further; this minimal model suffices for the substrate-instantiation
    tests below.

    Universal access (`access _ = univ`) means R is indisputable on every
    state but **not** state-based — same shape as `Aloni2022.deonticModel`. -/
def avoModel : QBSMLModel PowerSet2World FCAtom FCAtom QPred where
  access := λ _ => Finset.univ
  interp := λ w => monadicStructure id (λ _ d => w.holds d)

/-! ### Formulas -/

/-- The atomic formula `Px`. -/
def Px {Const : Type*} : QBSMLFormula QVar Const QPred := .pred .P .x

/-- The atomic formula `Qx`. -/
def Qx {Const : Type*} : QBSMLFormula QVar Const QPred := .pred .Q .x

/-- Disjunction `Px ∨ Qx` — paper's `Pa ∨ Pb`-shape with two distinct
    predicate-instances. -/
def PxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .disj Px Qx

/-- The negation premise `¬(Px ∨ Qx)` corresponding to the paper's
    `¬(Pa ∨ Pb)` schema. -/
def negPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .neg PxOrQx

/-- The narrow-scope FC premise `◇(Px ∨ Qx)` corresponding to the paper's
    `◇(Pa ∨ Pb)` schema. -/
def possPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .poss PxOrQx

/-- The □-FC premise `□(Px ∨ Qx)` (paper's Fact 7 schema; `□` derived). -/
def necPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := PxOrQx.nec

/-- The universal-FC premise `∀x◇(Px ∨ Qx)` (paper's Fact 9 schema). -/
def univPossPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .univ .x possPxOrQx

/-- The distribution premise `∀x(Px ∨ Qx)` (paper's Facts 4–6 schema). -/
def univPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .univ .x PxOrQx

theorem Px_isNEFree {Const : Type*} : (Px (Const := Const)).IsNEFree := .pred _ _
theorem Qx_isNEFree {Const : Type*} : (Qx (Const := Const)).IsNEFree := .pred _ _

/-! ### Fact 10 (negation): `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb` -/

/-- **Fact 10 (Negation behaviour)** at `avoModel`:

    Enriched negation `[¬(Px ∨ Qx)]⁺` entails the conjunction of negated
    disjuncts `¬Px ∧ ¬Qx`. One-line invocation of the substrate's
    `negationStrip_Q` (`Studies/AloniVanOrmondt2023/FreeChoice.lean`).
    Mirrors `Aloni2022.aloni2022_fact11_dual_prohibition` style — substrate
    theorem, model + NE-free witnesses applied. -/
theorem fact10_negation
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel negPxOrQx.enrich s) :
    support avoModel (.neg Px) s ∧ support avoModel (.neg Qx) s :=
  negationStrip_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

/-! ### Facts 7 and 8 (free choice): `[□/◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` -/

/-- **Fact 8 (Narrow-Scope free choice / ◇-FC)** at `avoModel`:

    Enriched possibility-disjunction `[◇(Px ∨ Qx)]⁺` entails `◇Px ∧ ◇Qx`.
    One-line invocation of `narrowScopeFC_Q`. The first-order analogue of
    `Aloni2022.aloni2022_fact4_NS_FC` — same template, lifted to QBSML's
    monadic predicate language. -/
theorem fact8_narrowScopeFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel possPxOrQx.enrich s) :
    support avoModel (.poss Px) s ∧ support avoModel (.poss Qx) s :=
  narrowScopeFC_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

/-- **Fact 7 (□-free choice)** at `avoModel`: `[□(Px ∨ Qx)]⁺` entails
    `◇Px ∧ ◇Qx`, with the derived `□`. One-line invocation of `boxFC_Q`. -/
theorem fact7_boxFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel necPxOrQx.enrich s) :
    support avoModel (.poss Px) s ∧ support avoModel (.poss Qx) s :=
  boxFC_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

/-! ### Facts 9 and 5 (universal FC and distribution) -/

/-- **Fact 9 (Universal free choice)** at `avoModel`:

    `[∀x◇(Px ∨ Qx)]⁺` entails `∀x◇Px ∧ ∀x◇Qx`. One-line invocation of
    `universalFC_Q` — the [chemla-2009]-attested pattern. -/
theorem fact9_universalFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel univPossPxOrQx.enrich s) :
    support avoModel (.univ .x (.poss Px)) s ∧
    support avoModel (.univ .x (.poss Qx)) s :=
  universalFC_Q avoModel Px Qx .x s Px_isNEFree Qx_isNEFree h

/-- **Fact 5 (Distribution at maximal information)** at `avoModel`: on any
    singleton state, `[∀x(Px ∨ Qx)]⁺` entails `∃xPx ∧ ∃xQx`. One-line
    invocation of `distribution_Q`. -/
theorem fact5_distribution
    (i : Index PowerSet2World QVar FCAtom)
    (h : support avoModel univPxOrQx.enrich {i}) :
    support avoModel (.exi .x Px) {i} ∧ support avoModel (.exi .x Qx) {i} :=
  distribution_Q avoModel Px Qx .x i Px_isNEFree Qx_isNEFree h

/-! ### Proposition 4.1 at the concrete model -/

/-- The (unenriched) universal premise `∀x(Px ∨ Qx)` translates into mathlib
    first-order syntax, and its support is classical `Formula.Realize` at
    every index — [aloni-vanormondt-2023] Proposition 4.1 instantiated at
    `avoModel`. The translation hypothesis is discharged by `rfl`: the
    compiler computes. -/
theorem univPxOrQx_classical
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (v : Index PowerSet2World QVar FCAtom → QVar → FCAtom)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support avoModel univPxOrQx s ↔
      ∀ i ∈ s, avoModel.RealizeAt i.world
        (Formula.all₁ QVar.x
          ((monadicRel QPred.P).formula₁ (Term.var QVar.x) ⊔
            (monadicRel QPred.Q).formula₁ (Term.var QVar.x))) (v i) :=
  support_iff_forall_realizeAt avoModel rfl s v hv

/-- The narrow-scope FC premise `◇(Px ∨ Qx)` translates into the modal layer
    over the monadic signature, and its support is Kripke satisfaction at
    every index — the **full** [aloni-vanormondt-2023] Proposition 4.1
    (modals included) at `avoModel`, the translation discharged by `rfl`. -/
theorem possPxOrQx_classical
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (v : Index PowerSet2World QVar FCAtom → QVar → FCAtom)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support avoModel possPxOrQx s ↔
      ∀ i ∈ s,
        (ModalFormula.dia
          (.sup (.ofFormula ((monadicRel QPred.P).formula₁ (Term.var QVar.x)))
            (.ofFormula
              ((monadicRel QPred.Q).formula₁ (Term.var QVar.x))))).Realize
          avoModel i.world (v i) :=
  support_iff_forall_realize avoModel rfl s v hv

/-- The closed standard translation of `∀x(Px ∨ Qx)`: quantifiers
    relativized to the individual sort, predicates world-relativized to the
    current-world variable `Sum.inr 0`. -/
def stUnivPxOrQx : (stLang FCAtom QPred).Formula (QVar ⊕ ℕ) :=
  Formula.all₁ (Sum.inl QVar.x)
    ((stIndiv.formula₁ (Term.var (Sum.inl QVar.x))).imp
      ((stRel QPred.P).formula₂ (Term.var (Sum.inr 0))
          (Term.var (Sum.inl QVar.x)) ⊔
        (stRel QPred.Q).formula₂ (Term.var (Sum.inr 0))
          (Term.var (Sum.inl QVar.x))))

/-- The closure is a genuine sentence: the compiler computes the
    free-variable finset. -/
theorem stUnivPxOrQx_closed :
    (stClose 0 stUnivPxOrQx).freeVarFinset = ∅ := by decide

/-- Support of `∀x(Px ∨ Qx)` at a singleton forces its sort-guarded closed
    standard translation as a **sentence** of `avoModel.stStructure` — the
    compactness-ready form, with every translation step (`toModal?`, `st?`,
    the free-variable check) computed by the compiler. -/
theorem univPxOrQx_sentence
    (i : Index PowerSet2World QVar FCAtom) (v : QVar → FCAtom)
    (hv : ∀ y, i.assign y = some (v y))
    (h : support avoModel univPxOrQx {i}) :
    letI := avoModel.stStructure
    (PowerSet2World ⊕ FCAtom) ⊨
      (stClose 0 stUnivPxOrQx).toSentence stUnivPxOrQx_closed :=
  models_toSentence_of_support avoModel rfl rfl stUnivPxOrQx_closed hv h

/-- Conversely, the sentence yields support at some singleton — sentencehood
    of the translation makes `∀x(Px ∨ Qx)`'s support assignment- and
    state-independent. -/
theorem support_of_stUnivPxOrQx_sentence
    (h : letI := avoModel.stStructure
         (PowerSet2World ⊕ FCAtom) ⊨
           (stClose 0 stUnivPxOrQx).toSentence stUnivPxOrQx_closed) :
    ∃ (i : Index PowerSet2World QVar FCAtom) (v : QVar → FCAtom),
      (∀ y, i.assign y = some (v y)) ∧ support avoModel univPxOrQx {i} :=
  haveI : Nonempty FCAtom := ⟨.a⟩
  exists_support_of_models_toSentence avoModel rfl rfl stUnivPxOrQx_closed h

/-! ### Frame condition: avoModel is indisputable on every state -/

/-- `avoModel`'s universal accessibility makes R indisputable on every state
    (every world sees the same `Finset.univ`). Mirrors
    `Aloni2022.deonticModel_indisputable_on_team` for the QBSML carrier.

    Indisputability vs state-basedness (paper §4.1.1, Definition 4.10):
    - Indisputable: all worlds in s↓ see the same accessible set (R constant).
    - State-based: every w ∈ s↓ sees exactly s↓ (R(w) = s↓).

    State-basedness is strictly stronger and is the precondition for the
    epistemic facts: Fact 3 (`ignorance_Q`) and Fact 6 (`distributionEpi_Q`),
    which therefore stay substrate-level (universal access is not
    state-based). Facts 7, 8 and 10 need no frame condition at all — they
    hold on every model. -/
theorem avoModel_indisputable
    (s : Finset (Index PowerSet2World QVar FCAtom)) :
    avoModel.IsIndisputable s := by
  intro _ _ _ _; rfl

/-! ### Fact 4 (obviation): the Fig. 14 countermodel

The paper's Fig. 14: a single index at the world where `Pa` and `Qb` both
hold, with an empty assignment and reflexive-only access. Its universal
`x`-extension supports the enriched disjunction by splitting *horizontally*
(`x/a` supports `Px`, `x/b` supports `Qx`), so the enriched premise holds;
but `∀x(◇Px ∧ ◇Qx)` fails because the `x/b` index cannot see any world
where `P` holds of `b`. -/

/-- The Fig. 14 domain: exactly the paper's two objects. (The third
    `FCAtom` atom would give the universal extension an `x/c` index
    supporting neither disjunct, breaking the premise — the paper notes the
    split works "because the domain contains two objects".) -/
inductive Fig14Atom | a | b
  deriving DecidableEq, Repr

instance : Fintype Fig14Atom where
  elems := {.a, .b}
  complete := by intro d; cases d <;> simp

/-- Fig. 14 valuation: `P` holds exactly of `a`, and `Q` exactly of `b`,
    wherever the world carries the corresponding atom — so `P` and `Q` have
    *divergent* extensions, unlike `avoModel`'s. -/
def fig14V (w : PowerSet2World) : QPred → Fig14Atom → Prop
  | .P, d => d = .a ∧ w.holds .a
  | .Q, d => d = .b ∧ w.holds .b

/-- The Fig. 14 model: reflexive-only access at the `both` world. -/
def fig14Model : QBSMLModel PowerSet2World Fig14Atom Fig14Atom QPred where
  access := λ _ => {PowerSet2World.both}
  interp := λ w => monadicStructure id (fig14V w)

/-- The Fig. 14 index: the `both` world with the empty assignment. -/
def fig14Index : Index PowerSet2World QVar Fig14Atom :=
  (PowerSet2World.both, fun _ => none)

/-- The Fig. 14 state: the single-index state of the counterexample. -/
def fig14State : Finset (Index PowerSet2World QVar Fig14Atom) := {fig14Index}

/-- The Fig. 14 state supports the enriched premise `[∀x(Px ∨ Qx)]⁺`: its
    universal extension splits into the `x/a` half supporting `[Px]⁺` and
    the `x/b` half supporting `[Qx]⁺` (paper Fig. 15). -/
theorem fig14_premise : support fig14Model univPxOrQx.enrich fig14State := by
  refine ⟨?_, Finset.singleton_nonempty _⟩
  show support fig14Model PxOrQx.enrich
    (State.extendUniversal fig14State QVar.x)
  refine ⟨⟨{fig14Index.update .x .a}, {fig14Index.update .x .b},
    ?_, ⟨?_, Finset.singleton_nonempty _⟩, ⟨?_, Finset.singleton_nonempty _⟩⟩,
    ⟨fig14Index.update .x .a, ?_⟩⟩
  · show ({fig14Index.update .x .a} ∪ {fig14Index.update .x .b} : Finset _)
      = State.extendUniversal fig14State QVar.x
    decide
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨.a, rfl, rfl, rfl⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨.b, rfl, rfl, rfl⟩
  · decide

/-- The Fig. 14 state does **not** support `∀x(◇Px ∧ ◇Qx)`: at the `x/b`
    index the only accessible world is `both`, where `P` holds of `a` alone
    (paper Fig. 16's failing substate). -/
theorem fig14_conclusion_fails :
    ¬ support fig14Model (.univ .x (.conj (.poss Px) (.poss Qx)))
      fig14State := by
  intro h
  obtain ⟨X, hX, hne, hsupp⟩ := h.1 (fig14Index.update .x .b) (by decide)
  have hX' : X ⊆ ({PowerSet2World.both} : Finset PowerSet2World) := hX
  have hXeq : X = {PowerSet2World.both} := by
    rcases Finset.subset_singleton_iff.mp hX' with h0 | h0
    · obtain ⟨y, hy⟩ := hne
      rw [h0] at hy
      exact absurd hy (Finset.notMem_empty y)
    · exact h0
  subst hXeq
  obtain ⟨d, hd, hP⟩ := hsupp
    (PowerSet2World.both, (fig14Index.update .x .b).assign)
    (State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩)
  rw [show (fig14Index.update QVar.x Fig14Atom.b).assign QVar.x
      = some Fig14Atom.b from rfl, Option.some.injEq] at hd
  subst hd
  exact Fig14Atom.noConfusion hP.1

/-- **Fact 4 (obviation)** of [aloni-vanormondt-2023]: the universal
    quantifier obviates the free-choice/ignorance effect —
    `[∀x(Px ∨ Qx)]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)`, witnessed by the Fig. 14
    countermodel. -/
theorem fact4_obviation :
    ∃ (M : QBSMLModel PowerSet2World Fig14Atom Fig14Atom QPred)
      (s : Finset (Index PowerSet2World QVar Fig14Atom)),
      support M univPxOrQx.enrich s ∧
      ¬ support M (.univ .x (.conj (.poss Px) (.poss Qx))) s :=
  ⟨fig14Model, fig14State, fig14_premise, fig14_conclusion_fails⟩

end AloniVanOrmondt2023
