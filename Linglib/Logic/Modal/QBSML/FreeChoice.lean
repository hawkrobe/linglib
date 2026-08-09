import Linglib.Logic.Modal.QBSML.Enrichment
import Linglib.Logic.Modal.QBSML.Properties

/-!
# QBSML free-choice facts

[aloni-vanormondt-2023] [aloni-2022]

The free-choice, ignorance, distribution and negation facts of QBSML
([aloni-vanormondt-2023] §5), as universal theorems over arbitrary QBSML
models — the framework's account of why pragmatically enriched disjunctions
under modals license both disjuncts:

| Fact | Statement |
|------|-----------|
| 3   | `[Pa ∨ Pb]⁺ ⊨_epi ◇Pa ∧ ◇Pb` (ignorance, R state-based) |
| 5   | `card(s)=1 ⇒ M, s ⊨ [∀x(Px ∨ Qx)]⁺ ⇒ M, s ⊨ ∃xPx ∧ ∃xQx` |
| 6   | `[∀x(Px ∨ Qx)]⁺ ⊨_epi ∃x◇Px ∧ ∃x◇Qx` (distribution◇) |
| 7   | `[□(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (□-free choice) |
| 8   | `[◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (◇-free choice) |
| 9   | `[∀x◇(Px ∨ Qx)]⁺ ⊨ ∀x◇Px ∧ ∀x◇Qx` (universal FC; [chemla-2009]) |
| 10  | `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb` (negation; ignorance disappears) |

plus the quantified □-FC composite `[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ`
(`boxExiFC`) behind [yan-2023]'s Asher and Heim solutions. Fact 4
(obviation) is a countermodel claim and lives with the concrete model in
`Studies/AloniVanOrmondt2023.lean`, which instantiates the frame-free facts
(5, 7–10) there; the epistemic Facts 3 and 6 require a state-based `R` and
stay substrate-level.

## Main declarations

* `diamond_split` — the shared core: an enriched split disjunction
  supported on a modal pairing yields a non-empty world-set witness for
  each disjunct.
* `narrowScopeFC`, `boxFC`, `universalFC` — the free-choice facts.
* `boxExiFC` — quantified □-FC ([yan-2023] §4.4.3).
* `ignorance`, `distribution`, `distributionEpi`, `negationStrip`.

## Implementation notes

1. **Enrichment strengthens** (`enrichment_strengthens_support`,
   `Logic/Modal/QBSML/Enrichment.lean`): the enriched form entails
   the original on the NE-free fragment.
2. **Diamond split** (`diamond_split`): the split `t₁ ∪ t₂ = modalLift X g`
   supports the enriched disjuncts on its pieces; each piece is recovered
   from its world projection, which serves as the `Finset W` witness.
3. **NE strips**: `support_enrich_nec_iff` peels the derived `□`'s
   enrichment; `antiSupport_strip_ne` the remaining `NE` conjuncts.
4. **Witness reconstruction** (`support_exi_of_update_closure`,
   `Logic/Modal/QBSML/Properties.lean`): existential witnesses for
   the quantified facts.

The negation fact requires no frame condition on `R` ([aloni-vanormondt-2023]
page 564 proof of Fact 10: "Assume M, s ⊨ [¬(Pa ∨ Pb)]⁺. It follows that
s ≠ ∅ and M, s ⫤ [Pa ∨ Pb]⁺" — frame conditions on `R` are not invoked);
Facts 7 and the quantified composite hold with the *derived* `□` even though
its enrichment differs from the paper's primitive `[□φ]⁺ = □[φ]⁺ ∧ NE`.
-/

namespace QBSML

open Team

variable {W Var Domain Const Pred : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]
variable (M : Model W Domain Const Pred)
variable {α β : Formula Var Const Pred} {s : Finset (Index W Var Domain)}

/-! ### The diamond split -/

/-- A subset of a modal pairing supporting an enriched formula yields a
    non-empty world-set witness: project the worlds, pair them back with the
    same assignment (`State.modalLift_worldProj_of_subset`), and discharge
    the enrichment (`enrichment_strengthens_support`). One-sided engine of
    `diamond_split`. -/
private theorem poss_of_subset_modalLift {X : Finset W}
    {g : Assignment Var Domain} {t : Finset (Index W Var Domain)}
    (hα : α.IsNEFree) (ht : t ⊆ State.modalLift X g)
    (h : support M α.enrich t) :
    ∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M α (State.modalLift Y g) :=
  ⟨State.worldProj t, State.worldProj_subset_of_subset_modalLift ht,
    State.worldProj_nonempty (enriched_support_implies_nonempty M α t h),
    (State.modalLift_worldProj_of_subset ht).symm ▸
      enrichment_strengthens_support M α t hα h⟩

/-- The shared core of the free-choice facts: an enriched split disjunction
    supported on a modal pairing yields a non-empty world-set witness for
    each disjunct — `poss_of_subset_modalLift` on each half of the split. -/
theorem diamond_split {X : Finset W} {g : Assignment Var Domain}
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (hsupp : support M (Formula.disj α β).enrich (State.modalLift X g)) :
    (∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M α (State.modalLift Y g)) ∧
    (∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M β (State.modalLift Y g)) := by
  obtain ⟨t₁, t₂, hsplit, h₁, h₂⟩ := hsupp.1
  exact ⟨poss_of_subset_modalLift M hα (splitsAs_left_subset hsplit) h₁,
    poss_of_subset_modalLift M hβ (splitsAs_right_subset hsplit) h₂⟩

/-- Per-index form of the core: a state whose every index sees an enriched
    split disjunction supports both diamonds (shared by Facts 8 and 9). -/
private theorem possFC_on (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (.poss (Formula.disj α β).enrich) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨X, hX, -, hsupp⟩ := h i hi
    exact (diamond_split M hα hβ hsupp).1.imp
      fun Y ⟨hYX, hYne, hY⟩ => ⟨hYX.trans hX, hYne, hY⟩
  · obtain ⟨X, hX, -, hsupp⟩ := h i hi
    exact (diamond_split M hα hβ hsupp).2.imp
      fun Y ⟨hYX, hYne, hY⟩ => ⟨hYX.trans hX, hYne, hY⟩

/-! ### Free choice (Facts 7, 8 and 9) -/

/-- **Fact 8 (◇-free choice / narrow-scope FC)** of [aloni-vanormondt-2023]
    (the first-order analogue of [aloni-2022] Fact 4):

    `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for NE-free `α`, `β`.

    Projects the diamond clause of the enrichment and applies the per-index
    core `possFC_on` at `s`. -/
theorem narrowScopeFC (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (Formula.enrich (.poss (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s :=
  possFC_on M hα hβ h.1

/-- **Fact 9 (universal free choice)** of [aloni-vanormondt-2023], the
    pattern attested experimentally by [chemla-2009]:

    `[∀x◇(α ∨ β)]⁺ ⊨ ∀x◇α ∧ ∀x◇β` for NE-free `α`, `β`.

    The enriched premise evaluates the enriched diamond at the universal
    extension `s[x]`, so the conclusion is `possFC_on` at `s[x]` — the same
    per-index argument as Fact 8, one extension up. -/
theorem universalFC {x : Var} (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (Formula.enrich (.univ x (.poss (.disj α β)))) s) :
    support M (.univ x (.poss α)) s ∧ support M (.univ x (.poss β)) s :=
  possFC_on M hα hβ h.1.1

/-- **Fact 7 (□-free choice)** of [aloni-vanormondt-2023]:

    `[□(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for NE-free `α`, `β`.

    `□` is derived (`Formula.nec`), so the enrichment here is the
    negation-clause enrichment of `¬◇¬(α ∨ β)` rather than the paper's
    primitive `[□φ]⁺ = □[φ]⁺ ∧ NE` — but the fact holds all the same:
    `support_enrich_nec_iff` puts the enriched disjunction on each index's
    full accessible lift `R(wᵢ)[gᵢ]`, and `diamond_split` produces the
    witnesses. -/
theorem boxFC (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (Formula.enrich (Formula.nec (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  rw [support_enrich_nec_iff] at h
  exact ⟨fun i hi => (diamond_split M hα hβ (h.1 i hi)).1,
    fun i hi => (diamond_split M hα hβ (h.1 i hi)).2⟩

/-! ### Quantified □-free choice

`[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ` — the composite of Fact 7 with an
existential under the modal, which is the form [yan-2023]'s Asher and Heim
solutions invoke (its §4.4.3; see `Studies/Yan2023.lean`). -/

/-- A non-empty subset `t` of a functional extension of a modal lift that
    supports `γ` yields a `◇∃xγ`-witness: project `t`'s worlds, pair them
    back with the original assignment, and reconstruct `t` via
    `support_exi_of_update_closure`. The quantified analogue of
    `poss_of_subset_modalLift`. -/
private theorem poss_exi_of_subset_extendFunctional
    {γ : Formula Var Const Pred} {X₀ : Finset W}
    {g : Assignment Var Domain} {x : Var}
    {hf : Index W Var Domain → Finset Domain}
    {t : Finset (Index W Var Domain)}
    (htsub : t ⊆ State.extendFunctional (State.modalLift X₀ g) x hf)
    (htne : t.Nonempty) (hsupp : support M γ t) :
    ∃ Y, Y ⊆ X₀ ∧ Y.Nonempty ∧
      support M (.exi x γ) (State.modalLift Y g) := by
  have hpar : ∀ j ∈ t, ∃ i ∈ State.modalLift (State.worldProj t) g,
      ∃ d, Index.update i x d = j := by
    intro j hj
    obtain ⟨i, hi, d, -, rfl⟩ := State.mem_extendFunctional.mp (htsub hj)
    refine ⟨i, State.mem_modalLift.mpr
      ⟨?_, (State.mem_modalLift.mp hi).2⟩, d, rfl⟩
    exact State.mem_worldProj.mpr ⟨i.update x d, hj, Index.world_update i x d⟩
  have hcov : ∀ i' ∈ State.modalLift (State.worldProj t) g,
      ∃ d, Index.update i' x d ∈ t := by
    intro i' hi'
    obtain ⟨hi'w, hi'g⟩ := State.mem_modalLift.mp hi'
    obtain ⟨j, hjt, hjw⟩ := State.mem_worldProj.mp hi'w
    obtain ⟨i, hi, d, -, rfl⟩ := State.mem_extendFunctional.mp (htsub hjt)
    have hii' : i' = i := by
      refine Prod.ext ?_ (hi'g.trans (State.mem_modalLift.mp hi).2.symm)
      show i'.world = i.world
      rw [← hjw, Index.world_update]
    exact ⟨d, hii' ▸ hjt⟩
  refine ⟨State.worldProj t, ?_, State.worldProj_nonempty htne,
    support_exi_of_update_closure M hpar hcov hsupp⟩
  intro w hw
  obtain ⟨j, hjt, rfl⟩ := State.mem_worldProj.mp hw
  obtain ⟨i, hi, d, -, rfl⟩ := State.mem_extendFunctional.mp (htsub hjt)
  rw [Index.world_update]
  exact (State.mem_modalLift.mp hi).1

/-- **Quantified □-free choice**: `[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ` for
    NE-free `α`, `β`. The shape behind [yan-2023]'s Asher and Heim
    solutions: the enriched premise puts the enriched split disjunction on
    each index's full accessible lift's functional extension; each
    non-empty half yields a `◇∃x`-witness by
    `poss_exi_of_subset_extendFunctional`. -/
theorem boxExiFC {x : Var} (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M
      (Formula.enrich (Formula.nec (.exi x (.disj α β)))) s) :
    support M (.poss (.exi x α)) s ∧ support M (.poss (.exi x β)) s := by
  rw [support_enrich_nec_iff] at h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨hf, -, hD⟩ := (h.1 i hi).1
    obtain ⟨t₁, t₂, hsplit, h₁, -⟩ := hD.1
    exact poss_exi_of_subset_extendFunctional M
      (splitsAs_left_subset hsplit)
      (enriched_support_implies_nonempty M α t₁ h₁)
      (enrichment_strengthens_support M α t₁ hα h₁)
  · obtain ⟨hf, -, hD⟩ := (h.1 i hi).1
    obtain ⟨t₁, t₂, hsplit, -, h₂⟩ := hD.1
    exact poss_exi_of_subset_extendFunctional M
      (splitsAs_right_subset hsplit)
      (enriched_support_implies_nonempty M β t₂ h₂)
      (enrichment_strengthens_support M β t₂ hβ h₂)

/-! ### Ignorance (Fact 3) -/

/-- A non-empty substate supporting a constant atom yields the diamond on
    the whole state when `R` is state-based: transplant the substate's
    worlds to every index. Sound only because constant atoms are
    *assignment-invariant*. One-sided engine of `ignorance`. -/
private theorem poss_predc_of_stateBased {P : Pred} {c : Const}
    {t : Finset (Index W Var Domain)} (hSB : M.IsStateBased s) (hts : t ⊆ s)
    (htne : t.Nonempty) (h : support M (.predc P c) t) :
    support M (.poss (.predc P c)) s := by
  intro i hi
  refine ⟨State.worldProj t, ?_, State.worldProj_nonempty htne, ?_⟩
  · rw [hSB i.world (State.mem_worldProj.mpr ⟨i, hi, rfl⟩)]
    exact State.worldProj_mono hts
  · intro k hk
    obtain ⟨hkw, -⟩ := State.mem_modalLift.mp hk
    obtain ⟨j, hj, hjw⟩ := State.mem_worldProj.mp hkw
    rw [← hjw]
    exact h j hj

/-- **Fact 3 (ignorance)** of [aloni-vanormondt-2023]: on epistemic models
    (state-based `R`),

    `[Pc₁ ∨ Qc₂]⁺ ⊨_epi ◇Pc₁ ∧ ◇Qc₂`.

    Stated for constant atoms, as in the paper's `Pa ∨ Pb`: the transplant
    argument of `poss_predc_of_stateBased` needs assignment-invariance —
    with a free variable in place of the constant the statement is false
    (the transplanted indices carry the wrong assignments). -/
theorem ignorance {P Q : Pred} {c₁ c₂ : Const} (hSB : M.IsStateBased s)
    (h : support M
      (Formula.enrich (.disj (.predc P c₁) (.predc Q c₂))) s) :
    support M (.poss (.predc P c₁)) s ∧
    support M (.poss (.predc Q c₂)) s := by
  obtain ⟨t₁, t₂, hsplit, h₁, h₂⟩ := h.1
  exact ⟨poss_predc_of_stateBased M hSB (splitsAs_left_subset hsplit)
      h₁.2 h₁.1,
    poss_predc_of_stateBased M hSB (splitsAs_right_subset hsplit)
      h₂.2 h₂.1⟩

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
theorem negationStrip (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (Formula.enrich (.neg (.disj α β))) s) :
    support M (.neg α) s ∧ support M (.neg β) s := by
  have hDisj : antiSupport M (.disj α.enrich β.enrich) s :=
    antiSupport_strip_ne M (.disj α.enrich β.enrich) s h.1
  exact ⟨enrichment_strengthens_antiSupport M α s hα hDisj.1,
    enrichment_strengthens_antiSupport M β s hβ hDisj.2⟩

/-! ### Distribution (Facts 5 and 6) -/

/-- A non-empty subset `t` of the universal extension of a singleton state
    that supports `γ` yields an existential witness on the singleton, by
    `support_exi_of_update_closure`. The engine of Fact 5. -/
private theorem exi_of_subset_extendUniversal_singleton
    {γ : Formula Var Const Pred}
    {i : Index W Var Domain} {x : Var} {t : Finset (Index W Var Domain)}
    (htsub : t ⊆ State.extendUniversal {i} x) (htne : t.Nonempty)
    (hsupp : support M γ t) :
    support M (.exi x γ) {i} := by
  refine support_exi_of_update_closure M ?_ ?_ hsupp
  · intro j hj
    obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp (htsub hj)
    exact ⟨i', hi', d, hupd⟩
  · intro i' hi'
    rw [Finset.mem_singleton] at hi'
    subst hi'
    obtain ⟨j₀, hj₀⟩ := htne
    obtain ⟨d, i'', hi'', hupd⟩ := State.mem_extendUniversal.mp (htsub hj₀)
    rw [Finset.mem_singleton] at hi''
    subst hi''
    exact ⟨d, by rwa [hupd]⟩

/-- **Fact 5 (distribution at maximal information)** of
    [aloni-vanormondt-2023]: on a state of maximal information
    (`card s = 1`, here `s = {i}`),

    `[∀x(α ∨ β)]⁺ ⊨ ∃xα ∧ ∃xβ` for NE-free `α`, `β`.

    The enriched premise splits the universal extension `{i}[x]` into
    non-empty parts supporting the enriched disjuncts; because the state is
    a singleton, every part extends the *same* index, so each part is the
    image of a functional extension witnessing the existential. -/
theorem distribution {x : Var} {i : Index W Var Domain}
    (hα : α.IsNEFree) (hβ : β.IsNEFree)
    (h : support M (Formula.enrich (.univ x (.disj α β))) {i}) :
    support M (.exi x α) {i} ∧ support M (.exi x β) {i} := by
  obtain ⟨t₁, t₂, hsplit, h₁, h₂⟩ := h.1.1
  exact ⟨exi_of_subset_extendUniversal_singleton M
      (splitsAs_left_subset hsplit)
      (enriched_support_implies_nonempty M α t₁ h₁)
      (enrichment_strengthens_support M α t₁ hα h₁),
    exi_of_subset_extendUniversal_singleton M
      (splitsAs_right_subset hsplit)
      (enriched_support_implies_nonempty M β t₂ h₂)
      (enrichment_strengthens_support M β t₂ hβ h₂)⟩

/-- A non-empty subset `t` of `s[x]` supporting the atom `Px` yields
    `∃x◇Px` on `s` when `R` is state-based: some index of `t` is `i₀[x/d]`
    with `d ∈ I(i₀.world)(P)`, the individual extension `s[x/d]` (as the
    constant functional) witnesses the existential, and state-basedness puts
    `i₀.world` in every index's accessible set, so the singleton
    `{i₀.world}` witnesses each diamond. The engine of Fact 6. -/
private theorem exi_poss_atom_of_subset_extendUniversal
    {P : Pred} {x : Var} {t : Finset (Index W Var Domain)}
    (hSB : M.IsStateBased s)
    (htsub : t ⊆ State.extendUniversal s x) (htne : t.Nonempty)
    (hsupp : support M (.pred P x) t) :
    support M (.exi x (.poss (.pred P x))) s := by
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
    rw [hSB j.world hjw]
    exact State.mem_worldProj.mpr ⟨i₀, hi₀s, rfl⟩
  · intro k hk
    obtain ⟨hkw, hka⟩ := State.mem_modalLift.mp hk
    rw [Finset.mem_singleton] at hkw
    refine ⟨d'', ?_, ?_⟩
    · rw [hka, ← hupd']
      simp only [Index.assign_update, Function.update_self]
    · rw [hkw]
      exact hmem

/-- **Fact 6 (distribution◇)** of [aloni-vanormondt-2023]: on epistemic
    models (state-based `R`),

    `[∀x(Px ∨ Qx)]⁺ ⊨ ∃x◇Px ∧ ∃x◇Qx`.

    Stated for atoms, as in the paper (the proof evaluates the atom
    pointwise at a single transplanted world; the paper notes the result
    "can easily be generalised", which for arbitrary NE-free formulas would
    route through flatness). -/
theorem distributionEpi {P Q : Pred} {x : Var} (hSB : M.IsStateBased s)
    (h : support M
      (Formula.enrich (.univ x (.disj (.pred P x) (.pred Q x)))) s) :
    support M (.exi x (.poss (.pred P x))) s ∧
    support M (.exi x (.poss (.pred Q x))) s := by
  obtain ⟨t₁, t₂, hsplit, h₁, h₂⟩ := h.1.1
  exact ⟨exi_poss_atom_of_subset_extendUniversal M hSB
      (splitsAs_left_subset hsplit)
      (enriched_support_implies_nonempty M (.pred P x) t₁ h₁) h₁.1,
    exi_poss_atom_of_subset_extendUniversal M hSB
      (splitsAs_right_subset hsplit)
      (enriched_support_implies_nonempty M (.pred Q x) t₂ h₂) h₂.1⟩

end QBSML
