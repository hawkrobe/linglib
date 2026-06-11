import Mathlib.ModelTheory.Semantics
import Linglib.Core.Logic.Modal.QBSML.Defs
import Linglib.Core.Logic.Team.Closure
import Linglib.Core.Logic.Team.Definability

/-!
# QBSML formula properties

[aloni-vanormondt-2023] [anttila-2021]

The QBSML instances of the closure properties of [anttila-2021]
Proposition 2.2.8: NE-free formulas have downward-closed, sup-closed,
empty-team support, hence flat support, via the same
`Core.Logic.Team.isFlat_iff` template as
`Core/Logic/Modal/BSML/Properties.lean`.

## Main declarations

* `support_empty_of_isNEFree`, `isLowerSet_support_of_isNEFree`,
  `supClosed_support_of_isNEFree` — the three closure properties.
* `isFlat_support_of_isNEFree` — flatness of the NE-free fragment
  ([anttila-2021] Proposition 2.2.16, QBSML specialisation).
* `soundFor_flat_neFree` — the NE-free fragment is sound for the flat cell
  of `Team/Definability.lean`.
* `QBSMLModel.RealizeAt`, `QBSMLFormula.toFormula?`,
  `support_iff_forall_realizeAt` — the quantifier- and modal-free case of
  [aloni-vanormondt-2023] Proposition 4.1: support of a translatable formula
  is mathlib `Formula.Realize` at every index.

## Implementation notes

BSML proves the closure properties in separate inductions; QBSML cannot.
The union case of support for `exi` (dually, anti-support for `univ`)
weakens `(t \ s).extendFunctional x h_t` to `t.extendFunctional x h_t` via
`State.extendFunctional_mono` plus downward closure of the subformula, so
union closure and downward closure must live in one joint induction — and
union closure holds only on the NE-free fragment, whereas BSML's is
unconditional. The flatness corollary is unaffected: flat consumers use
NE-free anyway.
-/

namespace Core.Logic.Modal.QBSML

open Core.Logic.Team

variable {W Var Domain Pred : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-! ### Empty-team property for NE-free formulas -/

/-- Joint empty-team property: NE-free QBSML formulas have BOTH support and
    anti-support on the empty team. The bilateral mutual induction handles
    the negation case (where support flips to antiSupport). All quantifier
    cases use `State.extendUniversal_empty` and
    `State.extendFunctional_empty`. -/
private theorem support_and_antiSupport_empty_of_isNEFree
    {φ : QBSMLFormula Var Pred} (hNE : φ.IsNEFree)
    (M : QBSMLModel W Domain Pred) :
    support M φ (∅ : Finset (Index W Var Domain)) ∧
    antiSupport M φ (∅ : Finset (Index W Var Domain)) := by
  induction hNE with
  | pred P x =>
    exact ⟨fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩
  | neg _ ih =>
    -- support (¬ψ) = antiSupport ψ; antiSupport (¬ψ) = support ψ
    exact ⟨ih.2, ih.1⟩
  | conj _ _ ih₁ ih₂ =>
    refine ⟨⟨ih₁.1, ih₂.1⟩, ?_⟩
    -- antiSupport (φ₁ ∧ φ₂) ∅: split (∅, ∅)
    refine ⟨∅, ∅, ?_, ih₁.2, ih₂.2⟩
    show ∅ ∪ ∅ = ∅
    simp
  | disj _ _ ih₁ ih₂ =>
    refine ⟨?_, ih₁.2, ih₂.2⟩
    refine ⟨∅, ∅, ?_, ih₁.1, ih₂.1⟩
    show ∅ ∪ ∅ = ∅
    simp
  | poss _ _ =>
    exact ⟨fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩
  | @exi x ψ _ ih =>
    refine ⟨?_, ?_⟩
    · -- support (∃x ψ) ∅: any functional works vacuously; take fun _ => ∅
      refine ⟨fun _ => ∅, fun i hi => absurd hi (by simp), ?_⟩
      rw [State.extendFunctional_empty]
      exact ih.1
    · show antiSupport M ψ
        (State.extendUniversal (∅ : Finset (Index W Var Domain)) x)
      rw [State.extendUniversal_empty]
      exact ih.2
  | @univ x ψ _ ih =>
    refine ⟨?_, ?_⟩
    · show support M ψ
        (State.extendUniversal (∅ : Finset (Index W Var Domain)) x)
      rw [State.extendUniversal_empty]
      exact ih.1
    · refine ⟨fun _ => ∅, fun i hi => absurd hi (by simp), ?_⟩
      rw [State.extendFunctional_empty]
      exact ih.2

/-- NE-free QBSML formulas are supported on the empty team. -/
theorem support_empty_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.IsNEFree) (M : QBSMLModel W Domain Pred) :
    support M φ ∅ :=
  (support_and_antiSupport_empty_of_isNEFree hNE M).1

/-! ### Joint downward + sup closure for NE-free formulas -/

/-- Joint statement of all four closure properties for both polarities of an
    NE-free QBSML formula. The union case of `exi` (and antiSupport `univ`)
    needs the IH's downward closure for the subformula to weaken
    `t.extendFunctional x h_t` to `(t \ s).extendFunctional x h_t`, so all
    four properties have to live inside one induction. -/
private theorem support_and_antiSupport_dc_uc_of_isNEFree
    {φ : QBSMLFormula Var Pred} (hNE : φ.IsNEFree)
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
  induction hNE with
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
  | neg _ ih =>
    obtain ⟨ihdc_s, ihuc_s, ihdc_a, ihuc_a⟩ := ih
    -- support (¬ψ) = antiSupport ψ; antiSupport (¬ψ) = support ψ
    exact ⟨ihdc_a, ihuc_a, ihdc_s, ihuc_s⟩
  | conj _ _ ih₁ ih₂ =>
    obtain ⟨ihdc_s₁, ihuc_s₁, ihdc_a₁, ihuc_a₁⟩ := ih₁
    obtain ⟨ihdc_s₂, ihuc_s₂, ihdc_a₂, ihuc_a₂⟩ := ih₂
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
      · show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
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
      · have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
        rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
          ext x; simp [Finset.mem_union]; tauto]
        rw [h1, h2]
      · exact ihuc_a₁ s₁ t₁ ha_s₁ ha_t₁
      · exact ihuc_a₂ s₂ t₂ ha_s₂ ha_t₂
  | disj _ _ ih₁ ih₂ =>
    obtain ⟨ihdc_s₁, ihuc_s₁, ihdc_a₁, ihuc_a₁⟩ := ih₁
    obtain ⟨ihdc_s₂, ihuc_s₂, ihdc_a₂, ihuc_a₂⟩ := ih₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- DC support: ∃ split (t₁,t₂) of s; intersect with t
      intro s t hsub ⟨t₁, t₂, hsplit, hs₁, hs₂⟩
      refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, ?_, ?_⟩
      · show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
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
      · have h1 : s₁ ∪ s₂ = s := hsplit_s
        have h2 : t₁ ∪ t₂ = t := hsplit_t
        show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
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
  | poss _ _ =>
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
  | @exi x ψ _ ih =>
    obtain ⟨ihdc_s, ihuc_s, ihdc_a, ihuc_a⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- DC support exi: same h works on subteam (via extendFunctional_mono + IH DC)
      intro s t hsub ⟨h, hne, hsupp⟩
      refine ⟨h, fun i hi => hne i (hsub hi), ?_⟩
      exact ihdc_s _ _ (State.extendFunctional_mono x h hsub) hsupp
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
          rw [decomp, State.extendFunctional_union]
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
            (State.extendFunctional_mono x h_t Finset.sdiff_subset) hsupp_t
        exact ihuc_s _ _ hsupp_s h_ext
    · -- DC antiSupport exi: extendUniversal t x ⊆ extendUniversal s x + IH DC
      intro s t hsub hsupp
      show antiSupport M ψ (State.extendUniversal t x)
      exact ihdc_a _ _ (State.extendUniversal_mono x hsub) hsupp
    · -- UC antiSupport exi: extendUniversal distributes + IH UC
      intro s t hs ht
      show antiSupport M ψ (State.extendUniversal (s ∪ t) x)
      rw [State.extendUniversal_union]
      exact ihuc_a _ _ hs ht
  | @univ x ψ _ ih =>
    obtain ⟨ihdc_s, ihuc_s, ihdc_a, ihuc_a⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- DC support univ: extendUniversal t x ⊆ extendUniversal s x + IH DC
      intro s t hsub hsupp
      show support M ψ (State.extendUniversal t x)
      exact ihdc_s _ _ (State.extendUniversal_mono x hsub) hsupp
    · -- UC support univ: extendUniversal distributes + IH UC
      intro s t hs ht
      show support M ψ (State.extendUniversal (s ∪ t) x)
      rw [State.extendUniversal_union]
      exact ihuc_s _ _ hs ht
    · -- DC antiSupport univ: same h works on subteam (mirror of DC support exi)
      intro s t hsub ⟨h, hne, hsupp⟩
      refine ⟨h, fun i hi => hne i (hsub hi), ?_⟩
      exact ihdc_a _ _ (State.extendFunctional_mono x h hsub) hsupp
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
          rw [decomp, State.extendFunctional_union]
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
            (State.extendFunctional_mono x h_t Finset.sdiff_subset) hsupp_t
        exact ihuc_a _ _ hsupp_s h_ext

/-- NE-free QBSML formulas are downward-closed ([anttila-2021]
    Proposition 2.2.8 part 1, extended to first-order). -/
theorem isLowerSet_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.IsNEFree) (M : QBSMLModel W Domain Pred) :
    IsLowerSet { t : Finset (Index W Var Domain) | support M φ t } :=
  fun _ _ hab hb =>
    (support_and_antiSupport_dc_uc_of_isNEFree hNE M).1 _ _ hab hb

/-- NE-free QBSML formulas have sup-closed support.

    NB: BSML's `supClosed_support` needs no NE-free hypothesis, but
    QBSML's `exi` UC case needs downward closure of the subformula as IH
    (see the module docstring), so the QBSML version narrows to NE-free.
    The downstream flat corollary consumes NE-free anyway. -/
theorem supClosed_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.IsNEFree) (M : QBSMLModel W Domain Pred) :
    SupClosed { t : Finset (Index W Var Domain) | support M φ t } :=
  fun _ ha _ hb =>
    (support_and_antiSupport_dc_uc_of_isNEFree hNE M).2.1 _ _ ha hb

/-! ### Flatness corollary -/

/-- **[anttila-2021] Proposition 2.2.16 (QBSML specialisation)**: NE-free
    QBSML formulas are flat. Derived from [anttila-2021] Proposition 2.2.2
    (`Core.Logic.Team.isFlat_iff`) applied to the three closure properties
    above. -/
theorem isFlat_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.IsNEFree) (M : QBSMLModel W Domain Pred) :
    IsFlat { t : Finset (Index W Var Domain) | support M φ t } :=
  isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_support_of_isNEFree hNE M)
    (supClosed_support_of_isNEFree hNE M)
    (support_empty_of_isNEFree hNE M)

/-! ### Soundness for the flat cell (Definability bridge) -/

/-- **The NE-free fragment of QBSML is sound for the flat cell**: every team
    property definable by an NE-free QBSML formula is flat (downward-closed,
    union-closed, empty-team). This restates [aloni-vanormondt-2023]'s
    observation that NE-free QBSML reduces to classical first-order modal
    logic, whose support is flat, in the `Team/Definability.lean` vocabulary.

    The restriction to the NE-free fragment is essential, not incidental: NE
    is the only source of non-classical behaviour, and union closure of `exi`
    already needs downward closure of the subformula as IH (see the module
    docstring), which NE breaks. So QBSML has no unconditional all-formula
    cell — unlike BSML, whose NE-bearing formulas still land in the convex,
    union-closed cell. -/
theorem soundFor_flat_neFree (M : QBSMLModel W Domain Pred) :
    definableClassWhere (support M)
      (fun φ : QBSMLFormula Var Pred => φ.IsNEFree) ⊆ flatProperties := by
  unfold flatProperties
  exact definableClassWhere_subset (C := IsFlat)
    fun _φ hφ => isFlat_support_of_isNEFree hφ M

/-! ### Classicality: the quantifier-free Realize bridge

[aloni-vanormondt-2023] Proposition 4.1 reduces the NE-free fragment to
classical quantified modal logic. The quantifier- and modal-free core of that
reduction is stated against mathlib first-order satisfaction:
`QBSMLFormula.toFormula?` translates the fragment into
`(monadicLang Pred).Formula Var`, support at a singleton state is
`Formula.Realize` in the structure the model carries at that world
(`support_singleton_iff_realizeAt`), and flatness extends the bridge to
arbitrary states (`support_iff_forall_realizeAt`). Extending the translation
to quantifiers (de Bruijn relabeling) and modals is future work. -/

open FirstOrder Language

/-- Classical first-order satisfaction at a world — `M, w ⊨_v ψ`, mathlib's
    `Formula.Realize` in the structure the model carries at `w`. The
    right-hand side of [aloni-vanormondt-2023] Proposition 4.1. -/
def QBSMLModel.RealizeAt (M : QBSMLModel W Domain Pred) (w : W)
    (ψ : (monadicLang Pred).Formula Var) (v : Var → Domain) : Prop :=
  @Formula.Realize _ _ (M.interp w) _ ψ v

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain] in
@[simp] theorem QBSMLModel.realizeAt_rel₁ (M : QBSMLModel W Domain Pred)
    (P : Pred) (x : Var) (w : W) (v : Var → Domain) :
    M.RealizeAt w ((monadicRel P).formula₁ (Term.var x)) v ↔
      M.pInterp P w (v x) := by
  letI := M.interp w
  show ((monadicRel P).formula₁ (Term.var x)).Realize v ↔ _
  have hfun : (![v x] : Fin 1 → Domain) = fun _ => v x := by
    funext j
    simp only [Matrix.cons_val_fin_one]
  rw [Formula.realize_rel₁, Term.realize_var, hfun]
  exact Iff.rfl

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain] in
@[simp] theorem QBSMLModel.realizeAt_not (M : QBSMLModel W Domain Pred)
    (w : W) (ψ : (monadicLang Pred).Formula Var) (v : Var → Domain) :
    M.RealizeAt w ψ.not v ↔ ¬ M.RealizeAt w ψ v := by
  letI := M.interp w
  exact Formula.realize_not

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain] in
@[simp] theorem QBSMLModel.realizeAt_inf (M : QBSMLModel W Domain Pred)
    (w : W) (ψ₁ ψ₂ : (monadicLang Pred).Formula Var) (v : Var → Domain) :
    M.RealizeAt w (ψ₁ ⊓ ψ₂) v ↔ M.RealizeAt w ψ₁ v ∧ M.RealizeAt w ψ₂ v := by
  letI := M.interp w
  exact Formula.realize_inf

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain] in
@[simp] theorem QBSMLModel.realizeAt_sup (M : QBSMLModel W Domain Pred)
    (w : W) (ψ₁ ψ₂ : (monadicLang Pred).Formula Var) (v : Var → Domain) :
    M.RealizeAt w (ψ₁ ⊔ ψ₂) v ↔ M.RealizeAt w ψ₁ v ∨ M.RealizeAt w ψ₂ v := by
  letI := M.interp w
  exact Formula.realize_sup

/-- Translate the quantifier- and modal-free fragment of QBSML into mathlib
    first-order formulas over the monadic signature (`none` on `NE`, modal,
    and quantified formulas). -/
def QBSMLFormula.toFormula? :
    QBSMLFormula Var Pred → Option ((monadicLang Pred).Formula Var)
  | .pred P x => some ((monadicRel P).formula₁ (Term.var x))
  | .neg φ => φ.toFormula?.map (·.not)
  | .conj φ ψ => φ.toFormula?.bind fun α => ψ.toFormula?.map (α ⊓ ·)
  | .disj φ ψ => φ.toFormula?.bind fun α => ψ.toFormula?.map (α ⊔ ·)
  | _ => none

omit [DecidableEq Var] [Fintype Var] in
/-- Translatable formulas are NE-free. -/
theorem isNEFree_of_toFormula? :
    ∀ {φ : QBSMLFormula Var Pred} {ψ : (monadicLang Pred).Formula Var},
      φ.toFormula? = some ψ → φ.IsNEFree := by
  intro φ
  induction φ with
  | pred P x => exact fun _ => .pred P x
  | neg φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [QBSMLFormula.toFormula?, hφ] at hψ
    | some α => exact .neg (ih hφ)
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [QBSMLFormula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [QBSMLFormula.toFormula?, hφ₁, hφ₂] at hψ
      | some β => exact .conj (ih₁ hφ₁) (ih₂ hφ₂)
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [QBSMLFormula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [QBSMLFormula.toFormula?, hφ₁, hφ₂] at hψ
      | some β => exact .disj (ih₁ hφ₁) (ih₂ hφ₂)
  | ne => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ
  | poss _ _ => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ
  | exi _ _ _ => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ
  | univ _ _ _ => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ

/-- Joint singleton bridge: support of a translatable formula at `{i}` is
    classical satisfaction at `i.world`, and anti-support its negation. The
    bilateral induction interleaves the two through negation; the split cases
    use that every subset of a singleton is `∅` or the singleton, plus the
    empty-team property of NE-free formulas. -/
private theorem support_and_antiSupport_singleton_realizeAt
    (M : QBSMLModel W Domain Pred) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = some (v y)) :
    ∀ {φ : QBSMLFormula Var Pred} {ψ : (monadicLang Pred).Formula Var},
      φ.toFormula? = some ψ →
      (support M φ {i} ↔ M.RealizeAt i.world ψ v) ∧
      (antiSupport M φ {i} ↔ ¬ M.RealizeAt i.world ψ v) := by
  intro φ
  induction φ with
  | pred P x =>
    intro ψ hψ
    rw [show (QBSMLFormula.pred P x).toFormula? =
        some ((monadicRel P).formula₁ (Term.var x)) from rfl,
      Option.some.injEq] at hψ
    subst hψ
    rw [QBSMLModel.realizeAt_rel₁]
    constructor
    · constructor
      · intro h
        obtain ⟨d, hd, hP⟩ := h i (Finset.mem_singleton_self i)
        rw [hv x, Option.some.injEq] at hd
        rw [hd]
        exact hP
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨v x, hv x, h⟩
    · constructor
      · intro h hP
        obtain ⟨d, hd, hnP⟩ := h i (Finset.mem_singleton_self i)
        rw [hv x, Option.some.injEq] at hd
        exact hnP (hd ▸ hP)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨v x, hv x, h⟩
  | neg φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [QBSMLFormula.toFormula?, hφ] at hψ
    | some α =>
      simp only [QBSMLFormula.toFormula?, hφ] at hψ
      rw [Option.map_some, Option.some.injEq] at hψ
      subst hψ
      obtain ⟨ihs, iha⟩ := ih hφ
      constructor
      · rw [QBSMLModel.realizeAt_not]
        exact iha
      · rw [QBSMLModel.realizeAt_not, not_not]
        exact ihs
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [QBSMLFormula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [QBSMLFormula.toFormula?, hφ₁, hφ₂] at hψ
      | some β =>
        simp only [QBSMLFormula.toFormula?, hφ₁, hφ₂] at hψ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hψ
        subst hψ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂
        constructor
        · rw [QBSMLModel.realizeAt_inf]
          exact and_congr ih₁s ih₂s
        · rw [QBSMLModel.realizeAt_inf, not_and_or]
          constructor
          · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              hsplit ▸ Finset.subset_union_left
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} := hsplit
                simpa using h'
              exact Or.inr (ih₂a.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁a.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ∅, Core.Logic.Team.splitsAs_self_empty _,
                ih₁a.mpr h,
                (support_and_antiSupport_empty_of_isNEFree
                  (isNEFree_of_toFormula? hφ₂) M).2⟩
            · exact ⟨∅, {i}, Core.Logic.Team.splitsAs_empty_self _,
                (support_and_antiSupport_empty_of_isNEFree
                  (isNEFree_of_toFormula? hφ₁) M).2,
                ih₂a.mpr h⟩
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [QBSMLFormula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [QBSMLFormula.toFormula?, hφ₁, hφ₂] at hψ
      | some β =>
        simp only [QBSMLFormula.toFormula?, hφ₁, hφ₂] at hψ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hψ
        subst hψ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂
        constructor
        · rw [QBSMLModel.realizeAt_sup]
          constructor
          · rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              hsplit ▸ Finset.subset_union_left
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} := hsplit
                simpa using h'
              exact Or.inr (ih₂s.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁s.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ∅, Core.Logic.Team.splitsAs_self_empty _,
                ih₁s.mpr h,
                (support_and_antiSupport_empty_of_isNEFree
                  (isNEFree_of_toFormula? hφ₂) M).1⟩
            · exact ⟨∅, {i}, Core.Logic.Team.splitsAs_empty_self _,
                (support_and_antiSupport_empty_of_isNEFree
                  (isNEFree_of_toFormula? hφ₁) M).1,
                ih₂s.mpr h⟩
        · rw [QBSMLModel.realizeAt_sup, not_or]
          exact and_congr ih₁a ih₂a
  | ne => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ
  | poss _ _ => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ
  | exi _ _ _ => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ
  | univ _ _ _ => intro ψ hψ; simp [QBSMLFormula.toFormula?] at hψ

/-- **[aloni-vanormondt-2023] Proposition 4.1, singleton case** (quantifier-
    and modal-free fragment): support of a translatable formula at a
    singleton state is classical first-order satisfaction at that index's
    world, for any total valuation the index's partial assignment refines. -/
theorem support_singleton_iff_realizeAt (M : QBSMLModel W Domain Pred)
    {φ : QBSMLFormula Var Pred} {ψ : (monadicLang Pred).Formula Var}
    (hψ : φ.toFormula? = some ψ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = some (v y)) :
    support M φ {i} ↔ M.RealizeAt i.world ψ v :=
  (support_and_antiSupport_singleton_realizeAt M hv hψ).1

/-- Anti-support of a translatable formula at a singleton state is the
    classical falsity of its translation. -/
theorem antiSupport_singleton_iff_realizeAt (M : QBSMLModel W Domain Pred)
    {φ : QBSMLFormula Var Pred} {ψ : (monadicLang Pred).Formula Var}
    (hψ : φ.toFormula? = some ψ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = some (v y)) :
    antiSupport M φ {i} ↔ ¬ M.RealizeAt i.world ψ v :=
  (support_and_antiSupport_singleton_realizeAt M hv hψ).2

/-- Flat (NE-free) support is pointwise: a team supports `φ` iff each of its
    singletons does (`Core.Logic.Team.IsFlat` unfolded at the support set). -/
theorem support_iff_forall_singleton {φ : QBSMLFormula Var Pred}
    (hNE : φ.IsNEFree) (M : QBSMLModel W Domain Pred)
    (s : Finset (Index W Var Domain)) :
    support M φ s ↔ ∀ i ∈ s, support M φ {i} :=
  isFlat_support_of_isNEFree hNE M s

/-- **[aloni-vanormondt-2023] Proposition 4.1** (quantifier- and modal-free
    fragment): a translatable formula is supported by a state iff it is
    classically satisfied at every index — `M, s ⊨ φ(x̄)` iff
    `M, w ⊨_g φ(x̄)` for all `⟨w, g⟩ ∈ s`, with the right-hand side mathlib's
    `Formula.Realize`. -/
theorem support_iff_forall_realizeAt (M : QBSMLModel W Domain Pred)
    {φ : QBSMLFormula Var Pred} {ψ : (monadicLang Pred).Formula Var}
    (hψ : φ.toFormula? = some ψ) (s : Finset (Index W Var Domain))
    (v : Index W Var Domain → Var → Domain)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support M φ s ↔ ∀ i ∈ s, M.RealizeAt i.world ψ (v i) := by
  rw [support_iff_forall_singleton (isNEFree_of_toFormula? hψ)]
  exact forall₂_congr fun i hi =>
    support_singleton_iff_realizeAt M hψ (hv i hi)

end Core.Logic.Modal.QBSML
