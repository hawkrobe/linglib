import Mathlib.ModelTheory.Satisfiability
import Linglib.Logic.Modal.FirstOrder.Correspondence
import Linglib.Logic.Modal.QBSML.Properties

/-!
# Classical model theory for the NE-free fragment of QBSML

[aloni-vanormondt-2023] Proposition 4.1 composed with the standard
translation (`Logic/Modal/FirstOrder/Correspondence.lean`): NE-free QBSML
support at a singleton state is mathlib `Formula.Realize` over the
correspondence structure (`support_singleton_iff_st`), support forces the
closed translation as a sentence and conversely
(`models_toSentence_of_support`, `exists_support_of_models_toSentence`),
and mathlib's first-order compactness transfers to finite team
satisfiability (`support_compactness`).
-/

universe u v

namespace QBSML

open FirstOrder Language

variable {W Var Const Pred Domain : Type*}
variable [DecidableEq W] [DecidableEq Var] [Fintype Var]
variable [DecidableEq Domain] [Fintype Domain]

/-! ### Proposition 4.1, composed: QBSML support is first-order realization -/

/-- **NE-free QBSML support is single-structure first-order satisfaction**:
    [aloni-vanormondt-2023] Proposition 4.1 composed with the standard
    translation. Support at a singleton state is mathlib `Formula.Realize`
    of the standard translation over `corrStructure` — the link along which
    classical model theory (compactness, Löwenheim–Skolem) transfers to the
    NE-free fragment. -/
theorem support_singleton_iff_st (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula (Language.monadicWithConstants Const Pred) Var} {k : ℕ}
    {ψ : (Language.correspondence Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : φ.toModal? = some τ) (hψ : τ.st? k = some ψ)
    {i : Index W Var Domain} {v : Var → Domain} (u : ℕ → W)
    (hv : ∀ y, i.assign y = some (v y)) (hu : u k = i.world) :
    support M φ {i} ↔
      (letI := M.corrStructure
       ψ.Realize (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ u))) :=
  (support_singleton_iff_realize M hτ hv).trans
    (realize_st? M hψ (fun _ => rfl) (by rw [Sum.elim_inr, Function.comp_apply, hu]))

/-- Support at a singleton state forces the closed standard translation,
    as a sentence of `corrStructure`. -/
theorem models_toSentence_of_support (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula (Language.monadicWithConstants Const Pred) Var}
    {ψ : (Language.correspondence Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : φ.toModal? = some τ) (hψ : τ.st? 0 = some ψ)
    (hcl : (stClose 0 ψ).freeVarFinset = ∅)
    {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = some (v y)) (hsupp : support M φ {i}) :
    (letI := M.corrStructure
     (W ⊕ Domain) ⊨ (stClose 0 ψ).toSentence hcl) := by
  letI := M.corrStructure
  have h1 : ψ.Realize
      (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world))) :=
    (support_singleton_iff_st M hτ hψ (fun _ => i.world) hv rfl).mp hsupp
  refine (Formula.realize_toSentence _ hcl
    (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world)))).mpr ?_
  refine (realize_stClose M 0 ψ _).mpr ⟨i.world, ?_⟩
  rw [show Function.update
      (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world)))
      (Sum.inr 0) (Sum.inl i.world)
      = Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world)) from
    Function.update_eq_self _ _]
  exact h1

/-- Conversely, the closed standard translation as a sentence of
    `corrStructure` yields support at some singleton state. -/
theorem exists_support_of_models_toSentence [Nonempty Domain]
    (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula (Language.monadicWithConstants Const Pred) Var}
    {ψ : (Language.correspondence Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : φ.toModal? = some τ) (hψ : τ.st? 0 = some ψ)
    (hcl : (stClose 0 ψ).freeVarFinset = ∅)
    (h : letI := M.corrStructure
         (W ⊕ Domain) ⊨ (stClose 0 ψ).toSentence hcl) :
    ∃ (i : Index W Var Domain) (v : Var → Domain),
      (∀ y, i.assign y = some (v y)) ∧ support M φ {i} := by
  letI := M.corrStructure
  obtain ⟨d₀⟩ := ‹Nonempty Domain›
  have h0 : (stClose 0 ψ).Realize
      (fun _ => (Sum.inr d₀ : W ⊕ Domain)) :=
    (Formula.realize_toSentence _ hcl _).mp h
  obtain ⟨w, hw⟩ := (realize_stClose M 0 ψ _).mp h0
  have hsorted : ∀ x : Var, Function.update
      (fun _ : Var ⊕ ℕ => (Sum.inr d₀ : W ⊕ Domain)) (Sum.inr 0)
      (Sum.inl w) (Sum.inl x) = Sum.inr d₀ := fun x => by
    rw [Function.update_of_ne (by simp)]
  have hmodal : τ.Realize M w (fun _ => d₀) :=
    (realize_st? M hψ hsorted (Function.update_self _ _ _)).mpr hw
  exact ⟨⟨w, fun _ => some d₀⟩, fun _ => d₀, fun _ => rfl,
    (support_singleton_iff_realize M hτ fun _ => rfl).mpr hmodal⟩

/-! ### Compactness for the NE-free fragment -/

/-- **Compactness transfer for NE-free QBSML** ([aloni-vanormondt-2023]
    Proposition 4.1, the standard translation, and mathlib's
    `Theory.isSatisfiable_iff_isFinitelySatisfiable`): if every finite
    subfamily of a family of NE-free formulas is supported at a singleton
    state of some model, the family's closed standard translations are
    jointly satisfiable in a single first-order structure.

    The converse recovery of a *team* model from that structure would need
    `Finset`-branching accessibility and a `Fintype` domain, which an
    arbitrary first-order structure does not supply, so the transfer is
    stated one-way. Compactness for team-semantic consequence is proved
    directly (ultraproducts and saturation, without translation) by
    [puljujarvi-quadrellaro-2024], who also separate satisfiability- from
    entailment-compactness in team logics. -/
theorem support_compactness {Var : Type*} [DecidableEq Var] [Fintype Var]
    {Const : Type u} {Pred : Type v} {ι : Type*}
    {φs : ι → Formula Var Const Pred}
    {τs : ι → ModalFormula (Language.monadicWithConstants Const Pred) Var}
    {ψs : ι → (Language.correspondence Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : ∀ i, (φs i).toModal? = some (τs i))
    (hψ : ∀ i, (τs i).st? 0 = some (ψs i))
    (hcl : ∀ i, (stClose 0 (ψs i)).freeVarFinset = ∅)
    (hfin : ∀ s : Finset ι, ∃ (W Domain : Type max u v)
      (_ : DecidableEq W) (_ : DecidableEq Domain) (_ : Fintype Domain)
      (M : Model W Domain Const Pred) (i : Index W Var Domain)
      (v : Var → Domain), (∀ y, i.assign y = some (v y)) ∧
        ∀ j ∈ s, support M (φs j) {i}) :
    Theory.IsSatisfiable
      (Set.range fun i => (stClose 0 (ψs i)).toSentence (hcl i)) := by
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T₀ hT₀
  classical
  choose f hf using fun x : T₀ => hT₀ x.2
  obtain ⟨W, Domain, _, _, _, M, i, v, hv, hs⟩ := hfin (Finset.univ.image f)
  letI := M.corrStructure
  haveI : Nonempty (W ⊕ Domain) := ⟨Sum.inl i.world⟩
  haveI : (W ⊕ Domain) ⊨ (T₀ : (Language.correspondence Const Pred).Theory) := by
    refine ⟨fun σ hσ => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x : T₀,
        (stClose 0 (ψs (f x))).toSentence (hcl (f x)) = σ :=
      ⟨⟨σ, hσ⟩, hf ⟨σ, hσ⟩⟩
    exact models_toSentence_of_support M (hτ (f x)) (hψ (f x)) (hcl (f x))
      hv (hs (f x) (Finset.mem_image_of_mem f (Finset.mem_univ x)))
  exact Theory.Model.isSatisfiable (W ⊕ Domain)

end QBSML
