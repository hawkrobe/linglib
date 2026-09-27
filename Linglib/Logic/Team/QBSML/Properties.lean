module

public import Mathlib.ModelTheory.Semantics
public import Linglib.Core.ModelTheory.Binders
public import Linglib.Logic.Team.QBSML.Defs
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability

/-!
# QBSML formula properties

[aloni-vanormondt-2023] [anttila-2021]

The QBSML instances of the closure properties of [anttila-2021]
Proposition 2.2.8: NE-free formulas have downward-closed, sup-closed,
empty-team support, hence flat support, via the same
`Team.isFlat_iff` template as
`Logic/Team/BSML/Properties.lean`.

## Main declarations

* `support_empty_of_neFree`, `isLowerSet_support_of_neFree`,
  `supClosed_support_of_neFree` — the three closure properties.
* `isFlat_support_of_neFree` — flatness of the NE-free fragment
  ([anttila-2021] Proposition 2.2.16, QBSML specialisation).
* `soundFor_flat_neFree` — the NE-free fragment is sound for the flat cell
  of `Team/Definability.lean`.
* `Formula.toFormula?`,
  `support_iff_forall_realizeAt` — the modal-free case of
  [aloni-vanormondt-2023] Proposition 4.1: support of a translatable formula
  is mathlib `Formula.Realize` at every index.
* `Formula.toModal?`, `support_iff_forall_realize` — the **full**
  Proposition 4.1: the NE-free fragment (modals included) translates into
  `ModalFormula` over `Logic/Modal/FirstOrder/Semantics.lean`, and support is
  Kripke satisfaction at every index; the translation is total on exactly
  the NE-free fragment (`exists_toModal?_of_neFree`).
* `eval_mapAtoms_iff` — atom-substitution congruence: an atom map with
  bilaterally equivalent images is *salva veritate*.
* `support_disj_inl`, `support_nec_iff`, `support_nec_mono`,
  `support_exi_of_update_closure` — upward monotonicity of the NE-free
  fragment and existential introduction via witness reconstruction.

## Implementation notes

The closure inductions are folds over the connective-level lemmas of
`Team/Operations.lean` and the quantifier clauses `State.univ`/`State.exi`
of `QBSML/Defs.lean`. BSML proves its closure properties in separate
inductions; QBSML cannot: union closure of the functional-extension clause
(`State.supClosed_exi`) needs downward closure of the subformula, so the
two properties live in one joint induction — and union closure holds only
on the NE-free fragment, whereas BSML's is unconditional. The flatness
corollary is unaffected: flat consumers use NE-free anyway.
-/

@[expose] public section

namespace QBSML

open Team

variable {W Var Domain Const Pred : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-! ### Empty-team property for NE-free formulas -/

/-- Joint empty-team property of NE-free formulas, both polarities: each case is the
    empty-team lemma of its connective (`Team/Operations.lean`, `State.empty_mem_univ`,
    `State.empty_mem_exi`). -/
private theorem support_and_antiSupport_empty_of_neFree
    {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) :
    support M φ (∅ : Finset (Index W Var Domain)) ∧
    antiSupport M φ (∅ : Finset (Index W Var Domain)) := by
  induction hNE with
  | pred P x => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | predc P c => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ => exact ⟨⟨ih₁.1, ih₂.1⟩, empty_mem_tensor ih₁.2 ih₂.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨empty_mem_tensor ih₁.1 ih₂.1, ⟨ih₁.2, ih₂.2⟩⟩
  | poss _ _ => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | @exi x _ _ ih => exact ⟨State.empty_mem_exi ih.1, State.empty_mem_univ ih.2⟩
  | @univ x _ _ ih => exact ⟨State.empty_mem_univ ih.1, State.empty_mem_exi ih.2⟩

/-- NE-free QBSML formulas are supported on the empty team. -/
theorem support_empty_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    support M φ ∅ :=
  (support_and_antiSupport_empty_of_neFree hNE M).1

/-! ### Downward and union closure for NE-free formulas -/

/-- Joint downward and union closure of NE-free formulas, both polarities — the quantifier
    cases are [aloni-vanormondt-2023] Fact 2, the rest the first-order re-run of
    [anttila-2021] Proposition 2.2.8. Each case is the closure lemma of its connective;
    union closure of the functional-extension clause (`State.supClosed_exi`) needs the
    downward closure of the subformula, so the two properties live in one induction. -/
private theorem support_and_antiSupport_dc_uc_of_neFree
    {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) :
    (IsLowerSet {s | support M φ s} ∧ SupClosed {s | support M φ s}) ∧
    (IsLowerSet {s | antiSupport M φ s} ∧ SupClosed {s | antiSupport M φ s}) := by
  induction hNE with
  | pred P x => exact ⟨⟨isLowerSet_flat _, supClosed_flat _⟩, ⟨isLowerSet_flat _, supClosed_flat _⟩⟩
  | predc P c =>
    exact ⟨⟨isLowerSet_flat _, supClosed_flat _⟩, ⟨isLowerSet_flat _, supClosed_flat _⟩⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ =>
    exact ⟨⟨ih₁.1.1.inter ih₂.1.1, ih₁.1.2.inter ih₂.1.2⟩,
      ⟨ih₁.2.1.tensor ih₂.2.1, ih₁.2.2.tensor ih₂.2.2⟩⟩
  | disj _ _ ih₁ ih₂ =>
    exact ⟨⟨ih₁.1.1.tensor ih₂.1.1, ih₁.1.2.tensor ih₂.1.2⟩,
      ⟨ih₁.2.1.inter ih₂.2.1, ih₁.2.2.inter ih₂.2.2⟩⟩
  | poss _ _ =>
    exact ⟨⟨isLowerSet_flat _, supClosed_flat _⟩, ⟨isLowerSet_flat _, supClosed_flat _⟩⟩
  | @exi x _ _ ih =>
    exact ⟨⟨State.isLowerSet_exi ih.1.1, State.supClosed_exi ih.1.1 ih.1.2⟩,
      ⟨State.isLowerSet_univ ih.2.1, State.supClosed_univ ih.2.2⟩⟩
  | @univ x _ _ ih =>
    exact ⟨⟨State.isLowerSet_univ ih.1.1, State.supClosed_univ ih.1.2⟩,
      ⟨State.isLowerSet_exi ih.2.1, State.supClosed_exi ih.2.1 ih.2.2⟩⟩

/-- NE-free QBSML formulas are downward-closed ([anttila-2021]
    Proposition 2.2.8 part 1, extended to first-order). -/
theorem isLowerSet_support_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    IsLowerSet { t : Finset (Index W Var Domain) | support M φ t } :=
  (support_and_antiSupport_dc_uc_of_neFree hNE M).1.1

/-- NE-free QBSML formulas have sup-closed support.

    NB: BSML's `supClosed_support` needs no NE-free hypothesis, but
    QBSML's `exi` UC case needs downward closure of the subformula as IH
    (see the module docstring), so the QBSML version narrows to NE-free.
    The downstream flat corollary consumes NE-free anyway. -/
theorem supClosed_support_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    SupClosed { t : Finset (Index W Var Domain) | support M φ t } :=
  (support_and_antiSupport_dc_uc_of_neFree hNE M).1.2

/-! ### Flatness corollary -/

/-- **[anttila-2021] Proposition 2.2.16 (QBSML specialisation)**: NE-free
    QBSML formulas are flat. Derived from [anttila-2021] Proposition 2.2.2
    (`Team.isFlat_iff`) applied to the three closure properties
    above. -/
theorem isFlat_support_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    IsFlat { t : Finset (Index W Var Domain) | support M φ t } :=
  isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_support_of_neFree hNE M)
    (supClosed_support_of_neFree hNE M)
    (support_empty_of_neFree hNE M)

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
theorem soundFor_flat_neFree (M : Model W Domain Const Pred) :
    definableClassWhere (support M)
      (fun φ : Formula Var Const Pred => φ.NEFree) ⊆ flatProperties := by
  unfold flatProperties
  exact definableClassWhere_subset (C := IsFlat)
    fun _φ hφ => isFlat_support_of_neFree hφ M

/-! ### Fact 1: classical validities

[aloni-vanormondt-2023] Fact 1 lists the classical equivalences QBSML
validates: double negation elimination, the De Morgan laws, and the `□`/`◇`
and `∀`/`∃` dualities. In the bilateral setup every one is definitional —
negation literally swaps `support` and `antiSupport`, whose clauses are
arranged in De Morgan pairs — so each is `Iff.rfl`. -/

section Fact1

variable (M : Model W Domain Const Pred) (φ ψ : Formula Var Const Pred)
  (x : Var) (s : Finset (Index W Var Domain))

/-- Double negation elimination ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_neg : support M (.neg (.neg φ)) s ↔ support M φ s :=
  Iff.rfl

/-- De Morgan: `¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_disj :
    support M (.neg (.disj φ ψ)) s ↔ support M (.conj (.neg φ) (.neg ψ)) s :=
  Iff.rfl

/-- De Morgan: `¬(φ ∧ ψ) ≡ ¬φ ∨ ¬ψ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_conj :
    support M (.neg (.conj φ ψ)) s ↔ support M (.disj (.neg φ) (.neg ψ)) s :=
  Iff.rfl

/-- Modal duality: `¬□φ ≡ ◇¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_nec :
    support M (.neg φ.nec) s ↔ support M (.poss (.neg φ)) s :=
  Iff.rfl

/-- Modal duality: `¬◇φ ≡ □¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_poss :
    support M (.neg (.poss φ)) s ↔ support M (Formula.neg φ).nec s :=
  Iff.rfl

/-- Quantifier duality: `¬∀xφ ≡ ∃x¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_univ :
    support M (.neg (.univ x φ)) s ↔ support M (.exi x (.neg φ)) s :=
  Iff.rfl

/-- Quantifier duality: `¬∃xφ ≡ ∀x¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_exi :
    support M (.neg (.exi x φ)) s ↔ support M (.univ x (.neg φ)) s :=
  Iff.rfl

end Fact1

/-! ### Flatness as pointwise evaluation -/

/-- Flat (NE-free) support is pointwise: a team supports `φ` iff each of its
    singletons does (`Team.IsFlat` unfolded at the support set). -/
theorem support_iff_forall_singleton {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) :
    support M φ s ↔ ∀ i ∈ s, support M φ {i} :=
  isFlat_support_of_neFree hNE M s

/-- Anti-support of an NE-free formula is likewise pointwise: flatness of the
    bilateral negation. -/
theorem antiSupport_iff_forall_singleton {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) :
    antiSupport M φ s ↔ ∀ i ∈ s, antiSupport M φ {i} :=
  support_iff_forall_singleton (.neg hNE) M s

/-! ### Atom substitution salva veritate -/

/-- **Atom-substitution congruence**: an atom map whose images are
    bilaterally equivalent to the atoms they replace is *salva veritate* —
    `φ.mapAtoms fp fc` and `φ` are supported and anti-supported by exactly
    the same states. Atom-rewriting operations (e.g. [yan-2023]'s
    reinterpretation function, `Studies/Yan2023.lean`) get truth-conditional
    harmlessness for the price of their two atom lemmas. -/
theorem eval_mapAtoms_iff (M : Model W Domain Const Pred)
    {fp : Pred → Var → Formula Var Const Pred}
    {fc : Pred → Const → Formula Var Const Pred}
    (hfp : ∀ (P : Pred) (x : Var) (b : Bool)
      (s : Finset (Index W Var Domain)),
      eval M b (fp P x) s ↔ eval M b (.pred P x) s)
    (hfc : ∀ (P : Pred) (c : Const) (b : Bool)
      (s : Finset (Index W Var Domain)),
      eval M b (fc P c) s ↔ eval M b (.predc P c) s)
    (φ : Formula Var Const Pred) :
    ∀ (b : Bool) (s : Finset (Index W Var Domain)),
      eval M b (φ.mapAtoms fp fc) s ↔ eval M b φ s := by
  induction φ with
  | pred P x => exact hfp P x
  | predc P c => exact hfc P c
  | ne => exact fun _ _ => Iff.rfl
  | neg ψ ih =>
    intro b s
    cases b with
    | true => exact ih false s
    | false => exact ih true s
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro b s
    cases b with
    | true => exact and_congr (ih₁ true s) (ih₂ true s)
    | false =>
      constructor
      · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
        exact ⟨t₁, (ih₁ false t₁).mp h₁, t₂, (ih₂ false t₂).mp h₂, hsplit⟩
      · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
        exact ⟨t₁, (ih₁ false t₁).mpr h₁, t₂, (ih₂ false t₂).mpr h₂, hsplit⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro b s
    cases b with
    | true =>
      constructor
      · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
        exact ⟨t₁, (ih₁ true t₁).mp h₁, t₂, (ih₂ true t₂).mp h₂, hsplit⟩
      · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
        exact ⟨t₁, (ih₁ true t₁).mpr h₁, t₂, (ih₂ true t₂).mpr h₂, hsplit⟩
    | false => exact and_congr (ih₁ false s) (ih₂ false s)
  | poss ψ ih =>
    intro b s
    cases b with
    | true =>
      constructor
      · intro h i hi
        obtain ⟨X, hX, hne, hsupp⟩ := h i hi
        exact ⟨X, hX, hne, (ih true _).mp hsupp⟩
      · intro h i hi
        obtain ⟨X, hX, hne, hsupp⟩ := h i hi
        exact ⟨X, hX, hne, (ih true _).mpr hsupp⟩
    | false =>
      constructor
      · exact fun h i hi => (ih false _).mp (h i hi)
      · exact fun h i hi => (ih false _).mpr (h i hi)
  | exi x ψ ih =>
    intro b s
    cases b with
    | true =>
      constructor
      · rintro ⟨hf, hne, hsupp⟩
        exact ⟨hf, hne, (ih true _).mp hsupp⟩
      · rintro ⟨hf, hne, hsupp⟩
        exact ⟨hf, hne, (ih true _).mpr hsupp⟩
    | false =>
      constructor
      · exact fun h => (ih false _).mp h
      · exact fun h => (ih false _).mpr h
  | univ x ψ ih =>
    intro b s
    cases b with
    | true =>
      constructor
      · exact fun h => (ih true _).mp h
      · exact fun h => (ih true _).mpr h
    | false =>
      constructor
      · rintro ⟨hf, hne, hsupp⟩
        exact ⟨hf, hne, (ih false _).mp hsupp⟩
      · rintro ⟨hf, hne, hsupp⟩
        exact ⟨hf, hne, (ih false _).mpr hsupp⟩

/-! ### Upward monotonicity of the NE-free fragment -/

/-- Disjunction introduction: `α ⊨ α ∨ β` for NE-free `β` (the right
    disjunct is supported by the empty half of the split). -/
theorem support_disj_inl (M : Model W Domain Const Pred)
    {α β : Formula Var Const Pred} (hβ : β.NEFree)
    {s : Finset (Index W Var Domain)} (h : support M α s) :
    support M (.disj α β) s :=
  ⟨s, h, ∅, support_empty_of_neFree hβ M, sup_bot_eq s⟩

/-- Support of the derived `□` is pointwise support at the full accessible
    lift — definitional, by the `neg`/`poss` clauses of `eval`. -/
@[simp] theorem support_nec_iff (M : Model W Domain Const Pred)
    (φ : Formula Var Const Pred) (s : Finset (Index W Var Domain)) :
    support M φ.nec s ↔
      ∀ i ∈ s, support M φ
        (State.modalLift (M.access i.world) i.assign) :=
  Iff.rfl

/-- `□` is monotone: a state-wise entailment between prejacents lifts to
    their necessitations. -/
theorem support_nec_mono (M : Model W Domain Const Pred)
    {α β : Formula Var Const Pred}
    (h : ∀ t : Finset (Index W Var Domain), support M α t → support M β t)
    {s : Finset (Index W Var Domain)} (hα : support M α.nec s) :
    support M β.nec s :=
  fun i hi => h _ (hα i hi)

/-! ### Existential introduction via witness reconstruction -/

/-- A state `t` of `x`-updates of `s` (covering all of `s`) that supports
    `γ` witnesses `∃x γ` on `s`: the functional collecting, at each index,
    the values whose updates land in `t` reconstructs `t` exactly
    (`State.extendFunctional_filter_of_update_mem`). The shared
    existential-witness step of the free-choice facts
    (`Logic/Team/QBSML/FreeChoice.lean`). -/
theorem support_exi_of_update_closure (M : Model W Domain Const Pred)
    {γ : Formula Var Const Pred} {x : Var}
    {s t : Finset (Index W Var Domain)}
    (hpar : ∀ j ∈ t, ∃ i ∈ s, ∃ d, i.update x d = j)
    (hcov : ∀ i ∈ s, ∃ d, i.update x d ∈ t)
    (hsupp : support M γ t) :
    support M (.exi x γ) s := by
  refine ⟨fun i => Finset.univ.filter (fun d => i.update x d ∈ t), ?_, ?_⟩
  · intro i hi
    obtain ⟨d, hd⟩ := hcov i hi
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩⟩
  · rw [State.extendFunctional_filter_of_update_mem hpar]
    exact hsupp

/-! ### Classicality: the modal-free Realize bridge

[aloni-vanormondt-2023] Proposition 4.1 reduces the NE-free fragment to
classical quantified modal logic. The modal-free part of that reduction is
stated against mathlib first-order satisfaction: `Formula.toFormula?`
translates the fragment into `((Language.monadic Pred)[[Const]]).Formula Var` — quantifiers
via the computable named binders `Formula.all₁` / `Formula.ex₁` of
`Core/ModelTheory/Binders.lean` — support at a singleton state is
`Formula.Realize` in the structure the model carries at that world
(`support_singleton_iff_realizeAt`), and flatness extends the bridge to
arbitrary states (`support_iff_forall_realizeAt`). Modals remain outside the
bridge: their right-hand side is classical *modal* logic, which mathlib's
`ModelTheory` does not carry. -/

open FirstOrder Language

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain] in
@[simp] theorem _root_.FirstOrder.Language.ModalStructure.realizeAt_rel₁
    (M : Model W Domain Const Pred)
    (P : Pred) (x : Var) (w : W) (v : Var → Domain) :
    ((predSymb P).formula₁ (Term.var x)).RealizeAt M.interp w v ↔
      M.relInterp₁ (predSymb P) w (v x) := by
  let _S := M.interp w
  show ((predSymb P).formula₁ (Term.var x)).Realize v ↔ _
  rw [Formula.realize_rel₁, Term.realize_var, Matrix.cons_fin_one]
  exact Iff.rfl

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain] in
@[simp] theorem _root_.FirstOrder.Language.ModalStructure.realizeAt_rel₁_const
    (M : Model W Domain Const Pred) (P : Pred) (c : Const) (w : W)
    (v : Var → Domain) :
    ((predSymb P).formula₁
      (((Language.monadic Pred).con c).term)).RealizeAt M.interp w v ↔
      M.relInterp₁ (predSymb P) w (M.constInterp ((Language.monadic Pred).con c) w) := by
  let _S := M.interp w
  show ((predSymb P).formula₁ (((Language.monadic Pred).con c).term)).Realize v
    ↔ _
  rw [Formula.realize_rel₁, Term.realize_constants, Matrix.cons_fin_one]
  exact Iff.rfl

/-- Translate the modal-free fragment of QBSML into mathlib first-order
    formulas over the monadic signature: quantifiers via the computable named
    binders `Formula.all₁` / `Formula.ex₁` (`none` on `NE` and modal
    formulas). -/
def Formula.toFormula? :
    Formula Var Const Pred → Option (((Language.monadic Pred)[[Const]]).Formula Var)
  | .pred P x => some ((predSymb P).formula₁ (Term.var x))
  | .predc P c => some ((predSymb P).formula₁ (((Language.monadic Pred).con c).term))
  | .neg φ => φ.toFormula?.map (·.not)
  | .conj φ ψ => φ.toFormula?.bind fun α => ψ.toFormula?.map (α ⊓ ·)
  | .disj φ ψ => φ.toFormula?.bind fun α => ψ.toFormula?.map (α ⊔ ·)
  | .exi x φ => φ.toFormula?.map (Formula.ex₁ x ·)
  | .univ x φ => φ.toFormula?.map (Formula.all₁ x ·)
  | _ => none

omit [DecidableEq W] [Fintype Var] in
/-- Translatable formulas are NE-free. -/
theorem neFree_of_toFormula? :
    ∀ {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var},
      φ.toFormula? = some ψ → φ.NEFree := by
  intro φ
  induction φ with
  | pred P x => exact fun _ => .pred P x
  | predc P c => exact fun _ => .predc P c
  | neg φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α => exact .neg (ih hφ)
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β => exact .conj (ih₁ hφ₁) (ih₂ hφ₂)
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β => exact .disj (ih₁ hφ₁) (ih₂ hφ₂)
  | exi x φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α => exact .exi x (ih hφ)
  | univ x φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α => exact .univ x (ih hφ)
  | ne => intro ψ hψ; simp [Formula.toFormula?] at hψ
  | poss _ _ => intro ψ hψ; simp [Formula.toFormula?] at hψ

omit [DecidableEq W] [Fintype Var] [DecidableEq Domain] [Fintype Domain] in
/-- Updating an index's assignment refines the matching valuation update. -/
private lemma update_refines {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = some (v y)) (x : Var) (d : Domain) :
    ∀ y, (i.update x d).assign y = some (Function.update v x d y) := by
  intro y
  rw [Index.assign_update]
  by_cases hy : y = x
  · subst hy
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hy, Function.update_of_ne hy]
    exact hv y

/-- Joint singleton bridge: support of a translatable formula at `{i}` is
    classical satisfaction at `i.world`, and anti-support its negation. The
    bilateral induction interleaves the two through negation; the split cases
    use that every subset of a singleton is `∅` or the singleton, plus the
    empty-team property; the quantifier cases decompose the extended states
    pointwise via flatness and apply the IH at the updated index and
    valuation. -/
private theorem support_and_antiSupport_singleton_realizeAt
    (M : Model W Domain Const Pred) :
    ∀ {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var},
      φ.toFormula? = some ψ →
      ∀ {i : Index W Var Domain} {v : Var → Domain},
        (∀ y, i.assign y = some (v y)) →
        (support M φ {i} ↔ ψ.RealizeAt M.interp i.world v) ∧
        (antiSupport M φ {i} ↔ ¬ ψ.RealizeAt M.interp i.world v) := by
  intro φ
  induction φ with
  | pred P x =>
    intro ψ hψ i v hv
    rw [show (Formula.pred P x).toFormula? =
        some ((predSymb P).formula₁ (Term.var x)) from rfl,
      Option.some.injEq] at hψ
    subst hψ
    rw [ModalStructure.realizeAt_rel₁]
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
  | predc P c =>
    intro ψ hψ i v hv
    rw [show (Formula.predc P c).toFormula? =
        some ((predSymb P).formula₁ (((Language.monadic Pred).con c).term))
        from rfl,
      Option.some.injEq] at hψ
    subst hψ
    rw [ModalStructure.realizeAt_rel₁_const]
    constructor
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
  | neg φ ih =>
    intro ψ hψ i v hv
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α =>
      simp only [Formula.toFormula?, hφ] at hψ
      rw [Option.map_some, Option.some.injEq] at hψ
      subst hψ
      obtain ⟨ihs, iha⟩ := ih hφ hv
      constructor
      · rw [Formula.realizeAt_not]
        exact iha
      · rw [Formula.realizeAt_not, not_not]
        exact ihs
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ i v hv
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β =>
        simp only [Formula.toFormula?, hφ₁, hφ₂] at hψ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hψ
        subst hψ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [Formula.realizeAt_inf]
          exact and_congr ih₁s ih₂s
        · rw [Formula.realizeAt_inf, not_and_or]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} := hsplit
                simpa using h'
              exact Or.inr (ih₂a.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁a.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁a.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₂) M).2, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₁) M).2, {i}, ih₂a.mpr h, bot_sup_eq _⟩
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ i v hv
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β =>
        simp only [Formula.toFormula?, hφ₁, hφ₂] at hψ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hψ
        subst hψ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [Formula.realizeAt_sup]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} := hsplit
                simpa using h'
              exact Or.inr (ih₂s.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁s.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁s.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₂) M).1, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₁) M).1, {i}, ih₂s.mpr h, bot_sup_eq _⟩
        · rw [Formula.realizeAt_sup, not_or]
          exact and_congr ih₁a ih₂a
  | exi x φ ih =>
    intro ψ hψ i v hv
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α =>
      simp only [Formula.toFormula?, hφ] at hψ
      rw [Option.map_some, Option.some.injEq] at hψ
      subst hψ
      have hNE : φ.NEFree := neFree_of_toFormula? hφ
      constructor
      · rw [Formula.realizeAt_ex₁]
        constructor
        · rintro ⟨h, hne, hsupp⟩
          have hsupp' := (support_iff_forall_singleton hNE M _).mp hsupp
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).1).mp
            (hsupp' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ => {d}, fun j _ => Finset.singleton_nonempty d,
            (support_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).1).mpr hd
      · rw [Formula.realizeAt_ex₁, not_exists]
        show antiSupport M φ (State.extendUniversal {i} x) ↔ _
        rw [antiSupport_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).2).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨d, i, Finset.mem_singleton_self i, rfl⟩))
        · intro h j hj
          obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).2).mpr (h d)
  | univ x φ ih =>
    intro ψ hψ i v hv
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α =>
      simp only [Formula.toFormula?, hφ] at hψ
      rw [Option.map_some, Option.some.injEq] at hψ
      subst hψ
      have hNE : φ.NEFree := neFree_of_toFormula? hφ
      constructor
      · rw [Formula.realizeAt_all₁]
        show support M φ (State.extendUniversal {i} x) ↔ _
        rw [support_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).1).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨d, i, Finset.mem_singleton_self i, rfl⟩))
        · intro h j hj
          obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).1).mpr (h d)
      · rw [Formula.realizeAt_all₁, not_forall]
        constructor
        · rintro ⟨h, hne, hanti⟩
          have hanti' := (antiSupport_iff_forall_singleton hNE M _).mp hanti
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).2).mp
            (hanti' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ => {d}, fun j _ => Finset.singleton_nonempty d,
            (antiSupport_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).2).mpr hd
  | ne => intro ψ hψ; simp [Formula.toFormula?] at hψ
  | poss _ _ => intro ψ hψ; simp [Formula.toFormula?] at hψ

/-- **[aloni-vanormondt-2023] Proposition 4.1, singleton case** (modal-free
    fragment): support of a translatable formula at a singleton state is
    classical first-order satisfaction at that index's world, for any total
    valuation the index's partial assignment refines. -/
theorem support_singleton_iff_realizeAt (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var}
    (hψ : φ.toFormula? = some ψ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = some (v y)) :
    support M φ {i} ↔ ψ.RealizeAt M.interp i.world v :=
  (support_and_antiSupport_singleton_realizeAt M hψ hv).1

/-- Anti-support of a translatable formula at a singleton state is the
    classical falsity of its translation. -/
theorem antiSupport_singleton_iff_realizeAt (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var}
    (hψ : φ.toFormula? = some ψ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = some (v y)) :
    antiSupport M φ {i} ↔ ¬ ψ.RealizeAt M.interp i.world v :=
  (support_and_antiSupport_singleton_realizeAt M hψ hv).2

/-- **[aloni-vanormondt-2023] Proposition 4.1** (modal-free fragment): a
    translatable formula is supported by a state iff it is classically
    satisfied at every index — `M, s ⊨ φ(x̄)` iff `M, w ⊨_g φ(x̄)` for all
    `⟨w, g⟩ ∈ s`, with the right-hand side mathlib's `Formula.Realize`. -/
theorem support_iff_forall_realizeAt (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var}
    (hψ : φ.toFormula? = some ψ) (s : Finset (Index W Var Domain))
    (v : Index W Var Domain → Var → Domain)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support M φ s ↔ ∀ i ∈ s, ψ.RealizeAt M.interp i.world (v i) := by
  rw [support_iff_forall_singleton (neFree_of_toFormula? hψ)]
  exact forall₂_congr fun i hi =>
    support_singleton_iff_realizeAt M hψ (hv i hi)

/-! ### Classicality II: the full modal bridge

The complete [aloni-vanormondt-2023] Proposition 4.1: `Formula.toModal?`
translates the **whole NE-free fragment** — modals included — into
`ModalFormula` over the monadic signature
(`Logic/Modal/FirstOrder/Semantics.lean`), and support is Kripke satisfaction at
every index. The translation is total on exactly the NE-free fragment. -/

/-- Translate QBSML into modal formulas over the monadic signature: atoms
    embed as classical formulas, `◇` becomes the derived `ModalFormula.diamond`,
    quantifiers become named binders; only `NE` returns `none`. -/
def Formula.toModal? :
    Formula Var Const Pred →
      Option (ModalFormula ((Language.monadic Pred)[[Const]]) Var)
  | .pred P x => some ((predSymb P).modalFormula₁ (Term.var x))
  | .predc P c =>
      some ((predSymb P).modalFormula₁ (((Language.monadic Pred).con c).term))
  | .ne => none
  | .neg φ => φ.toModal?.map .not
  | .conj φ ψ =>
      φ.toModal?.bind fun α => ψ.toModal?.map (α ⊓ ·)
  | .disj φ ψ =>
      φ.toModal?.bind fun α => ψ.toModal?.map (α ⊔ ·)
  | .poss φ => φ.toModal?.map ModalFormula.diamond
  | .exi x φ => φ.toModal?.map (ModalFormula.ex x ·)
  | .univ x φ => φ.toModal?.map (ModalFormula.all x ·)

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] in
/-- Modally translatable formulas are NE-free. -/
theorem neFree_of_toModal? :
    ∀ {φ : Formula Var Const Pred}
      {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var},
      φ.toModal? = some τ → φ.NEFree := by
  intro φ
  induction φ with
  | pred P x => exact fun _ => .pred P x
  | predc P c => exact fun _ => .predc P c
  | neg φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .neg (ih hφ)
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β => exact .conj (ih₁ hφ₁) (ih₂ hφ₂)
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β => exact .disj (ih₁ hφ₁) (ih₂ hφ₂)
  | poss φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .poss (ih hφ)
  | exi x φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .exi x (ih hφ)
  | univ x φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .univ x (ih hφ)
  | ne => intro τ hτ; simp [Formula.toModal?] at hτ

omit [DecidableEq W] [DecidableEq Var] [Fintype Var] in
/-- The modal translation is total on the NE-free fragment: together with
    `neFree_of_toModal?`, the translatable and NE-free fragments
    coincide. -/
theorem exists_toModal?_of_neFree :
    ∀ {φ : Formula Var Const Pred}, φ.NEFree →
      ∃ τ, φ.toModal? = some τ := by
  intro φ h
  induction h with
  | pred P x => exact ⟨_, rfl⟩
  | predc P c => exact ⟨_, rfl⟩
  | neg _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨.not τ, by simp [Formula.toModal?, hτ]⟩
  | conj _ _ ih₁ ih₂ =>
    obtain ⟨τ₁, hτ₁⟩ := ih₁
    obtain ⟨τ₂, hτ₂⟩ := ih₂
    exact ⟨τ₁ ⊓ τ₂, by simp [Formula.toModal?, hτ₁, hτ₂]⟩
  | disj _ _ ih₁ ih₂ =>
    obtain ⟨τ₁, hτ₁⟩ := ih₁
    obtain ⟨τ₂, hτ₂⟩ := ih₂
    exact ⟨τ₁ ⊔ τ₂, by simp [Formula.toModal?, hτ₁, hτ₂]⟩
  | poss _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨τ.diamond, by simp [Formula.toModal?, hτ]⟩
  | @exi x _ _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨.ex x τ, by simp [Formula.toModal?, hτ]⟩
  | @univ x _ _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨.all x τ, by simp [Formula.toModal?, hτ]⟩

/-- Joint singleton bridge for the **full** NE-free fragment: support of a
    modally translatable formula at `{i}` is Kripke satisfaction at
    `i.world`, and anti-support its negation. The modal case decomposes the
    accessible lift pointwise via flatness: a nonempty witnessing subteam
    collapses to a single accessible world. -/
private theorem support_and_antiSupport_singleton_realize
    (M : Model W Domain Const Pred) :
    ∀ {φ : Formula Var Const Pred}
      {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var},
      φ.toModal? = some τ →
      ∀ {i : Index W Var Domain} {v : Var → Domain},
        (∀ y, i.assign y = some (v y)) →
        (support M φ {i} ↔ τ.Realize M i.world v) ∧
        (antiSupport M φ {i} ↔ ¬ τ.Realize M i.world v) := by
  intro φ
  induction φ with
  | pred P x =>
    intro τ hτ i v hv
    rw [show (Formula.pred P x).toModal? =
        some ((predSymb P).modalFormula₁ (Term.var x)) from rfl,
      Option.some.injEq] at hτ
    subst hτ
    let _I := M.interp i.world
    rw [ModalFormula.realize_rel₁, Term.realize_var]
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
  | predc P c =>
    intro τ hτ i v hv
    rw [show (Formula.predc P c).toModal? =
        some ((predSymb P).modalFormula₁
          (((Language.monadic Pred).con c).term)) from rfl,
      Option.some.injEq] at hτ
    subst hτ
    rw [ModalFormula.realize_rel₁, ModalStructure.realize_constants]
    constructor
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
  | neg φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      obtain ⟨ihs, iha⟩ := ih hφ hv
      constructor
      · rw [ModalFormula.realize_not]
        exact iha
      · rw [ModalFormula.realize_not, not_not]
        exact ihs
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ i v hv
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β =>
        simp only [Formula.toModal?, hφ₁, hφ₂] at hτ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hτ
        subst hτ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [ModalFormula.realize_inf]
          exact and_congr ih₁s ih₂s
        · rw [ModalFormula.realize_inf, not_and_or]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} :=
                  hsplit
                simpa using h'
              exact Or.inr (ih₂a.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁a.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁a.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₂) M).2, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₁) M).2, {i}, ih₂a.mpr h, bot_sup_eq _⟩
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ i v hv
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β =>
        simp only [Formula.toModal?, hφ₁, hφ₂] at hτ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hτ
        subst hτ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [ModalFormula.realize_sup]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} :=
                  hsplit
                simpa using h'
              exact Or.inr (ih₂s.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁s.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁s.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₂) M).1, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₁) M).1, {i}, ih₂s.mpr h, bot_sup_eq _⟩
        · rw [ModalFormula.realize_sup, not_or]
          exact and_congr ih₁a ih₂a
  | poss φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      have hNE : φ.NEFree := neFree_of_toModal? hφ
      constructor
      · rw [ModalFormula.realize_diamond]
        constructor
        · intro h
          obtain ⟨X, hX, ⟨w', hw'⟩, hsupp⟩ :=
            h i (Finset.mem_singleton_self i)
          have hs := (support_iff_forall_singleton hNE M _).mp hsupp
            (w', i.assign) (State.mem_modalLift.mpr ⟨hw', rfl⟩)
          exact ⟨w', hX hw', ((ih hφ (i := (w', i.assign)) hv).1).mp hs⟩
        · rintro ⟨w', hw', hreal⟩ j hj
          rw [Finset.mem_singleton] at hj
          subst hj
          refine ⟨{w'}, Finset.singleton_subset_iff.mpr hw',
            Finset.singleton_nonempty _, ?_⟩
          rw [State.modalLift_singleton]
          exact ((ih hφ (i := (w', j.assign)) hv).1).mpr hreal
      · constructor
        · intro h hex
          rw [ModalFormula.realize_diamond] at hex
          obtain ⟨w', hw', hreal⟩ := hex
          have hanti := (antiSupport_iff_forall_singleton hNE M _).mp
            (h i (Finset.mem_singleton_self i)) (w', i.assign)
            (State.mem_modalLift.mpr ⟨hw', rfl⟩)
          exact ((ih hφ (i := (w', i.assign)) hv).2).mp hanti hreal
        · intro h j hj
          rw [Finset.mem_singleton] at hj
          subst hj
          refine (antiSupport_iff_forall_singleton hNE M _).mpr ?_
          intro k hk
          obtain ⟨hkw, hka⟩ := State.mem_modalLift.mp hk
          refine ((ih hφ (i := k) fun y => by rw [hka]; exact hv y).2).mpr ?_
          intro hreal
          exact h ((ModalFormula.realize_diamond M j.world v α).mpr
            ⟨k.world, hkw, hreal⟩)
  | exi x φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      have hNE : φ.NEFree := neFree_of_toModal? hφ
      constructor
      · rw [ModalFormula.realize_ex]
        constructor
        · rintro ⟨h, hne, hsupp⟩
          have hsupp' := (support_iff_forall_singleton hNE M _).mp hsupp
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).1).mp
            (hsupp' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ => {d}, fun j _ => Finset.singleton_nonempty d,
            (support_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).1).mpr hd
      · rw [ModalFormula.realize_ex, not_exists]
        show antiSupport M φ (State.extendUniversal {i} x) ↔ _
        rw [antiSupport_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).2).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨d, i, Finset.mem_singleton_self i, rfl⟩))
        · intro h j hj
          obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).2).mpr (h d)
  | univ x φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      have hNE : φ.NEFree := neFree_of_toModal? hφ
      constructor
      · rw [ModalFormula.realize_all]
        show support M φ (State.extendUniversal {i} x) ↔ _
        rw [support_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).1).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨d, i, Finset.mem_singleton_self i, rfl⟩))
        · intro h j hj
          obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).1).mpr (h d)
      · rw [ModalFormula.realize_all, not_forall]
        constructor
        · rintro ⟨h, hne, hanti⟩
          have hanti' := (antiSupport_iff_forall_singleton hNE M _).mp hanti
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).2).mp
            (hanti' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ => {d}, fun j _ => Finset.singleton_nonempty d,
            (antiSupport_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).2).mpr hd
  | ne => intro τ hτ; simp [Formula.toModal?] at hτ

/-- **[aloni-vanormondt-2023] Proposition 4.1, singleton case** (full
    NE-free fragment): support of a modally translatable formula at a
    singleton state is Kripke satisfaction at that index's world. -/
theorem support_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = some (v y)) :
    support M φ {i} ↔ τ.Realize M i.world v :=
  (support_and_antiSupport_singleton_realize M hτ hv).1

/-- Anti-support of a modally translatable formula at a singleton state is
    classical modal falsity. -/
theorem antiSupport_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = some (v y)) :
    antiSupport M φ {i} ↔ ¬ τ.Realize M i.world v :=
  (support_and_antiSupport_singleton_realize M hτ hv).2

/-- **[aloni-vanormondt-2023] Proposition 4.1** (full NE-free fragment):
    an NE-free formula is supported by a state iff its modal translation is
    classically satisfied at every index — `M, s ⊨ φ(x̄)` iff
    `M, w ⊨_g φ(x̄)` for all `⟨w, g⟩ ∈ s`, the right-hand side Kripke
    satisfaction over mathlib structures. -/
theorem support_iff_forall_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ) (s : Finset (Index W Var Domain))
    (v : Index W Var Domain → Var → Domain)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support M φ s ↔ ∀ i ∈ s, τ.Realize M i.world (v i) := by
  rw [support_iff_forall_singleton (neFree_of_toModal? hτ)]
  exact forall₂_congr fun i hi =>
    support_singleton_iff_realize M hτ (hv i hi)

end QBSML
