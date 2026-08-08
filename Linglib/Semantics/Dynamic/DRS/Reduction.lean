import Linglib.Semantics.Dynamic.DRS.Verification
import Mathlib.ModelTheory.Semantics

/-!
# From DRT to predicate logic: the DRS → first-order reduction

The bespoke DRS box language is *equivalent to ordinary first-order
logic*. We translate each DRS into a mathlib
`FirstOrder.Language.Formula` and prove its `Realize` coincides with the
bespoke `Embedding.Verifies` — [kamp-reyle-1993]'s §1.5 ("From DRT to Predicate
Logic") and [muskens-1996]'s "DRSs are already present in classical logic",
now a Lean theorem (`DRS.realize_toFormula`) rather than an assertion.

The universe of a (sub-)DRS is *existentially closed* (`closeExists`, via
mathlib's `Formula.iExs`); the antecedent of a `⇒` is *universally closed*
(`closeForall`, via `Formula.iAlls`).

## Main declarations

* `DRS.toFormula` / `Condition.toFormula` — the translation into `L.Formula V`.
* `DRS.realize_toFormula` — the agreement theorem: a DRS's bespoke truth matches
  its first-order translation's `Realize`.
* `realize_closeExists` / `realize_closeForall` — the universe-closure operators
  realize as `∃`/`∀` over embeddings extending `v` on the closed referents.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w}

/-- Relabel the free referents `V` so that those in `U` move to the bound side
`{x // x ∈ U}` (and the rest stay free) — the splitting `iExs`/`iAlls` quantify
over. `DecidableEq V` is needed only for the `x ∈ U` test, not by `iExs`/`iAlls`. -/
def splitOn [DecidableEq V] (U : Finset V) : V → V ⊕ {x // x ∈ U} :=
  fun x => if h : x ∈ U then Sum.inr ⟨x, h⟩ else Sum.inl x

/-- Existentially close the referents in `U` within a formula over free
referents `V` (relabel via `splitOn`, then `Formula.iExs`). -/
noncomputable def closeExists [DecidableEq V] (U : Finset V) (φ : L.Formula V) : L.Formula V :=
  (φ.relabel (splitOn U)).iExs {x // x ∈ U}

/-- Universally close the referents in `U` (used for the antecedent of `⇒`). -/
noncomputable def closeForall [DecidableEq V] (U : Finset V) (φ : L.Formula V) : L.Formula V :=
  (φ.relabel (splitOn U)).iAlls {x // x ∈ U}

/-- Translate a single DRS-condition to a formula: each sub-box's universe is
existentially closed over the conjunction of its translated conditions; the
antecedent of a `⇒` is universally closed instead (§1.5). -/
noncomputable def Condition.toFormula [DecidableEq V] : Condition L V → L.Formula V
  | .rel R args => Relations.formula R (fun i => Term.var (args i))
  | .eq a b => Term.equal (Term.var a) (Term.var b)
  | .neg K =>
      (closeExists K.referents ((K.conditions.map Condition.toFormula).foldr (· ⊓ ·) ⊤)).not
  | .imp a c => closeForall a.referents
      (((a.conditions.map Condition.toFormula).foldr (· ⊓ ·) ⊤).imp
        (closeExists c.referents ((c.conditions.map Condition.toFormula).foldr (· ⊓ ·) ⊤)))
  | .dis l r =>
      closeExists l.referents ((l.conditions.map Condition.toFormula).foldr (· ⊓ ·) ⊤) ⊔
        closeExists r.referents ((r.conditions.map Condition.toFormula).foldr (· ⊓ ·) ⊤)
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- The conjunction of a list of translated conditions. -/
noncomputable def Condition.toFormulaAll [DecidableEq V] (cs : List (Condition L V)) :
    L.Formula V := (cs.map Condition.toFormula).foldr (· ⊓ ·) ⊤

/-- The conjunction of a DRS's conditions, *without* closing its universe (the
antecedent body of a `⇒`). -/
noncomputable def DRS.bodyFormula [DecidableEq V] (K : DRS L V) : L.Formula V :=
  Condition.toFormulaAll K.conditions

/-- Translate a DRS to a first-order formula: existentially close the universe
over the conjunction of the (translated) conditions (§1.5). -/
noncomputable def DRS.toFormula [DecidableEq V] (K : DRS L V) : L.Formula V :=
  closeExists K.referents (Condition.toFormulaAll K.conditions)

theorem Condition.toFormulaAll_nil [DecidableEq V] :
    Condition.toFormulaAll ([] : List (Condition L V)) = ⊤ := rfl

theorem Condition.toFormulaAll_cons [DecidableEq V] (c : Condition L V)
    (cs : List (Condition L V)) :
    Condition.toFormulaAll (c :: cs) = Condition.toFormula c ⊓ Condition.toFormulaAll cs := rfl

theorem Condition.toFormula_neg [DecidableEq V] (K : DRS L V) :
    Condition.toFormula (.neg K) = (DRS.toFormula K).not := by
  simp only [Condition.toFormula]; rfl

theorem Condition.toFormula_imp [DecidableEq V] (a c : DRS L V) :
    Condition.toFormula (.imp a c) =
      closeForall a.referents ((DRS.bodyFormula a).imp (DRS.toFormula c)) := by
  simp only [Condition.toFormula]; rfl

theorem Condition.toFormula_dis [DecidableEq V] (l r : DRS L V) :
    Condition.toFormula (.dis l r) = DRS.toFormula l ⊔ DRS.toFormula r := by
  simp only [Condition.toFormula]; rfl

variable {M : Type x} [L.Structure M]

/-! ### Agreement of the translation with the bespoke semantics -/

/-- The assignment that agrees with `v` off `U` and is given by `i` on `U`. -/
private def extendOn [DecidableEq V] (U : Finset V) (v : V → M) (i : {x // x ∈ U} → M) : V → M :=
  fun x => if h : x ∈ U then i ⟨x, h⟩ else v x

private theorem elim_comp_splitOn [DecidableEq V] (U : Finset V) (v : V → M)
    (i : {x // x ∈ U} → M) : (Sum.elim v i) ∘ (splitOn U) = extendOn U v i := by
  funext x
  simp only [splitOn, extendOn, Function.comp_apply]
  by_cases h : x ∈ U <;> simp [h]

private theorem extendOn_agrees [DecidableEq V] (U : Finset V) (v : V → M)
    (i : {x // x ∈ U} → M) : ∀ x ∉ U, extendOn U v i x = v x := by
  intro x hx; simp only [extendOn, dif_neg hx]

private theorem extendOn_restrict [DecidableEq V] (U : Finset V) (v v' : V → M)
    (h : ∀ x ∉ U, v' x = v x) : extendOn U v (fun s => v' s.val) = v' := by
  funext x
  simp only [extendOn]
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, h x hx]

/-- The `∃` over an assignment to the universe-subtype `{x // x ∈ U}` is the `∃`
over embeddings extending `v` on `U`. -/
private theorem exists_extend_iff [DecidableEq V] (U : Finset V) (v : V → M)
    (P : (V → M) → Prop) :
    (∃ i : {x // x ∈ U} → M, P (extendOn U v i)) ↔
      ∃ v', (∀ x ∉ U, v' x = v x) ∧ P v' := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨extendOn U v i, extendOn_agrees U v i, hi⟩
  · rintro ⟨v', hagree, hv'⟩
    refine ⟨fun s => v' s.val, ?_⟩
    rw [extendOn_restrict U v v' hagree]; exact hv'

/-- The `∀` analogue of `exists_extend_iff`. -/
private theorem forall_extend_iff [DecidableEq V] (U : Finset V) (v : V → M)
    (P : (V → M) → Prop) :
    (∀ i : {x // x ∈ U} → M, P (extendOn U v i)) ↔
      ∀ v', (∀ x ∉ U, v' x = v x) → P v' := by
  constructor
  · intro hi v' hagree
    have := hi (fun s => v' s.val)
    rwa [extendOn_restrict U v v' hagree] at this
  · intro hv' i
    exact hv' (extendOn U v i) (extendOn_agrees U v i)

/-- `closeExists` realizes as existential quantification over embeddings that
extend `v` on `U`. -/
theorem realize_closeExists [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeExists U φ).Realize v ↔ ∃ v', (∀ x ∉ U, v' x = v x) ∧ φ.Realize v' := by
  rw [closeExists, Formula.realize_iExs]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  exact exists_extend_iff U v (Formula.Realize φ)

/-- `closeForall` realizes as universal quantification over embeddings that extend
`v` on `U`. -/
theorem realize_closeForall [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeForall U φ).Realize v ↔ ∀ v', (∀ x ∉ U, v' x = v x) → φ.Realize v' := by
  rw [closeForall, Formula.realize_iAlls]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  exact forall_extend_iff U v (Formula.Realize φ)

private theorem Condition.realize_toFormulaAll_of_forall [DecidableEq V]
    {cs : List (Condition L V)} {v : Embedding V M}
    (ih : ∀ c ∈ cs, (Condition.toFormula c).Realize v ↔ v.VerifiesCondition c) :
    (Condition.toFormulaAll cs).Realize v ↔ ∀ c ∈ cs, v.VerifiesCondition c := by
  induction cs with
  | nil => simp [Condition.toFormulaAll_nil, Formula.realize_top]
  | cons c cs ihl =>
    rw [Condition.toFormulaAll_cons, Formula.realize_inf, List.forall_mem_cons]
    exact and_congr (ih c (by simp)) (ihl fun d hd => ih d (List.mem_cons_of_mem c hd))

private theorem DRS.realize_bodyFormula_of_forall [DecidableEq V] {K : DRS L V}
    {v : Embedding V M}
    (ih : ∀ c ∈ K.conditions, (Condition.toFormula c).Realize v ↔ v.VerifiesCondition c) :
    (DRS.bodyFormula K).Realize v ↔ v.Verifies K :=
  Condition.realize_toFormulaAll_of_forall ih

private theorem DRS.realize_toFormula_of_forall [DecidableEq V] {K : DRS L V}
    {v : Embedding V M}
    (ih : ∀ c ∈ K.conditions, ∀ w : Embedding V M,
      (Condition.toFormula c).Realize w ↔ w.VerifiesCondition c) :
    (DRS.toFormula K).Realize v ↔ ∃ v', K.Extends v v' ∧ v'.Verifies K := by
  simp only [DRS.toFormula, realize_closeExists, Box.Extends, Embedding.Verifies]
  exact exists_congr fun v' => and_congr_right fun _ =>
    Condition.realize_toFormulaAll_of_forall fun c hc => ih c hc v'

/-- A single condition's translation realizes as `VerifiesCondition`. -/
theorem Condition.realize_toFormula [DecidableEq V] (c : Condition L V) (v : Embedding V M) :
    (Condition.toFormula c).Realize v ↔ v.VerifiesCondition c := by
  match c with
  | .rel R args =>
    simp [Condition.toFormula, Relations.formula, Formula.Realize,
      BoundedFormula.realize_rel, Term.realize_var]
  | .eq a b => simp [Condition.toFormula, Formula.realize_equal]
  | .neg K =>
    have ih : ∀ d ∈ K.conditions, ∀ w : Embedding V M,
        (Condition.toFormula d).Realize w ↔ w.VerifiesCondition d :=
      fun d _ w => Condition.realize_toFormula d w
    rw [Condition.toFormula_neg, Formula.realize_not, DRS.realize_toFormula_of_forall ih,
      Embedding.verifies_neg]
  | .imp a c' =>
    have iha : ∀ d ∈ a.conditions, ∀ w : Embedding V M,
        (Condition.toFormula d).Realize w ↔ w.VerifiesCondition d :=
      fun d _ w => Condition.realize_toFormula d w
    have ihc : ∀ d ∈ c'.conditions, ∀ w : Embedding V M,
        (Condition.toFormula d).Realize w ↔ w.VerifiesCondition d :=
      fun d _ w => Condition.realize_toFormula d w
    rw [Condition.toFormula_imp, Embedding.verifies_imp, realize_closeForall]
    refine forall_congr' fun v' => imp_congr_right fun _ => ?_
    rw [Formula.realize_imp, DRS.realize_bodyFormula_of_forall fun d hd => iha d hd v',
      DRS.realize_toFormula_of_forall ihc]
  | .dis l r =>
    have ihl : ∀ d ∈ l.conditions, ∀ w : Embedding V M,
        (Condition.toFormula d).Realize w ↔ w.VerifiesCondition d :=
      fun d _ w => Condition.realize_toFormula d w
    have ihr : ∀ d ∈ r.conditions, ∀ w : Embedding V M,
        (Condition.toFormula d).Realize w ↔ w.VerifiesCondition d :=
      fun d _ w => Condition.realize_toFormula d w
    rw [Condition.toFormula_dis, Formula.realize_sup, Embedding.verifies_dis,
      DRS.realize_toFormula_of_forall ihl, DRS.realize_toFormula_of_forall ihr]
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- A list of conditions' conjoined translation realizes as the conjunction of
their realizations. -/
theorem Condition.realize_toFormulaAll [DecidableEq V] (cs : List (Condition L V))
    (v : Embedding V M) :
    (Condition.toFormulaAll cs).Realize v ↔ ∀ c ∈ cs, v.VerifiesCondition c :=
  Condition.realize_toFormulaAll_of_forall fun c _ => Condition.realize_toFormula c v

/-- The open body of a DRS (its conditions, no universe closure) realizes as
`Verifies` of the DRS (used for the antecedent of `⇒`). -/
theorem DRS.realize_bodyFormula [DecidableEq V] (K : DRS L V) (v : Embedding V M) :
    (DRS.bodyFormula K).Realize v ↔ v.Verifies K :=
  DRS.realize_bodyFormula_of_forall fun c _ => Condition.realize_toFormula c v

/-- **DRT ⊆ FOL** (§1.5): the
translated formula's `Realize` coincides with the bespoke `Embedding.Verifies`. As
`toFormula` existentially closes the universe, the correspondence is with an
embedding `v'` extending `v` over `K.referents`. -/
theorem DRS.realize_toFormula [DecidableEq V] (K : DRS L V) (v : Embedding V M) :
    (K.toFormula).Realize v ↔ ∃ v', K.Extends v v' ∧ v'.Verifies K :=
  DRS.realize_toFormula_of_forall fun c _ w => Condition.realize_toFormula c w

end DRT
