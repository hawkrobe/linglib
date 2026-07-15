import Linglib.Semantics.Dynamic.DRS.Semantics
import Mathlib.ModelTheory.Syntax

/-!
# From DRT to predicate logic: the DRS → first-order reduction
[kamp-reyle-1993] (§1.5), [muskens-1996]

The bespoke DRS box language is *equivalent to ordinary first-order
logic*. We translate each DRS into a mathlib
`FirstOrder.Language.Formula` and prove its `Realize` coincides with the bespoke
`DRS.Realize` — Kamp & Reyle's §1.5 ("From DRT to Predicate Logic") and Muskens's
"DRSs are already present in classical logic", now a Lean theorem
(`DRS.realize_toFormula`) rather than an assertion.

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

mutual
/-- Translate a DRS to a first-order formula: existentially close the universe
over the conjunction of the (translated) conditions ([kamp-reyle-1993] §1.5). -/
noncomputable def DRS.toFormula [DecidableEq V] : DRS L V → L.Formula V
  | .mk U conds => closeExists U (Condition.toFormulaAll conds)
/-- The conjunction of a DRS's conditions, *without* closing its universe (used
as the antecedent body of a `⇒`). A mutual sibling — the composite
`Condition.toFormulaAll ∘ conditions` fails the nested-inductive
structural-recursion checker. -/
noncomputable def DRS.bodyFormula [DecidableEq V] : DRS L V → L.Formula V
  | .mk _ conds => Condition.toFormulaAll conds
/-- Translate a single DRS-condition to a formula. -/
noncomputable def Condition.toFormula [DecidableEq V] : Condition L V → L.Formula V
  | .rel R args => Relations.formula R (fun i => Term.var (args i))
  | .eq a b => Term.equal (Term.var a) (Term.var b)
  | .neg K => (DRS.toFormula K).not
  | .imp a c => closeForall a.referents ((DRS.bodyFormula a).imp (DRS.toFormula c))
  | .dis l r => DRS.toFormula l ⊔ DRS.toFormula r
/-- The conjunction of a list of (translated) conditions. A `List` helper — the
higher-order `(cs.map Condition.toFormula).foldr (· ⊓ ·) ⊤` form fails the
nested-inductive structural-recursion checker. -/
noncomputable def Condition.toFormulaAll [DecidableEq V] : List (Condition L V) → L.Formula V
  | [] => ⊤
  | c :: cs => Condition.toFormula c ⊓ Condition.toFormulaAll cs
end

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
    (i : {x // x ∈ U} → M) : ∀ x, x ∉ U → extendOn U v i x = v x := by
  intro x hx; simp only [extendOn, dif_neg hx]

private theorem extendOn_restrict [DecidableEq V] (U : Finset V) (v v' : V → M)
    (h : ∀ x, x ∉ U → v' x = v x) : extendOn U v (fun s => v' s.val) = v' := by
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
      ∃ v', (∀ x, x ∉ U → v' x = v x) ∧ P v' := by
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
      ∀ v', (∀ x, x ∉ U → v' x = v x) → P v' := by
  constructor
  · intro hi v' hagree
    have := hi (fun s => v' s.val)
    rwa [extendOn_restrict U v v' hagree] at this
  · intro hv' i
    exact hv' (extendOn U v i) (extendOn_agrees U v i)

/-- `closeExists` realizes as existential quantification over embeddings that
extend `v` on `U`. -/
theorem realize_closeExists [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeExists U φ).Realize v ↔ ∃ v', (∀ x, x ∉ U → v' x = v x) ∧ φ.Realize v' := by
  rw [closeExists, Formula.realize_iExs]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  exact exists_extend_iff U v (Formula.Realize φ)

/-- `closeForall` realizes as universal quantification over embeddings that extend
`v` on `U`. -/
theorem realize_closeForall [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeForall U φ).Realize v ↔ ∀ v', (∀ x, x ∉ U → v' x = v x) → φ.Realize v' := by
  rw [closeForall, Formula.realize_iAlls]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  exact forall_extend_iff U v (Formula.Realize φ)

mutual
/-- **DRT ⊆ FOL** ([kamp-reyle-1993] §1.5; [muskens-1996]): the
translated formula's `Realize` coincides with the bespoke `DRS.Realize`. As
`toFormula` existentially closes the universe, the correspondence is with an
embedding `v'` extending `v` over `K.referents`. -/
theorem DRS.realize_toFormula [DecidableEq V] (K : DRS L V) (v : V → M) :
    (K.toFormula).Realize v ↔ ∃ v', (∀ x, x ∉ K.referents → v' x = v x) ∧ DRS.Realize v' K := by
  match K with
  | .mk U conds =>
    rw [DRS.toFormula, realize_closeExists]
    simp only [DRS.referents_mk, DRS.Realize]
    exact exists_congr fun v' =>
      and_congr_right fun _ => Condition.realize_toFormulaAll conds v'
/-- The open body of a DRS (its conditions, no universe closure) realizes as
`DRS.Realize` (used for the antecedent of `⇒`). -/
theorem DRS.realize_bodyFormula [DecidableEq V] (K : DRS L V) (v : V → M) :
    (DRS.bodyFormula K).Realize v ↔ DRS.Realize v K := by
  match K with
  | .mk _ conds => exact Condition.realize_toFormulaAll conds v
/-- A single condition's translation realizes as `Condition.Realize`. -/
theorem Condition.realize_toFormula [DecidableEq V] (c : Condition L V) (v : V → M) :
    (Condition.toFormula c).Realize v ↔ Condition.Realize v c := by
  match c with
  | .rel R args =>
    simp [Condition.toFormula, Condition.Realize, Relations.formula, Formula.Realize,
      BoundedFormula.realize_rel, Term.realize_var]
  | .eq a b => simp [Condition.toFormula, Condition.Realize, Formula.realize_equal]
  | .neg K =>
    simp only [Condition.toFormula, Condition.Realize, Formula.realize_not]
    rw [DRS.realize_toFormula K v]
  | .imp a c =>
    simp only [Condition.toFormula, Condition.Realize]
    rw [realize_closeForall]
    simp only [Formula.realize_imp]
    refine forall_congr' (fun v' => imp_congr_right (fun _ => ?_))
    rw [DRS.realize_bodyFormula a v', DRS.realize_toFormula c v']
  | .dis l r =>
    simp only [Condition.toFormula, Condition.Realize, Formula.realize_sup]
    rw [DRS.realize_toFormula l v, DRS.realize_toFormula r v]
/-- A list of conditions' conjoined translation realizes as `RealizeAll`. -/
theorem Condition.realize_toFormulaAll [DecidableEq V] (cs : List (Condition L V)) (v : V → M) :
    (Condition.toFormulaAll cs).Realize v ↔ Condition.RealizeAll v cs := by
  match cs with
  | [] => simp [Condition.toFormulaAll, Condition.RealizeAll, Formula.realize_top]
  | c :: cs =>
    rw [Condition.toFormulaAll, Condition.RealizeAll, Formula.realize_inf,
      Condition.realize_toFormula c v, Condition.realize_toFormulaAll cs v]
end

end DRT
