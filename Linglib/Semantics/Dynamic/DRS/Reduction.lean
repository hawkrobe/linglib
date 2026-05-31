import Linglib.Semantics.Dynamic.DRS.Semantics
import Mathlib.ModelTheory.Syntax

/-!
# From DRT to predicate logic: the DRS → first-order reduction
@cite{kamp-reyle-1993} (§1.5), @cite{muskens-1996}

The "surprise" theorem of the whole development: the bespoke DRS box language is
*equivalent to ordinary first-order logic*. We translate each DRS into a mathlib
`FirstOrder.Language.Formula` and prove its `Realize` coincides with the bespoke
`DRS.Realize` — Kamp & Reyle's §1.5 ("From DRT to Predicate Logic") and Muskens's
"DRSs are already present in classical logic", now a Lean theorem rather than an
assertion.

The universe of a (sub-)DRS is *existentially closed* (`closeExists`, via
mathlib's `Formula.iExs`); the antecedent of a `⇒` is *universally closed*
(`closeForall`, via `Formula.iAlls`).

## Main declarations

* `DRS.toFormula` / `Condition.toFormula` — the translation into `L.Formula V`.
* `DRS.realize_toFormula` — the agreement theorem (currently `sorry`; see TODO).
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w}

/-- Existentially close the referents in `U` within a formula over free
referents `V` (relabel `U`-referents to the bound side, then `Formula.iExs`). -/
noncomputable def closeExists [DecidableEq V] (U : Finset V) (φ : L.Formula V) : L.Formula V :=
  (φ.relabel (fun x => if h : x ∈ U then Sum.inr ⟨x, h⟩ else Sum.inl x)).iExs {x // x ∈ U}

/-- Universally close the referents in `U` (used for the antecedent of `⇒`). -/
noncomputable def closeForall [DecidableEq V] (U : Finset V) (φ : L.Formula V) : L.Formula V :=
  (φ.relabel (fun x => if h : x ∈ U then Sum.inr ⟨x, h⟩ else Sum.inl x)).iAlls {x // x ∈ U}

mutual
/-- Translate a DRS to a first-order formula: existentially close the universe
over the conjunction of the (translated) conditions (@cite{kamp-reyle-1993} §1.5). -/
noncomputable def DRS.toFormula [DecidableEq V] : DRS L V → L.Formula V
  | .mk U conds => closeExists U (Condition.toFormulaAll conds)
/-- The conjunction of a DRS's conditions, *without* closing its universe (used
as the antecedent body of a `⇒`). -/
noncomputable def DRS.bodyFormula [DecidableEq V] : DRS L V → L.Formula V
  | .mk _ conds => Condition.toFormulaAll conds
/-- Translate a single DRS-condition to a formula. -/
noncomputable def Condition.toFormula [DecidableEq V] : Condition L V → L.Formula V
  | .rel R args => Relations.formula R (fun i => Term.var (args i))
  | .eq a b => Term.equal (Term.var a) (Term.var b)
  | .neg K => (DRS.toFormula K).not
  | .imp a c => closeForall a.referents ((DRS.bodyFormula a).imp (DRS.toFormula c))
  | .dis l r => DRS.toFormula l ⊔ DRS.toFormula r
/-- The conjunction of a list of (translated) conditions. -/
noncomputable def Condition.toFormulaAll [DecidableEq V] : List (Condition L V) → L.Formula V
  | [] => ⊤
  | c :: cs => Condition.toFormula c ⊓ Condition.toFormulaAll cs
end

variable {M : Type x} [L.Structure M]

/-- **DRT ⊆ FOL** (@cite{kamp-reyle-1993} §1.5; @cite{muskens-1996}): the
translated formula's `Realize` coincides with the bespoke `DRS.Realize`. Because
`toFormula` existentially closes the universe, the correspondence is with an
embedding `v'` extending `v` over `K.referents`.

TODO: mutual induction on `DRS`/`Condition`. Key lemmas:
`Formula.realize_iExs`/`realize_iAlls` turn `closeExists`/`closeForall` into the
`∃`/`∀` over an assignment to the universe-subtype `{x // x ∈ U}`;
`Formula.realize_relabel` turns the split relabel into the agreement condition
`∀ x ∉ U, v' x = v x` (the `∃ i : {x // x ∈ U} → M` of `realize_iExs` corresponds
to `v' := fun x => if h : x ∈ U then i ⟨x, h⟩ else v x`); then `realize_rel`,
`realize_inf`, `realize_sup`, `realize_not`, `realize_imp` discharge the
condition cases against the matching clauses of `DRS.Realize`. -/
theorem DRS.realize_toFormula [DecidableEq V] (K : DRS L V) (v : V → M) :
    (K.toFormula).Realize v ↔ ∃ v', (∀ x, x ∉ K.referents → v' x = v x) ∧ K.Realize v' := by
  sorry

end DRT
