import Linglib.Core.ModelTheory.FiniteModel
import Linglib.Logic.Modal.FirstOrder.Semantics

/-!
# World-relative denotations over the monadic signature

The predicate and constant denotations a first-order Kripke model over
`Language.monadicWithConstants Const Pred` assigns at each world — the
world-relativized `I(w)(P)` and `I(w)(c)` of monadic quantified modal
logic, read off the world's structure.

## References

* [aloni-vanormondt-2023] — Definitions 4.2 and 4.8
-/

namespace FirstOrder.Language

variable {Const Pred Domain W : Type*}

/-- The predicate denotation at a world, read off a Kripke model's
    world-indexed family via `Structure.RelMap`. -/
def KripkeModel.predInterp
    (K : KripkeModel (monadicWithConstants Const Pred) W Domain)
    (P : Pred) (w : W) (d : Domain) : Prop :=
  (K.interp w).RelMap (monadicRel P) (fun _ => d)

/-- The constant denotation at a world, read off `Structure.funMap`. -/
def KripkeModel.constInterp
    (K : KripkeModel (monadicWithConstants Const Pred) W Domain)
    (c : Const) (w : W) : Domain :=
  (K.interp w).funMap (monadicConst c) default

/-- Realization of a monadic atom: the predicate denotation at the world,
    of the term's value. -/
@[simp] theorem ModalFormula.realize_monadicRel {α : Type*} [DecidableEq α]
    (K : KripkeModel (monadicWithConstants Const Pred) W Domain)
    (w : W) (v : α → Domain) (P : Pred)
    (t : (monadicWithConstants Const Pred).Term α) :
    ((monadicRel P).modalFormula₁ t).Realize K w v ↔
      K.predInterp P w (letI := K.interp w; t.realize v) := by
  rw [Relations.modalFormula₁, ModalFormula.realize_rel]
  exact iff_of_eq (congrArg _ (funext fun i => by rw [Subsingleton.elim i 0, Matrix.cons_val_zero]))

/-- A constant term's value at a world is its `constInterp` denotation. -/
theorem realize_monadicConst {α : Type*}
    (K : KripkeModel (monadicWithConstants Const Pred) W Domain)
    (w : W) (v : α → Domain) (c : Const) :
    (letI := K.interp w;
      (Constants.term (monadicConst (Pred := Pred) c)).realize v) =
      K.constInterp c w :=
  congrArg _ (funext fun i => i.elim0)

end FirstOrder.Language
