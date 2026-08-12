import Linglib.Core.ModelTheory.FiniteModel
import Linglib.Logic.Modal.FirstOrder.Kripke

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

end FirstOrder.Language
