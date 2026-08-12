import Linglib.Core.ModelTheory.FiniteModel
import Linglib.Logic.Modal.FirstOrder.Kripke

/-!
# The monadic signature with individual constants

`Language.monadicWithConstants Const Pred` is the relations-only monadic
language `Language.monadic Pred` (`Core/ModelTheory/FiniteModel.lean`) with
constants adjoined by mathlib's `withConstants` — one individual constant
per `Const`, one unary relation symbol per `Pred`: the object-language
signature of monadic quantified modal logic ([aloni-vanormondt-2023]
Definition 4.1, terms `t := c | x`). Structures compose from
`monadicStructure` on the relations side and `constantsOn.structure` on
the constants side.

## Main definitions

* `Language.monadicWithConstants` — the signature, as
  `(Language.monadic Pred)[[Const]]`.
* `monadicWithConstantsStructure` — its structure from a constant
  interpretation and a predicate valuation (cf. mathlib's
  `orderStructure`).
* `KripkeModel.pInterp`, `KripkeModel.cInterp` — world-relative
  predicate and constant denotations of a Kripke model over the
  signature.
-/

universe u v

namespace FirstOrder.Language

/-- The monadic signature with constants:
    `(Language.monadic Pred)[[Const]]`. -/
abbrev monadicWithConstants (Const : Type u) (Pred : Type v) : Language :=
  (monadic Pred)[[Const]]

variable {Const Pred Domain : Type*}

/-- A constant as a symbol of the signature (mathlib's `Language.con`). -/
abbrev monadicConst (c : Const) :
    (monadicWithConstants Const Pred).Constants := Sum.inr c

/-- A predicate as a relation symbol of the signature. -/
abbrev monadicRel (P : Pred) :
    (monadicWithConstants Const Pred).Relations 1 := Sum.inl P

/-- The `monadicWithConstants` structure a constant interpretation and a
    predicate valuation induce: `monadicStructure` on the relations side,
    `constantsOn.structure` on the constants side. -/
@[reducible] def monadicWithConstantsStructure (κ : Const → Domain)
    (V : Pred → Domain → Prop) :
    (monadicWithConstants Const Pred).Structure Domain :=
  letI := monadicStructure V
  letI := constantsOn.structure κ
  inferInstance

@[simp] theorem monadicWithConstantsStructure_relMap (κ : Const → Domain)
    (V : Pred → Domain → Prop) (P : Pred) (v : Fin 1 → Domain) :
    (monadicWithConstantsStructure κ V).RelMap (monadicRel P) v ↔ V P (v 0) :=
  Iff.rfl

@[simp] theorem monadicWithConstantsStructure_funMap (κ : Const → Domain)
    (V : Pred → Domain → Prop) (c : Const) (v : Fin 0 → Domain) :
    (monadicWithConstantsStructure κ V).funMap
      (monadicConst (Pred := Pred) c) v = κ c :=
  rfl

variable {W : Type*}

/-- The predicate denotation at a world, read off a Kripke model's
    world-indexed family via `Structure.RelMap` — the world-relativized
    `I(w)(Pⁿ)` of [aloni-vanormondt-2023] Definition 4.2, specialised to
    monadic `P`. -/
def KripkeModel.pInterp
    (K : KripkeModel (monadicWithConstants Const Pred) W Domain)
    (P : Pred) (w : W) (d : Domain) : Prop :=
  (K.interp w).RelMap (monadicRel P) (fun _ => d)

/-- The constant denotation at a world — the world-relative `I(w)(c)` of
    [aloni-vanormondt-2023] Definitions 4.2 and 4.8, read off
    `Structure.funMap`. -/
def KripkeModel.cInterp
    (K : KripkeModel (monadicWithConstants Const Pred) W Domain)
    (c : Const) (w : W) : Domain :=
  (K.interp w).funMap (monadicConst c) default

end FirstOrder.Language
