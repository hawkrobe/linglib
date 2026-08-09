import Linglib.Logic.Modal.FirstOrder.Kripke

/-!
# The monadic signature with individual constants

The first-order signature with one individual constant per `Const` and one
unary relation symbol per `Pred` — the object-language signature of monadic
quantified modal logic ([aloni-vanormondt-2023] Definition 4.1: terms
`t := c | x`, monadic relations) — together with its canonical structures
and the world-relative denotation readers for Kripke structures over it.

Up to definitional shape this signature is `(Language.monadic Pred)[[Const]]`
(the relations-only `Language.monadic` of `Core/ModelTheory/FiniteModel.lean`
with constants adjoined via mathlib's `withConstants`); it is kept as a
direct definition so that interpretation `match` patterns stay structural.

## Main declarations

* `Language.monadicWithConstants` — the signature.
* `monadicWithConstantsStructure` — its structure from a constant
  interpretation and a predicate valuation (cf. mathlib's `orderStructure`).
* `KripkeStructure.pInterp`, `KripkeStructure.cInterp` — world-relative
  predicate and constant denotations of a Kripke structure over the
  signature.
-/

universe u v

namespace FirstOrder.Language

/-- The monadic signature with constants: one individual constant per
    `Const`, one unary relation symbol per `Pred`. -/
def monadicWithConstants.{u', v'} (Const : Type u') (Pred : Type v') :
    Language where
  Functions := fun n => match n with
    | 0 => Const
    | _ => PEmpty
  Relations := fun n => match n with
    | 1 => Pred
    | _ => PEmpty

variable {Const Pred Domain : Type*}

/-- A constant as a symbol of the signature (defeq; the parametric analogue
    of mathlib's per-symbol abbreviations). -/
abbrev monadicConst (c : Const) :
    (monadicWithConstants Const Pred).Constants := c

/-- A predicate as a relation symbol of the signature (defeq). -/
abbrev monadicRel (P : Pred) :
    (monadicWithConstants Const Pred).Relations 1 := P

/-- The `monadicWithConstants` structure a constant interpretation and a
    predicate valuation induce. -/
@[reducible] def monadicWithConstantsStructure (κ : Const → Domain)
    (V : Pred → Domain → Prop) :
    (monadicWithConstants Const Pred).Structure Domain where
  funMap := fun {n} f => match n, f with
    | 0, c => fun _ => κ c
    | _ + 1, f => f.elim
  RelMap := fun {n} r => match n, r with
    | 1, P => fun v => V P (v 0)
    | 0, r => r.elim
    | _ + 2, r => r.elim

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

/-- The predicate denotation at a world, read off a Kripke structure's
    world-indexed family via `Structure.RelMap` — the world-relativized
    `I(w)(Pⁿ)` of [aloni-vanormondt-2023] Definition 4.2, specialised to
    monadic `P`. -/
def KripkeStructure.pInterp
    (K : KripkeStructure (monadicWithConstants Const Pred) W Domain)
    (P : Pred) (w : W) (d : Domain) : Prop :=
  (K.interp w).RelMap (monadicRel P) (fun _ => d)

/-- The constant denotation at a world — the world-relative `I(w)(c)` of
    [aloni-vanormondt-2023] Definitions 4.2 and 4.8, read off
    `Structure.funMap`. -/
def KripkeStructure.cInterp
    (K : KripkeStructure (monadicWithConstants Const Pred) W Domain)
    (c : Const) (w : W) : Domain :=
  (K.interp w).funMap (monadicConst c) default

end FirstOrder.Language
