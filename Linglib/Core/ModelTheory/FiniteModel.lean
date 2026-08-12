import Mathlib.ModelTheory.Semantics

/-!
# Finite model checking for first-order structures

Two pieces of substrate for studies that verify claims on small hand-built
models:

* `Language.monadic Sym` — the purely unary-relational language whose arity-1
  symbols are `Sym` (mathlib precedent: `Language.graph`, one binary symbol),
  with `monadicStructure` building its structures from a `Sym → E → Prop`
  table.
* `Language.monadicWithConstants Const Pred` — the monadic signature with
  individual constants adjoined (`(monadic Pred)[[Const]]`), with
  `monadicWithConstantsStructure` building its structures from a constant
  interpretation and a predicate valuation.
* `BoundedFormula.decRealize` — decidable realization over a finite structure
  with decidable atoms, by structural recursion on the formula. Mathlib has no
  such instance; with it, `decide` kernel-checks `Formula.Realize` facts on
  concrete finite models.
-/

namespace FirstOrder.Language

/-- The monadic language: arity-1 relation symbols `Sym`, nothing else. -/
def monadic (Sym : Type*) : Language where
  Functions := fun _ => Empty
  Relations := fun n => match n with
    | 1 => Sym
    | _ => PEmpty

/-- Build a `monadic`-structure from a truth table for the symbols. -/
@[implicit_reducible] def monadicStructure {Sym E : Type*} (holds : Sym → E → Prop) :
    (monadic Sym).Structure E where
  funMap := fun f => f.elim
  RelMap := fun {n} r v =>
    match n, r with
    | 1, s => holds s (v 0)
    | 0, r => r.elim
    | (_ + 2), r => r.elim

/-- Atom decidability for a `monadicStructure` with a decidable table. As a
named `def` so concrete interpretation families can supply it by unification
(`exact monadicStructure.decRelMap _`) where synthesis would be stuck on a
metavariable table. -/
def monadicStructure.decRelMap {Sym E : Type*} (holds : Sym → E → Prop)
    [∀ s e, Decidable (holds s e)] :
    ∀ (n : ℕ) (r : (monadic Sym).Relations n) (v : Fin n → E),
      Decidable (@Structure.RelMap _ _ (monadicStructure holds) n r v) :=
  fun n r v =>
    match n, r with
    | 1, s => inferInstanceAs (Decidable (holds s (v 0)))
    | 0, r => r.elim
    | (_ + 2), r => r.elim

instance {Sym E : Type*} (holds : Sym → E → Prop)
    [∀ s e, Decidable (holds s e)] (n : ℕ)
    (r : (monadic Sym).Relations n) (v : Fin n → E) :
    Decidable (@Structure.RelMap _ _ (monadicStructure holds) n r v) :=
  monadicStructure.decRelMap holds n r v

/-- The monadic signature with constants:
    `(Language.monadic Pred)[[Const]]`. -/
abbrev monadicWithConstants (Const : Type*) (Pred : Type*) : Language :=
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

/-- Decidable realization on a finite structure with decidable atoms:
structural recursion on the formula. `decide` kernel-reduces through it. -/
instance BoundedFormula.decRealize {L : Language} {M : Type*} [L.Structure M]
    [Fintype M] [DecidableEq M]
    [∀ (n : ℕ) (r : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap r x)]
    {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M),
      Decidable (φ.Realize v xs)
  | _, .falsum, _, _ => .isFalse id
  | _, .equal _ _, _, _ => inferInstanceAs (Decidable (_ = _))
  | _, .rel R _, _, _ => inferInstanceAs (Decidable (Structure.RelMap R _))
  | _, .imp φ ψ, v, xs =>
      haveI := BoundedFormula.decRealize φ v xs
      haveI := BoundedFormula.decRealize ψ v xs
      inferInstanceAs (Decidable (_ → _))
  | _, .all φ, v, xs =>
      haveI : ∀ a, Decidable (φ.Realize v (Fin.snoc xs a)) :=
        fun a => BoundedFormula.decRealize φ v (Fin.snoc xs a)
      inferInstanceAs (Decidable (∀ a, φ.Realize v (Fin.snoc xs a)))

instance Formula.decRealize {L : Language} {M : Type*} [L.Structure M]
    [Fintype M] [DecidableEq M]
    [∀ (n : ℕ) (r : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap r x)]
    {α : Type*} (φ : L.Formula α) (v : α → M) :
    Decidable (φ.Realize v) :=
  BoundedFormula.decRealize φ v default

end FirstOrder.Language
