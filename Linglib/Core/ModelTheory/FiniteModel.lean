import Mathlib.ModelTheory.Semantics

/-!
# Finite model checking for first-order structures

Two pieces of substrate for studies that verify claims on small hand-built
models:

* `Language.monadic Sym` — the purely unary-relational language whose arity-1
  symbols are `Sym` (mathlib precedent: `Language.graph`, one binary symbol),
  with `monadicStructure` building its structures from a `Sym → E → Prop`
  table.
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
