import Mathlib.ModelTheory.Semantics

/-!
# Monadic languages and decidable satisfaction on finite structures

This file defines the monadic first-order language on a type of predicate symbols and decidable
satisfaction on a finite structure.

## Main definitions

- `FirstOrder.Language.monadic Sym` is the relational language whose relation symbols are the
  elements of `Sym`, all of arity one: the relational counterpart of `Language.constantsOn`.
- `FirstOrder.Language.monadic.structure holds` is the `monadic Sym`-structure on `E`
  interpreting each symbol `s` as the predicate `holds s`.
- `FirstOrder.Language.BoundedFormula.decidableRealize` decides `BoundedFormula.Realize` on a
  finite structure with decidable equality and decidable relations by recursion on the formula,
  so that `decide` checks satisfaction on concrete finite models.

## Implementation notes

The monadic signature with individual constants is `(monadic Pred)[[Const]]`, mathlib's
`Language.withConstants`. Its structures are `withConstantsStructure` over `monadic.structure`
and `constantsOn.structure`, the constant symbol of `c` is `(monadic Pred).con c`, and the
relation symbol of `P` is `Sum.inl P`.
-/

universe u

namespace FirstOrder.Language

open Structure

section Monadic

variable (Sym : Type u)

/-- The relation symbols of the monadic language on `Sym` are the elements of `Sym` at arity one,
with no symbols at any other arity. -/
def monadicRel : ℕ → Type u
  | 1 => Sym
  | _ => PEmpty

/-- The monadic language on `Sym` has one unary relation symbol for each element of `Sym` and no
other symbols. -/
@[simps]
def monadic : Language.{0, u} := ⟨fun _ => Empty, monadicRel Sym⟩
  deriving IsRelational

variable {Sym}

theorem monadic_relations_one : (monadic Sym).Relations 1 = Sym :=
  rfl

instance isEmpty_relations_monadic_zero : IsEmpty ((monadic Sym).Relations 0) :=
  inferInstanceAs (IsEmpty PEmpty)

instance isEmpty_relations_monadic_succ_succ {n : ℕ} :
    IsEmpty ((monadic Sym).Relations (n + 2)) :=
  inferInstanceAs (IsEmpty PEmpty)

variable {E : Type*}

/-- The `monadic Sym`-structure on `E` interpreting each symbol `s` as the predicate `holds s`. -/
@[instance_reducible]
def monadic.structure (holds : Sym → E → Prop) : (monadic Sym).Structure E where
  RelMap {n} r v :=
    match n, r with
    | 1, s => holds s (v 0)

variable (holds : Sym → E → Prop)

@[simp]
theorem monadic.structure_relMap (s : Sym) (v : Fin 1 → E) :
    @RelMap _ _ (monadic.structure holds) 1 s v ↔ holds s (v 0) :=
  Iff.rfl

instance monadic.structure.decidableRelMap [∀ s e, Decidable (holds s e)] :
    ∀ {n : ℕ} (r : (monadic Sym).Relations n) (v : Fin n → E),
      Decidable (@RelMap _ _ (monadic.structure holds) n r v)
  | 1, s, v => inferInstanceAs (Decidable (holds s (v 0)))

end Monadic

section DecidableRealize

variable {L : Language} {M : Type*} [L.Structure M] [Fintype M] [DecidableEq M]
  [∀ (n : ℕ) (r : L.Relations n) (x : Fin n → M), Decidable (RelMap r x)] {α : Type*}

/-- Satisfaction on a finite structure with decidable equality and decidable relations is
decidable, by recursion on the formula; `decide` reduces through it on concrete models. -/
instance BoundedFormula.decidableRealize :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M),
      Decidable (φ.Realize v xs)
  | _, .falsum, _, _ => .isFalse id
  | _, .equal _ _, _, _ => inferInstanceAs (Decidable (_ = _))
  | _, .rel R _, _, _ => inferInstanceAs (Decidable (RelMap R _))
  | _, .imp φ ψ, v, xs =>
    haveI := decidableRealize φ v xs
    haveI := decidableRealize ψ v xs
    inferInstanceAs (Decidable (_ → _))
  | _, .all φ, v, xs =>
    haveI : ∀ a, Decidable (φ.Realize v (Fin.snoc xs a)) := fun a =>
      decidableRealize φ v (Fin.snoc xs a)
    inferInstanceAs (Decidable (∀ a, φ.Realize v (Fin.snoc xs a)))

instance Formula.decidableRealize (φ : L.Formula α) (v : α → M) : Decidable (φ.Realize v) :=
  BoundedFormula.decidableRealize φ v default

end DecidableRealize

end FirstOrder.Language
