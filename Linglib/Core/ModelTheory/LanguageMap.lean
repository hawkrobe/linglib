module

public import Mathlib.ModelTheory.Basic

/-!
# The monadic language on a type of predicate symbols

This file defines the monadic first-order language on a type `Sym` of predicate symbols, the
relational counterpart of `Language.constantsOn`, and its structures. Like `constantsOn`, it is a
language constructor rather than a fixed signature, and it sits beside `constantsOn` in
`Mathlib/ModelTheory/LanguageMap.lean`.

## Main definitions

- `FirstOrder.Language.monadic Sym` is the relational language whose relation symbols are the
  elements of `Sym`, all of arity one.
- `FirstOrder.Language.monadic.structure holds` is the `monadic Sym`-structure on `E`
  interpreting each symbol `s` as the predicate `holds s`.

## Implementation notes

The monadic signature with individual constants is `(monadic Pred)[[Const]]`, mathlib's
`Language.withConstants`. Its structures are `withConstantsStructure` over `monadic.structure`
and `constantsOn.structure`, the constant symbol of `c` is `(monadic Pred).con c`, and the
relation symbol of `P` is `Sum.inl P`.
-/

@[expose] public section

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

end FirstOrder.Language
