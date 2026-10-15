module

public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Data.Finset.Option
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Pi

/-!
# Dimensioned parthood

Mereological syntax replaces set-theoretic Merge by Subjoin, which makes one syntactic object a
proper part of another. Parthood comes in two dimensions: the first subjunction to an object
makes a 1-part, interpreted as the extended-projection complement, the second a 2-part, the
specifier, and there is no third (Dimensionality). Parthood is transitive within a dimension
but not across dimensions, which is what makes 2-parts locality domains.

This file defines the parthood structure `Parthood α` on a type of objects, its immediate and
transitive parthood relations, and the Subjoin operation, decides the parthood relations of a
finite structure, and shows how parthood chains leave a domain closed under parenthood.

## Main definitions

* `MereologicalSyntax.Parthood` — the 1-part and 2-part functions, indexed by the dimensions
  `Parthood.Dim`.
* `Parthood.Imm n x y` — `x` is the immediate `n`-part of `y`; `Parthood.NPart n` is its
  transitive closure, the `n`-part relation; `Parthood.Descendant` — parthood through both
  dimensions.
* `Parthood.subjoin` — Subjoin, filling the next free dimension of the target.

## Main statements

* `Parthood.exit_of_nPart` — an `n`-part chain leaving a domain closed under parenthood except
  at `b` leaves in `b`'s own dimension of attachment, and reaches `b` first.

## Implementation notes

* An object has at most one `n`-part, so its `n`-parts form a chain, and `NPart n` is decided by
  following it (`Relation.ReflTransGen.decidable_TransGen_of_option`). `Descendant` branches,
  and is decided by closing a set.
* Irreflexivity is not part of `Parthood`, and `subjoin` does not check it: theorems that need it
  take `∀ x, ¬ P.Descendant x x`, which `decide` checks on a finite structure.

## References

* [adger-2025]
-/

@[expose] public section

namespace MereologicalSyntax

/-- A dimensioned parthood structure on `α` gives each object at most one 1-part and at most one
2-part (Dimensionality). -/
@[ext]
structure Parthood (α : Type*) where
  /-- The 1-part of an object, if any. -/
  onePart : α → Option α
  /-- The 2-part of an object, if any. -/
  twoPart : α → Option α

namespace Parthood

open Relation

/-- The two dimensions of parthood, the extended-projection complement (1-part) and the specifier
(2-part). -/
inductive Dim
  | one
  | two
  deriving DecidableEq, Repr, Fintype

variable {α : Type*} (P : Parthood α)

instance [Fintype α] [DecidableEq α] : DecidableEq (Parthood α) := fun _ _ ↦
  decidable_of_iff _ Parthood.ext_iff.symm

/-- The `n`-part of an object, if any. -/
def part : Dim → α → Option α
  | .one => P.onePart
  | .two => P.twoPart

/-! ### Parthood relations -/

/-- `x` is the immediate `n`-part of `y`. -/
def Imm (n : Dim) (x y : α) : Prop := P.part n y = some x

/-- `x` is an `n`-part of `y`, through a chain of immediate `n`-parts. -/
def NPart (n : Dim) : α → α → Prop := TransGen (P.Imm n)

/-- `x` is reachable from `y` through parts of either dimension. -/
def Descendant : α → α → Prop := TransGen fun x y ↦ ∃ n, P.Imm n x y

instance [DecidableEq α] (n : Dim) : DecidableRel (P.Imm n) := fun _ _ ↦
  inferInstanceAs (Decidable (_ = _))

section Fintype

variable [Fintype α] [DecidableEq α]

instance (n : Dim) : DecidableRel (P.NPart n) := fun x y ↦
  haveI := ReflTransGen.decidable_TransGen_of_option (P.part n) y x
  decidable_of_iff _ transGen_swap

instance : DecidableRel P.Descendant := fun x y ↦
  haveI := ReflTransGen.decidable_TransGen_of_fintype_step
    (r := Function.swap fun x y ↦ ∃ n, P.Imm n x y)
    (fun y ↦ Finset.univ.biUnion fun n ↦ (P.part n y).toFinset)
    (fun _ _ ↦ by simp [Function.swap, Imm]) y x
  decidable_of_iff _ transGen_swap

end Fintype

variable {P}

theorem descendant_of_nPart {n : Dim} {x y : α} (h : P.NPart n x y) : P.Descendant x y :=
  TransGen.mono (fun _ _ h ↦ ⟨n, h⟩) _ _ h

theorem Descendant.trans {x y z : α} (h₁ : P.Descendant x y) (h₂ : P.Descendant y z) :
    P.Descendant x z :=
  TransGen.trans h₁ h₂

/-! ### Chains out of domains -/

/-- If a domain `S` is closed under parenthood except at `b`, and `b` is attached only in
dimension `d`, then an `n`-part chain from inside `S` to outside it runs in dimension `d` and
reaches `b` first. -/
theorem exit_of_nPart {S : Set α} {b : α} {d : Dim}
    (hS : ∀ x ∈ S, x ≠ b → ∀ n y, P.Imm n x y → y ∈ S) (hb : ∀ n y, P.Imm n b y → n = d)
    {n : Dim} {x y : α} (h : P.NPart n x y) (hx : x ∈ S) (hy : y ∉ S) :
    n = d ∧ (x = b ∨ P.NPart d x b) := by
  revert hx
  induction h using TransGen.head_induction_on with
  | @single a h =>
    intro hx
    by_cases hab : a = b
    · exact ⟨hb _ _ (hab ▸ h), .inl hab⟩
    · exact absurd (hS _ hx hab _ _ h) hy
  | @head a c h' _ ih =>
    intro hx
    by_cases hab : a = b
    · exact ⟨hb _ _ (hab ▸ h'), .inl hab⟩
    · obtain ⟨rfl, hcb⟩ := ih (hS _ hx hab _ _ h')
      exact ⟨rfl, .inr (hcb.elim (fun e ↦ e ▸ .single h') (.head h'))⟩

/-! ### Subjoin -/

variable (P) in
/-- Subjoin `x` to `y`, as its 1-part if it has none, as its 2-part if it has a 1-part only, and
not at all if it has both (Dimensionality). -/
def subjoin [DecidableEq α] (x y : α) : Option (Parthood α) :=
  match P.onePart y, P.twoPart y with
  | none, _ => some { P with onePart := Function.update P.onePart y (some x) }
  | some _, none => some { P with twoPart := Function.update P.twoPart y (some x) }
  | some _, some _ => none

theorem subjoin_eq_none_of_full [DecidableEq α] {x y : α} (h₁ : (P.onePart y).isSome)
    (h₂ : (P.twoPart y).isSome) : P.subjoin x y = none := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h₁
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h₂
  simp [subjoin, ha, hb]

end Parthood

end MereologicalSyntax
