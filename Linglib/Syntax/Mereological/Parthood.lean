import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Pi

/-!
# Dimensioned parthood

Mereological syntax replaces set-theoretic Merge by Subjoin, which makes one syntactic object a
proper part of another. Parthood comes in two dimensions: the first subjunction to an object
makes a 1-part, interpreted as the extended-projection complement, the second a 2-part, the
specifier, and there is no third (Dimensionality). Parthood is transitive within a dimension
but not across dimensions, which is what makes 2-parts locality domains.

This file defines the parthood structure `Parthood α` on a type of objects, its immediate and
transitive parthood relations, the Subjoin operation, rank functions as certificates of
acyclicity, and how parthood chains leave a domain closed under parenthood.

## Main definitions

* `MereologicalSyntax.Parthood` — the 1-part and 2-part functions.
* `Parthood.Imm n x y` — `x` is the immediate `n`-part of `y`; `Parthood.NPart n` is its
  transitive closure, the `n`-part relation; `Parthood.WithinDim` — an `n`-part for some `n`;
  `Parthood.Descendant` — parthood through both dimensions.
* `Parthood.subjoin` — Subjoin, filling the next free dimension of the target.

## Main statements

* `Parthood.lt_of_descendant` — a rank increasing along immediate parthood increases along
  `Descendant`; hence `Parthood.not_descendant_of_le` and `Parthood.acyclic_of_rank`.
* `Parthood.nPart_iff_of_unique` — an `n`-part chain from an object with a unique parent passes
  through that parent.
* `Parthood.exit_of_nPart` — an `n`-part chain leaving a domain closed under parenthood except
  at `b` leaves in `b`'s own dimension of attachment, and reaches `b` first.

## References

* [adger-2025]
-/

namespace MereologicalSyntax

/-- The two dimensions of parthood: 1-parts are extended-projection complements, 2-parts are
specifiers. -/
inductive Dim
  | one
  | two
  deriving DecidableEq, Repr, Fintype

/-- A dimensioned parthood structure on `α`: each object has at most one 1-part and at most one
2-part (Dimensionality). -/
@[ext]
structure Parthood (α : Type*) where
  /-- The 1-part of an object, if any. -/
  onePart : α → Option α
  /-- The 2-part of an object, if any. -/
  twoPart : α → Option α

namespace Parthood

variable {α : Type*} (P : Parthood α)

instance [Fintype α] [DecidableEq α] : DecidableEq (Parthood α) := fun P Q =>
  decidable_of_iff (P.onePart = Q.onePart ∧ P.twoPart = Q.twoPart)
    ⟨fun h => Parthood.ext h.1 h.2, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- The `n`-part of an object, if any. -/
def part : Dim → α → Option α
  | .one => P.onePart
  | .two => P.twoPart

/-! ### Parthood relations -/

/-- `x` is the immediate `n`-part of `y`. -/
def Imm (n : Dim) (x y : α) : Prop := P.part n y = some x

instance [DecidableEq α] (n : Dim) (x y : α) : Decidable (P.Imm n x y) :=
  inferInstanceAs (Decidable (_ = _))

/-- `x` is an `n`-part of `y`: parthood is transitive within a dimension. -/
def NPart (n : Dim) : α → α → Prop := Relation.TransGen (P.Imm n)

/-- `x` is a part of `y` within a single dimension. -/
def WithinDim (x y : α) : Prop := P.NPart .one x y ∨ P.NPart .two x y

/-- `x` is reachable from `y` through parts of either dimension. -/
def Descendant : α → α → Prop := Relation.TransGen fun x y => P.Imm .one x y ∨ P.Imm .two x y

variable {P}

theorem NPart.imm {n : Dim} {x y : α} (h : P.Imm n x y) : P.NPart n x y := .single h

theorem NPart.trans {n : Dim} {x y z : α} (h₁ : P.NPart n x y) (h₂ : P.NPart n y z) :
    P.NPart n x z :=
  Relation.TransGen.trans h₁ h₂

theorem descendant_of_imm {n : Dim} {x y : α} (h : P.Imm n x y) : P.Descendant x y :=
  match n, h with
  | .one, h => .single (.inl h)
  | .two, h => .single (.inr h)

theorem descendant_of_nPart {n : Dim} {x y : α} (h : P.NPart n x y) : P.Descendant x y :=
  Relation.TransGen.mono (fun _ _ h => match n, h with
    | .one, h => .inl h
    | .two, h => .inr h) _ _ h

theorem descendant_of_withinDim {x y : α} (h : P.WithinDim x y) : P.Descendant x y :=
  h.elim descendant_of_nPart descendant_of_nPart

theorem Descendant.trans {x y z : α} (h₁ : P.Descendant x y) (h₂ : P.Descendant y z) :
    P.Descendant x z :=
  Relation.TransGen.trans h₁ h₂

/-! ### Rank certificates -/

theorem lt_of_descendant (rank : α → ℕ) (hrank : ∀ n x y, P.Imm n x y → rank x < rank y)
    {x y : α} (h : P.Descendant x y) : rank x < rank y := by
  induction h with
  | single h => exact h.elim (hrank _ _ _) (hrank _ _ _)
  | tail _ h ih => exact ih.trans (h.elim (hrank _ _ _) (hrank _ _ _))

theorem not_descendant_of_le (rank : α → ℕ) (hrank : ∀ n x y, P.Imm n x y → rank x < rank y)
    {x y : α} (h : rank y ≤ rank x) : ¬ P.Descendant x y :=
  fun hd => absurd (lt_of_descendant rank hrank hd) (not_lt.2 h)

/-- An increasing rank certifies that no object is a part of itself. -/
theorem acyclic_of_rank (rank : α → ℕ) (hrank : ∀ n x y, P.Imm n x y → rank x < rank y)
    (x : α) : ¬ P.Descendant x x :=
  not_descendant_of_le rank hrank le_rfl

/-! ### Chains through unique parents and out of domains -/

/-- An `n`-part chain from an object whose only parent is `u`, in dimension `n`, stops at `u` or
continues from it. -/
theorem nPart_iff_of_unique {n : Dim} {x u : α} (hu : P.Imm n x u)
    (hx : ∀ m y, P.Imm m x y → m = n ∧ y = u) {z : α} :
    P.NPart n x z ↔ z = u ∨ P.NPart n u z := by
  constructor
  · intro h
    obtain ⟨b, hb, hbz⟩ := Relation.TransGen.head'_iff.1 h
    obtain rfl := (hx n b hb).2
    exact Relation.reflTransGen_iff_eq_or_transGen.1 hbz
  · rintro (rfl | h)
    exacts [.single hu, .head hu h]

/-- An object whose only parent is in dimension `n` is not an `m`-part of anything, `m ≠ n`. -/
theorem not_nPart_of_unique {n : Dim} {x u : α} (hx : ∀ m y, P.Imm m x y → m = n ∧ y = u)
    {m : Dim} (hmn : m ≠ n) (z : α) : ¬ P.NPart m x z := fun h =>
  let ⟨b, hb, _⟩ := Relation.TransGen.head'_iff.1 h
  hmn (hx m b hb).1

theorem not_nPart_of_no_parent {n : Dim} {x : α} (hx : ∀ y, ¬ P.Imm n x y) (z : α) :
    ¬ P.NPart n x z := fun h =>
  let ⟨b, hb, _⟩ := Relation.TransGen.head'_iff.1 h
  hx b hb

/-- A domain `S` closed under parenthood except at `b`, which is attached only in dimension `d`:
an `n`-part chain from inside `S` to outside it runs in dimension `d` and reaches `b` first. -/
theorem exit_of_nPart {S : Set α} {b : α} {d : Dim}
    (hS : ∀ x ∈ S, x ≠ b → ∀ n y, P.Imm n x y → y ∈ S) (hb : ∀ n y, P.Imm n b y → n = d)
    {n : Dim} {x y : α} (h : P.NPart n x y) (hx : x ∈ S) (hy : y ∉ S) :
    n = d ∧ (x = b ∨ P.NPart d x b) := by
  revert hx
  induction h using Relation.TransGen.head_induction_on with
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
      exact ⟨rfl, .inr (hcb.elim (fun e => e ▸ .single h') (.head h'))⟩

end Parthood

end MereologicalSyntax
