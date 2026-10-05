module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Linglib.Syntax.Category.Coordinator

/-!
# The denotation of a coordinator

A coordinator denotes an operation on the set of its coordinands, which its semantic type fixes:
the infimum of the set for conjunctive and adversative coordinators, its supremum for disjunctive
ones, and the complement of its supremum for negative ones. Coordinating two constituents is the
case of a two-element set, so the one operation conjoins truth values, predicates and generalized
quantifiers, coordinates lists of any length, and builds the quantifiers that Japanese *ka* and
*mo* form from indeterminate pronouns. The composition engine applies it to two sisters of one
conjoinable type in `Semantics/Composition/Coordination.lean`.

## Main definitions

* `Coordinator.Role.denote`: the operation a semantic type denotes on a set of coordinands.

## Main results

* `Coordinator.Role.denote_singleton`, `Coordinator.Role.denote_pair_self`: coordinating a
  constituent alone or with itself returns it, except under negative coordination.
* `Coordinator.Role.denote_apply`: the coordination of functions is computed pointwise.

## Implementation notes

The denotation is the truth-conditional content only. The contrast an adversative coordinator
adds to conjunction is a relation between the coordinands in discourse, and `denote_adversative`
records that it is invisible here. The operation needs a complete Boolean algebra, which the
domain of every conjoinable type is, since such a type ends in `t`.

## References

* [partee-rooth-1983]
-/

@[expose] public section

namespace Coordinator.Role

variable {α : Type*} [CompleteBooleanAlgebra α]

/-- On a set of coordinands a coordinator denotes their infimum under conjunctive and adversative
coordination, their supremum under disjunctive coordination, and the complement of their supremum
under negative coordination. -/
def denote : Role → Set α → α
  | .conjunctive | .adversative => sInf
  | .disjunctive => sSup
  | .negative => fun s ↦ (sSup s)ᶜ

@[simp] theorem denote_conjunctive (s : Set α) : denote .conjunctive s = sInf s := rfl

@[simp] theorem denote_disjunctive (s : Set α) : denote .disjunctive s = sSup s := rfl

@[simp] theorem denote_negative (s : Set α) : denote .negative s = (sSup s)ᶜ := rfl

/-- An adversative coordinator has the truth conditions of conjunction. -/
@[simp] theorem denote_adversative (s : Set α) : denote .adversative s = sInf s := rfl

/-- Coordinating a constituent alone returns it, except under negative coordination. -/
theorem denote_singleton {r : Role} (hr : r ≠ .negative) (p : α) : r.denote {p} = p := by
  cases r <;> simp_all

/-- Coordinating a constituent with itself returns it, except under negative coordination. -/
theorem denote_pair_self {r : Role} (hr : r ≠ .negative) (p : α) : r.denote {p, p} = p := by
  rw [Set.pair_eq_singleton, denote_singleton hr]

/-- The coordination of functions is computed pointwise. -/
theorem denote_apply {ι : Type*} (r : Role) (s : Set (ι → α)) (i : ι) :
    r.denote s i = r.denote ((· i) '' s) := by
  cases r <;> simp [sSup_apply, sInf_apply, sSup_image', sInf_image']

end Coordinator.Role
