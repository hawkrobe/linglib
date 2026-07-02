import Mathlib.Order.Basic
import Mathlib.Data.Set.Subsingleton

/-!
# Outcome cardinality

The cardinality *tier* of a verb root's outcome set ([bhadra-2024], eq. 62): the
light invariant of what a root encodes along the outcome axis — `empty` (no
change specified), `singleton` (a single lexically-specified result — change-of-
state and impingement roots), or `multi` (potential-for-change roots). Only the
tier, not an exact count, is grammatically load-bearing, so this is a
three-element linear order rather than `ℕ∞`.

Factored out from `Semantics/Verb/Root/Outcomes.lean` (which carries the heavy
event-relative machinery — `res`/`pre`, `VerbOutcomes`) so that `Root` itself
can carry the outcome axis without depending on `Event`/`EventRel`.

## Main definitions

* `OutcomeCardinality` — the `empty < singleton < multi` tier
* `OutcomeCardinality.ofSet` — the tier of a concrete outcome set

## References

* [bhadra-2024] (roots encode outcome sets; the eq. 62 hierarchy)
-/

namespace Verb

/-- The cardinality tier of an outcome set ([bhadra-2024], eq. 62). -/
inductive OutcomeCardinality where
  | empty
  | singleton
  | multi
  deriving Repr, BEq

namespace OutcomeCardinality

/-- Rank embedding into `ℕ`, giving the `empty < singleton < multi` order. -/
def toNat : OutcomeCardinality → ℕ
  | .empty => 0
  | .singleton => 1
  | .multi => 2

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [toNat]

instance : LinearOrder OutcomeCardinality := LinearOrder.lift' toNat toNat_injective

theorem empty_lt_singleton : empty < singleton := by decide
theorem singleton_lt_multi : singleton < multi := by decide

/-- The tier of a concrete outcome set: multi-membered iff `Nontrivial`,
    empty iff there is no outcome, singleton otherwise. -/
noncomputable def ofSet {State : Type*} (O : Set State) : OutcomeCardinality :=
  open Classical in
  if O.Nontrivial then .multi else if O.Nonempty then .singleton else .empty

variable {State : Type*} {O : Set State}

theorem ofSet_eq_multi (h : O.Nontrivial) : ofSet O = .multi := by
  rw [ofSet, if_pos h]

theorem ofSet_eq_singleton (hne : O.Nonempty) (hnt : ¬ O.Nontrivial) :
    ofSet O = .singleton := by
  rw [ofSet, if_neg hnt, if_pos hne]

theorem ofSet_eq_empty (h : ¬ O.Nonempty) : ofSet O = .empty := by
  rw [ofSet, if_neg (fun hnt => h hnt.nonempty), if_neg h]

@[simp] theorem ofSet_singleton (s : State) : ofSet ({s} : Set State) = .singleton :=
  ofSet_eq_singleton ⟨s, rfl⟩ (by rw [Set.not_nontrivial_iff]; exact Set.subsingleton_singleton)

@[simp] theorem ofSet_empty : ofSet (∅ : Set State) = .empty :=
  ofSet_eq_empty (by simp)

end OutcomeCardinality

end Verb
