import Linglib.Semantics.Events.Basic
import Linglib.Semantics.ArgumentStructure.Defs

/-!
# Root outcomes

A verb root lexically encodes the **set of outcomes** its object can be in after
the action — the dimension [bhadra-2024] adds to root semantics, distinct from
the manner/result/cause kinds of [beavers-koontz-garboden-2020]'s
`Root.FeatureSignature`. Two roots with identical feature signatures can carry
different outcome sets (*bend* vs *break*), so this is a genuinely orthogonal
axis of what a root encodes.

This file is the substrate: the cardinality invariant, the boundary operators,
and the outcome-bearing carrier. Affix semantics built on top (reversative
*un-*, restitutive *re-*/*again*) live in the consuming study files.

## Main definitions

* `OutcomeCardinality` — the `empty < singleton < multi` tier of an outcome set
  (the light invariant; [bhadra-2024]'s eq. 62 hierarchy)
* `OutcomeCardinality.ofSet` — the tier of a concrete outcome set
* `resState` / `preState` — an object's state at the right / left boundary of an
  event ([bhadra-2024], eqs. 64–65)
* `VerbOutcomes` — an outcome-bearing predicate: base predicate, outcome set,
  threshold set

## References

* [bhadra-2024] (roots encode outcome sets)
* [beavers-koontz-garboden-2020] (the orthogonal manner/result/cause axis)
-/

namespace Semantics.Lexical

open Semantics.ArgumentStructure (EventRel)

/-! ### Outcome cardinality (the light invariant)

The cardinality *tier* of a root's outcome set: empty (no-change-specified
roots), singleton (a single lexically-specified result — change-of-state and
impingement roots), or multi-membered (potential-for-change roots). Only the
tier — not an exact count — is grammatically load-bearing, so this is a
three-element linear order rather than `ℕ∞`. -/

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

/-! ### Event boundaries (eqs. 64–65)

`res` and `pre` read an object's lexically-relevant state (the paper's *state*
`k : t ↦ l(x)`, abstracted here as `State`) at the right and left boundaries of
an event's temporal trace `τ`. They are equivalence operators, not temporal
ones — they yield states, not times. -/

/-- A state function tracks an object's state at each time point. -/
abbrev StateFunction (Entity State Time : Type*) := Time → Entity → State

variable {Entity State Time : Type*} [LinearOrder Time]

/-- `res(e)(x)` (eq. 64): the object's state at the right boundary of `e`. -/
def resState (k : StateFunction Entity State Time) (e : Event Time) (x : Entity) : State :=
  k (Event.τ e).snd x

/-- `pre(e)(x)` (eq. 65): the object's state at the left boundary of `e`. -/
def preState (k : StateFunction Entity State Time) (e : Event Time) (x : Entity) : State :=
  k (Event.τ e).fst x

/-! ### The outcome-bearing verb root (the heavy witness)

An outcome-bearing predicate bundles the base predicate `P` (event-first, the
`⟨v,⟨e,t⟩⟩` meaning affixes modify) with the lexical outcome set `O` and the
contextual threshold set `T`. -/

/-- A verb root carrying an outcome set, the carrier result-state modifiers act
    on ([bhadra-2024], eqs. 56, 60). -/
structure VerbOutcomes (Entity State Time : Type*) [LinearOrder Time] where
  /-- The base predicate `P(e)(x)` (`⟨v,⟨e,t⟩⟩`). -/
  verb : EventRel Time Entity
  /-- The lexically-encoded outcome set `O` (states at the right boundary). -/
  outcomes : Set State
  /-- The contextual threshold set `T` (states at the left boundary). -/
  thresholds : Set State

/-- The cardinality tier of a root's outcome set. -/
noncomputable def VerbOutcomes.cardinality (vro : VerbOutcomes Entity State Time) :
    OutcomeCardinality :=
  OutcomeCardinality.ofSet vro.outcomes

end Semantics.Lexical
