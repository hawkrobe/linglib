/-
# Dynamic Semantics Shared Infrastructure

Common types for dynamic semantic theories.

## Main definitions

`Possibility`, `InfoState`, `Context`, `subsistsIn`, `supports`

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. L&P 14:39-100.
-/

import Mathlib.Data.Set.Basic

namespace Semantics.Dynamic.Core


/-- A possibility: world paired with variable assignment. -/
structure Possibility (W : Type*) (E : Type*) where
  world : W
  assignment : Nat → E

namespace Possibility

variable {W E : Type*}

/-- Two possibilities agree on all variables in a set -/
def agreeOn (p q : Possibility W E) (vars : Set Nat) : Prop :=
  ∀ x ∈ vars, p.assignment x = q.assignment x

/-- Same world, possibly different assignment -/
def sameWorld (p q : Possibility W E) : Prop := p.world = q.world

/-- Extend an assignment at a single variable -/
def extend (p : Possibility W E) (x : Nat) (e : E) : Possibility W E :=
  { p with assignment := λ n => if n = x then e else p.assignment n }

@[simp]
theorem extend_at (p : Possibility W E) (x : Nat) (e : E) :
    (p.extend x e).assignment x = e := by simp [extend]

@[simp]
theorem extend_other (p : Possibility W E) (x y : Nat) (e : E) (h : y ≠ x) :
    (p.extend x e).assignment y = p.assignment y := by simp [extend, h]

@[simp]
theorem extend_world (p : Possibility W E) (x : Nat) (e : E) :
    (p.extend x e).world = p.world := rfl

end Possibility


/-- Information state: set of possibilities. -/
abbrev InfoState (W : Type*) (E : Type*) := Set (Possibility W E)

namespace InfoState

variable {W E : Type*}

/-- The trivial state: all possibilities -/
def univ : InfoState W E := Set.univ

/-- The absurd state: no possibilities -/
def empty : InfoState W E := (∅ : Set (Possibility W E))

/-- State is consistent (non-empty) -/
def consistent (s : InfoState W E) : Prop := s.Nonempty

/-- State is trivial (all possibilities) -/
def trivial (s : InfoState W E) : Prop := s = Set.univ


/-- Variable x is defined in state s iff all possibilities agree on x's value. -/
def definedAt (s : InfoState W E) (x : Nat) : Prop :=
  ∀ p q : Possibility W E, p ∈ s → q ∈ s → p.assignment x = q.assignment x

/-- The set of defined variables in a state -/
def definedVars (s : InfoState W E) : Set Nat :=
  { x | s.definedAt x }

/-- Variable x is novel in state s iff x is not defined. -/
def novelAt (s : InfoState W E) (x : Nat) : Prop := ¬s.definedAt x

/-- In a consistent state, novel means assignments actually disagree -/
theorem novelAt_iff_disagree (s : InfoState W E) (x : Nat) (hs : s.consistent) :
    s.novelAt x ↔ ∃ p q : Possibility W E, p ∈ s ∧ q ∈ s ∧ p.assignment x ≠ q.assignment x := by
  constructor
  · intro h
    simp only [novelAt, definedAt] at h
    push_neg at h
    exact h
  · intro ⟨p, q, hp, hq, hne⟩
    simp only [novelAt, definedAt]
    push_neg
    exact ⟨p, q, hp, hq, hne⟩


/-- Project to the set of worlds in the state -/
def worlds (s : InfoState W E) : Set W :=
  { w | ∃ p ∈ s, p.world = w }

/-- Filter state by a world predicate -/
def filterWorlds (s : InfoState W E) (pred : W → Bool) : InfoState W E :=
  { p ∈ s | pred p.world }

/-- Filter state by an assignment predicate -/
def filterAssign (s : InfoState W E) (pred : (Nat → E) → Bool) : InfoState W E :=
  { p ∈ s | pred p.assignment }

end InfoState


/-- Context extends InfoState with metadata. -/
structure Context (W : Type*) (E : Type*) where
  state : InfoState W E
  definedVars : Set Nat := ∅
  domain : Set E := Set.univ

namespace Context

variable {W E : Type*}

/-- Empty context with all possibilities -/
def initial : Context W E where
  state := InfoState.univ
  definedVars := ∅

/-- Context is consistent iff its state is -/
def consistent (c : Context W E) : Prop := c.state.consistent

/-- Mark a variable as defined -/
def introduce (c : Context W E) (x : Nat) : Context W E :=
  { c with definedVars := c.definedVars ∪ {x} }

/-- Narrow the state -/
def narrow (c : Context W E) (s : InfoState W E) : Context W E :=
  { c with state := c.state ∩ s }

end Context


/-- State subsistence: s subsists in s' iff every possibility in s has a descendant in s'. -/
def InfoState.subsistsIn {W E : Type*} (s s' : InfoState W E) : Prop :=
  ∀ p ∈ s, ∃ p' ∈ s', p.world = p'.world ∧
    ∀ x, s.definedAt x → p.assignment x = p'.assignment x

notation:50 s " ⪯ " s' => InfoState.subsistsIn s s'

namespace InfoState

variable {W E : Type*}

/-- Subsistence is reflexive -/
theorem subsistsIn_refl (s : InfoState W E) : s ⪯ s := by
  intro p hp
  exact ⟨p, hp, rfl, λ _ _ => rfl⟩

/-- Subset implies subsistence -/
theorem subset_subsistsIn {s s' : InfoState W E} (h : s ⊆ s') : s ⪯ s' := by
  intro p hp
  exact ⟨p, h hp, rfl, λ _ _ => rfl⟩


/-- State s supports proposition φ iff φ holds at all worlds in s. -/
def supports (s : InfoState W E) (φ : W → Bool) : Prop :=
  ∀ p ∈ s, φ p.world

notation:50 s " ⊫ " φ => InfoState.supports s φ

/-- Support is preserved by subset -/
theorem supports_mono {s s' : InfoState W E} (h : s ⊆ s')
    (φ : W → Bool) (hsupp : s' ⊫ φ) : s ⊫ φ := by
  intro p hp
  exact hsupp p (h hp)

end InfoState


end Semantics.Dynamic.Core
