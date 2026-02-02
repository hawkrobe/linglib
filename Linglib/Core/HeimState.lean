/-
# Heimian Information States

Information states as sets of (world, assignment) pairs, following Heim (1982).

## Motivation

In static Montague semantics, sentences denote propositions (sets of worlds).
In dynamic semantics, sentences denote context change potentials - functions
from information states to information states.

Heim's "File Change Semantics" models an information state as a "file" of
information about discourse referents. Formally, this is a set of
(world, assignment) pairs - each pair represents a way the world might be
and what discourse referents have been introduced.

## Key Concepts

- `Possibility`: A (world, assignment) pair
- `HeimState`: Set of possibilities
- `definedAt`: Variable x is defined if all assignments agree
- `update`: Eliminate possibilities not satisfying a proposition
- `randomAssign`: Introduce new discourse referent (existential)
- `subsistsIn`: Every possibility has a "descendant" in the new state

## Architecture

This module provides *infrastructure* for dynamic semantics. Specific theories
(File Change Semantics, DRT, Update Semantics, BUS) build on this.

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases. UMass dissertation.
- Heim, I. (1983). File Change Semantics. In Bäuerle et al. (eds.), Meaning, Use, and Interpretation.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. L&P 14:39-100.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
-/

import Linglib.Theories.Montague.Variables
import Mathlib.Data.Set.Basic

namespace Core

-- ============================================================================
-- PART 1: Possibilities
-- ============================================================================

/--
A possibility: a world paired with a variable assignment.

In Heim's file metaphor, a possibility represents one way the conversation
could be going - both what the world is like and what discourse referents
have been established.

The entity type E is the domain of individuals that variables range over.
-/
structure Possibility (W : Type*) (E : Type*) where
  /-- The possible world -/
  world : W
  /-- The variable assignment -/
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
  { p with assignment := fun n => if n = x then e else p.assignment n }

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

-- ============================================================================
-- PART 2: Heimian States
-- ============================================================================

/--
A Heimian information state: a set of possibilities.

This represents the information available in a discourse context. Each
possibility is a consistent way the world might be given what's been said.

The "file" metaphor: each possibility is a "file card" recording information
about discourse referents. The state is the set of all live file cards.
-/
def HeimState (W : Type*) (E : Type*) := Set (Possibility W E)

instance {W E : Type*} : Membership (Possibility W E) (HeimState W E) := Set.instMembership
instance {W E : Type*} : EmptyCollection (HeimState W E) := Set.instEmptyCollection
instance {W E : Type*} : HasSubset (HeimState W E) := Set.instHasSubset
instance {W E : Type*} : Union (HeimState W E) := Set.instUnion
instance {W E : Type*} : Inter (HeimState W E) := Set.instInter

@[ext]
theorem HeimState.ext {W E : Type*} {s t : HeimState W E} (h : ∀ p, p ∈ s ↔ p ∈ t) : s = t :=
  Set.ext h

namespace HeimState

variable {W E : Type*}

-- ============================================================================
-- PART 3: Basic State Operations
-- ============================================================================

/-- The trivial state: all possibilities -/
def univ : HeimState W E := Set.univ

/-- The absurd state: no possibilities -/
def empty : HeimState W E := (∅ : Set (Possibility W E))

/-- State is consistent (non-empty) -/
def consistent (s : HeimState W E) : Prop := s.Nonempty

/-- State is trivial (all possibilities) -/
def trivial (s : HeimState W E) : Prop := s = Set.univ

-- ============================================================================
-- PART 4: Definedness and Familiarity
-- ============================================================================

/--
Variable x is *defined* in state s iff all possibilities agree on x's value.

This corresponds to the familiarity condition in Heim (1982): a definite
description presupposes its variable is already defined (familiar).

Note: In a consistent state, definedness means there's a unique value.
In the empty state, all variables are vacuously defined.
-/
def definedAt (s : HeimState W E) (x : Nat) : Prop :=
  ∀ p q : Possibility W E, p ∈ s → q ∈ s → p.assignment x = q.assignment x

/-- The set of defined variables in a state -/
def definedVars (s : HeimState W E) : Set Nat :=
  { x | s.definedAt x }

/--
Variable x is *novel* in state s iff x is NOT defined (free to vary).

Novel variables can be bound by existential quantifiers or indefinites.
-/
def novelAt (s : HeimState W E) (x : Nat) : Prop := ¬s.definedAt x

/-- In a consistent state, novel means assignments actually disagree -/
theorem novelAt_iff_disagree (s : HeimState W E) (x : Nat) (hs : s.consistent) :
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

-- ============================================================================
-- PART 5: State Updates
-- ============================================================================

/--
Update a state with a proposition: keep only possibilities where φ holds.

This is the basic dynamic operation: learning that φ eliminates all
possibilities where φ is false.

s[φ] = { p ∈ s | φ(p.world) }
-/
def update (s : HeimState W E) (φ : W → Bool) : HeimState W E :=
  { p ∈ s | φ p.world }

notation:max s "⟦" φ "⟧" => HeimState.update s φ

/-- Update is monotonic: larger states give larger results -/
theorem update_mono {s s' : HeimState W E} (h : s ⊆ s') (φ : W → Bool) :
    s⟦φ⟧ ⊆ s'⟦φ⟧ := by
  intro p ⟨hp, hφ⟩
  exact ⟨h hp, hφ⟩

/-- Update is idempotent -/
theorem update_update (s : HeimState W E) (φ : W → Bool) :
    s⟦φ⟧⟦φ⟧ = s⟦φ⟧ := by
  ext p
  simp only [update, Set.mem_setOf_eq]
  constructor
  · intro ⟨⟨hs, _⟩, hφ⟩; exact ⟨hs, hφ⟩
  · intro ⟨hs, hφ⟩; exact ⟨⟨hs, hφ⟩, hφ⟩

/-- Sequential update = conjunction -/
theorem update_seq (s : HeimState W E) (φ ψ : W → Bool) :
    s⟦φ⟧⟦ψ⟧ = s⟦fun w => φ w && ψ w⟧ := by
  ext p
  simp only [update, Set.mem_setOf_eq, Bool.and_eq_true]
  constructor
  · intro ⟨⟨hs, hφ⟩, hψ⟩; exact ⟨hs, hφ, hψ⟩
  · intro ⟨hs, hφ, hψ⟩; exact ⟨⟨hs, hφ⟩, hψ⟩

/-- Update preserves definedness -/
theorem update_preserves_defined (s : HeimState W E) (φ : W → Bool) (x : Nat)
    (h : s.definedAt x) : s⟦φ⟧.definedAt x := by
  intro p q hp hq
  exact h p q hp.1 hq.1

-- ============================================================================
-- PART 6: Random Assignment (Existential Introduction)
-- ============================================================================

/--
Random assignment: introduce a new discourse referent at variable x.

This is the dynamic interpretation of existential quantification:
∃x.φ is interpreted as "introduce x, then update with φ".

s[x:=?] = { p.extend(x,e) | p ∈ s, e ∈ domain }

After random assignment, x is no longer defined (its value varies across
possibilities).
-/
def randomAssign (s : HeimState W E) (x : Nat) (domain : Set E) : HeimState W E :=
  { p' | ∃ p ∈ s, ∃ e ∈ domain, p' = p.extend x e }

/-- Random assignment with full domain -/
def randomAssignFull (s : HeimState W E) (x : Nat) : HeimState W E :=
  { p' | ∃ p ∈ s, ∃ e : E, p' = p.extend x e }

/-- Random assignment makes x novel (when domain has multiple elements) -/
theorem randomAssign_makes_novel (s : HeimState W E) (x : Nat) (domain : Set E)
    (hs : s.consistent) (hdom : ∃ e₁ e₂ : E, e₁ ∈ domain ∧ e₂ ∈ domain ∧ e₁ ≠ e₂) :
    (s.randomAssign x domain).novelAt x := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨e₁, e₂, he₁, he₂, hne⟩ := hdom
  simp only [novelAt, definedAt]
  push_neg
  refine ⟨p.extend x e₁, p.extend x e₂, ?_, ?_, ?_⟩
  · exact ⟨p, hp, e₁, he₁, rfl⟩
  · exact ⟨p, hp, e₂, he₂, rfl⟩
  · simp [Possibility.extend, hne]

-- ============================================================================
-- PART 7: State Subsistence (Elliott & Sudo 2025)
-- ============================================================================

/--
State subsistence: s subsists in s' iff every possibility in s has a
"descendant" in s'.

This notion is central to Elliott & Sudo (2025): bilateral updates must
preserve subsistence relations to validate key inferences.

Formally: s ⪯ s' iff ∀p ∈ s, ∃p' ∈ s' with p.world = p'.world and
p and p' agree on all variables defined in s.
-/
def subsistsIn (s s' : HeimState W E) : Prop :=
  ∀ p ∈ s, ∃ p' ∈ s', p.world = p'.world ∧
    ∀ x, s.definedAt x → p.assignment x = p'.assignment x

notation:50 s " ⪯ " s' => HeimState.subsistsIn s s'

/-- Subsistence is reflexive -/
theorem subsistsIn_refl (s : HeimState W E) : s ⪯ s := by
  intro p hp
  exact ⟨p, hp, rfl, fun _ _ => rfl⟩

/-- Subset implies subsistence -/
theorem subset_subsistsIn {s s' : HeimState W E} (h : s ⊆ s') : s ⪯ s' := by
  intro p hp
  exact ⟨p, h hp, rfl, fun _ _ => rfl⟩

-- ============================================================================
-- PART 8: Support Relation
-- ============================================================================

/--
State s supports proposition φ iff φ holds at all worlds in s.

s ⊨ φ iff ∀p ∈ s, φ(p.world)

This is the dynamic notion of truth: a sentence is true relative to an
information state if it holds throughout that state.
-/
def supports (s : HeimState W E) (φ : W → Bool) : Prop :=
  ∀ p ∈ s, φ p.world

notation:50 s " ⊫ " φ => HeimState.supports s φ

/-- Support after update: s[φ] ⊫ φ -/
theorem update_supports (s : HeimState W E) (φ : W → Bool) : s⟦φ⟧ ⊫ φ := by
  intro p ⟨_, hφ⟩
  exact hφ

/-- Support is preserved by subset -/
theorem supports_mono {s s' : HeimState W E} (h : s ⊆ s')
    (φ : W → Bool) (hsupp : s' ⊫ φ) : s ⊫ φ := by
  intro p hp
  exact hsupp p (h hp)

-- ============================================================================
-- PART 9: Dynamic Entailment
-- ============================================================================

/--
Dynamic entailment: φ entails ψ iff for all states s,
if s is consistent after φ, then s[φ] supports ψ.

This is the dynamic notion of logical consequence.
-/
def dynamicEntails (φ ψ : W → Bool) : Prop :=
  ∀ s : HeimState W E, (s⟦φ⟧).consistent → s⟦φ⟧ ⊫ ψ

/-- Classical entailment implies dynamic entailment -/
theorem classical_implies_dynamic {φ ψ : W → Bool}
    (h : ∀ w, φ w → ψ w) : @dynamicEntails W E φ ψ := by
  intro s _ p hp
  exact h p.world hp.2

end HeimState

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Core Types
- `Possibility W E`: (world, assignment) pair
- `HeimState W E`: Set of possibilities (the information state)

### Possibility Operations
- `extend`: Modify assignment at one variable
- `agreeOn`: Agreement on a set of variables
- `sameWorld`: Same world component

### State Properties
- `consistent`: Non-empty state
- `definedAt`: Variable is uniquely determined
- `novelAt`: Variable is free to vary
- `definedVars`: Set of defined variables

### State Operations
- `update` (notation: s⟦φ⟧): Propositional update
- `randomAssign`: Introduce discourse referent with domain
- `randomAssignFull`: Random assignment with full domain

### Relations
- `subsistsIn` (notation: s ⪯ s'): Every possibility has descendant
- `supports` (notation: s ⊫ φ): Proposition holds throughout state
- `dynamicEntails`: Dynamic logical consequence

### Key Theorems
- `update_mono`: Update is monotonic
- `update_preserves_defined`: Update preserves definedness
- `randomAssign_makes_novel`: Random assignment makes variable novel
- `subsistsIn_refl`: Subsistence is reflexive
- `update_supports`: s⟦φ⟧ ⊫ φ

## Architecture

This module provides infrastructure for:
- File Change Semantics (Heim 1982, 1983)
- Dynamic Predicate Logic (G&S 1991)
- Bilateral Update Semantics (Elliott & Sudo 2025)

Specific theories extend this with their own update operations and
logical connectives.
-/

end Core
