/-
# Core Dynamic Semantics Infrastructure

Abstract foundations shared by PLA, DRT, DPL, CDRT, and other dynamic semantics theories.

## Key Abstractions

1. **InfoState**: Set of possibilities (what we know)
2. **CCP**: Context Change Potential (how meaning changes state)
3. **Galois Connection**: Support ↔ Content duality

## Mathematical Structures

- `InfoState` forms a `CompleteLattice` (from Set)
- `CCP` forms a `Monoid` (composition + identity)
- Support and Content form a Galois connection

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
- Veltman, F. (1996). Defaults in Update Semantics.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Defs

namespace Theories.DynamicSemantics.Core


/--
An **InfoState** is a set of possibilities.

Different theories instantiate `P` differently:
- PLA: Assignment × WitnessSeq
- DRT: Assignment
- Intensional: World × Assignment
-/
abbrev InfoStateOf (P : Type*) := Set P

-- InfoState is just Set, so we get:
-- ⊤ = Set.univ, ⊥ = ∅, ⊔ = ∪, ⊓ = ∩


/--
A **Context Change Potential** (CCP) is a function from states to states.

This is the semantic type for dynamic meanings.
-/
abbrev CCP (P : Type*) := InfoStateOf P → InfoStateOf P

namespace CCP

variable {P : Type*}

/-- Identity CCP: leaves state unchanged -/
def id : CCP P := fun s => s

/-- Absurd CCP: yields empty state -/
def absurd : CCP P := fun _ => ∅

/-- Sequential composition of CCPs -/
def seq (u v : CCP P) : CCP P := fun s => v (u s)

infixl:70 " ;; " => seq

-- Monoid laws
theorem seq_assoc (u v w : CCP P) : (u ;; v) ;; w = u ;; (v ;; w) := rfl
theorem id_seq (u : CCP P) : id ;; u = u := rfl
theorem seq_id (u : CCP P) : u ;; id = u := rfl

/-- CCPs form a monoid under sequential composition -/
instance : Monoid (CCP P) where
  mul := seq
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- seq_absurd: anything followed by absurd is absurd -/
theorem seq_absurd (u : CCP P) : u ;; absurd = absurd := rfl

end CCP


/--
An update is **eliminative** if it never adds possibilities.

This is THE fundamental property of dynamic semantics:
information only grows (possibilities only decrease).
-/
def IsEliminative {P : Type*} (u : CCP P) : Prop :=
  ∀ s, u s ⊆ s

/-- Identity is eliminative -/
theorem eliminative_id {P : Type*} : IsEliminative (CCP.id : CCP P) :=
  fun _ => Set.Subset.rfl

/-- Sequential composition preserves eliminativity -/
theorem eliminative_seq {P : Type*} (u v : CCP P)
    (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u ;; v) := fun s _ hp =>
  hu s (hv (u s) hp)


/--
A **test** is a CCP that either passes (returns input) or fails (returns ∅).

Tests don't change information - they check compatibility.
Examples: might, must, presupposition triggers.
-/
def IsTest {P : Type*} (u : CCP P) : Prop :=
  ∀ s, u s = s ∨ u s = ∅

/-- Tests are eliminative -/
theorem test_eliminative {P : Type*} (u : CCP P) (h : IsTest u) :
    IsEliminative u := fun s p hp => by
  cases h s with
  | inl heq => rw [heq] at hp; exact hp
  | inr hemp => rw [hemp] at hp; exact False.elim hp


section GaloisContent

variable {P φ : Type*}

/--
**Support relation**: s supports ψ if all possibilities in s satisfy ψ.

This is the fundamental entailment relation of dynamic semantics.
-/
def supportOf (sat : P → φ → Prop) (s : InfoStateOf P) (ψ : φ) : Prop :=
  ∀ p ∈ s, sat p ψ

/--
**Content of a formula**: all possibilities satisfying it.
-/
def contentOf (sat : P → φ → Prop) (ψ : φ) : InfoStateOf P :=
  { p | sat p ψ }

/--
**Galois Connection**: s ⊆ content ψ  ↔  s supports ψ

This is the fundamental duality of dynamic semantics.
-/
theorem support_iff_subset_content (sat : P → φ → Prop) (s : InfoStateOf P) (ψ : φ) :
    supportOf sat s ψ ↔ s ⊆ contentOf sat ψ := by
  constructor
  · intro h p hp
    exact h p hp
  · intro h p hp
    exact h hp

/--
**Support is downward closed**: smaller states support more.
-/
theorem support_mono (sat : P → φ → Prop) (s t : InfoStateOf P) (ψ : φ)
    (h : t ⊆ s) (hs : supportOf sat s ψ) : supportOf sat t ψ :=
  fun p hp => hs p (h hp)

/--
**Empty state supports everything** (vacuously).
-/
theorem empty_supports (sat : P → φ → Prop) (ψ : φ) :
    supportOf sat ∅ ψ := fun _ hp => False.elim hp

/--
**Content is antitone in entailment**.
-/
theorem content_mono (sat : P → φ → Prop) (ψ₁ ψ₂ : φ)
    (h : ∀ p, sat p ψ₁ → sat p ψ₂) :
    contentOf sat ψ₁ ⊆ contentOf sat ψ₂ :=
  fun _ hp => h _ hp

end GaloisContent


/--
The standard update construction: filter by satisfaction.

This is how PLA, DRT, DPL all define updates.
-/
def updateFromSat {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) : CCP P :=
  fun s => { p ∈ s | sat p ψ }

/-- Standard updates are eliminative -/
theorem updateFromSat_eliminative {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    IsEliminative (updateFromSat sat ψ) :=
  fun _ _ hp => hp.1

/-- Standard update membership -/
theorem mem_updateFromSat {P φ : Type*} (sat : P → φ → Prop) (ψ : φ)
    (s : InfoStateOf P) (p : P) :
    p ∈ updateFromSat sat ψ s ↔ p ∈ s ∧ sat p ψ := Iff.rfl

/-- Update equals intersection with content -/
theorem updateFromSat_eq_inter_content {P φ : Type*} (sat : P → φ → Prop)
    (ψ : φ) (s : InfoStateOf P) :
    updateFromSat sat ψ s = s ∩ contentOf sat ψ := by
  ext p
  simp only [mem_updateFromSat, contentOf, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- Support-Update equivalence -/
theorem support_iff_update_eq {P φ : Type*} (sat : P → φ → Prop)
    (ψ : φ) (s : InfoStateOf P) :
    supportOf sat s ψ ↔ updateFromSat sat ψ s = s := by
  constructor
  · intro h
    ext p
    simp only [mem_updateFromSat]
    constructor
    · intro ⟨hp, _⟩; exact hp
    · intro hp; exact ⟨hp, h p hp⟩
  · intro h p hp
    have : p ∈ updateFromSat sat ψ s := by rw [h]; exact hp
    exact this.2


/--
**Dynamic Entailment**: φ dynamically entails ψ if updating with φ
always yields a state that supports ψ.
-/
def dynamicEntailsOf {P φ : Type*} (sat : P → φ → Prop) (ψ₁ ψ₂ : φ) : Prop :=
  ∀ s : InfoStateOf P, supportOf sat (updateFromSat sat ψ₁ s) ψ₂

/-- Dynamic entailment is reflexive -/
theorem dynamicEntails_refl {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    dynamicEntailsOf sat ψ ψ :=
  fun _ _ hp => hp.2

/-- Dynamic entailment is transitive -/
theorem dynamicEntails_trans {P φ : Type*} (sat : P → φ → Prop)
    (ψ₁ ψ₂ ψ₃ : φ) (h1 : dynamicEntailsOf sat ψ₁ ψ₂) (h2 : dynamicEntailsOf sat ψ₂ ψ₃) :
    dynamicEntailsOf sat ψ₁ ψ₃ := fun s p hp => by
  -- p ∈ updateFromSat sat ψ₁ s means p ∈ s and sat p ψ₁
  have hp_sat1 : sat p ψ₁ := hp.2
  have hp_in_s : p ∈ s := hp.1
  -- By h1, updateFromSat sat ψ₁ s supports ψ₂, so sat p ψ₂
  have hp_sat2 : sat p ψ₂ := h1 s p hp
  -- p ∈ updateFromSat sat ψ₂ s
  have hp_in_2 : p ∈ updateFromSat sat ψ₂ s := ⟨hp_in_s, hp_sat2⟩
  -- By h2, updateFromSat sat ψ₂ s supports ψ₃
  exact h2 s p hp_in_2


/--
**Update is monotone**: larger input states yield larger output states.
-/
theorem updateFromSat_monotone {P φ : Type*} (sat : P → φ → Prop) (ψ : φ)
    (s t : InfoStateOf P) (h : s ⊆ t) :
    updateFromSat sat ψ s ⊆ updateFromSat sat ψ t := by
  intro p hp
  exact ⟨h hp.1, hp.2⟩

-- SUMMARY

/-!
## What This Module Provides

### Core Types
- `InfoStateOf P`: Set of possibilities (just `Set P`)
- `CCP P`: Context Change Potential (`InfoStateOf P → InfoStateOf P`)

### Algebraic Structure
- `CCP` is a `Monoid` under sequential composition
- `CCP.id`: identity update
- `CCP.seq`: sequential composition (notation `;;`)

### Properties
- `IsEliminative`: Update never adds possibilities
- `IsTest`: Update is pass/fail
- `eliminative_seq`: Eliminativity is preserved by composition

### Support and Content
- `supportOf sat s ψ`: All possibilities in s satisfy ψ
- `contentOf sat ψ`: All possibilities satisfying ψ
- `support_iff_subset_content`: Galois connection

### Standard Updates
- `updateFromSat`: Filter by satisfaction
- `updateFromSat_eliminative`: Standard updates are eliminative
- `support_iff_update_eq`: Support ↔ update is identity

### Dynamic Entailment
- `dynamicEntailsOf sat ψ₁ ψ₂`: ψ₁ dynamically entails ψ₂
- `dynamicEntails_refl`: Reflexivity
- `dynamicEntails_trans`: Transitivity

## Usage

To instantiate for a specific theory:

```lean
-- Define your possibility type
abbrev MyPoss := Assignment E × WitnessSeq E

-- Define satisfaction
def mySat : MyPoss → Formula → Prop := ...

-- Use the infrastructure
#check updateFromSat mySat φ  -- : CCP MyPoss
#check supportOf mySat s φ      -- : Prop
#check dynamicEntailsOf mySat φ ψ  -- : Prop
```
-/

end Theories.DynamicSemantics.Core
