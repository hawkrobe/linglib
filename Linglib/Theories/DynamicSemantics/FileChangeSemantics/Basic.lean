/-
# File Change Semantics (Heim 1982, 1983)

Stub for Heim's File Change Semantics (FCS), the foundational theory
that treats meanings as context change potentials.

## Key Ideas

Heim's File Metaphor:
- The context is a "file" of information about discourse referents
- Each "file card" is a possibility: (world, assignment) pair
- Sentences update the file by adding/removing cards
- Indefinites "open" new file cards

## Core Concepts

| Concept | Description |
|---------|-------------|
| File | Set of (world, assignment) pairs = information state |
| File card | Single (world, assignment) pair = possibility |
| Novelty | Indefinites require novel variables (not yet defined) |
| Familiarity | Definites require familiar variables (already defined) |

## Semantic Type

⟦φ⟧ : File → File
(Sentences are context change potentials)

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
  PhD dissertation, University of Massachusetts.
- Heim, I. (1983). File Change Semantics and the Familiarity Theory of
  Definiteness. In Bäuerle et al. (eds.), Meaning, Use, and Interpretation.
-/

import Linglib.Theories.DynamicSemantics.Core.Update

namespace Theories.DynamicSemantics.FileChangeSemantics

open Theories.DynamicSemantics.Core
open Classical

-- ============================================================================
-- File = InfoState
-- ============================================================================

/--
A File is an information state: set of (world, assignment) pairs.

This is Heim's "file metaphor" - each pair is a "file card".
-/
abbrev File (W : Type*) (E : Type*) := InfoState W E

/--
A File Card is a single possibility: (world, assignment).
-/
abbrev FileCard (W : Type*) (E : Type*) := Possibility W E

-- ============================================================================
-- Novelty and Familiarity
-- ============================================================================

/--
Variable x is NOVEL in file f iff f doesn't constrain x.

Indefinites require their variable to be novel - this prevents
the same variable being reused inappropriately.
-/
def File.novel {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.novelAt x

/--
Variable x is FAMILIAR in file f iff f constrains x uniquely.

Definites require their variable to be familiar - the discourse
must have already established who "the X" refers to.
-/
def File.familiar {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.definedAt x

-- ============================================================================
-- File Updates
-- ============================================================================

/--
Update file with proposition: eliminate cards where φ fails.

f[φ] = { c ∈ f | φ(c.world) }
-/
def File.updateProp {W E : Type*} (f : File W E) (φ : W → Bool) : File W E :=
  f.update φ

/--
Introduce new discourse referent (indefinite).

f[x:=?] adds cards for each possible entity value of x.
Requires x to be NOVEL (precondition).
-/
def File.introduce {W E : Type*} (f : File W E) (x : Nat) (dom : Set E) : File W E :=
  f.randomAssign x dom

-- ============================================================================
-- Context Change Potentials
-- ============================================================================

/--
File Change Potential (FCP): the semantic type for sentences in FCS.
-/
abbrev FCP (W : Type*) (E : Type*) := File W E → File W E

/--
Atomic predicate update.
-/
def FCP.atom {W E : Type*} (pred : W → Bool) : FCP W E :=
  fun f => f.updateProp pred

/--
Indefinite introduction: requires novelty.

This models "a man" - introduces a new discourse referent.
-/
def FCP.indefinite {W E : Type*} (x : Nat) (dom : Set E) (body : FCP W E) : FCP W E :=
  fun f => body (f.introduce x dom)

/--
Definite reference: requires familiarity.

This models "the man" - presupposes the referent is established.
-/
def FCP.definite {W E : Type*} (x : Nat) (body : FCP W E) : FCP W E :=
  fun f => if f.familiar x then body f else ∅

/--
Conjunction: sequential file update.

f[φ ∧ ψ] = f[φ][ψ]
-/
def FCP.conj {W E : Type*} (φ ψ : FCP W E) : FCP W E :=
  fun f => ψ (φ f)

/--
Negation: test-based (standard FCS).

f[¬φ] = f if f[φ] = ∅, else ∅

Note: This does NOT validate DNE.
-/
def FCP.neg {W E : Type*} (φ : FCP W E) : FCP W E :=
  fun f => if (φ f).Nonempty then ∅ else f

-- ============================================================================
-- Key Properties
-- ============================================================================

/--
Novelty precondition for indefinites.

Attempting to introduce a non-novel variable is undefined behavior
(typically modeled as returning ∅ or crash).
-/
def requiresNovelty {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.novel x

/--
Familiarity precondition for definites.
-/
def requiresFamiliarity {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.familiar x

-- ============================================================================
-- Connection to InfoState
-- ============================================================================

/-!
## Relation to DynamicSemantics.Core.Basic

The `Theories.DynamicSemantics.Core.Basic` module provides the canonical infrastructure.
This module provides FCS-specific vocabulary as aliases:

| This Module | DynamicSemantics.Core |
|-------------|----------------------|
| File | InfoState |
| FileCard | Possibility |
| novel | novelAt |
| familiar | definedAt |
| introduce | randomAssign |
| updateProp | update |
-/

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Will Provide

### Core Types (via aliases)
- `File W E`: Information state (= InfoState)
- `FileCard W E`: Single possibility
- `FCP W E`: File Change Potential

### Novelty/Familiarity
- `novel`: Variable is not yet constrained
- `familiar`: Variable is uniquely constrained

### Operations
- `updateProp`: Propositional update
- `introduce`: Discourse referent introduction
- `atom`: Atomic predicate
- `indefinite`: "a/an" with novelty requirement
- `definite`: "the" with familiarity requirement
- `conj`: Sequential conjunction
- `neg`: Test-based negation

## Key Insight: The File Metaphor

Heim's file metaphor makes anaphora resolution concrete:
- Opening a new card = introducing a discourse referent
- Looking up a card = anaphoric reference
- Novelty = can't reuse names
- Familiarity = must already have a card for "the X"

## TODO

Full implementation including:
- Presupposition projection
- Accommodation
- Connection to Core.HeimState proofs
-/

end Theories.DynamicSemantics.FileChangeSemantics
