/-
# Linglib.Core.InformationStructure

Abstract interface for Information Structure (theme/rheme, focus/background, QUD).

## Overview

Information Structure partitions utterances along two orthogonal dimensions:
1. Theme/Rheme (topic/comment): What's being talked about vs. what's said about it
2. Focus/Background: What's contrasted vs. what's given

The Question Under Discussion (QUD) connects these to pragmatics:
- The theme presupposes a QUD (set of alternatives)
- The rheme answers/restricts the QUD
- Informativity in RSA is relative to the QUD

## Architecture

This module defines the interface. Implementations include:
- `Theories/CCG/Intonation.lean`: Prosodic realization (Steedman 2000)
- (Future) Syntactic focus marking, discourse models, etc.

## References

- Steedman (2000). The Syntactic Process, Chapter 5.
- Rooth (1992). A theory of focus interpretation.
- Roberts (1996/2012). Information structure in discourse.
- Beaver & Clark (2008). Sense and Sensitivity.
-/

namespace Theories.Montague.Sentence.InformationStructure

-- Alternative Sets (Rooth-style Focus Semantics)

/--
An alternative set: a value together with its contextually relevant alternatives.

In focus semantics, every expression has:
- An ordinary semantic value
- A focus semantic value (set of alternatives)

The alternatives are determined by what's focused/contrasted.
-/
structure Alternatives (α : Type) where
  /-- The actual/chosen value -/
  actual : α
  /-- The set of alternatives (including actual) -/
  alternatives : List α
  /-- The actual value is among the alternatives -/
  actual_mem : actual ∈ alternatives := by simp
  deriving Repr

/-- Singleton alternative set (no contrast) -/
def Alternatives.singleton {α : Type} (x : α) : Alternatives α :=
  ⟨x, [x], List.Mem.head _⟩

/-- Create alternatives from actual + others -/
def Alternatives.mk' {α : Type} (actual : α) (others : List α) : Alternatives α :=
  ⟨actual, actual :: others, List.Mem.head _⟩

-- Question Under Discussion (QUD)

/--
A Question Under Discussion, represented as a partition of the context set.

A QUD like "Who ate the beans?" partitions possible worlds into:
- Worlds where John ate the beans
- Worlds where Mary ate the beans
- ...

Each cell of the partition is a possible complete answer.
-/
structure QUD (World : Type) where
  /-- The cells of the partition (possible answers) -/
  cells : List (World → Prop)
  -- The cells are mutually exclusive (simplified: we don't enforce this)

/--
A QUD can be represented as a λ-abstract over the "questioned" position.

"Who ate the beans?" ↝ λx. ate(x, beans)

This connects to the theme: the theme IS the QUD as a property.
-/
structure QUDAbstract (Domain Entity : Type) where
  /-- The domain of quantification (who/what) -/
  domain : List Domain
  /-- The open proposition -/
  property : Domain → Prop

/--
A complete answer to a QUD: specifies which cell is true.
-/
structure Answer (World : Type) where
  qud : QUD World
  /-- Index of the true cell -/
  cellIndex : Nat
  /-- The index is valid -/
  valid : cellIndex < qud.cells.length := by simp

-- Theme and Rheme

/--
Theme: what the utterance is about (the "topic" or "given" part).

The theme:
- Presupposes a QUD (set of alternatives)
- Is often prosodically marked (L+H* LH% in English)
- Corresponds to the λ-abstract in structured meanings

Example: In "FRED ate the beans" (answering "Who ate the beans?"),
the theme is "λx. ate(x, beans)" or informally "_ ate the beans".
-/
structure Theme (P : Type) where
  /-- The thematic content (often a property/λ-abstract) -/
  content : P
  /-- Whether the theme is prosodically marked -/
  marked : Bool := false

/--
Rheme: what's asserted about the theme (the "comment" or "new" part).

The rheme:
- Restricts the QUD alternatives to one
- Is often prosodically marked (H* LL% in English)
- Provides the "answer" to the implicit question

Example: In "FRED ate the beans", the rheme is "Fred".
-/
structure Rheme (P : Type) where
  /-- The rhematic content -/
  content : P
  /-- Whether the rheme is prosodically marked -/
  marked : Bool := true

-- Focus and Background

/--
Focus: the contrasted element(s) within theme or rheme.

Focus is marked by pitch accent and:
- Evokes alternatives (Rooth)
- Associates with focus-sensitive particles (only, even)
- Determines the "question" being answered

Focus is orthogonal to theme/rheme: both can contain focused elements.
-/
structure Focus (α : Type) where
  /-- The focused element -/
  focused : α
  /-- Alternatives evoked by focus -/
  alternatives : Alternatives α

/--
Background: the non-focused, given material.

Background material is:
- Not pitch-accented
- Presupposed to be salient in context
- Often recoverable/predictable
-/
structure Background (α : Type) where
  /-- The background elements -/
  elements : List α

-- Information Structure Partition

/--
A complete Information Structure analysis of an utterance.

Partitions the utterance into:
- Theme vs. Rheme (what's talked about vs. what's said)
- Focus vs. Background (within each)
-/
structure InfoStructure (P : Type) where
  /-- The theme (topic, λ-abstract, presupposed QUD) -/
  theme : Theme P
  /-- The rheme (comment, answer, assertion) -/
  rheme : Rheme P
  /-- Focused elements (evoking alternatives) -/
  foci : List P := []
  /-- Background elements (given) -/
  background : List P := []

-- Information Structure Interface (Typeclass)

/--
Typeclass for theories that provide Information Structure.

Implementations:
- CCG/Intonation: prosodic realization
- (Future) Syntactic approaches, discourse models

The key insight: different surface forms (derivations, prosody) can
map to the same propositional content but different Information Structures.
-/
class HasInfoStructure (D : Type) (P : Type) where
  /-- Extract Information Structure from a derivation/form -/
  infoStructure : D → InfoStructure P

/--
Typeclass for computing alternative sets from focus.

This is the core of Rooth-style focus semantics: focused elements
evoke alternatives of the same semantic type.
-/
class HasAlternatives (α : Type) where
  /-- Compute alternatives for a focused element -/
  alternatives : α → List α

-- QUD-Based Pragmatics Interface

/--
Connection between Information Structure and pragmatics (RSA).

The QUD determines:
- What counts as a relevant/informative answer
- Which interpretations are preferred
- Felicity conditions for focus
-/
class QUDSemantics (S : Type) where
  World : Type
  Utterance : Type
  P : Type

  /-- The current QUD stack (Roberts-style) -/
  QUDStack : Type

  /-- Extract the QUD that an utterance addresses -/
  addressedQUD : Utterance → QUDStack → Option (QUD World)

  /-- Check if a proposition answers a QUD -/
  answers : P → QUD World → Bool

  /-- Informativity of an utterance relative to a QUD -/
  informativity : Utterance → QUD World → Float

  /-- Felicity: theme must match QUD -/
  felicitous : InfoStructure P → QUD World → Bool

-- Congruence (Question-Answer Congruence)

/--
Question-Answer Congruence: the focus of an answer must match the QUD.

"Who ate the beans?" requires focus on the subject:
- ✓ "FRED ate the beans" (focus matches wh-word)
- ✗ "Fred ate the BEANS" (focus mismatch)

This is enforced by the theme presupposing the right QUD.
-/
def congruent {P World : Type} (info : InfoStructure P) (_qud : QUD World) : Bool :=
  -- Simplified: placeholder
  -- Full version would check focus-QUD alignment via QUDSemantics
  true  -- TODO: implement properly

end InformationStructure
