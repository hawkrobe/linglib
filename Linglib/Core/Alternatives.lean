/-
# Core.Alternatives

Alternative sets for focus semantics and information structure.

## Overview

Every expression in Rooth-style focus semantics has two semantic values:
- An ordinary semantic value (the actual denotation)
- A focus semantic value (set of alternatives)

This module provides the foundational types for representing these
two-dimensional meanings, used across focus theory, information structure,
and RSA implementations.

## References

- Rooth, M. (1992). A Theory of Focus Interpretation. NLS 1: 75-116.
- Kratzer, A. & Selkirk, E. (2020). Deconstructing Information Structure.
-/

namespace Core.Alternatives

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

/--
Typeclass for computing alternative sets from focus.

This is the core of Rooth-style focus semantics: focused elements
evoke alternatives of the same semantic type.
-/
class HasAlternatives (α : Type) where
  /-- Compute alternatives for a focused element -/
  alternatives : α → List α

/-- Two-dimensional meaning in Alternatives Semantics.
    Every expression has an O-value and an A-value.

    Kratzer & Selkirk (2020) §3, §8. -/
structure AltMeaning (α : Type) where
  /-- O(rdinary)-value: the actual denotation -/
  oValue : α
  /-- A(lternatives)-value: the set of alternatives (including oValue) -/
  aValue : List α

/-- The O-value of a non-featured expression equals its ordinary denotation.
    The A-value of a non-featured expression is a singleton containing
    its O-value (no alternatives evoked). -/
def AltMeaning.unfeatured {α : Type} (x : α) : AltMeaning α :=
  { oValue := x, aValue := [x] }

end Core.Alternatives
