/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.OCP

/-!
# Consonantal roots

A **consonantal root** is an ordered melody of segments stored independently
of vocalization or template — the nonconcatenative counterpart of a linear
`Morph`. The segment type `α` is parametric: sonority-class roots instantiate
`α := Phonology.Sonority.Class` ([afkir-zellou-2025]), IPA-symbol roots
`α := String`. Debates over the cognitive reality of roots are orthogonal to
the data type — what status a theory gives the sequence is parameterized at
the study level. In autosegmental terms a root is an unlinked melody on the
consonantal tier; the canonical injection into
`Phonology/Autosegmental/Melody.lean` awaits its first root-and-pattern
consumer, as does a vocalism sibling (the same melody shape on the vowel
tier).

## Namespace separation

Owner-relative roots coexist: the top-level root is a contentful morph
(`Morphology/Root/Basic.lean`, under whose definition consonantal skeletons
are explicitly *not* roots); `Morphology.ConsonantalRoot` (this file) is the
*consonantal melody*; `Morphology.DM.Root` is the abstract acategorial
terminal; `Panagiotidis2015.RootFamily` records a category-neutral lexical
root with its category-stamped derivatives; `Verb.Root`
(`Semantics/Verb/Root/`) is the *lexical-semantic* root. No identification
between them is substrate — homs live in the studies that assert them.
-/

namespace Morphology

/-- A consonantal root: an ordered list of segments. Polymorphic in the
segment type so that fragments may pick the granularity they need (sonority
class, IPA symbol, full feature matrix). -/
structure ConsonantalRoot (α : Type*) where
  /-- The root segments, in order. -/
  segments : List α
  deriving Repr, DecidableEq

namespace ConsonantalRoot

variable {α : Type*}

/-- The number of root segments. -/
def arity (r : ConsonantalRoot α) : Nat := r.segments.length

/-- Position `i` is the *final* root position. -/
def IsFinal (r : ConsonantalRoot α) (i : Nat) : Prop := i + 1 = r.arity

instance (r : ConsonantalRoot α) (i : Nat) : Decidable (r.IsFinal i) :=
  inferInstanceAs (Decidable (_ = _))

/-- Position `i` is *nonfinal* (some position strictly past it exists).
    Used by *Misalignment ([faust-2026] (2)). -/
def IsNonfinal (r : ConsonantalRoot α) (i : Nat) : Prop := i + 1 < r.arity

instance (r : ConsonantalRoot α) (i : Nat) : Decidable (r.IsNonfinal i) :=
  inferInstanceAs (Decidable (_ < _))

/-- A root with exactly two segments (e.g. √qt → QaTaT-template
    biradicals in Hebrew, [mccarthy-1981]). -/
def Biradical (r : ConsonantalRoot α) : Prop := r.arity = 2

/-- A root with exactly three segments (the unmarked Semitic case). -/
def Triradical (r : ConsonantalRoot α) : Prop := r.arity = 3

/-- A root with exactly four segments (e.g. quadriliteral verbs). -/
def Quadriradical (r : ConsonantalRoot α) : Prop := r.arity = 4

instance (r : ConsonantalRoot α) : Decidable r.Biradical := inferInstanceAs (Decidable (_ = _))
instance (r : ConsonantalRoot α) : Decidable r.Triradical := inferInstanceAs (Decidable (_ = _))
instance (r : ConsonantalRoot α) : Decidable r.Quadriradical := inferInstanceAs (Decidable (_ = _))

/-- The last segment of the root, if any. -/
def finalSegment (r : ConsonantalRoot α) : Option α := r.segments.getLast?

/-- The segment at position `i`, if in range. -/
def segmentAt (r : ConsonantalRoot α) (i : Nat) : Option α := r.segments[i]?

/-- **Root-level OCP** ([mccarthy-1981], [faust-2026]): a consonantal root has no two
    adjacent identical segments. Segment-level and theory-neutral — it commits to no
    tier projection or feature decomposition (stronger tier-relative variants go
    through `OCP.IsCleanOn`). Definitionally the segment tier being
    `OCP.IsClean`. -/
def IsOCPClean [DecidableEq α] (r : ConsonantalRoot α) : Prop :=
  OCP.IsClean r.segments

instance instDecidablePredIsOCPClean [DecidableEq α] :
    DecidablePred (IsOCPClean (α := α)) :=
  fun r => inferInstanceAs (Decidable (OCP.IsClean r.segments))

end ConsonantalRoot
end Morphology
