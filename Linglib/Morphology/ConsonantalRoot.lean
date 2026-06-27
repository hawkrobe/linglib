import Linglib.Phonology.OCP

/-!
# Consonantal Roots

Single source of truth for the Semitic-style notion of a *consonantal root*:
an ordered melody of segments stored independently of vocalization or template.

The segment type `α` is parametric. Studies of Tarifit Berber may instantiate
`α := Phonology.SonorityClass` (sonority-class roots, used by
[afkir-zellou-2025]); studies of Hebrew or Amharic typically instantiate
`α := String` for IPA symbols.

Theory-laden questions about the cognitive reality of roots
(e.g. Ussishkin 2000, Bat-El 2003) are orthogonal to the data type itself —
`Root` is a sequence; what status linguistic theory gives that sequence is a
separate matter, parameterized at the study level.

## Namespace separation

`Morphology.Root` (this file): a *consonantal* melody, a morphological
primitive (the underlying form of a morpheme).
The root-level `Root` (`Semantics/Lexical/Roots/Basic.lean`):
a bundle of `LexEntailment` atoms in the [beavers-koontz-garboden-2020]
sense — same English word, different concept.
`Root.Profile` (`Semantics/Lexical/Roots/Profile.lean`): semantic
quality dimensions on a verb root — orthogonal to both.
-/

namespace Morphology

/-- A consonantal root: an ordered list of segments. Polymorphic in the
    segment type so that fragments may pick the granularity they need
    (sonority class, IPA symbol, full feature matrix). -/
structure Root (α : Type) where
  segments : List α
  deriving Repr, DecidableEq

namespace Root

variable {α : Type}

/-- The number of root segments. -/
def arity (r : Root α) : Nat := r.segments.length

/-- Position `i` is the *final* root position. -/
def isFinal (r : Root α) (i : Nat) : Bool := i + 1 == r.arity

/-- Position `i` is *nonfinal* (some position strictly past it exists).
    Used by *Misalignment ([faust-2026] (2)). -/
def isNonfinal (r : Root α) (i : Nat) : Bool := decide (i + 1 < r.arity)

/-- A root with exactly two segments (e.g. √qt → QaTaT-template
    biradicals in Hebrew, [mccarthy-1981]). -/
def biradical (r : Root α) : Bool := r.arity == 2

/-- A root with exactly three segments (the unmarked Semitic case). -/
def triradical (r : Root α) : Bool := r.arity == 3

/-- A root with exactly four segments (e.g. quadriliteral verbs). -/
def quadriradical (r : Root α) : Bool := r.arity == 4

/-- The last segment of the root, if any. -/
def finalSegment (r : Root α) : Option α := r.segments.getLast?

/-- The segment at position `i`, if in range. -/
def segmentAt (r : Root α) (i : Nat) : Option α := r.segments[i]?

/-- **Root-level OCP** ([mccarthy-1981], [faust-2026]): a consonantal root has no two
    adjacent identical segments. Segment-level and theory-neutral — it commits to no
    tier projection or feature decomposition (stronger tier-relative variants go
    through `OCP.IsCleanOn`). Definitionally the segment tier being
    `OCP.IsClean`. -/
def IsOCPClean [DecidableEq α] (r : Root α) : Prop :=
  OCP.IsClean r.segments

instance instDecidablePredIsOCPClean [DecidableEq α] :
    DecidablePred (IsOCPClean (α := α)) :=
  fun r => inferInstanceAs (Decidable (OCP.IsClean r.segments))

end Root
end Morphology
