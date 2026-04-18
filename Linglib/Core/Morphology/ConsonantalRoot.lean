/-!
# Consonantal Roots

Single source of truth for the Semitic-style notion of a *consonantal root*:
an ordered melody of segments stored independently of vocalization or template.

The segment type `α` is parametric. Studies of Tarifit Berber may instantiate
`α := Phonology.Syllable.NatClass` (sonority-class roots, used by
@cite{afkir-zellou-2025}); studies of Hebrew or Amharic typically instantiate
`α := String` for IPA symbols.

Theory-laden questions about the cognitive reality of roots
(e.g. Ussishkin 2000, Bat-El 2003) are orthogonal to the data type itself —
`Root` is a sequence; what status linguistic theory gives that sequence is a
separate matter, parameterized at the study level.

## Namespace separation

`Core.Morphology.Root` (this file): a *consonantal* melody, a morphological
primitive (the underlying form of a morpheme).
`Semantics.Verb.Roots.Root` (`Theories/Semantics/Verb/Roots/Basic.lean`):
a bundle of `LexEntailment` atoms in the @cite{beavers-koontz-garboden-2020}
sense — same English word, different concept.
`Core.Lexical.RootFeatures` (`Core/Lexical/RootFeatures.lean`): semantic
quality dimensions on a verb root — orthogonal to both.
-/

namespace Core.Morphology

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
    Used by *Misalignment (@cite{faust-2026} (2)). -/
def isNonfinal (r : Root α) (i : Nat) : Bool := decide (i + 1 < r.arity)

/-- A root with exactly two segments (e.g. √qt → QaTaT-template
    biradicals in Hebrew, @cite{mccarthy-1981}). -/
def biradical (r : Root α) : Bool := r.arity == 2

/-- A root with exactly three segments (the unmarked Semitic case). -/
def triradical (r : Root α) : Bool := r.arity == 3

/-- A root with exactly four segments (e.g. quadriliteral verbs). -/
def quadriradical (r : Root α) : Bool := r.arity == 4

/-- The last segment of the root, if any. -/
def finalSegment (r : Root α) : Option α := r.segments.getLast?

/-- The segment at position `i`, if in range. -/
def segmentAt (r : Root α) (i : Nat) : Option α := r.segments[i]?

/-- Auxiliary: count adjacent identical segments in a root.
    A root with no adjacent duplicates returns `0`. Used by
    `satisfiesOCP` and by templatic-morphology studies that need
    to check root-level OCP independently of any specific tier
    projection (cf. `Phonology.Constraints.adjacentIdentical`,
    which is the tier-projection-level analogue used inside OT
    constraint constructors). -/
def adjDupCount [BEq α] : List α → Nat
  | [] | [_] => 0
  | a :: b :: rest => (if a == b then 1 else 0) + adjDupCount (b :: rest)

/-- Root-level OCP (@cite{mccarthy-1981}, @cite{faust-2026}): a root
    has no adjacent identical segments. The predicate is segment-level
    and theory-neutral — it does not commit to any particular tier
    projection or feature decomposition. Specific theories may impose
    stronger OCP variants on derived tiers (place, voicing, etc.) via
    `Phonology.Constraints.mkOCP`. -/
def satisfiesOCP [BEq α] (r : Root α) : Bool := adjDupCount r.segments == 0

end Root
end Core.Morphology
