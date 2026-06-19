import Linglib.Phonology.OCP
import Linglib.Core.Computability.Subregular.ForbiddenPairs

/-!
# Consonantal Roots

Single source of truth for the Semitic-style notion of a *consonantal root*:
an ordered melody of segments stored independently of vocalization or template.

The segment type `α` is parametric. Studies of Tarifit Berber may instantiate
`α := Phonology.Syllable.NatClass` (sonority-class roots, used by
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

/-- Root-level OCP ([mccarthy-1981], [faust-2026]): a root
    has no adjacent identical segments. The predicate is segment-level
    and theory-neutral — it does not commit to any particular tier
    projection or feature decomposition. Specific theories may impose
    stronger OCP variants on derived tiers (place, voicing, etc.) via
    `Phonology.Constraints.mkOCP`. -/
def satisfiesOCP [BEq α] (r : Root α) : Bool := adjDupCount r.segments == 0

/-- `adjDupCount` is the substrate `countAdjacent (· = ·)` on the segment list;
    `LawfulBEq` reconciles `==` with `=`. -/
theorem adjDupCount_eq_countAdjacent [DecidableEq α] [LawfulBEq α] (xs : List α) :
    adjDupCount xs = Core.Computability.Subregular.countAdjacent (· = ·) xs := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b rest =>
      simp only [adjDupCount, Core.Computability.Subregular.countAdjacent, ih]
      by_cases h : a = b <;> simp [h]

/-- **Root-level OCP is `Phonology.OCP.IsClean`**: a root satisfies the
    segment-level OCP iff its segment tier is OCP-clean. Routes the hand-rolled
    `adjDupCount` through the unified predicate ([faust-2026]'s consumer). -/
theorem satisfiesOCP_iff_isClean [DecidableEq α] [LawfulBEq α] (r : Root α) :
    satisfiesOCP r = true ↔ Phonology.OCP.IsClean r.segments := by
  unfold satisfiesOCP
  rw [beq_iff_eq, adjDupCount_eq_countAdjacent,
    Core.Computability.Subregular.countAdjacent_eq_zero_iff_isChain]
  rfl

end Root
end Morphology
