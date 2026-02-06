import Linglib.Theories.DependencyGrammar.Basic

/-!
# Non-Projective Dependencies

Extension of the DG module for non-projective (crossing) dependencies,
which handle long-distance phenomena (extraction, wh-movement, scrambling).

In projective dependency trees, no arcs cross. Non-projective dependencies
arise when an element is displaced from its canonical position, creating
crossing arcs — the DG analogue of movement/SLASH/composition.

## Connection to Müller (2013)

Müller §2.3: non-projective dependencies in DG correspond to:
- Internal Merge in Minimalism (movement)
- Head-Filler Schema in HPSG (SLASH mechanism)
- Composition in CCG (function composition for extraction)

## References

- Hudson, R. (1984, 1990, 2007). Word Grammar.
- Nivre, J. (2006). Constraints on Non-Projective Dependency Parsing.
- Müller, S. (2013). Unifying Everything. Language 89(4):920–950.
-/

namespace DepGrammar

/-! ## Non-projectivity detection -/

/-- Check whether two dependencies cross (are non-projective with respect to each other).

Two dependencies cross iff their spans overlap without one containing the other.
Specifically, dep1 (h1, d1) crosses dep2 (h2, d2) iff the intervals [min(h1,d1), max(h1,d1)]
and [min(h2,d2), max(h2,d2)] overlap but neither contains the other. -/
def depsCross (d1 d2 : Dependency) : Bool :=
  if d1 == d2 then false
  else if d1.headIdx == d2.headIdx then false
  else
    let (min1, max1) := (min d1.headIdx d1.depIdx, max d1.headIdx d1.depIdx)
    let (min2, max2) := (min d2.headIdx d2.depIdx, max d2.headIdx d2.depIdx)
    -- They cross iff they overlap but neither contains the other
    ¬(max1 <= min2 || max2 <= min1 ||
      (min1 <= min2 && max2 <= max1) ||
      (min2 <= min1 && max1 <= max2))

/-- Get all non-projective (crossing) dependencies from a tree. -/
def nonProjectiveDeps (t : DepTree) : List Dependency :=
  t.deps.filter λ d1 =>
    t.deps.any λ d2 => depsCross d1 d2

/-- Check whether a specific dependency is non-projective in a tree. -/
def isNonProjectiveDep (t : DepTree) (d : Dependency) : Bool :=
  t.deps.any λ d2 => depsCross d d2

/-! ## Filler-gap dependencies -/

/-- A filler-gap dependency is a non-projective dependency that models extraction.

In DG, when a wh-phrase is fronted ("Who did you see __?"), the dependency
from the verb to the wh-phrase crosses the dependencies within the clause,
creating a non-projective arc.

This is the DG analogue of:
- Minimalism: Internal Merge (movement of wh-phrase)
- HPSG: SLASH feature propagation + Head-Filler discharge
- CCG: function composition enabling long-distance combination -/
structure FillerGapDep where
  /-- The underlying dependency -/
  dep : Dependency
  /-- The tree containing this dependency -/
  tree : DepTree
  /-- The dependency is part of the tree -/
  inTree : dep ∈ tree.deps
  /-- The dependency is non-projective (crosses other arcs) -/
  nonProj : isNonProjectiveDep tree dep = true

/-- Check whether a tree has any filler-gap (non-projective) dependencies. -/
def hasFillerGap (t : DepTree) : Bool :=
  (nonProjectiveDeps t).length > 0

/-! ## Well-formedness with non-projectivity -/

/-- A relaxed well-formedness check that allows non-projective dependencies.

Standard `isWellFormed` from Basic.lean requires projectivity.
This version drops the projectivity constraint, enabling trees with
long-distance dependencies. -/
def isWellFormedNonProj (t : DepTree) : Bool :=
  hasUniqueHeads t &&
  isAcyclic t &&
  checkSubjVerbAgr t &&
  checkDetNounAgr t &&
  checkVerbSubcat t

/-- Non-projective well-formedness implies all structural constraints
except projectivity hold. -/
theorem nonProj_implies_structural (t : DepTree) :
    isWellFormedNonProj t = true →
    hasUniqueHeads t = true ∧ isAcyclic t = true := by
  intro h
  unfold isWellFormedNonProj at h
  -- isWellFormedNonProj = hasUniqueHeads && isAcyclic && checkSubjVerbAgr && checkDetNounAgr && checkVerbSubcat
  revert h
  cases hasUniqueHeads t <;> cases isAcyclic t <;> simp [Bool.and]

/-- Projective well-formedness implies non-projective well-formedness.

A projective tree trivially satisfies the relaxed constraints. -/
theorem projective_implies_nonProj_wf (t : DepTree) :
    isWellFormed t = true → isWellFormedNonProj t = true := by
  unfold isWellFormed isWellFormedNonProj
  intro h
  revert h
  cases hasUniqueHeads t <;> cases isAcyclic t <;> cases isProjective t <;>
    cases checkSubjVerbAgr t <;> cases checkDetNounAgr t <;> cases checkVerbSubcat t <;>
    simp [Bool.and]

/-! ## Example: wh-extraction -/

/-- Example: non-projective dependency from topicalization.

"Beans, I know John likes"
Word order: beans(0) I(1) know(2) John(3) likes(4)
Dependencies:
- subj: know(2) → I(1)        — projective: span [1,2]
- comp: know(2) → likes(4)    — projective: span [2,4]
- subj: likes(4) → John(3)    — projective: span [3,4]
- obj: likes(4) → beans(0)    — NON-PROJECTIVE: span [0,4]

Arc obj(4→0) span [0,4] and arc subj(2→1) span [1,2]:
- [1,2] is contained within [0,4] → not crossing per containment check.

Actually the crossing happens between obj(4→0) span [0,4] and comp(2→4) span [2,4]:
- min1=0, max1=4, min2=2, max2=4
- Neither contains the other? max1=max2=4, min1=0 < min2=2
- [0,4] contains [2,4] → not crossing.

For TRUE crossing we need: arc from 1→3 and arc from 2→4.
Consider scrambling: word order a(0) b(1) c(2) d(3)
- dep 0→2 (span [0,2]) and dep 1→3 (span [1,3])
- min1=0, max1=2, min2=1, max2=3
- Neither contains the other: 0 ≤ 1 but 2 < 3; 1 > 0 so [1,3] doesn't contain [0,2]
- This is genuine crossing! -/
def nonProjectiveTree : DepTree :=
  { words := [ ⟨"A", .NOUN, {}⟩, ⟨"B", .VERB, {}⟩, ⟨"C", .NOUN, {}⟩, ⟨"D", .VERB, {}⟩ ]
  , deps := [ ⟨0, 2, .obj⟩, ⟨1, 3, .obj⟩ ]
  , rootIdx := 0 }

/-- The example tree has non-projective (crossing) dependencies. -/
example : hasFillerGap nonProjectiveTree = true := by native_decide

/-- The example tree is NOT projective (per Basic.lean's `isProjective`). -/
example : isProjective nonProjectiveTree = false := by native_decide

end DepGrammar
