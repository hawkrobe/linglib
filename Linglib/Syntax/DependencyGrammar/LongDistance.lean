import Linglib.Syntax.DependencyGrammar.Projection

/-!
# Long-distance dependencies in UD enhanced graphs

Implements the gap-filling step of Universal Dependencies' enhanced dependency
graphs ([de-marneffe-nivre-2019]): the basic tree obeys a unique-heads
constraint that loses the predicate–argument relation across a filler–gap
configuration, and the enhanced graph recovers it by adding an explicit edge
from the gap-host word to the filler.

## Main declarations

* `GapType` — the four core UD argument positions a missing element may fill
  (subject, object, indirect object, oblique).
* `gapToDepRel` — the UD `DepRel` corresponding to a `GapType`.
* `fillGap` — enhanced-edge construction: produce a `DepGraph` from a basic
  `DepTree` by appending an edge that records gap-filling.
* `extractionLabel` — recover the gap-type label at a node by diffing the basic
  tree against the enhanced graph.
* `checkNoIslandViolation` — coarse modifier/conjunct heuristic over a list of
  gap sites; not a full Ross-1967 inventory.
* `isLDWellFormed` — structural well-formedness plus the coarse island
  heuristic plus filler-licensing.

## Implementation notes

* The `Bool`-valued predicates follow `DepGrammar.isWellFormed`'s substrate
  convention; converting them to `Prop` + `Decidable` is a substrate-wide
  refactor not done here.
* `hasGapInModifierOrConjunct` is deliberately coarse: it flags any gap whose
  direct head is `nmod` or `conj`. It does *not* recognise CNPC, CSC, adjunct,
  or subject islands. Richer island handling lives in
  `Syntax/DependencyGrammar/Formal/Islands.lean`.
* Word Grammar ([hudson-2010]) handles the same data with a structurally
  analogous *hopping* mechanism; GPSG ([gazdar-1981]) uses SLASH-feature
  percolation. Neither is implemented here.

## Todo

* Consume the Ross-1967 `ConstraintType` enum (`Studies/Ross1967.lean`) here
  and in `Formal/Islands.lean` so the two files share a single inventory.
* Build a cross-framework `FillerGap` abstraction so the RSRL `GAP`
  (`Syntax/HPSG/Construction`), `LongDistance.GapType`, and Minimalist movement
  labels all specialise a shared interface.
-/

namespace DepGrammar.LongDistance

open DepGrammar

/-! ### Gap types and the UD relation map -/

/-- Argument position of the missing element: the four core UD argument
relations subject, object, indirect object, and oblique. -/
inductive GapType where
  | subjGap
  | objGap
  | iobjGap
  | oblGap
  deriving Repr, DecidableEq

/-- The UD `DepRel` corresponding to a `GapType`. -/
@[simp] def gapToDepRel : GapType → UD.DepRel
  | .subjGap => .nsubj
  | .objGap  => .obj
  | .iobjGap => .iobj
  | .oblGap  => .obl

/-! ### Enhanced-edge construction -/

/-- Add a single enhanced edge to `t`: the filler becomes a dependent of the
gap host with the UD relation corresponding to `gapType`. -/
def fillGap (t : DepTree) (fillerIdx gapHostIdx : Nat) (gapType : GapType) :
    DepGraph :=
  { words := t.words
    deps  := t.deps ++ [⟨gapHostIdx, fillerIdx, gapToDepRel gapType⟩]
    rootIdx := t.rootIdx }

/-- Recover the gap-type label at `nodeIdx` by diffing `basic` against
`enhanced`: returns the first enhanced-only argument-shaped edge's `GapType`,
or `none`. -/
def extractionLabel (basic : DepTree) (enhanced : DepGraph) (nodeIdx : Nat) :
    Option GapType :=
  let enhancedOnly := enhanced.deps.filter λ d =>
    d.depIdx == nodeIdx &&
    !(basic.deps.any λ bd =>
        bd.depIdx == d.depIdx && bd.headIdx == d.headIdx &&
        bd.depType == d.depType)
  enhancedOnly.head?.bind λ d =>
    match d.depType with
    | .nsubj => some .subjGap
    | .obj   => some .objGap
    | .iobj  => some .iobjGap
    | .obl   => some .oblGap
    | _      => none

/-! ### Island heuristic and well-formedness -/

/-- Coarse check: does the word at `gapIdx` head an `nmod` or `conj` relation.
This does *not* recognise any of the four classical Ross-1967 islands. -/
def hasGapInModifierOrConjunct (t : DepTree) (gapIdx : Nat) : Bool :=
  t.deps.any λ d =>
    (d.depType == .nmod || d.depType == .conj) && d.depIdx == gapIdx

/-- No gap is reported inside the coarse modifier/conjunct heuristic. -/
def checkNoIslandViolation (t : DepTree) (gaps : List (Nat × Nat × GapType)) :
    Bool :=
  gaps.all λ (_, gapHostIdx, _) => !hasGapInModifierOrConjunct t gapHostIdx

/-- Combined well-formedness for trees with long-distance gaps: substrate
tree-level checks (minus `checkVerbSubcat`, since LD trees inherently have
argument gaps), the coarse island heuristic, and filler-licensing (wh-word,
leftward topicalization, or relative-clause head). -/
def isLDWellFormed (t : DepTree) (gaps : List (Nat × Nat × GapType)) : Bool :=
  hasUniqueHeads t &&
  isAcyclic t &&
  isProjective t &&
  checkSubjVerbAgr t &&
  checkDetNounAgr t &&
  checkNoIslandViolation t gaps &&
  gaps.all λ (fillerIdx, _, _) =>
    match t.words[fillerIdx]? with
    | some w =>
      w.features.isWh || fillerIdx < t.rootIdx ||
        t.deps.any λ d => d.headIdx == fillerIdx && d.depType == .acl
    | none => false

end DepGrammar.LongDistance
