import Linglib.Core.Dependency.Projection

/-!
# Long-distance dependencies in UD enhanced graphs
@cite{de-marneffe-nivre-2019}

Implements the gap-filling step of Universal Dependencies' enhanced
dependency graphs (@cite{de-marneffe-nivre-2019}, §4.2 and Figure 9):
the basic dependency tree obeys a unique-heads constraint that loses the
predicate-argument relation across a filler-gap configuration, and the
enhanced graph recovers it by adding an explicit edge from the gap-host
word to the filler, producing a directed graph (not a tree) in which a
word may have multiple incoming arcs.

Word Grammar (@cite{hudson-2010}, §7.6.4-5) handles the same data with a
structurally analogous "hopping" mechanism: the extracted element bears an
*extractee* dependency from each intermediate verb in the chain, in
addition to the grammatical relation (e.g. `object`) it holds of the
deepest verb. This file follows the UD presentation rather than Hudson's
extractee-and-`isA` machinery; cf. Hudson 2010 Figure 7.19 / 7.21 for the
WG analogue.

The earlier GPSG approach (@cite{gazdar-1981}) handles unbounded
dependencies via SLASH-feature percolation through phrase-structure
nodes — a categorially distinct mechanism not implemented here, and the
historical source of HPSG's `SlashValue` apparatus. The file is named
"LongDistance" rather than "SLASH" precisely because the data structure
is a dependency graph, not a slash-augmented constituent category.

## Main declarations

* `GapType` — the four core UD argument positions a missing element may
  fill (subject, object, indirect object, oblique).
* `gapToDepRel` — the UD `DepRel` corresponding to a `GapType`.
* `fillGap`, `fillGaps` — enhanced-edge construction: produce a `DepGraph`
  from a basic `DepTree` by appending edges that record gap-filling.
* `extractionLabel` — recover the gap-type label at a node by diffing the
  basic tree against the enhanced graph.
* `hasGapInModifierOrConjunct`, `checkNoIslandViolation` — a coarse
  modifier/conjunct heuristic; does *not* implement Ross 1967's full
  island inventory.
* `isLDWellFormed` — structural well-formedness plus the coarse island
  heuristic plus filler-licensing.

## Implementation notes

* The `Bool`-valued predicates follow `Core.Dependency.Projection`'s
  convention of returning `Bool`; converting them to `Prop` + `Decidable`
  is a substrate-wide refactor not done here.
* `hasGapInModifierOrConjunct` is a deliberately coarse check: it flags
  any gap whose direct head is `nmod` or `conj`. It does *not* correctly
  recognize CNPC (which requires `acl` inside a nominal), CSC (which bans
  extraction *out of* a single conjunct), adjunct islands (`advcl`), or
  subject islands (`csubj`). The predicate is named to reflect what it
  actually checks. Richer island handling for dependency grammar lives
  in `DependencyGrammar/Formal/Islands.lean` (@cite{osborne-2019}), which
  builds a finer taxonomy on top of rising catenae.
* `GapType` covers only the four core UD argument positions (`nsubj`,
  `obj`, `iobj`, `obl`). Possessor extraction (`nmod:poss`), parasitic
  gaps, ATB extraction, and pied-piping are out of scope.
* Filler licensing in `isLDWellFormed` recognizes wh-fronting,
  topicalization (heuristic: `fillerIdx < rootIdx`), and relative-clause
  heads (via `acl`). Clefts, pseudo-clefts, reduced relatives, and
  tough-movement are out of scope.

## Todo

* Replace `hasGapInModifierOrConjunct` with structurally correct island
  checks (CNPC via `acl` under a nominal, CSC via "out of a single
  conjunct", adjunct via `advcl`, subject via `csubj`).
* Promote `Phenomena.Islands.ConstraintType` (the canonical Ross-1967
  enum) to substrate so this file and `Formal/Islands.lean` can share it
  instead of each defining a private subset.
* Build a cross-framework `FillerGap` abstract layer so `HPSG.SlashValue`,
  `LongDistance.GapType`, and Minimalist movement labels all specialize a
  shared interface.
-/

namespace DepGrammar.LongDistance

open DepGrammar

/-! ### Gap types and the UD relation map -/

/-- Argument position of the missing element: the four core UD argument
relations subject (`nsubj`), object (`obj`), indirect object (`iobj`), and
oblique (`obl`). -/
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

/-- Add a single enhanced edge to `t`, producing a `DepGraph`: the filler
becomes a dependent of the gap-host with the UD relation corresponding to
`gapType`. Matches the construction in @cite{de-marneffe-nivre-2019}
Figure 9. -/
def fillGap (t : DepTree) (fillerIdx gapHostIdx : Nat) (gapType : GapType) :
    DepGraph :=
  { words := t.words
    deps  := t.deps ++ [⟨gapHostIdx, fillerIdx, gapToDepRel gapType⟩]
    rootIdx := t.rootIdx }

/-- Add multiple enhanced edges at once. -/
def fillGaps (t : DepTree) (gaps : List (Nat × Nat × GapType)) : DepGraph :=
  let newDeps := gaps.map λ (filler, host, gtype) =>
    (⟨host, filler, gapToDepRel gtype⟩ : Dependency)
  { words := t.words
    deps  := t.deps ++ newDeps
    rootIdx := t.rootIdx }

/-- Recover the gap-type label at `nodeIdx` by diffing `basic` against
`enhanced`: returns the first enhanced-only argument-shaped edge's
`GapType` interpretation, or `none`. -/
def extractionLabel (basic : DepTree) (enhanced : DepGraph) (nodeIdx : Nat) :
    Option GapType :=
  let enhancedOnly := enhanced.deps.filter λ d=>
    d.depIdx == nodeIdx &&
    !(basic.deps.any λ bd=>
        bd.depIdx == d.depIdx && bd.headIdx == d.headIdx &&
        bd.depType == d.depType)
  enhancedOnly.head?.bind λ d=>
    match d.depType with
    | .nsubj => some .subjGap
    | .obj   => some .objGap
    | .iobj  => some .iobjGap
    | .obl   => some .oblGap
    | _      => none

/-! ### Island heuristic and well-formedness -/

/-- Coarse check: does the word at `gapIdx` head an `nmod` or `conj`
relation. This does *not* correctly recognize any of the four classical
Ross-1967 islands; see the module docstring's Todo. -/
def hasGapInModifierOrConjunct (t : DepTree) (gapIdx : Nat) : Bool :=
  t.deps.any λ d=>
    (d.depType == .nmod || d.depType == .conj) && d.depIdx == gapIdx

/-- No gap is reported inside the coarse modifier/conjunct heuristic. -/
def checkNoIslandViolation (t : DepTree) (gaps : List (Nat × Nat × GapType)) :
    Bool :=
  gaps.all λ (_, gapHostIdx, _) => !hasGapInModifierOrConjunct t gapHostIdx

/-- Combined well-formedness for trees with long-distance gaps: structural
tree-level checks (from `Core.Dependency.Projection.isWellFormed` minus
`checkVerbSubcat`, since LD trees inherently have argument gaps), the
coarse island heuristic, and filler-licensing (wh-word, leftward
topicalization, or relative-clause head). -/
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
      w.features.wh || fillerIdx < t.rootIdx ||
        t.deps.any λ d=> d.headIdx == fillerIdx && d.depType == .acl
    | none => false

end DepGrammar.LongDistance
