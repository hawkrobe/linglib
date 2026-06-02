import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Coordination in UD enhanced graphs

Implements coordination in Universal Dependencies' enhanced-dependency
graphs ([de-marneffe-nivre-2019], §4.2 and Figure 9, applied to
coordinate structures): the basic dependency tree attaches each shared
dependent to the first conjunct only, and the enhanced graph recovers the
parallel attachments by propagating `obj` / `nsubj` / `iobj` edges from the
first-conjunct head to every other conjunct.

Word Grammar ([hudson-2010], §7.5.4 "Non-constituent coordination")
handles the same data via a different device: a contiguous string of
words may be treated as a single chunk ("word string") and entered into a
dependency relation as a whole, eliminating the need to propagate shared
dependents. For the historical phrase-structure approach to coordination
(Coordinate Structure Constraint, ATB extraction as theorems of a
complex-symbol grammar), see [gazdar-1981].

## Main declarations

* `getConjuncts`, `hasConjuncts`, `allConjuncts` — inspect the conjunct
  structure of a head node in a basic dependency tree.
* `checkCatMatch` — verifies that every `conj` edge connects words of
  matching UPOS categories.
* `checkArgStrMatch` — for verbal `conj` edges, verifies matching valence.
* `enhanceSharedDeps` — produce a `DepGraph` from a basic `DepTree` by
  propagating shared `obj` / `nsubj` / `iobj` edges from the first
  conjunct's head to each subsequent conjunct.

## Implementation notes

* The `Bool`-valued predicates follow `DepGrammar`'s substrate convention;
  migrating to `Prop` + `Decidable` is a substrate-wide refactor not done
  here.
* Paper-replication fixtures and worked theorems for `enhanceSharedDeps`
  live in `Studies/DeMarneffeNivre2019.lean`. Downstream substrate
  consumers (`Formal/EnhancedDependencies.lean`,
  `Formal/CoordinationParallelism.lean`) define their own local minimal
  fixtures.
* `checkArgStrMatch` is a coarse heuristic over `Features.valence`. Real
  coordination-parallelism judgements (gapping, ATB extraction) live in
  `Formal/CoordinationParallelism.lean`.
-/

namespace DepGrammar.Coordination

open DepGrammar

/-! ### Coordinate structure -/

/-- Conjuncts of a head: words linked by `conj` edges from `headIdx`.
In UD basic-tree convention these are the second-and-later conjuncts;
the first conjunct *is* `headIdx`. -/
def getConjuncts (t : DepTree) (headIdx : Nat) : List Nat :=
  t.deps.filter (λ d => d.headIdx == headIdx && d.depType == .conj)
    |>.map (·.depIdx)

/-- Word `i` heads a coordinate structure iff it has at least one outgoing
`conj` edge. -/
def hasConjuncts (t : DepTree) (i : Nat) : Bool :=
  ¬ (getConjuncts t i).isEmpty

/-- All conjuncts of a coordinate structure headed at `headIdx`: `headIdx`
itself (first conjunct, which heads the structure in UD basic-tree
convention) plus the words linked via `conj`. -/
def allConjuncts (t : DepTree) (headIdx : Nat) : List Nat :=
  headIdx :: getConjuncts t headIdx

/-! ### Parallelism heuristics -/

/-- Every `conj` edge connects words of matching UPOS categories. -/
def checkCatMatch (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .conj then
      match t.words[d.headIdx]?, t.words[d.depIdx]? with
      | some hw, some dw => hw.cat == dw.cat
      | _, _ => false
    else true

/-- For verbal `conj` edges, conjuncts have matching `valence`. Coarse
heuristic — does not handle clausal coordination (`ccomp` / `xcomp`) or
finer subcategorization. -/
def checkArgStrMatch (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .conj then
      match t.words[d.headIdx]?, t.words[d.depIdx]? with
      | some hw, some dw =>
        if hw.cat == UD.UPOS.VERB then
          hw.features.valence == dw.features.valence
        else true
      | _, _ => false
    else true

/-! ### UD enhanced-edge construction -/

/-- Enhance a basic tree by propagating shared dependents from the first
conjunct to all subsequent conjuncts. For each `conj` edge head→dep,
propagates the head's `obj` / `nsubj` / `iobj` edges to `dep`. Returns a
`DepGraph` (words may have multiple incoming edges). Cf.
[de-marneffe-nivre-2019] Figure 9 for the relative-clause analogue. -/
def enhanceSharedDeps (t : DepTree) : DepGraph :=
  let conjEdges := t.deps.filter (·.depType == .conj)
  let enhancedDeps := conjEdges.foldl (λ acc conjEdge =>
    let sharedDeps := t.deps.filter λ d =>
      d.headIdx == conjEdge.headIdx &&
      (d.depType == .obj || d.depType == .nsubj || d.depType == .iobj)
    let newDeps := sharedDeps.map λ d => { d with headIdx := conjEdge.depIdx }
    acc ++ newDeps
  ) []
  { words := t.words
    deps  := t.deps ++ enhancedDeps
    rootIdx := t.rootIdx }

end DepGrammar.Coordination
