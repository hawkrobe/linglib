import Mathlib.Data.List.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Linglib.Data.UD.Basic
import Linglib.Syntax.Category.Verb.Frame
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Dependency grammar substrate

Core data types for dependency grammar: words connected by typed directed
edges (`Dependency`), trees built over them (`DepTree`), and enhanced
graphs allowing multiple incoming arcs (`DepGraph`). Argument structures
(`ArgStr`) record direction and selectional category for each slot.

Dependency relations use `UD.DepRel` from `Core/UD.lean` (Universal
Dependencies v2). [hudson-2010], [gibson-2025].

## Main declarations

* `Dependency`, `DepGraph`, `DepTree` — the basic graph-shaped data;
  `DepTree extends DepGraph` with argument-structure frames.
* `DepGraph.parentsOf`, `children`, `inDegree`, `toDigraph` — the graph API;
  `toDigraph` presents the graph as a mathlib `Digraph` with decidable
  adjacency (`ParentEdge` is the adjacency at the edge-list level), and
  `toDigraph_mono` orders basic below enhanced graphs in the `Digraph` lattice.
* `ArgStr`, `argStrV0/VN/VNN/VPassive` — argument-structure schemas for the
  standard intransitive / transitive / ditransitive / passive valences.
* `hasUniqueHeads`, `isAcyclic`, `isWellFormed` — structural well-formedness
  predicates (`Bool`-valued; see Implementation notes).
* `mkSVTree`, `mkSVOTree`, `mkDetNVTree`, `mkDitransTree` — small fixture
  builders used by Studies and Formal/ test data.

## Implementation notes

* Predicate-shape definitions return `Bool` rather than `Prop` +
  `[Decidable]`; this is a substrate-wide convention that downstream files
  inherit, and migrating it is a separate refactor.
-/

namespace DepGrammar


section ArgumentStructure

/-- Direction of a dependent relative to head. -/
inductive Dir where
  | left   -- dependent precedes head
  | right  -- dependent follows head
  deriving Repr, DecidableEq, Inhabited

/-- A single argument slot in an argument structure. -/
structure ArgSlot where
  depType : UD.DepRel
  dir : Dir
  required : Bool := true
  cat : Option UD.UPOS := none
  deriving Repr, DecidableEq

/-- Argument structure: what dependents a word requires/allows. -/
structure ArgStr where
  slots : List ArgSlot
  deriving Repr, DecidableEq

end ArgumentStructure

/-! ### Dependencies and trees -/

section DependenciesAndTrees

/-- A dependency: directed edge from head to dependent. -/
structure Dependency where
  /-- Index of the head word in the sentence's `words` list. -/
  headIdx : Nat
  /-- Index of the dependent word in the sentence's `words` list. -/
  depIdx : Nat
  /-- The UD v2 relation label; length metrics ignore it. -/
  depType : UD.DepRel
  deriving Repr, DecidableEq

/-- A dependency graph for a sentence: tokens in surface order plus directed
    head → dependent edges. A word may carry several incoming arcs, as in the
    UD *enhanced* representation; the single-headed case is `DepTree`. -/
structure DepGraph where
  /-- The sentence's tokens, in surface order. -/
  words : List Word
  /-- Directed head → dependent edges. -/
  deps : List Dependency
  /-- Index into `words` of the sentence root. -/
  rootIdx : Nat
  deriving Repr

/-- The head → dependent adjacency of an edge list: there is an edge `(v → w)`
    in `deps`. The atomic relation whose reflexive-transitive closure is
    `Dominates`; sites that need "v is a head with dependent w" should use
    this rather than re-spelling the existential. -/
def ParentEdge (deps : List Dependency) (v w : Nat) : Prop :=
  ∃ d ∈ deps, d.headIdx = v ∧ d.depIdx = w

namespace DepGraph

/-- The edges into position `i`. -/
def parentsOf (g : DepGraph) (i : Nat) : List Dependency :=
  g.deps.filter (·.depIdx == i)

/-- The dependent positions of the word at position `i`. -/
def children (g : DepGraph) (i : Nat) : List Nat :=
  g.deps.filter (·.headIdx == i) |>.map (·.depIdx)

/-- The number of incoming edges at position `i`. -/
def inDegree (g : DepGraph) (i : Nat) : Nat :=
  (g.parentsOf i).length

/-- The graph as a mathlib `Digraph` on word positions. Built with
    `Digraph.mk'`, so adjacency is decidable and digraph-level goals close by
    `decide`. -/
def toDigraph (g : DepGraph) : Digraph Nat :=
  Digraph.mk' λ v w => g.deps.any λ d => d.headIdx == v && d.depIdx == w

@[simp] theorem toDigraph_adj (g : DepGraph) (v w : Nat) :
    g.toDigraph.Adj v w ↔ ParentEdge g.deps v w := by
  simp [toDigraph, ParentEdge]

/-- More edges, larger digraph: a graph's digraph is a subgraph of any
    enhancement of it (in the `Digraph` lattice order). -/
theorem toDigraph_mono {g g' : DepGraph} (h : ∀ d ∈ g.deps, d ∈ g'.deps) :
    g.toDigraph ≤ g'.toDigraph := λ v w hvw => by
  obtain ⟨d, hd, hh, hdep⟩ := (g.toDigraph_adj v w).mp hvw
  exact (g'.toDigraph_adj v w).mpr ⟨d, h d hd, hh, hdep⟩

end DepGraph

/-- A dependency tree: a `DepGraph` meant to be single-headed (`hasUniqueHeads`
    checks it), plus DG-specific lexical argument-structure premises. `frames`
    is aligned with `words` (missing/short = no frame): the frame is framework
    apparatus (like HPSG's ARG-ST), so it lives on DG's tree, not on the shared
    `Word` token; frames come from the lexical carrier at tree construction
    (`complementToArgStr` applied to a verb's `complementType`). -/
structure DepTree extends DepGraph where
  /-- Argument-structure premises aligned with `words`; short or missing list
      means "no frame at this position" (see `DepTree.frame`). -/
  frames : List (Option ArgStr) := []
  deriving Repr

/-- The argument-structure frame at position `i`, if one was supplied. -/
def DepTree.frame (t : DepTree) (i : Nat) : Option ArgStr :=
  (t.frames[i]?).getD none

end DependenciesAndTrees

section StandardArgStr

/-- Intransitive verb: subject to the left -/
def argStrV0 : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩] }

/-- Transitive verb: subject left, object right -/
def argStrVN : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.obj, .right, true, some .DET⟩] }

/-- Ditransitive verb: subject left, indirect object right, object right -/
def argStrVNN : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.iobj, .right, true, some .DET⟩,
              ⟨.obj, .right, true, some .DET⟩] }

/-- Passive transitive: subject left (was patient), optional by-phrase right -/
def argStrVPassive : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.obl, .right, false, some .ADP⟩] }  -- by-phrase is optional

/-- Map a complement type to the corresponding standard DG argument structure.
    Returns `none` for frames without a standard schema: clause-embedding
    types take xcomp/ccomp, not obj, and `.np_pp` has no fixture here. -/
def complementToArgStr : ComplementType → Option ArgStr
  | .none => some argStrV0
  | .np => some argStrVN
  | .np_np => some argStrVNN
  | _ => Option.none

end StandardArgStr

section WellFormedness

/-- Check if every word except root has exactly one head. -/
def hasUniqueHeads (t : DepTree) : Bool :=
  (List.range t.words.length).all λ i =>
    t.toDepGraph.inDegree i == (if i == t.rootIdx then 0 else 1)

/-- Check for cycles: no word is its own ancestor. -/
def isAcyclic (t : DepTree) : Bool :=
  let n := t.words.length
  List.range n |>.all λ start =>
    let rec follow (current : Nat) (visited : List Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => true
      | fuel' + 1 =>
        if visited.contains current then false
        else
          match t.deps.find? (·.depIdx == current) with
          | some dep => follow dep.headIdx (current :: visited) fuel'
          | none => true
    follow start [] (n + 1)

/-- Bundled well-formedness: unique heads + valid index bounds.
    Collects the three hypotheses that most dominance/planarity theorems need. -/
structure DepTree.WF (t : DepTree) : Prop where
  uniqueHeads : hasUniqueHeads t = true
  depIdx_lt : ∀ d ∈ t.deps, d.depIdx < t.words.length
  headIdx_lt : ∀ d ∈ t.deps, d.headIdx < t.words.length

end WellFormedness

section AgreementChecking

/-- Check subject-verb number agreement. -/
def checkSubjVerbAgr (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .nsubj then
      match t.words[d.depIdx]?, t.words[d.headIdx]? with
      | some subj, some verb =>
        match subj.features.number, verb.features.number with
        | some sn, some vn => sn == vn
        | _, _ => true
      | _, _ => true
    else true

/-- Check determiner-noun number agreement. -/
def checkDetNounAgr (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .det then
      match t.words[d.depIdx]?, t.words[d.headIdx]? with
      | some det, some noun =>
        match det.features.number, noun.features.number with
        | some dn, some nn => dn == nn
        | _, _ => true
      | _, _ => true
    else true

end AgreementChecking

section ArgStrSatisfaction

/-- Check if a dependency tree satisfies an argument structure -/
def satisfiesArgStr (t : DepTree) (headIdx : Nat) (argStr : ArgStr) : Bool :=
  argStr.slots.all λ slot =>
    if slot.required then
      -- Required slot: must have a matching dependency
      t.deps.any λ d =>
        d.headIdx == headIdx &&
        d.depType == slot.depType &&
        -- Check direction
        (match slot.dir with
         | .left => d.depIdx < headIdx
         | .right => d.depIdx > headIdx)
    else
      -- Optional slot: if present, must be in correct direction
      t.deps.all λ d =>
        if d.headIdx == headIdx && d.depType == slot.depType then
          match slot.dir with
          | .left => d.depIdx < headIdx
          | .right => d.depIdx > headIdx
        else true

/-- Core argument relations governed by lexical frames. -/
def coreArgRels : List UD.DepRel := [.nsubj, .obj, .iobj]

/-- Every core-argument dependent of `headIdx` is licensed by a slot of
    `argStr` — the closed-world half of frame checking (`satisfiesArgStr`
    only checks that required slots are filled). -/
def coreArgsLicensed (t : DepTree) (headIdx : Nat) (argStr : ArgStr) : Bool :=
  t.deps.all λ d =>
    if d.headIdx == headIdx && coreArgRels.contains d.depType then
      argStr.slots.any (·.depType == d.depType)
    else true

/-- Check each verb's dependents against its lexical frame: required slots
    filled in the right direction (`satisfiesArgStr`) and no unlicensed core
    arguments (`coreArgsLicensed`). Verbs without a frame are skipped. -/
def checkVerbSubcat (t : DepTree) : Bool :=
  List.range t.words.length |>.all λ i =>
    match t.words[i]? with
    | some w =>
      if w.cat == UD.UPOS.VERB then
        match t.frame i with
        | some a => satisfiesArgStr t i a && coreArgsLicensed t i a
        | none => true
      else true
    | none => true

end ArgStrSatisfaction

section TreeConstructionHelpers

/-- Create a simple SV tree: subject -> verb. -/
def mkSVTree (subj verb : Word) (frame : Option ArgStr := none) : DepTree :=
  { words := [subj, verb]
    deps := [⟨1, 0, .nsubj⟩]
    rootIdx := 1
    frames := [none, frame] }

/-- Create a simple SVO tree: subject -> verb <- object. -/
def mkSVOTree (subj verb obj : Word) (frame : Option ArgStr := none) : DepTree :=
  { words := [subj, verb, obj]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1
    frames := [none, frame, none] }

/-- Create Det-N-V tree: det -> noun -> verb. -/
def mkDetNVTree (det noun verb : Word) (frame : Option ArgStr := none) : DepTree :=
  { words := [det, noun, verb]
    deps := [⟨1, 0, .det⟩, ⟨2, 1, .nsubj⟩]
    rootIdx := 2
    frames := [none, none, frame] }

/-- Create a ditransitive tree: subj -> verb <- iobj <- obj. -/
def mkDitransTree (subj verb iobj obj : Word) (frame : Option ArgStr := none) : DepTree :=
  { words := [subj, verb, iobj, obj]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .iobj⟩, ⟨1, 3, .obj⟩]
    rootIdx := 1
    frames := [none, frame, none, none] }

end TreeConstructionHelpers

end DepGrammar
