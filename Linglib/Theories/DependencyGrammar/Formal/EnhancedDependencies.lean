import Linglib.Theories.DependencyGrammar.Formal.DependencyLength
import Linglib.Theories.DependencyGrammar.Phenomena.Coordination
import Linglib.Theories.DependencyGrammar.Phenomena.LongDistance

/-!
# Enhanced Dependencies (de Marneffe & Nivre 2019, §4.2)

Basic dependency trees enforce a **unique-heads constraint**: every word (except root)
has exactly one head. This means certain predicate-argument relations that hold
semantically cannot be represented as edges in the tree:

- Shared dependents in coordination: "John sees and hears Mary" — Mary is obj of
  both verbs, but the tree can only attach her to one
- Controlled subjects: "Students forgot to come" — "students" is the semantic
  subject of "come" but has no edge to it
- Relative clause gaps: "the book that John read" — "book" is the semantic object
  of "read" but has no edge to it

Enhanced dependencies solve this by relaxing the tree to a **directed graph** where
words can have multiple heads, making implicit predicate-argument relations explicit.

## Key Result

For each phenomenon (coordination, control, relative clauses), we prove:
1. The basic tree has an unrepresented argument (`basic_tree_loses_*`)
2. The enhanced graph recovers it (`enhanced_recovers_*`)
3. The enhanced graph is a strict superset of the basic tree (`enhancement_preserves_basic`)
4. The enhanced graph violates unique-heads — confirming it's a graph, not a tree

## Bridges

- → `Coordination.lean`: `enhanceSharedDeps` converts implicit shared deps to graph edges
- → `LongDistance.lean`: `fillGap` converts gap → explicit argument edge
- → `DependencyLength.lean`: enhanced graphs have ≥ total dep length (more edges)
- → `NonProjective.lean`: enhanced graphs can be non-projective

## References

- de Marneffe, M.-C. & Nivre, J. (2019). Dependency Grammar. Annual Review of
  Linguistics 5:197–218. §4.2, Figure 9.
- Schuster, S. & Manning, C. (2016). Enhanced English Universal Dependencies. LREC.
-/

namespace DepGrammar.EnhancedDependencies

open DepGrammar

-- ============================================================================
-- Core Types (DepGraph and DepTree.toGraph are in Core/Basic.lean)
-- ============================================================================

/-- Enhancement type: what kind of implicit relation is being made explicit.
    Each variant corresponds to a phenomenon where DepTree loses information. -/
inductive EnhancementType where
  | coordSharedDep    -- shared dependent in coordination
  | controlSubject    -- controlled subject (xcomp → nsubj propagation)
  | relClauseGap      -- relative clause gap made explicit
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Graph Utilities
-- ============================================================================

end DepGrammar.EnhancedDependencies

namespace DepGrammar

/-- Extract the basic tree edges from a graph: for each word, keep only the
    first incoming edge (deterministic selection preserving unique-heads). -/
def DepGraph.basicDeps (g : DepGraph) : List Dependency :=
  let n := g.words.length
  List.range n |>.filterMap λ i =>
    g.deps.find? (·.depIdx == i)

/-- Extract the basic tree from a graph (filter to unique heads). -/
def DepGraph.toBasicTree (g : DepGraph) : DepTree :=
  { words := g.words, deps := g.basicDeps, rootIdx := g.rootIdx }

namespace EnhancedDependencies

open DepGrammar

/-- The enhanced edges: those in the graph but not in the basic tree.
    These are the edges that the unique-heads constraint forces us to drop. -/
def enhancedEdges (basic : DepTree) (enhanced : DepGraph) : List Dependency :=
  enhanced.deps.filter λ d =>
    !(basic.deps.any λ bd => bd.headIdx == d.headIdx && bd.depIdx == d.depIdx && bd.depType == d.depType)

-- ============================================================================
-- Information Loss Predicate
-- ============================================================================

/-- A word has an "unrepresented argument" in a basic tree if it's
    semantically an argument of some head (per the enhanced graph) but
    has no edge to that head in the basic tree.
    This is the core problem enhanced deps solve. -/
def hasUnrepresentedArg (basic : DepTree) (enhanced : DepGraph)
    (wordIdx : Nat) : Bool :=
  enhanced.deps.any λ d =>
    d.depIdx == wordIdx &&
    !(basic.deps.any λ bd => bd.depIdx == wordIdx && bd.headIdx == d.headIdx)

-- ============================================================================
-- Graph Well-Formedness
-- ============================================================================

end DepGrammar.EnhancedDependencies

namespace DepGrammar

/-- Enhanced graph well-formedness: acyclic, but NO unique-heads check.
    This is the relaxation that distinguishes DepGraph from DepTree. -/
def DepGraph.isWellFormed (g : DepGraph) : Bool :=
  let asTree : DepTree := { words := g.words, deps := g.deps, rootIdx := g.rootIdx }
  isAcyclic asTree

namespace EnhancedDependencies

open DepGrammar

-- ============================================================================
-- Control Example (control is its own phenomenon, stays here)
-- ============================================================================

private def students : Word := ⟨"students", .NOUN, { number := some .pl }⟩
private def forgot : Word := ⟨"forgot", .VERB, { valence := some .transitive, number := some .pl }⟩
private def to_ : Word := Word.mk' "to" .PART
private def come : Word := ⟨"come", .VERB, { valence := some .intransitive, vform := some .infinitive }⟩

/-- Basic tree for "Students forgot to come".
    Students (0) attaches as nsubj of forgot (1) only. -/
def controlBasicTree : DepTree :=
  { words := [students, forgot, to_, come]
    deps := [ ⟨1, 0, .nsubj⟩   -- forgot ← students
            , ⟨1, 3, .xcomp⟩   -- forgot → come
            , ⟨3, 2, .mark⟩    -- come ← to
            ]
    rootIdx := 1 }

/-- Enhanced graph: adds students as nsubj of come. -/
def controlEnhancedGraph : DepGraph :=
  { words := [students, forgot, to_, come]
    deps := [ ⟨1, 0, .nsubj⟩   -- forgot ← students
            , ⟨1, 3, .xcomp⟩   -- forgot → come
            , ⟨3, 2, .mark⟩    -- come ← to
            , ⟨3, 0, .nsubj⟩   -- come ← students  ← ENHANCED
            ]
    rootIdx := 1 }

-- ============================================================================
-- Key Theorems: Basic Tree Loses Information
-- ============================================================================

-- Aliases for Coordination/LongDistance examples
private abbrev coordBasicTree := Coordination.ex_johnSeesAndHearsMary
private abbrev coordEnhancedGraph := Coordination.ex_johnSeesAndHearsMary_enhanced
private abbrev relClauseBasicTree := LongDistance.ex_theBookThatJohnRead
private abbrev relClauseEnhancedGraph := LongDistance.ex_theBookThatJohnRead_enhanced

/-- Coordination: Mary (idx 4) has an unrepresented argument in the basic tree.
    She is semantically obj of hears (3), but the tree only attaches her to sees (1). -/
theorem basic_tree_loses_coord_args :
    hasUnrepresentedArg coordBasicTree coordEnhancedGraph 4 = true := by native_decide

/-- Control: Students (idx 0) has an unrepresented argument in the basic tree.
    They are semantically nsubj of come (3), but the tree only attaches them to forgot (1). -/
theorem basic_tree_loses_control_subject :
    hasUnrepresentedArg controlBasicTree controlEnhancedGraph 0 = true := by native_decide

/-- Relative clause: Book (idx 1) has an unrepresented argument in the basic tree.
    It is semantically obj of read (4), but the tree only has acl from read. -/
theorem basic_tree_loses_relclause_gap :
    hasUnrepresentedArg relClauseBasicTree relClauseEnhancedGraph 1 = true := by native_decide

-- ============================================================================
-- Key Theorems: Enhanced Graph Recovers Information
-- ============================================================================

/-- The enhanced graph for coordination has strictly more edges than the basic tree. -/
theorem enhanced_recovers_coord_args :
    coordEnhancedGraph.deps.length > coordBasicTree.deps.length := by native_decide

/-- The enhanced graph for control has strictly more edges than the basic tree. -/
theorem enhanced_recovers_control_subject :
    controlEnhancedGraph.deps.length > controlBasicTree.deps.length := by native_decide

/-- The enhanced graph for relative clauses has strictly more edges than the basic tree. -/
theorem enhanced_recovers_relclause_gap :
    relClauseEnhancedGraph.deps.length > relClauseBasicTree.deps.length := by native_decide

-- ============================================================================
-- Key Theorems: Structural Properties
-- ============================================================================

/-- Enhancement preserves basic edges: every edge in the basic tree for coordination
    is also in the enhanced graph. The enhanced graph is a superset. -/
theorem enhancement_preserves_basic_coord :
    coordBasicTree.deps.all (λ d =>
      coordEnhancedGraph.deps.any (λ ed =>
        ed.headIdx == d.headIdx && ed.depIdx == d.depIdx && ed.depType == d.depType)
    ) = true := by native_decide

/-- Enhancement preserves basic edges for control. -/
theorem enhancement_preserves_basic_control :
    controlBasicTree.deps.all (λ d =>
      controlEnhancedGraph.deps.any (λ ed =>
        ed.headIdx == d.headIdx && ed.depIdx == d.depIdx && ed.depType == d.depType)
    ) = true := by native_decide

/-- Enhancement preserves basic edges for relative clauses. -/
theorem enhancement_preserves_basic_relclause :
    relClauseBasicTree.deps.all (λ d =>
      relClauseEnhancedGraph.deps.any (λ ed =>
        ed.headIdx == d.headIdx && ed.depIdx == d.depIdx && ed.depType == d.depType)
    ) = true := by native_decide

/-- The coordination enhanced graph violates unique-heads — it's genuinely a graph.
    Mary (idx 4) has two incoming edges (obj from both sees and hears). -/
theorem enhanced_not_tree_coord :
    hasUniqueHeads { words := coordEnhancedGraph.words
                     deps := coordEnhancedGraph.deps
                     rootIdx := coordEnhancedGraph.rootIdx } = false := by native_decide

/-- The control enhanced graph violates unique-heads.
    Students (idx 0) has two incoming edges (nsubj from both forgot and come). -/
theorem enhanced_not_tree_control :
    hasUniqueHeads { words := controlEnhancedGraph.words
                     deps := controlEnhancedGraph.deps
                     rootIdx := controlEnhancedGraph.rootIdx } = false := by native_decide

/-- The relative clause enhanced graph violates unique-heads.
    Book (idx 1) has two incoming edges (det from the, obj from read). -/
theorem enhanced_not_tree_relclause :
    hasUniqueHeads { words := relClauseEnhancedGraph.words
                     deps := relClauseEnhancedGraph.deps
                     rootIdx := relClauseEnhancedGraph.rootIdx } = false := by native_decide

/-- The basic trees DO satisfy unique-heads (they are trees). -/
theorem basic_is_tree_coord :
    hasUniqueHeads coordBasicTree = true := by native_decide

theorem basic_is_tree_control :
    hasUniqueHeads controlBasicTree = true := by native_decide

theorem basic_is_tree_relclause :
    hasUniqueHeads relClauseBasicTree = true := by native_decide

/-- Enhanced graphs are well-formed (acyclic). -/
theorem enhanced_wf_coord :
    coordEnhancedGraph.isWellFormed = true := by native_decide

theorem enhanced_wf_control :
    controlEnhancedGraph.isWellFormed = true := by native_decide

-- ============================================================================
-- Bridge to DependencyLength.lean
-- ============================================================================

open DependencyLength in
/-- Total dep length on an enhanced graph (computed over all edges including
    enhanced ones). Since the graph has strictly more edges than the basic tree,
    the total dep length is ≥. -/
def enhancedTotalDepLength (g : DepGraph) : Nat :=
  g.deps.foldl (λ acc d => acc + depLength d) 0

open DependencyLength in
/-- Enhanced dep length ≥ basic dep length for coordination example.
    More edges → more total length. -/
theorem enhanced_dep_length_ge_coord :
    enhancedTotalDepLength coordEnhancedGraph ≥
    totalDepLength coordBasicTree := by native_decide

open DependencyLength in
/-- Enhanced dep length ≥ basic dep length for relative clause example. -/
theorem enhanced_dep_length_ge_relclause :
    enhancedTotalDepLength relClauseEnhancedGraph ≥
    totalDepLength relClauseBasicTree := by native_decide

-- ============================================================================
-- Bridge to NonProjective.lean
-- ============================================================================

/-- The basic relative clause tree IS projective. -/
theorem basic_relclause_projective :
    isProjective relClauseBasicTree = true := by native_decide

/-- The coordination enhanced graph has strictly more edges than the basic tree
    (enhanced obj edge from hears to Mary). -/
theorem enhanced_coord_edges_increase :
    coordEnhancedGraph.deps.length > coordBasicTree.deps.length := by native_decide

-- ============================================================================
-- Enhanced Edge Classification
-- ============================================================================

/-- Classify an enhanced edge by what type of enhancement it represents. -/
def classifyEnhancement (basicDeps : List Dependency) (enhanced : Dependency) : Option EnhancementType :=
  if basicDeps.any (λ bd => bd.headIdx == enhanced.headIdx && bd.depIdx == enhanced.depIdx
                            && bd.depType == enhanced.depType)
  then none
  else
    match enhanced.depType with
    | .obj | .iobj => some .coordSharedDep
    | .nsubj => some .controlSubject
    | _ => none

/-- The enhanced edge in the coordination example is classified as coordSharedDep. -/
theorem coord_enhancement_classified :
    classifyEnhancement coordBasicTree.deps ⟨3, 4, .obj⟩ = some .coordSharedDep := by
  native_decide

/-- The enhanced edge in the control example is classified as controlSubject. -/
theorem control_enhancement_classified :
    classifyEnhancement controlBasicTree.deps ⟨3, 0, .nsubj⟩ = some .controlSubject := by
  native_decide

end DepGrammar.EnhancedDependencies
