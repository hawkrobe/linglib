import Linglib.Syntax.DependencyGrammar.Coordination
import Linglib.Syntax.DependencyGrammar.LongDistance

open Morphology (Word)

/-!
# Enhanced dependencies
[de-marneffe-nivre-2019]

Basic dependency trees enforce a **unique-heads constraint**: every word
(except root) has exactly one head, so certain predicate-argument relations
that hold semantically cannot be represented as tree edges — shared
dependents in coordination, controlled subjects, and relative-clause gaps
are the canonical cases. Enhanced dependencies relax the tree to a
directed graph in which words may have multiple heads.

## Main declarations

* `EnhancementType` — coarse classification of an enhanced edge.
* `hasUnrepresentedArg` — a word has an argument relation in the enhanced
  graph that the basic tree fails to encode.
* `classifyEnhancement` — assign an `EnhancementType` to an enhanced edge.

## Implementation notes

Predicate-shape definitions inherit the substrate-wide `Bool` convention;
statements use `... = true` / `= false`. Worked fixtures for the three
phenomena (coordination, control, relative-clause gap) are kept minimal —
feature-rich `Word` payloads were dropped because the theorems are
structural. `Coordination.enhanceSharedDeps` is the bridge used to build
the coordination enhanced graph; the control and relative-clause graphs
are stipulated.
-/

namespace DepGrammar.EnhancedDependencies


open DepGrammar

/-! ### Enhancement classification -/

/-- The kind of implicit relation an enhanced edge makes explicit. Each
variant corresponds to a phenomenon where the basic tree loses information. -/
inductive EnhancementType where
  | coordSharedDep
  | controlSubject
  | relClauseGap
  deriving Repr, DecidableEq

/-- A word has an *unrepresented argument* in the basic tree if it appears
as a dependent in the enhanced graph under some head to which the basic
tree has no edge. -/
def hasUnrepresentedArg (basic : DepTree) (enhanced : DepGraph)
    (wordIdx : Nat) : Bool :=
  enhanced.deps.any λ d =>
    d.depIdx == wordIdx &&
    !(basic.deps.any λ bd => bd.depIdx == wordIdx && bd.headIdx == d.headIdx)

/-- Classify an enhanced edge by what type of enhancement it represents.
Returns `none` when the edge is already in the basic tree. -/
def classifyEnhancement (basicDeps : List Dependency)
    (enhanced : Dependency) : Option EnhancementType :=
  if basicDeps.any (λ bd => bd.headIdx == enhanced.headIdx &&
                            bd.depIdx == enhanced.depIdx &&
                            bd.depType == enhanced.depType)
  then none
  else
    match enhanced.depType with
    | .obj | .iobj => some .coordSharedDep
    | .nsubj       => some .controlSubject
    | _            => none

/-! ### Coordination fixture: "John sees and hears Mary" -/

def coordBasicTree : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "sees" .VERB,
              Word.mk' "and" .CCONJ, Word.mk' "hears" .VERB,
              Word.mk' "Mary" .PROPN]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 2, .cc⟩, ⟨1, 3, .conj⟩, ⟨1, 4, .obj⟩]
    rootIdx := 1 }

def coordEnhancedGraph : DepGraph :=
  Coordination.enhanceSharedDeps coordBasicTree

/-! ### Control fixture: "Students forgot to come" -/

def controlBasicTree : DepTree :=
  { words := [Word.mk' "students" .NOUN, Word.mk' "forgot" .VERB,
              Word.mk' "to" .PART, Word.mk' "come" .VERB]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 3, .xcomp⟩, ⟨3, 2, .mark⟩]
    rootIdx := 1 }

def controlEnhancedGraph : DepGraph :=
  { controlBasicTree.toGraph with
    deps := controlBasicTree.deps ++ [⟨3, 0, .nsubj⟩] }

/-! ### Relative-clause fixture: "the book that John read" -/

def relClauseBasicTree : DepTree :=
  { words := [Word.mk' "the" .DET, Word.mk' "book" .NOUN,
              Word.mk' "that" .SCONJ, Word.mk' "John" .PROPN,
              Word.mk' "read" .VERB]
    deps  := [⟨1, 0, .det⟩, ⟨1, 4, .acl⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

def relClauseEnhancedGraph : DepGraph :=
  { relClauseBasicTree.toGraph with
    deps := relClauseBasicTree.deps ++ [⟨4, 1, .obj⟩] }

/-! ### Basic tree loses information -/

theorem basic_tree_loses_coord_args :
    hasUnrepresentedArg coordBasicTree coordEnhancedGraph 4 = true := by decide

theorem basic_tree_loses_control_subject :
    hasUnrepresentedArg controlBasicTree controlEnhancedGraph 0 = true := by decide

theorem basic_tree_loses_relclause_gap :
    hasUnrepresentedArg relClauseBasicTree relClauseEnhancedGraph 1 = true := by decide

/-! ### Enhancement preserves basic edges -/

theorem enhancement_preserves_basic_coord :
    coordBasicTree.deps.all (λ d =>
      coordEnhancedGraph.deps.any (λ ed =>
        ed.headIdx == d.headIdx && ed.depIdx == d.depIdx && ed.depType == d.depType)
    ) = true := by decide

theorem enhancement_preserves_basic_control :
    controlBasicTree.deps.all (λ d =>
      controlEnhancedGraph.deps.any (λ ed =>
        ed.headIdx == d.headIdx && ed.depIdx == d.depIdx && ed.depType == d.depType)
    ) = true := by decide

theorem enhancement_preserves_basic_relclause :
    relClauseBasicTree.deps.all (λ d =>
      relClauseEnhancedGraph.deps.any (λ ed =>
        ed.headIdx == d.headIdx && ed.depIdx == d.depIdx && ed.depType == d.depType)
    ) = true := by decide

/-! ### Enhanced graphs violate unique-heads -/

theorem enhanced_not_tree_coord :
    hasUniqueHeads { words := coordEnhancedGraph.words
                     deps := coordEnhancedGraph.deps
                     rootIdx := coordEnhancedGraph.rootIdx } = false := by decide

theorem enhanced_not_tree_control :
    hasUniqueHeads { words := controlEnhancedGraph.words
                     deps := controlEnhancedGraph.deps
                     rootIdx := controlEnhancedGraph.rootIdx } = false := by decide

theorem enhanced_not_tree_relclause :
    hasUniqueHeads { words := relClauseEnhancedGraph.words
                     deps := relClauseEnhancedGraph.deps
                     rootIdx := relClauseEnhancedGraph.rootIdx } = false := by decide

/-! ### Enhanced edges classify correctly -/

theorem coord_enhancement_classified :
    classifyEnhancement coordBasicTree.deps ⟨3, 4, .obj⟩ = some .coordSharedDep := by
  decide

theorem control_enhancement_classified :
    classifyEnhancement controlBasicTree.deps ⟨3, 0, .nsubj⟩ = some .controlSubject := by
  decide

end DepGrammar.EnhancedDependencies
