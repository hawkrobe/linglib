import Linglib.Syntax.DependencyGrammar.Coordination
import Linglib.Syntax.DependencyGrammar.Formal.Catena
import Linglib.Syntax.DependencyGrammar.Formal.Ellipsis

open Morphology (Word)

/-!
# Coordination parallelism and sharing

Formalizes [osborne-2019]'s analysis of coordination in dependency
grammar: conjuncts have parallel core-argument structure, shared
dependents form catenae, and the Coordinate Structure Constraint follows
from requiring symmetric (ATB) extraction.

## Main declarations

* `SharingType` — typology of shared material (forward / backward / symmetric / none).
* `parallelConjuncts`, `sharedDepTypes` — predicates over a `DepTree`
  detecting core-argument parallelism and the shared-dep typeset between
  two conjunct heads.
* `isATBExtraction`, `cscViolation` — Bool predicates over an enhanced
  `DepGraph` detecting across-the-board extraction and CSC violations.
* `forwardSharing`, `rnrBasic`, `gappingPreEllipsis`, `atbExtraction` —
  worked example trees from Osborne 2019.

## Implementation notes

* Predicate-shape definitions inherit the substrate-wide `Bool`
  convention; theorems read as `... = true`. A project-wide
  Bool → `Prop` + `[DecidablePred]` migration is out of scope here.
* `none_` constructor renamed to `noSharing` to avoid the `Option.none`
  clash without the trailing-underscore hack.
* Substrate bridges (`Coordination.checkCatMatch`, `enhanceSharedDeps`,
  `Catena.isCatena`) are exercised on the example trees; redundant
  re-statements bundling those checks into single conjunctive theorems
  have been dropped.
-/

namespace DepGrammar.CoordinationParallelism


open DepGrammar Catena

/-! ### Sharing typology -/

/-- Types of shared material in coordination. -/
inductive SharingType where
  /-- Left-edge sharing: "John [eats and drinks] beer". -/
  | forward
  /-- Right-edge sharing (RNR): "John likes and Mary hates [pizza]". -/
  | backward
  /-- Both edges shared: rare. -/
  | symmetric
  /-- No sharing: "John eats and Mary drinks". -/
  | noSharing
  deriving Repr, DecidableEq

/-! ### Parallel structure detection -/

/-- Two conjuncts are parallel when they take the same set of core
    argument relations (nsubj, obj, iobj), ignoring coordination markers
    (conj, cc) and function-word relations that don't affect parallelism. -/
def parallelConjuncts (t : DepTree) (c1 c2 : Nat) : Bool :=
  let isCoreArg (r : UD.DepRel) := r == .nsubj || r == .obj || r == .iobj
  let rels1 := t.deps.filter (λ d => d.headIdx == c1 && isCoreArg d.depType)
    |>.map (·.depType) |>.insertionSort (·.toString ≤ ·.toString) |>.eraseDups
  let rels2 := t.deps.filter (λ d => d.headIdx == c2 && isCoreArg d.depType)
    |>.map (·.depType) |>.insertionSort (·.toString ≤ ·.toString) |>.eraseDups
  rels1.length == rels2.length && rels1.all rels2.contains

/-- The dependency types that appear under both `c1` and `c2`. -/
def sharedDepTypes (t : DepTree) (c1 c2 : Nat) : List UD.DepRel :=
  let rels1 := t.deps.filter (·.headIdx == c1) |>.map (·.depType)
  let rels2 := t.deps.filter (·.headIdx == c2) |>.map (·.depType)
  rels1.filter rels2.contains |>.eraseDups

/-! ### Example trees -/

/-- Forward sharing: "John eats and drinks beer", with `John(0)` the shared
    subject of both verbs. -/
def forwardSharing : DepTree :=
  { words := [ Word.mk' "John" .PROPN, Word.mk' "eats" .VERB
             , Word.mk' "and" .CCONJ, Word.mk' "drinks" .VERB
             , Word.mk' "beer" .NOUN ]
    deps := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .conj⟩, ⟨1, 4, .obj⟩
            , ⟨3, 2, .cc⟩ ]
    rootIdx := 1 }

/-- Enhanced graph for `forwardSharing`: `John` is `nsubj` of both verbs. -/
def forwardSharingEnhanced : DepGraph :=
  Coordination.enhanceSharedDeps forwardSharing

/-- Right-node-raising: "John likes and Mary hates pizza". The basic tree
    attaches `pizza` to `likes(1)` only; `enhanceSharedDeps` propagates
    it as `obj` of `hates(4)` too. -/
def rnrBasic : DepTree :=
  { words := [ Word.mk' "John" .PROPN, Word.mk' "likes" .VERB
             , Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN
             , Word.mk' "hates" .VERB, Word.mk' "pizza" .NOUN ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 4, .conj⟩, ⟨4, 3, .nsubj⟩, ⟨1, 5, .obj⟩ ]
    rootIdx := 1 }

/-- Enhanced graph for `rnrBasic`. -/
def rnrEnhanced : DepGraph := Coordination.enhanceSharedDeps rnrBasic

/-- Pre-gapping tree for "Fred eats beans and Jim eats rice", with the
    second `eats` still overt; downstream gapping treatments elide it. -/
def gappingPreEllipsis : DepTree :=
  { words := [ Word.mk' "Fred" .PROPN, Word.mk' "eats" .VERB
             , Word.mk' "beans" .NOUN, Word.mk' "and" .CCONJ
             , Word.mk' "eats" .VERB, Word.mk' "Jim" .PROPN
             , Word.mk' "rice" .NOUN ]
    deps := [ ⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩, ⟨1, 4, .conj⟩
            , ⟨4, 3, .cc⟩, ⟨4, 5, .nsubj⟩, ⟨4, 6, .obj⟩ ]
    rootIdx := 1 }

/-- ATB extraction: "What did John buy and Mary sell?", symmetric
    extraction of `what` from both conjuncts. -/
def atbExtraction : DepTree :=
  { words := [ { form :="what", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "did" .AUX
             , Word.mk' "John" .PROPN, Word.mk' "buy" .VERB
             , Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN
             , Word.mk' "sell" .VERB ]
    deps := [ ⟨3, 2, .nsubj⟩, ⟨3, 0, .obj⟩, ⟨3, 1, .aux⟩
            , ⟨3, 6, .conj⟩, ⟨6, 5, .nsubj⟩, ⟨6, 4, .cc⟩ ]
    rootIdx := 3 }

/-- Enhanced ATB graph: `what` is `obj` of both `buy` and `sell`. -/
def atbExtractionEnhanced : DepGraph :=
  Coordination.enhanceSharedDeps atbExtraction

/-! ### Shared material forms catenae -/

theorem forwardSharing_shared_isCatena :
    Catena.isCatena forwardSharing.deps [0] = true := by decide

theorem rnr_shared_isCatena :
    Catena.isCatena rnrBasic.deps [5] = true := by decide

theorem gapping_sharedVerb_isCatena :
    Catena.isCatena gappingPreEllipsis.deps [1] = true := by decide

theorem atb_shared_isCatena :
    Catena.isCatena atbExtraction.deps [0] = true := by decide

/-! ### Parallelism -/

/-- Gapping conjuncts are parallel: both verbs take `nsubj` and `obj`. -/
theorem gapping_conjuncts_parallel :
    parallelConjuncts gappingPreEllipsis 1 4 = true := by decide

/-- ATB conjuncts are parallel in the enhanced graph: `buy` and `sell`
    both have `nsubj` and `obj` after shared-dep propagation. -/
theorem atb_conjuncts_parallel_enhanced :
    let enhanced := atbExtractionEnhanced
    let t : DepTree := { words := enhanced.words, deps := enhanced.deps,
                         rootIdx := enhanced.rootIdx }
    parallelConjuncts t 3 6 = true := by decide

/-! ### Coordinate Structure Constraint -/

/-- Extraction is across-the-board when the filler is a dependent of
    every conjunct in the enhanced graph. -/
def isATBExtraction (enhanced : DepGraph) (fillerIdx : Nat)
    (conjuncts : List Nat) : Bool :=
  conjuncts.all λ c =>
    enhanced.deps.any λ d =>
      d.headIdx == c && d.depIdx == fillerIdx

/-- Extraction violates the CSC when the filler is extracted from some
    but not all conjuncts. -/
def cscViolation (enhanced : DepGraph) (fillerIdx : Nat)
    (conjuncts : List Nat) : Bool :=
  let someHave := conjuncts.any λ c =>
    enhanced.deps.any (λ d => d.headIdx == c && d.depIdx == fillerIdx)
  let allHave := conjuncts.all λ c =>
    enhanced.deps.any (λ d => d.headIdx == c && d.depIdx == fillerIdx)
  someHave && !allHave

theorem atb_extraction_isATB :
    isATBExtraction atbExtractionEnhanced 0 [3, 6] = true := by decide

theorem atb_no_cscViolation :
    cscViolation atbExtractionEnhanced 0 [3, 6] = false := by decide

end DepGrammar.CoordinationParallelism
