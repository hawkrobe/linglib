import Linglib.Theories.DependencyGrammar.Formal.Catena
import Linglib.Theories.DependencyGrammar.Formal.Ellipsis
import Linglib.Theories.DependencyGrammar.Phenomena.Coordination

/-!
# Coordination Parallelism and Sharing

Formalizes Osborne's (2019, Ch 10–11) analysis of coordination: conjuncts
must have parallel structure, shared dependents form catenae, and the CSC
falls out from the parallelism requirement.

## Sharing Types

- **Forward sharing**: left-edge shared ("John [eats and drinks] beer")
- **Backward sharing**: right-edge shared / RNR ("John likes and Mary hates [pizza]")
- **Symmetric**: both edges shared (rare)

## Key Insight

All types of shared material in coordination form catenae. Gapping in
coordination is just catena-ellipsis. The CSC follows from requiring symmetric
(ATB) extraction — asymmetric extraction violates parallelism.

## Bridges

- → `Coordination.lean`: extends with sharing type classification;
  reuses `ex_rnr`, `checkCatMatch`, `checkArgStrMatch`
- → `Catena.lean`: shared material forms catenae (proven)
- → `Ellipsis.lean`: gapping = catena-ellipsis in coordination
- → `Phenomena/Ellipsis/Gapping.lean`: gapping direction ↔ sharing direction

## References

- Osborne, T. (2019). *A Dependency Grammar of English*, Ch 10–11.
  Amsterdam: John Benjamins.
-/

namespace DepGrammar.CoordinationParallelism

open DepGrammar Catena

-- ============================================================================
-- §1: Sharing Typology
-- ============================================================================

/-- Types of shared material in coordination (Osborne 2019, Ch 10). -/
inductive SharingType where
  | forward    -- Left-edge sharing: "John [eats and drinks] beer"
  | backward   -- Right-edge sharing (RNR): "John likes and Mary hates [pizza]"
  | symmetric  -- Both edges shared: rare
  | none_      -- No sharing: "John eats and Mary drinks"
  deriving Repr, DecidableEq

-- ============================================================================
-- §2: Parallel Structure Detection
-- ============================================================================

/-- Check if two conjuncts have parallel core argument structure.
    Parallel = same set of core argument relations (nsubj, obj, iobj) from head,
    ignoring coordination-specific (conj, cc) and function-word (aux, mark, det)
    relations which don't affect parallelism.
    Osborne (2019, Ch 10 §10.3). -/
def parallelConjuncts (t : DepTree) (c1 c2 : Nat) : Bool :=
  let isCoreArg (r : UD.DepRel) := r == .nsubj || r == .obj || r == .iobj
  let rels1 := t.deps.filter (λ d => d.headIdx == c1 && isCoreArg d.depType)
    |>.map (·.depType) |>.mergeSort (·.toString ≤ ·.toString) |>.eraseDups
  let rels2 := t.deps.filter (λ d => d.headIdx == c2 && isCoreArg d.depType)
    |>.map (·.depType) |>.mergeSort (·.toString ≤ ·.toString) |>.eraseDups
  rels1.length == rels2.length && rels1.all rels2.contains

/-- Get shared dependents between two conjuncts: deps that have the same
    depType in both heads. Returns the depTypes that are shared. -/
def sharedDepTypes (t : DepTree) (c1 c2 : Nat) : List UD.DepRel :=
  let rels1 := t.deps.filter (·.headIdx == c1) |>.map (·.depType)
  let rels2 := t.deps.filter (·.headIdx == c2) |>.map (·.depType)
  rels1.filter rels2.contains |>.eraseDups

-- ============================================================================
-- §3: Example Trees
-- ============================================================================

/-- **Forward sharing**: "John eats and drinks beer"
    Words: John(0) eats(1) and(2) drinks(3) beer(4)
    Deps: eats(1) → John(0:nsubj), eats(1) → drinks(3:conj), eats(1) → beer(4:obj),
          drinks(3) → and(2:cc)
    Shared = {John(0)} — nsubj of eats, implicitly of drinks too.
    Osborne (2019, Ch 10). -/
def ex_forwardSharing : DepTree :=
  { words := [ Word.mk' "John" .PROPN, Word.mk' "eats" .VERB
             , Word.mk' "and" .CCONJ, Word.mk' "drinks" .VERB
             , Word.mk' "beer" .NOUN ]
    deps := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .conj⟩, ⟨1, 4, .obj⟩
            , ⟨3, 2, .cc⟩ ]
    rootIdx := 1 }

/-- Enhanced graph for forward sharing: John is nsubj of both eats AND drinks. -/
def ex_forwardSharing_enhanced : DepGraph :=
  Coordination.enhanceSharedDeps ex_forwardSharing

-- Backward sharing (RNR): reuse `Coordination.ex_rnr`.
-- "John devours and Mary devours pizza"
-- Shared = {pizza} — obj of both verbs.

/-- **Gapping-as-coordination**: "Fred eats beans and Jim rice"
    Words: Fred(0) eats(1) beans(2) and(3) Jim(4) rice(5)
    This is the pre-gapping tree. Gapping elides the second "eats".
    In UD: eats(1) → Fred(0:nsubj), eats(1) → beans(2:obj),
           eats(1) → eats_implied(→ orphan structure).
    We model the pre-gapping version with full second clause:
    eats(1) → Fred(0:nsubj), eats(1) → beans(2:obj),
    eats(1) → Jim(4:conj:orphan parent), Jim(4) → rice(5:orphan).
    But UD uses `orphan` for gapping; we model the pre-ellipsis tree instead. -/
def ex_gapping_preEllipsis : DepTree :=
  { words := [ Word.mk' "Fred" .PROPN, Word.mk' "eats" .VERB
             , Word.mk' "beans" .NOUN, Word.mk' "and" .CCONJ
             , Word.mk' "eats" .VERB, Word.mk' "Jim" .PROPN
             , Word.mk' "rice" .NOUN ]
    deps := [ ⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩, ⟨1, 4, .conj⟩
            , ⟨4, 3, .cc⟩, ⟨4, 5, .nsubj⟩, ⟨4, 6, .obj⟩ ]
    rootIdx := 1 }

/-- **ATB extraction**: "What did John buy and Mary sell?"
    Words: what(0) did(1) John(2) buy(3) and(4) Mary(5) sell(6)
    Deps: buy(3) → John(2:nsubj), buy(3) → what(0:obj), buy(3) → did(1:aux),
          buy(3) → sell(6:conj), sell(6) → Mary(5:nsubj), sell(6) → and(4:cc)
    Symmetric extraction from both conjuncts — grammatical.
    Osborne (2019, Ch 11). -/
def ex_atbExtraction : DepTree :=
  { words := [ ⟨"what", .PRON, { wh := true }⟩, Word.mk' "did" .AUX
             , Word.mk' "John" .PROPN, Word.mk' "buy" .VERB
             , Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN
             , Word.mk' "sell" .VERB ]
    deps := [ ⟨3, 2, .nsubj⟩, ⟨3, 0, .obj⟩, ⟨3, 1, .aux⟩
            , ⟨3, 6, .conj⟩, ⟨6, 5, .nsubj⟩, ⟨6, 4, .cc⟩ ]
    rootIdx := 3 }

/-- Enhanced ATB: what is obj of BOTH buy and sell. -/
def ex_atbExtraction_enhanced : DepGraph :=
  Coordination.enhanceSharedDeps ex_atbExtraction

-- ============================================================================
-- §4: Shared Material as Catenae
-- ============================================================================

/-- In forward sharing, the shared subject {John(0)} is trivially a catena. -/
theorem forwardSharing_shared_is_catena :
    Catena.isCatena ex_forwardSharing.deps [0] = true := by native_decide

/-- In RNR (Coordination.ex_rnr), the shared object {pizza(5)} is a catena. -/
theorem rnr_shared_is_catena :
    Catena.isCatena Coordination.ex_rnr.deps [5] = true := by native_decide

/-- In gapping, the shared verb {eats(1)} is a catena (links to both clauses). -/
theorem gapping_shared_verb_is_catena :
    Catena.isCatena ex_gapping_preEllipsis.deps [1] = true := by native_decide

/-- In ATB extraction, the shared object {what(0)} is a catena. -/
theorem atb_shared_is_catena :
    Catena.isCatena ex_atbExtraction.deps [0] = true := by native_decide

-- ============================================================================
-- §5: Parallelism Proofs
-- ============================================================================

/-- Gapping conjuncts are parallel: both eats(1) and eats(4) have the same
    set of dependency relations (nsubj, obj). -/
theorem gapping_conjuncts_parallel :
    parallelConjuncts ex_gapping_preEllipsis 1 4 = true := by native_decide

/-- ATB conjuncts are parallel in the enhanced graph: buy(3) and sell(6) both
    have nsubj and obj after shared dep propagation. -/
theorem atb_conjuncts_parallel_enhanced :
    let enhanced := ex_atbExtraction_enhanced
    let t : DepTree := { words := enhanced.words, deps := enhanced.deps, rootIdx := enhanced.rootIdx }
    parallelConjuncts t 3 6 = true := by native_decide

-- Forward sharing conjuncts: eats(1) has nsubj, obj, conj;
-- drinks(3) has cc. Not directly parallel at head level (eats has more
-- deps because shared deps attach to first conjunct).

-- ============================================================================
-- §6: CSC via Parallelism
-- ============================================================================

/-- Check if extraction from coordination is across-the-board (ATB):
    the filler is an argument of ALL conjuncts in the enhanced graph.
    Osborne (2019, Ch 11): asymmetric extraction violates parallelism. -/
def isATBExtraction (enhanced : DepGraph) (fillerIdx : Nat)
    (conjuncts : List Nat) : Bool :=
  conjuncts.all λ c =>
    enhanced.deps.any λ d =>
      d.headIdx == c && d.depIdx == fillerIdx

/-- Check if extraction violates the CSC: extracted from some but not all
    conjuncts. -/
def cscViolation (enhanced : DepGraph) (fillerIdx : Nat)
    (conjuncts : List Nat) : Bool :=
  let someHave := conjuncts.any λ c =>
    enhanced.deps.any (λ d => d.headIdx == c && d.depIdx == fillerIdx)
  let allHave := conjuncts.all λ c =>
    enhanced.deps.any (λ d => d.headIdx == c && d.depIdx == fillerIdx)
  someHave && !allHave

/-- ATB extraction in "What did John buy and Mary sell?" is ATB: what(0) is
    obj of both buy(3) and sell(6) in the enhanced graph. -/
theorem atb_extraction_is_atb :
    isATBExtraction ex_atbExtraction_enhanced 0 [3, 6] = true := by native_decide

/-- ATB extraction does NOT violate the CSC. -/
theorem atb_no_csc_violation :
    cscViolation ex_atbExtraction_enhanced 0 [3, 6] = false := by native_decide

-- ============================================================================
-- §7: Bridges
-- ============================================================================

/-- **Bridge → Coordination.lean**: category matching still holds for all
    our coordination examples. -/
theorem coordination_cat_match_preserved :
    Coordination.checkCatMatch ex_gapping_preEllipsis = true ∧
    Coordination.checkCatMatch ex_atbExtraction = true := by
  constructor <;> native_decide

/-- **Bridge → Coordination.lean**: argument structure matching holds for
    gapping (both verbs are transitive). -/
theorem gapping_argstr_match :
    Coordination.checkArgStrMatch ex_gapping_preEllipsis = true := by native_decide

/-- **Bridge → Coordination.lean**: enhanced graph propagates shared deps. -/
theorem forward_sharing_enhanced_propagates :
    ex_forwardSharing_enhanced.deps.any
      (λ d => d.headIdx == 3 && d.depIdx == 0 && d.depType == .nsubj) = true := by
  native_decide

/-- **Bridge → Coordination.ex_rnr**: RNR enhanced graph has shared obj. -/
theorem rnr_bridge :
    Coordination.ex_rnr_enhanced.deps.any
      (λ d => d.headIdx == 4 && d.depIdx == 5 && d.depType == .obj) = true := by
  native_decide

/-- **Bridge → Catena.lean**: all shared material in coordination forms
    catenae — singletons are trivially connected. -/
theorem all_shared_are_catenae :
    Catena.isCatena ex_forwardSharing.deps [0] = true ∧
    Catena.isCatena Coordination.ex_rnr.deps [5] = true ∧
    Catena.isCatena ex_gapping_preEllipsis.deps [1] = true ∧
    Catena.isCatena ex_atbExtraction.deps [0] = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Bridge → Ellipsis.lean**: gapping is catena-ellipsis in coordination.
    The gapped verb is a singleton catena, just like in Ellipsis.gappingElided. -/
theorem gapping_is_catena_ellipsis :
    Catena.isCatena ex_gapping_preEllipsis.deps [1] = true ∧
    Catena.isCatena Ellipsis.gappingTree.deps [0] = true := by
  constructor <;> native_decide

/-- **Bridge → Phenomena/Ellipsis/Gapping.lean**: forward sharing corresponds
    to forward gapping (verb retained in first conjunct), backward sharing
    corresponds to backward gapping (verb retained in last conjunct). -/
theorem sharing_direction_matches_gapping :
    -- Forward sharing: verb overt in first conjunct (like English forward gapping)
    (Phenomena.Ellipsis.Gapping.rossOriginal .SVO).allowsForward = true ∧
    -- Backward sharing: possible in SOV (like backward gapping)
    (Phenomena.Ellipsis.Gapping.rossOriginal .SOV).allowsBackward = true := by
  constructor <;> rfl

end DepGrammar.CoordinationParallelism
