/-
# Word Grammar Analysis of Coordination

Word Grammar (Hudson 1984, 1990) analysis of coordination structures.
Coordination is represented directly using DepTree (basic) and DepGraph (enhanced).
The basic tree attaches shared dependents to the first conjunct only; the enhanced
graph propagates them to all conjuncts, making implicit predicate-argument relations
explicit (de Marneffe & Nivre 2019, §4.2).

Reference: Hudson (1990), Gibson (2025) Section 3.8
-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic

namespace DepGrammar.Coordination

open DepGrammar

private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev mary := Fragments.English.Nouns.mary.toWordSg
private abbrev and_ := Fragments.English.FunctionWords.and_.toWord
private abbrev sleep := Fragments.English.Predicates.Verbal.sleep.toWordPl
private abbrev sleeps := Fragments.English.Predicates.Verbal.sleep.toWord3sg
private abbrev sees := Fragments.English.Predicates.Verbal.see.toWord3sg
private abbrev the := Fragments.English.Determiners.the.toWord
private abbrev happy := Fragments.English.Modifiers.Adjectives.happy.toWord
private abbrev smart := Fragments.English.Modifiers.Adjectives.smart.toWord
private abbrev boy := Fragments.English.Nouns.boy.toWordSg
private abbrev eats := Fragments.English.Predicates.Verbal.eat.toWord3sg
private abbrev pizza := Fragments.English.Nouns.pizza.toWordSg
private abbrev devours := Fragments.English.Predicates.Verbal.devour.toWord3sg

-- ============================================================================
-- Coordination Structure (derived from graph edges)
-- ============================================================================

/-- Conjunction types -/
inductive ConjType where
  | and_   -- "and"
  | or_    -- "or"
  | but_   -- "but"
  deriving Repr, DecidableEq, Inhabited

/-- Get conjuncts of a head: words linked by `conj` edges from headIdx. -/
def getConjuncts (t : DepTree) (headIdx : Nat) : List Nat :=
  t.deps.filter (λ d => d.headIdx == headIdx && d.depType == .conj)
    |>.map (·.depIdx)

/-- Check that for every `conj` edge, the conjuncts have matching categories. -/
def checkCatMatch (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .conj then
      match t.words[d.headIdx]?, t.words[d.depIdx]? with
      | some hw, some dw => hw.cat == dw.cat
      | _, _ => false
    else true

/-- For verbal `conj` edges, check that conjuncts have matching argument structures. -/
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

-- ============================================================================
-- Enhanced Coordination (shared dep propagation)
-- ============================================================================

/-- Enhance a basic tree by propagating shared dependents from first conjunct
    to all other conjuncts. For each `conj` edge head→dep, propagates obj/nsubj/iobj
    edges from head to dep. Returns a DepGraph (multiple heads per word). -/
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
    deps := t.deps ++ enhancedDeps
    rootIdx := t.rootIdx }

-- ============================================================================
-- Example Trees
-- ============================================================================

/-- "John and Mary sleep" - NP coordination.
    Words: John(0) and(1) Mary(2) sleep(3)
    Basic tree is sufficient — no shared deps needed. -/
def ex_johnAndMarySleep : DepTree :=
  { words := [john, and_, mary, sleep]
    deps := [⟨3, 0, .nsubj⟩, ⟨0, 2, .conj⟩]
    rootIdx := 3 }

/-- "John sleeps and Mary sleeps" - S coordination.
    Words: John(0) sleeps(1) and(2) Mary(3) sleeps(4) -/
def ex_johnSleepsAndMarySleeps : DepTree :=
  { words := [john, sleeps, and_, mary, sleeps]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .conj⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- "John sees and hears Mary" - VP coordination (basic tree).
    Words: John(0) sees(1) and(2) hears(3) Mary(4)
    Mary attaches as obj of sees only. Hears is conj of sees. -/
def ex_johnSeesAndHearsMary : DepTree :=
  { words := [john, sees, and_, sees, mary]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .cc⟩, ⟨1, 3, .conj⟩, ⟨1, 4, .obj⟩]
    rootIdx := 1 }

/-- Enhanced graph for "John sees and hears Mary".
    Mary is obj of BOTH sees and hears — the shared dep is propagated. -/
def ex_johnSeesAndHearsMary_enhanced : DepGraph :=
  enhanceSharedDeps ex_johnSeesAndHearsMary

/-- "the old and wise man" - Adjective coordination.
    Words: the(0) happy(1) and(2) smart(3) boy(4) -/
def ex_oldAndWiseMan : DepTree :=
  { words := [the, happy, and_, smart, boy]
    deps := [⟨4, 0, .det⟩, ⟨4, 1, .amod⟩, ⟨1, 3, .conj⟩]
    rootIdx := 4 }

/-- "John likes and Mary hates pizza" - Right Node Raising.
    Words: John(0) devours(1) and(2) Mary(3) devours(4) pizza(5)
    Pizza attaches to devours(1) only in the basic tree. -/
def ex_rnr : DepTree :=
  { words := [john, devours, and_, mary, devours, pizza]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .conj⟩, ⟨4, 3, .nsubj⟩, ⟨1, 5, .obj⟩]
    rootIdx := 1 }

/-- Enhanced graph for RNR: pizza is obj of both verbs. -/
def ex_rnr_enhanced : DepGraph :=
  enhanceSharedDeps ex_rnr

-- ============================================================================
-- Tests
-- ============================================================================

#eval checkCatMatch ex_johnAndMarySleep          -- true
#eval checkCatMatch ex_johnSleepsAndMarySleeps   -- true
#eval checkArgStrMatch ex_johnSeesAndHearsMary   -- true

-- ============================================================================
-- Proofs
-- ============================================================================

/-- NP coordination has matching categories. -/
theorem johnAndMary_cat_match :
    checkCatMatch ex_johnAndMarySleep = true := by native_decide

/-- S coordination has matching categories. -/
theorem johnSleepsAndMarySleeps_cat_match :
    checkCatMatch ex_johnSleepsAndMarySleeps = true := by native_decide

/-- VP coordination has matching argument structures. -/
theorem seesAndHears_argstr_match :
    checkArgStrMatch ex_johnSeesAndHearsMary = true := by native_decide

/-- Adjective coordination has matching categories. -/
theorem oldAndWise_cat_match :
    checkCatMatch ex_oldAndWiseMan = true := by native_decide

/-- enhanceSharedDeps produces a graph with the missing obj edge from hears to Mary. -/
theorem enhanced_has_shared_obj :
    ex_johnSeesAndHearsMary_enhanced.deps.any
      (λ d => d.headIdx == 3 && d.depIdx == 4 && d.depType == .obj) = true := by
  native_decide

/-- The basic tree does NOT have this edge. -/
theorem basic_lacks_shared_obj :
    ¬ (ex_johnSeesAndHearsMary.deps.any
      (λ d => d.headIdx == 3 && d.depIdx == 4 && d.depType == .obj) = true) := by
  native_decide

/-- Enhanced graph has more edges than the basic tree. -/
theorem enhanced_more_edges :
    ex_johnSeesAndHearsMary_enhanced.deps.length >
    ex_johnSeesAndHearsMary.deps.length := by native_decide

/-- Enhanced graph violates unique-heads — it's genuinely a graph, not a tree.
    Mary (idx 4) has two incoming obj edges (from sees and hears). -/
theorem enhanced_not_tree :
    hasUniqueHeads { words := ex_johnSeesAndHearsMary_enhanced.words
                     deps := ex_johnSeesAndHearsMary_enhanced.deps
                     rootIdx := ex_johnSeesAndHearsMary_enhanced.rootIdx } = false := by
  native_decide

/-- The basic tree IS a tree (unique heads). -/
theorem basic_is_tree :
    hasUniqueHeads ex_johnSeesAndHearsMary = true := by native_decide

/-- RNR enhancement propagates obj to second conjunct. -/
theorem rnr_enhanced_has_shared_obj :
    ex_rnr_enhanced.deps.any
      (λ d => d.headIdx == 4 && d.depIdx == 5 && d.depType == .obj) = true := by
  native_decide

/-- RNR enhanced graph violates unique-heads. -/
theorem rnr_enhanced_not_tree :
    hasUniqueHeads { words := ex_rnr_enhanced.words
                     deps := ex_rnr_enhanced.deps
                     rootIdx := ex_rnr_enhanced.rootIdx } = false := by
  native_decide

end DepGrammar.Coordination
