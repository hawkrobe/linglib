/-
# Word Grammar Analysis of Coordination

Word Grammar (Hudson 1984, 1990) analysis of coordination structures.

Reference: Hudson (1990), Gibson (2025) Section 3.8
-/

import Linglib.Theories.DependencyGrammar.Basic
import Linglib.Phenomena.Coordination.Data

namespace Coordination.WordGrammarAnalysis

open DepGrammar

private def john : Word := ⟨"John", .D, { number := some .sg, person := some .third }⟩
private def mary : Word := ⟨"Mary", .D, { number := some .sg, person := some .third }⟩
private def and_ : Word := ⟨"and", .C, {}⟩
private def sleep : Word := ⟨"sleep", .V, { valence := some .intransitive, number := some .pl }⟩
private def sleeps : Word := ⟨"sleeps", .V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
private def sees : Word := ⟨"sees", .V, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def the : Word := ⟨"the", .D, {}⟩
private def happy : Word := ⟨"happy", .Adj, {}⟩
private def smart : Word := ⟨"smart", .Adj, {}⟩
private def boy : Word := ⟨"boy", .N, { number := some .sg, countable := some true }⟩
private def eats : Word := ⟨"eats", .V, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def pizza : Word := ⟨"pizza", .N, { number := some .sg }⟩
private def devours : Word := ⟨"devours", .V, { valence := some .transitive, number := some .sg, person := some .third }⟩

-- ============================================================================
-- Coordination Structure
-- ============================================================================

/-- Conjunction types -/
inductive ConjType where
  | and_   -- "and"
  | or_    -- "or"
  | but_   -- "but"
  deriving Repr, DecidableEq, Inhabited

/-- A coordination structure: conjunction + coordinated elements -/
structure CoordStr where
  conjType : ConjType
  conjIdx : Nat           -- Index of the conjunction word
  firstConjunct : Nat     -- Index of first conjunct (typically head)
  otherConjuncts : List Nat  -- Indices of other conjuncts
  deriving Repr

/-- Extended tree with coordination information -/
structure CoordTree where
  words : List Word
  deps : List Dependency
  rootIdx : Nat
  coordinations : List CoordStr := []
  deriving Repr

-- ============================================================================
-- Coordination Constraints
-- ============================================================================

/-- Conjuncts must have matching categories -/
def checkCatMatch (t : CoordTree) : Bool :=
  t.coordinations.all λ coord =>
    match t.words[coord.firstConjunct]? with
    | some firstWord =>
      coord.otherConjuncts.all λ idx =>
        match t.words[idx]? with
        | some w => w.cat == firstWord.cat
        | none => false
    | none => false

/-- For verb coordination, argument structures must match -/
def checkArgStrMatch (t : CoordTree) : Bool :=
  t.coordinations.all λ coord =>
    match t.words[coord.firstConjunct]? with
    | some firstWord =>
      if firstWord.cat == Cat.V then
        coord.otherConjuncts.all λ idx =>
          match t.words[idx]? with
          | some w => firstWord.features.valence == w.features.valence
          | none => false
      else true
    | none => false

/-- Get the category of a coordinated phrase -/
def coordCategory (t : CoordTree) (coord : CoordStr) : Option Cat :=
  t.words[coord.firstConjunct]? |>.map (·.cat)

-- ============================================================================
-- Gapping and Right Node Raising
-- ============================================================================

/-- Gapping: verb is elided in second conjunct -/
structure GappingStr where
  fullClauseRoot : Nat
  gappedClauseElements : List Nat
  deriving Repr

/-- Right Node Raising: shared element on the right -/
structure RNRStr where
  raisedElement : Nat
  gapPositions : List Nat
  deriving Repr

/-- Extended tree with gapping -/
structure GappedTree where
  base : CoordTree
  gapping : Option GappingStr := none
  deriving Repr

-- ============================================================================
-- Well-formedness
-- ============================================================================

/-- A coordinated structure is well-formed if:
    1. Categories match
    2. Argument structures match (for verbs)
    3. Base tree is well-formed -/
def isCoordWellFormed (t : CoordTree) : Bool :=
  let basic : DepTree := { words := t.words, deps := t.deps, rootIdx := t.rootIdx }
  isWellFormed basic &&
  checkCatMatch t &&
  checkArgStrMatch t

-- ============================================================================
-- Example Trees
-- ============================================================================

/-- "John and Mary sleep" - NP coordination -/
def ex_johnAndMarySleep : CoordTree :=
  { words := [john, and_, mary, sleep]
    deps := [⟨3, 0, .subj⟩, ⟨0, 2, .conj⟩]
    rootIdx := 3
    coordinations := [⟨.and_, 1, 0, [2]⟩] }

/-- "John sleeps and Mary sleeps" - S coordination -/
def ex_johnSleepsAndMarySleeps : CoordTree :=
  { words := [john, sleeps, and_, mary, sleeps]
    deps := [⟨1, 0, .subj⟩, ⟨1, 4, .conj⟩, ⟨4, 3, .subj⟩]
    rootIdx := 1
    coordinations := [⟨.and_, 2, 1, [4]⟩] }

/-- "John sees and hears Mary" - VP coordination -/
def ex_johnSeesAndHearsMary : CoordTree :=
  { words := [john, sees, and_, sees, mary]
    deps := [⟨1, 0, .subj⟩, ⟨1, 3, .conj⟩, ⟨1, 4, .obj⟩]
    rootIdx := 1
    coordinations := [⟨.and_, 2, 1, [3]⟩] }

/-- "the old and wise man" - Adjective coordination -/
def ex_oldAndWiseMan : CoordTree :=
  { words := [the, happy, and_, smart, boy]
    deps := [⟨4, 0, .det⟩, ⟨4, 1, .amod⟩, ⟨1, 3, .conj⟩]
    rootIdx := 4
    coordinations := [⟨.and_, 2, 1, [3]⟩] }

/-- "John ate pizza and Mary salad" - Gapping -/
def ex_gapping : GappedTree :=
  { base := {
      words := [john, eats, pizza, and_, mary, pizza]
      deps := [⟨1, 0, .subj⟩, ⟨1, 2, .obj⟩, ⟨1, 4, .conj⟩]
      rootIdx := 1
      coordinations := [⟨.and_, 3, 1, [4]⟩]
    }
    gapping := some ⟨1, [4, 5]⟩ }

/-- "John likes and Mary hates pizza" - Right Node Raising -/
def ex_rnr : CoordTree :=
  { words := [john, devours, and_, mary, devours, pizza]
    deps := [⟨1, 0, .subj⟩, ⟨1, 4, .conj⟩, ⟨4, 3, .subj⟩, ⟨1, 5, .obj⟩]
    rootIdx := 1
    coordinations := [⟨.and_, 2, 1, [4]⟩] }

-- ============================================================================
-- Tests
-- ============================================================================

#eval checkCatMatch ex_johnAndMarySleep          -- true
#eval checkCatMatch ex_johnSleepsAndMarySleeps   -- true
#eval checkArgStrMatch ex_johnSeesAndHearsMary   -- true

-- ============================================================================
-- Proofs
-- ============================================================================

/-- NP coordination has matching categories -/
theorem johnAndMary_cat_match :
    checkCatMatch ex_johnAndMarySleep = true := by native_decide

/-- VP coordination has matching argument structures -/
theorem seesAndHears_argstr_match :
    checkArgStrMatch ex_johnSeesAndHearsMary = true := by native_decide

end Coordination.WordGrammarAnalysis
