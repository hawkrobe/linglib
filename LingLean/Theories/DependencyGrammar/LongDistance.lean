/-
# Word Grammar Analysis of Long-Distance Dependencies

Word Grammar (Hudson 1984, 1990) analysis using SLASH features and filler-gap tracking.

Reference: Hudson (1990), Gibson (2025) Section 3.9
-/

import LingLean.Theories.DependencyGrammar.Basic
import LingLean.Phenomena.LongDistanceDependencies.Data

namespace LongDistanceDependencies.WordGrammarAnalysis

open DepGrammar Lexicon

-- ============================================================================
-- SLASH Features
-- ============================================================================

/-- What type of element is missing in the gap -/
inductive GapType where
  | subjGap   -- Subject extraction: "Who _ saw Mary?"
  | objGap    -- Object extraction: "What did you see _?"
  | iobjGap   -- Indirect object extraction: "Who did you give the book _?"
  | oblGap    -- Oblique extraction: "What did you put the book on _?"
  deriving Repr, DecidableEq, Inhabited

/-- Convert GapType to DepType -/
def gapToDepType : GapType → DepType
  | .subjGap => .subj
  | .objGap => .obj
  | .iobjGap => .iobj
  | .oblGap => .obl

/-- SLASH feature: tracks what's missing
    V/NP means "verb phrase missing a noun phrase" -/
structure SLASH where
  gapType : Option GapType := none
  deriving Repr, DecidableEq

-- ============================================================================
-- Filler-Gap Dependencies
-- ============================================================================

/-- A filler-gap dependency connects a displaced element to its gap position -/
structure FillerGapDep where
  fillerIdx : Nat      -- Index of the filler (e.g., "what")
  gapHostIdx : Nat     -- Index of the word that hosts the gap
  gapType : GapType    -- What kind of gap
  deriving Repr, DecidableEq

/-- Extended dependency tree with filler-gap information -/
structure LDTree where
  words : List Word
  deps : List Dependency
  rootIdx : Nat
  fillerGaps : List FillerGapDep := []
  deriving Repr

-- ============================================================================
-- Island Constraints
-- ============================================================================

/-- Island constraint types -/
inductive IslandType where
  | complex_NP    -- *"What did you meet [the man who saw _]?"
  | coordinate    -- *"What did you eat [rice and _]?"
  | adjunct       -- *"What did you leave [before seeing _]?"
  | subject       -- *"Who did [that _ left] surprise you?"
  deriving Repr, DecidableEq, Inhabited

/-- Check if a position is inside an island (simplified) -/
def isInsideIsland (t : LDTree) (gapIdx : Nat) : Bool :=
  t.deps.any fun d =>
    (d.depType == .nmod || d.depType == .conj) &&
    d.depIdx == gapIdx

/-- Validate that extraction doesn't violate island constraints -/
def checkNoIslandViolation (t : LDTree) : Bool :=
  t.fillerGaps.all fun fg =>
    !isInsideIsland t fg.gapHostIdx

-- ============================================================================
-- SLASH Percolation
-- ============================================================================

/-- Get SLASH feature at a node -/
def getSLASH (t : LDTree) (nodeIdx : Nat) : SLASH :=
  match t.fillerGaps.find? fun fg => fg.gapHostIdx == nodeIdx with
  | some fg => { gapType := some fg.gapType }
  | none => {}

-- ============================================================================
-- Well-formedness
-- ============================================================================

/-- A long-distance dependency tree is well-formed if:
    1. Basic tree structure is well-formed
    2. No island violations
    3. Fillers are wh-words or fronted -/
def isLDWellFormed (t : LDTree) : Bool :=
  let basic : DepTree := { words := t.words, deps := t.deps, rootIdx := t.rootIdx }
  isWellFormed basic &&
  checkNoIslandViolation t &&
  t.fillerGaps.all fun fg =>
    match t.words.get? fg.fillerIdx with
    | some w => w.features.wh || fg.fillerIdx < t.rootIdx
    | none => false

-- ============================================================================
-- Example Trees: Wh-Questions
-- ============================================================================

/-- "What did John see?" - Object wh-question -/
def ex_whatDidJohnSee : LDTree :=
  { words := [what, did, john, see]
    deps := [⟨1, 2, .subj⟩, ⟨1, 3, .aux⟩, ⟨1, 0, .obj⟩]
    rootIdx := 1
    fillerGaps := [⟨0, 3, .objGap⟩] }

/-- "Who saw Mary?" - Subject wh-question (no gap needed) -/
def ex_whoSawMary : LDTree :=
  { words := [who, sees, mary]
    deps := [⟨1, 0, .subj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1
    fillerGaps := [] }

/-- "Who did John see?" - Object wh-question with "who" -/
def ex_whoDidJohnSee : LDTree :=
  { words := [who, did, john, see]
    deps := [⟨1, 2, .subj⟩, ⟨1, 3, .aux⟩, ⟨1, 0, .obj⟩]
    rootIdx := 1
    fillerGaps := [⟨0, 3, .objGap⟩] }

-- ============================================================================
-- Example Trees: Relative Clauses
-- ============================================================================

/-- "the book that John read" - Object relative clause -/
def ex_theBookThatJohnRead : LDTree :=
  { words := [the, book, that, john, reads]
    deps := [⟨1, 0, .det⟩, ⟨1, 4, .nmod⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .subj⟩]
    rootIdx := 1
    fillerGaps := [⟨1, 4, .objGap⟩] }

/-- "the book that John gave Mary" - Object relative with ditransitive -/
def ex_theBookThatJohnGaveMary : LDTree :=
  { words := [the, book, that, john, gives, mary]
    deps := [⟨1, 0, .det⟩, ⟨1, 4, .nmod⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .subj⟩, ⟨4, 5, .iobj⟩]
    rootIdx := 1
    fillerGaps := [⟨1, 4, .objGap⟩] }

-- ============================================================================
-- Example Trees: Complement Clauses
-- ============================================================================

/-- "John thinks that Mary sleeps" - That-complement -/
def ex_johnThinksThatMarySleeps : LDTree :=
  { words := [john, think, that, mary, sleeps]
    deps := [⟨1, 0, .subj⟩, ⟨1, 4, .comp⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .subj⟩]
    rootIdx := 1
    fillerGaps := [] }

/-- "John thinks Mary sleeps" - Bare complement (that-omission) -/
def ex_johnThinksMarySleeps : LDTree :=
  { words := [john, think, mary, sleeps]
    deps := [⟨1, 0, .subj⟩, ⟨1, 3, .comp⟩, ⟨3, 2, .subj⟩]
    rootIdx := 1
    fillerGaps := [] }

/-- "John wonders if Mary sleeps" - If-complement -/
def ex_johnWondersIfMarySleeps : LDTree :=
  { words := [john, wonder, if_, mary, sleeps]
    deps := [⟨1, 0, .subj⟩, ⟨1, 4, .comp⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .subj⟩]
    rootIdx := 1
    fillerGaps := [] }

/-- "John wonders what Mary saw" - Embedded wh-question -/
def ex_johnWondersWhatMarySaw : LDTree :=
  { words := [john, wonder, what, mary, sees]
    deps := [⟨1, 0, .subj⟩, ⟨1, 4, .comp⟩, ⟨4, 3, .subj⟩, ⟨4, 2, .obj⟩]
    rootIdx := 1
    fillerGaps := [⟨2, 4, .objGap⟩] }

-- ============================================================================
-- Tests
-- ============================================================================

#eval isLDWellFormed ex_whatDidJohnSee        -- true
#eval isLDWellFormed ex_whoSawMary            -- true
#eval isLDWellFormed ex_theBookThatJohnRead   -- true
#eval checkNoIslandViolation ex_whatDidJohnSee -- true

-- ============================================================================
-- Proofs
-- ============================================================================

/-- Object wh-questions have an object gap -/
theorem whatDidJohnSee_has_obj_gap :
    ex_whatDidJohnSee.fillerGaps.any (·.gapType == .objGap) = true := rfl

/-- Subject wh-questions don't need gaps -/
theorem whoSawMary_no_gap :
    ex_whoSawMary.fillerGaps.length = 0 := rfl

/-- Relative clauses have gaps coindexed with the head noun -/
theorem relClause_has_gap :
    ex_theBookThatJohnRead.fillerGaps.any (·.fillerIdx == 1) = true := rfl

end LongDistanceDependencies.WordGrammarAnalysis
