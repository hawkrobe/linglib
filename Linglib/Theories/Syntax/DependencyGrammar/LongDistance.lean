/-
# Word Grammar Analysis of Long-Distance Dependencies

Word Grammar (Hudson 1984, 1990) analysis using SLASH features and filler-gap tracking.
Long-distance dependencies are represented directly using DepTree (basic) and DepGraph
(enhanced). The basic tree represents the surface structure; the enhanced graph fills
gaps with explicit argument edges (de Marneffe & Nivre 2019, §4.2).

Reference: Hudson (1990), Gibson (2025) Section 3.9
-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic
import Linglib.Phenomena.FillerGap.LongDistance

namespace DepGrammar.LongDistance

open DepGrammar

private abbrev what := Fragments.English.Pronouns.what.toWord
private abbrev who := Fragments.English.Pronouns.who.toWord
private abbrev did := Fragments.English.FunctionWords.did.toWord
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev mary := Fragments.English.Nouns.mary.toWordSg
private abbrev see := Fragments.English.Predicates.Verbal.see.toWordPl
private abbrev sees := Fragments.English.Predicates.Verbal.see.toWord3sg
private abbrev reads := Fragments.English.Predicates.Verbal.read.toWord3sg
private abbrev gives := Fragments.English.Predicates.Verbal.give.toWord3sg
private abbrev sleeps := Fragments.English.Predicates.Verbal.sleep.toWord3sg
private abbrev think := Fragments.English.Predicates.Verbal.think.toWordPl
private abbrev wonder := Fragments.English.Predicates.Verbal.wonder.toWordPl
private abbrev the := Fragments.English.Determiners.the.toWord
private abbrev book := Fragments.English.Nouns.book.toWordSg
private abbrev that := Fragments.English.Determiners.that.toWord
private abbrev if_ := Fragments.English.FunctionWords.if_.toWord

-- ============================================================================
-- SLASH Features and Gap Types
-- ============================================================================

/-- What type of element is missing in the gap -/
inductive GapType where
  | subjGap   -- Subject extraction: "Who _ saw Mary?"
  | objGap    -- Object extraction: "What did you see _?"
  | iobjGap   -- Indirect object extraction: "Who did you give the book _?"
  | oblGap    -- Oblique extraction: "What did you put the book on _?"
  deriving Repr, DecidableEq, Inhabited

/-- Convert GapType to UD dependency relation -/
def gapToDepRel : GapType → UD.DepRel
  | .subjGap => .nsubj
  | .objGap => .obj
  | .iobjGap => .iobj
  | .oblGap => .obl

/-- SLASH feature: tracks what's missing
    V/NP means "verb phrase missing a noun phrase" -/
structure SLASH where
  gapType : Option GapType := none
  deriving Repr, DecidableEq

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

/-- Check if a position is inside an island (simplified).
    Works on a DepTree directly. -/
def isInsideIsland (t : DepTree) (gapIdx : Nat) : Bool :=
  t.deps.any λ d =>
    (d.depType == .nmod || d.depType == .conj) &&
    d.depIdx == gapIdx

/-- Validate that no extraction site is inside an island.
    Takes explicit filler-gap pairs as (fillerIdx, gapHostIdx, gapType). -/
def checkNoIslandViolation (t : DepTree)
    (gaps : List (Nat × Nat × GapType)) : Bool :=
  gaps.all λ (_, gapHostIdx, _) =>
    !isInsideIsland t gapHostIdx

-- ============================================================================
-- Gap Filling: DepTree → DepGraph
-- ============================================================================

/-- Fill a gap by adding an argument edge to the enhanced graph.
    The fillerIdx word becomes a dependent of gapHostIdx with the relation
    corresponding to gapType. -/
def fillGap (t : DepTree) (fillerIdx gapHostIdx : Nat) (gapType : GapType) : DepGraph :=
  let newDep : Dependency := ⟨gapHostIdx, fillerIdx, gapToDepRel gapType⟩
  { words := t.words
    deps := t.deps ++ [newDep]
    rootIdx := t.rootIdx }

/-- Fill multiple gaps at once. -/
def fillGaps (t : DepTree) (gaps : List (Nat × Nat × GapType)) : DepGraph :=
  let newDeps := gaps.map λ (filler, host, gtype) =>
    ({ headIdx := host, depIdx := filler, depType := gapToDepRel gtype } : Dependency)
  { words := t.words
    deps := t.deps ++ newDeps
    rootIdx := t.rootIdx }

-- ============================================================================
-- SLASH Derivation from Graph Difference
-- ============================================================================

/-- Get SLASH feature at a node by comparing basic tree vs enhanced graph.
    If the enhanced graph has an argument edge to a word that the basic tree
    doesn't, that word has a SLASH feature. -/
def getSLASH (basic : DepTree) (enhanced : DepGraph) (nodeIdx : Nat) : SLASH :=
  let enhancedOnly := enhanced.deps.filter λ d =>
    d.depIdx == nodeIdx &&
    !(basic.deps.any λ bd => bd.depIdx == d.depIdx && bd.headIdx == d.headIdx
                             && bd.depType == d.depType)
  match enhancedOnly.head? with
  | some d =>
    if d.depType == .nsubj then { gapType := some .subjGap }
    else if d.depType == .obj then { gapType := some .objGap }
    else if d.depType == .iobj then { gapType := some .iobjGap }
    else if d.depType == .obl then { gapType := some .oblGap }
    else {}
  | none => {}

-- ============================================================================
-- Well-formedness
-- ============================================================================

/-- A long-distance dependency tree is well-formed if:
    1. Basic tree structure is well-formed
    2. No island violations
    3. Fillers are wh-words or fronted -/
def isLDWellFormed (t : DepTree) (gaps : List (Nat × Nat × GapType)) : Bool :=
  isWellFormed t &&
  checkNoIslandViolation t gaps &&
  gaps.all λ (fillerIdx, _, _) =>
    match t.words[fillerIdx]? with
    | some w => w.features.wh || fillerIdx < t.rootIdx
    | none => false

-- ============================================================================
-- Example Trees: Wh-Questions
-- ============================================================================

/-- "What did John see?" - Object wh-question (basic tree).
    Words: what(0) did(1) John(2) see(3)
    In UD, the wh-word attaches as obj of the main verb. -/
def ex_whatDidJohnSee : DepTree :=
  { words := [what, did, john, see]
    deps := [⟨1, 2, .nsubj⟩, ⟨1, 3, .aux⟩, ⟨1, 0, .obj⟩]
    rootIdx := 1 }

/-- "Who saw Mary?" - Subject wh-question (no gap needed). -/
def ex_whoSawMary : DepTree :=
  { words := [who, sees, mary]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1 }

/-- "Who did John see?" - Object wh-question with "who". -/
def ex_whoDidJohnSee : DepTree :=
  { words := [who, did, john, see]
    deps := [⟨1, 2, .nsubj⟩, ⟨1, 3, .aux⟩, ⟨1, 0, .obj⟩]
    rootIdx := 1 }

-- ============================================================================
-- Example Trees: Relative Clauses
-- ============================================================================

/-- "the book that John read" - Object relative clause (basic tree).
    Words: the(0) book(1) that(2) John(3) read(4)
    In UD, the relative clause attaches via `acl` from head noun to RC verb.
    The gap (book as obj of read) is implicit. -/
def ex_theBookThatJohnRead : DepTree :=
  { words := [the, book, that, john, reads]
    deps := [⟨1, 0, .det⟩, ⟨1, 4, .acl⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- Enhanced graph for "the book that John read" — gap filled.
    Book (1) is added as obj of read (4). -/
def ex_theBookThatJohnRead_enhanced : DepGraph :=
  fillGap ex_theBookThatJohnRead 1 4 .objGap

/-- "the book that John gave Mary" - Object relative with ditransitive. -/
def ex_theBookThatJohnGaveMary : DepTree :=
  { words := [the, book, that, john, gives, mary]
    deps := [⟨1, 0, .det⟩, ⟨1, 4, .acl⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩, ⟨4, 5, .iobj⟩]
    rootIdx := 1 }

-- ============================================================================
-- Example Trees: Complement Clauses
-- ============================================================================

/-- "John thinks that Mary sleeps" - That-complement (no gap). -/
def ex_johnThinksThatMarySleeps : DepTree :=
  { words := [john, think, that, mary, sleeps]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- "John thinks Mary sleeps" - Bare complement (that-omission, no gap). -/
def ex_johnThinksMarySleeps : DepTree :=
  { words := [john, think, mary, sleeps]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .ccomp⟩, ⟨3, 2, .nsubj⟩]
    rootIdx := 1 }

/-- "John wonders if Mary sleeps" - If-complement (no gap). -/
def ex_johnWondersIfMarySleeps : DepTree :=
  { words := [john, wonder, if_, mary, sleeps]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- "John wonders what Mary saw" - Embedded wh-question.
    Words: john(0) wonder(1) what(2) mary(3) sees(4) -/
def ex_johnWondersWhatMarySaw : DepTree :=
  { words := [john, wonder, what, mary, sees]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 3, .nsubj⟩, ⟨4, 2, .obj⟩]
    rootIdx := 1 }

-- ============================================================================
-- Tests
-- ============================================================================

#eval isLDWellFormed ex_whatDidJohnSee [(0, 3, .objGap)]       -- true
#eval isLDWellFormed ex_whoSawMary []                           -- true
#eval isLDWellFormed ex_theBookThatJohnRead [(1, 4, .objGap)]  -- true

-- ============================================================================
-- Proofs
-- ============================================================================

/-- Object wh-questions have wh-word at index 0. -/
theorem whatDidJohnSee_has_wh :
    (ex_whatDidJohnSee.words[0]?.map (·.features.wh)) = some true := rfl

/-- Subject wh-questions don't need gaps (empty gap list). -/
theorem whoSawMary_no_gap :
    isLDWellFormed ex_whoSawMary [] = true := by native_decide

/-- Enhanced graph for relative clause has the filled gap edge. -/
theorem relclause_enhanced_has_obj :
    ex_theBookThatJohnRead_enhanced.deps.any
      (λ d => d.headIdx == 4 && d.depIdx == 1 && d.depType == .obj) = true := by
  native_decide

/-- The basic tree of "the book that John read" does NOT have this obj edge. -/
theorem relclause_basic_lacks_obj :
    ¬ (ex_theBookThatJohnRead.deps.any
      (λ d => d.headIdx == 4 && d.depIdx == 1 && d.depType == .obj) = true) := by
  native_decide

/-- Enhanced graph has more edges than the basic tree. -/
theorem relclause_enhanced_more_edges :
    ex_theBookThatJohnRead_enhanced.deps.length >
    ex_theBookThatJohnRead.deps.length := by native_decide

/-- Enhanced graph violates unique-heads (book has edges from both det and obj). -/
theorem relclause_enhanced_not_tree :
    hasUniqueHeads { words := ex_theBookThatJohnRead_enhanced.words
                     deps := ex_theBookThatJohnRead_enhanced.deps
                     rootIdx := ex_theBookThatJohnRead_enhanced.rootIdx } = false := by
  native_decide

/-- The basic tree IS a tree (unique heads). -/
theorem relclause_basic_is_tree :
    hasUniqueHeads ex_theBookThatJohnRead = true := by native_decide

/-- SLASH derivation: book (1) gets an obj SLASH from comparing basic vs enhanced. -/
theorem relclause_slash_derived :
    getSLASH ex_theBookThatJohnRead ex_theBookThatJohnRead_enhanced 1
      = { gapType := some .objGap } := by native_decide

/-- Complement clauses have no filler-gap dependencies. -/
theorem complement_no_gap :
    checkNoIslandViolation ex_johnThinksThatMarySleeps [] = true := by native_decide

end DepGrammar.LongDistance
