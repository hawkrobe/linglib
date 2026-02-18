import Linglib.Core.Basic

/-!
# Word-Order Typology (Dryer 2013 / WALS)

WALS data from Gibson (2025, Ch. 5.3, Tables 1–3): cross-linguistic counts
of harmonic vs disharmonic word-order pairings. Dryer (1992, 2013) documents
that languages overwhelmingly prefer consistent head direction across
construction types (the **head-direction generalization**, Greenberg 1963).

## Data

Three cross-tabulations from WALS:
- **Table 1**: VO × Adposition order (981 languages)
- **Table 2**: VO × Subordinator order (456 languages)
- **Table 3**: VO × Relative clause order (665 languages)

Each table is a 2×2 contingency table: VO/OV × head-initial/head-final for
the second construction. Harmonic cells (both HI or both HF) dominate.

## Single-Word Exceptions (Table 4)

Some constructions show *disharmonic* tendencies cross-linguistically:
adjective-noun, demonstrative-noun, intensifier-adjective, negator-verb.
Gibson (2025) argues these are cases where the dependent is a single word
(no recursive subtree), so head direction is irrelevant to DLM.

## References

- Dryer, M. (1992). The Greenbergian word order correlations. Language 68.
- Dryer, M. (2013). Order of object and verb / Order of adposition and NP.
  In Dryer & Haspelmath (eds.), WALS Online. https://wals.info
- Gibson, E. (2025). Syntax: A cognitive approach. Ch. 5.3. MIT Press.
- Greenberg, J. (1963). Some universals of grammar. In Greenberg (ed.),
  Universals of Language.
-/

namespace Phenomena.WordOrder.Typology

-- ============================================================================
-- Types
-- ============================================================================

-- HeadDirection is defined in Core.Basic (imported transitively)

/-- A single cell in a 2×2 alignment table.
    `dir1` is the direction for the first construction (verb-object order),
    `dir2` is the direction for the second construction. -/
structure AlignmentCell where
  dir1 : HeadDirection
  dir2 : HeadDirection
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- Whether an alignment cell represents a harmonic (consistent-direction) pair. -/
def AlignmentCell.isHarmonic (c : AlignmentCell) : Bool :=
  c.dir1 == c.dir2

/-- A 2×2 cross-tabulation of two construction types. -/
structure CrossTab where
  name : String
  construction1 : String  -- e.g. "Verb-Object"
  construction2 : String  -- e.g. "Adposition"
  hihi : AlignmentCell     -- both head-initial
  hihf : AlignmentCell     -- construction 1 HI, construction 2 HF
  hfhi : AlignmentCell     -- construction 1 HF, construction 2 HI
  hfhf : AlignmentCell     -- both head-final
  deriving Repr

/-- Total count of harmonic (diagonal) cells. -/
def CrossTab.harmonicCount (t : CrossTab) : Nat :=
  t.hihi.count + t.hfhf.count

/-- Total count of disharmonic (off-diagonal) cells. -/
def CrossTab.disharmonicCount (t : CrossTab) : Nat :=
  t.hihf.count + t.hfhi.count

/-- Total number of languages in the table. -/
def CrossTab.totalCount (t : CrossTab) : Nat :=
  t.harmonicCount + t.disharmonicCount

/-- Whether harmonic pairings are the majority. -/
def CrossTab.harmonicDominant (t : CrossTab) : Bool :=
  t.harmonicCount > t.disharmonicCount

-- ============================================================================
-- Data: Gibson (2025) Tables 1–3
-- ============================================================================

/-- Table 1: Verb-Object order × Adposition order (Dryer 2013, WALS).
    Gibson (2025) Table 1. 981 languages. -/
def voAdposition : CrossTab :=
  { name := "VO × Adposition"
    construction1 := "Verb-Object"
    construction2 := "Adposition"
    hihi := ⟨.headInitial, .headInitial, 454⟩
    hihf := ⟨.headInitial, .headFinal, 41⟩
    hfhi := ⟨.headFinal, .headInitial, 14⟩
    hfhf := ⟨.headFinal, .headFinal, 472⟩ }

/-- Table 2: Verb-Object order × Subordinator order (Dryer 2013, WALS).
    Gibson (2025) Table 2. 456 languages. -/
def voSubordinator : CrossTab :=
  { name := "VO × Subordinator"
    construction1 := "Verb-Object"
    construction2 := "Subordinator"
    hihi := ⟨.headInitial, .headInitial, 302⟩
    hihf := ⟨.headInitial, .headFinal, 2⟩
    hfhi := ⟨.headFinal, .headInitial, 61⟩
    hfhf := ⟨.headFinal, .headFinal, 91⟩ }

/-- Table 3: Verb-Object order × Relative clause order (Dryer 2013, WALS).
    Gibson (2025) Table 3. 665 languages. -/
def voRelativeClause : CrossTab :=
  { name := "VO × Relative clause"
    construction1 := "Verb-Object"
    construction2 := "Relative clause"
    hihi := ⟨.headInitial, .headInitial, 415⟩
    hihf := ⟨.headInitial, .headFinal, 5⟩
    hfhi := ⟨.headFinal, .headInitial, 113⟩
    hfhf := ⟨.headFinal, .headFinal, 132⟩ }

/-- All three tables from Gibson (2025) Ch. 5.3. -/
def allTables : List CrossTab :=
  [voAdposition, voSubordinator, voRelativeClause]

-- ============================================================================
-- Per-Cell Verification (12 cells)
-- ============================================================================

-- Table 1 cells
example : voAdposition.hihi.count = 454 := by native_decide
example : voAdposition.hihf.count = 41 := by native_decide
example : voAdposition.hfhi.count = 14 := by native_decide
example : voAdposition.hfhf.count = 472 := by native_decide

-- Table 2 cells
example : voSubordinator.hihi.count = 302 := by native_decide
example : voSubordinator.hihf.count = 2 := by native_decide
example : voSubordinator.hfhi.count = 61 := by native_decide
example : voSubordinator.hfhf.count = 91 := by native_decide

-- Table 3 cells
example : voRelativeClause.hihi.count = 415 := by native_decide
example : voRelativeClause.hihf.count = 5 := by native_decide
example : voRelativeClause.hfhi.count = 113 := by native_decide
example : voRelativeClause.hfhf.count = 132 := by native_decide

-- ============================================================================
-- Harmonic vs Disharmonic: Per-Table Theorems
-- ============================================================================

/-- Table 1: harmonic (926) > disharmonic (55). -/
theorem voAdposition_harmonic_dominant :
    voAdposition.harmonicDominant = true := by native_decide

/-- Table 2: harmonic (393) > disharmonic (63). -/
theorem voSubordinator_harmonic_dominant :
    voSubordinator.harmonicDominant = true := by native_decide

/-- Table 3: harmonic (547) > disharmonic (118). -/
theorem voRelativeClause_harmonic_dominant :
    voRelativeClause.harmonicDominant = true := by native_decide

-- ============================================================================
-- The Head-Direction Generalization (Greenberg 1963 / Dryer 1992)
-- ============================================================================

/-- The head-direction generalization: across all three construction pairs,
    harmonic word-order pairings dominate.

    This is the core empirical observation that Gibson (2025) Ch. 5.3
    argues DLM explains: consistent head direction keeps recursive spine
    dependencies local. -/
theorem head_direction_generalization :
    allTables.all CrossTab.harmonicDominant = true := by native_decide

-- ============================================================================
-- Harmonic cells are themselves diagonal
-- ============================================================================

/-- Harmonic cells have matching directions. -/
theorem hihi_is_harmonic : voAdposition.hihi.isHarmonic = true := by native_decide
theorem hfhf_is_harmonic : voAdposition.hfhf.isHarmonic = true := by native_decide

/-- Disharmonic cells have mismatched directions. -/
theorem hihf_is_disharmonic : voAdposition.hihf.isHarmonic = false := by native_decide
theorem hfhi_is_disharmonic : voAdposition.hfhi.isHarmonic = false := by native_decide

-- ============================================================================
-- Totals
-- ============================================================================

/-- Table 1 total: 981 languages. -/
example : voAdposition.totalCount = 981 := by native_decide

/-- Table 2 total: 456 languages. -/
example : voSubordinator.totalCount = 456 := by native_decide

/-- Table 3 total: 665 languages. -/
example : voRelativeClause.totalCount = 665 := by native_decide

-- ============================================================================
-- Single-Word Exceptions (Gibson Table 4)
-- ============================================================================

/-- Construction types where disharmonic order is common (Gibson Table 4).

    These are cases where the dependent is typically a single word (no recursive
    subtree), so head direction doesn't affect DLM. Gibson's argument: DLM
    only cares about direction when subtrees intervene between head and dependent.

    Data here is qualitative — WALS counts not provided in Gibson for these.
    Marked as data TBD for future WALS lookup. -/
inductive SingleWordException where
  | adjN         -- adjective-noun: many VO languages have Adj-N (head-final order)
  | demN         -- demonstrative-noun: many OV languages have Dem-N (head-initial order)
  | intensAdj    -- intensifier-adjective: "very tall" is head-initial in many OV languages
  | negVerb      -- negator-verb: "not run" is head-initial in many OV languages
  deriving Repr, DecidableEq, BEq

/-- All single-word exceptions from Gibson Table 4. -/
def singleWordExceptions : List SingleWordException :=
  [.adjN, .demN, .intensAdj, .negVerb]

/-- These exceptions all involve dependents that are typically single words
    (leaves in the dependency tree), not recursive phrases. -/
def isSingleWordDependent : SingleWordException → Bool
  | .adjN => true        -- adjectives are typically leaves
  | .demN => true        -- demonstratives are single words
  | .intensAdj => true   -- intensifiers like "very" are single words
  | .negVerb => true     -- negation markers are single words

theorem all_exceptions_single_word :
    singleWordExceptions.all isSingleWordDependent = true := by native_decide

end Phenomena.WordOrder.Typology
