/-
# Island Constraints

## The Phenomenon

Certain syntactic configurations block long-distance dependencies between a
filler (e.g., a wh-word) and its associated gap. These constraints are
observed across diverse theoretical frameworks.

## The Data

### Wh-Islands (Embedded Question Constraint)

  (1a)  What did John buy?                    ✓
  (1b) *What do you wonder who bought?        ✗  wh-word separated by another wh

### Complex NP Constraint (CNPC)

  (2a)  Who did you see?                      ✓
  (2b) *Who did you meet the man that saw?    ✗  wh-word associated into relative clause

### Adjunct Clause Constraint

  (3a)  What did John buy?                    ✓
  (3b) *What did John leave before buying?    ✗  wh-word associated into adjunct

### Coordinate Structure Constraint (CSC)

  (4a)  What did John buy?                    ✓
  (4b) *What did John buy books and?          ✗  asymmetric: wh from one conjunct

### Subject Constraint

  (5a)  Who did you see pictures of?          ✓  wh from object
  (5b) *Who did pictures of please you?       ✗  wh from subject

## References

- Ross, J.R. (1967). Constraints on Variables in Syntax.
- Huang, C.-T. J. (1982). Logical Relations in Chinese and the Theory of Grammar.
- Szabolcsi, A. (2006). "Strong vs. Weak Islands" in The Blackwell Companion to Syntax.
-/

import Linglib.Phenomena.Basic

open Lexicon

-- ============================================================================
-- Embedded Question Constraint (Wh-Islands)
-- ============================================================================

/-- Embedded question constraint: wh-dependencies blocked across intervening wh-phrase -/
def embeddedQuestionConstraint : PhenomenonData := {
  name := "Embedded Question Constraint"
  generalization := "A wh-word cannot be associated with a position inside an embedded question"
  pairs := [
    { grammatical := [what, did, john, buy]
      ungrammatical := [what, do_, you, wonder, who, bought]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked by intervening wh-word"
      citation := some "Ross (1967)" },

    { grammatical := [who, did, john, see]
      ungrammatical := [who, do_, you, wonder, what, saw]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked across embedded question" }
  ]
}

-- ============================================================================
-- Complex NP Constraint (CNPC)
-- ============================================================================

/-- CNPC: wh-dependencies blocked into relative clauses and noun complements -/
def complexNPConstraint : PhenomenonData := {
  name := "Complex NP Constraint"
  generalization := "A wh-word cannot be associated with a position inside a complex NP"
  pairs := [
    { grammatical := [who, did, you, see]
      ungrammatical := [who, did, you, met, the, man, that, saw]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked into relative clause"
      citation := some "Ross (1967)" }
  ]
}

-- ============================================================================
-- Adjunct Clause Constraint
-- ============================================================================

/-- Adjunct constraint: wh-dependencies blocked into adjunct clauses -/
def adjunctClauseConstraint : PhenomenonData := {
  name := "Adjunct Clause Constraint"
  generalization := "A wh-word cannot be associated with a position inside an adjunct clause"
  pairs := [
    { grammatical := [what, did, john, buy]
      ungrammatical := [what, did, john, leave, before, buy]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked into temporal adjunct"
      citation := some "Huang (1982)" },

    { grammatical := [what, did, john, buy]
      ungrammatical := [what, did, john, leave, because, mary, bought]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked into causal adjunct" }
  ]
}

-- ============================================================================
-- Coordinate Structure Constraint (CSC)
-- ============================================================================

/-- CSC: asymmetric wh-dependencies blocked in coordination -/
def coordinateStructureConstraint : PhenomenonData := {
  name := "Coordinate Structure Constraint"
  generalization := "A wh-word cannot be associated with a position in just one conjunct"
  pairs := [
    { grammatical := [what, did, john, buy]
      ungrammatical := [what, did, john, buy, books, and_]
      clauseType := .matrixQuestion
      description := "Wh-dependency into single conjunct blocked"
      citation := some "Ross (1967)" },

    -- Across-the-board pattern is grammatical
    { grammatical := [what, did, john, buy, and_, sell]
      ungrammatical := [what, did, john, buy, and_, sell, books]
      clauseType := .matrixQuestion
      description := "Symmetric (ATB) ok; asymmetric blocked" }
  ]
}

-- ============================================================================
-- Subject Constraint
-- ============================================================================

/-- Subject constraint: wh-dependencies into subjects degraded -/
def subjectConstraint : PhenomenonData := {
  name := "Subject Constraint"
  generalization := "Wh-dependencies into subject position are blocked or degraded"
  pairs := [
    { grammatical := [who, did, you, see]
      ungrammatical := [who, did, sees, john]
      clauseType := .matrixQuestion
      description := "Wh-dependency into subject blocked"
      citation := some "Ross (1967)" }
  ]
}

-- ============================================================================
-- Combined Island Data
-- ============================================================================

/-- All island constraint data -/
def islandData : List PhenomenonData := [
  embeddedQuestionConstraint,
  complexNPConstraint,
  adjunctClauseConstraint,
  coordinateStructureConstraint,
  subjectConstraint
]

-- ============================================================================
-- Constraint Types (for categorization)
-- ============================================================================

/-- Types of island constraints (descriptive labels) -/
inductive ConstraintType where
  | embeddedQuestion  -- Wh-word blocks further wh-dependency
  | complexNP         -- Complex NP blocks dependency
  | adjunct           -- Adjunct clause blocks dependency
  | coordinate        -- Coordination blocks asymmetric dependency
  | subject           -- Subject position blocks dependency
  | sententialSubject -- Sentential subject blocks dependency
  deriving Repr, DecidableEq

/-- Constraint strength classification (Szabolcsi 2006) -/
inductive ConstraintStrength where
  | strong  -- Consistently blocks the dependency
  | weak    -- Ameliorated in some contexts (e.g., D-linked wh-phrases)
  deriving Repr, DecidableEq

/-- Classification of constraint types by strength -/
def constraintStrength : ConstraintType → ConstraintStrength
  | .embeddedQuestion => .weak      -- Ameliorated with D-linking
  | .complexNP => .strong           -- Generally strong
  | .adjunct => .strong             -- Generally strong
  | .coordinate => .strong          -- Strong (but ATB pattern ok)
  | .subject => .weak               -- Varies cross-linguistically
  | .sententialSubject => .strong

-- ============================================================================
-- Tests
-- ============================================================================

#eval wordsToString [what, did, john, buy]                    -- "what did John buy"
#eval wordsToString [what, do_, you, wonder, who, bought]    -- "*what do you wonder who bought"
#eval wordsToString [what, did, john, buy, and_, sell]       -- "what did John buy and sell" (ATB)
