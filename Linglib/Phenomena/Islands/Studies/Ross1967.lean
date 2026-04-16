import Linglib.Core.Grammar

set_option autoImplicit false

/-!
# Constraints on Variables in Syntax
@cite{ross-1967}

@cite{ross-1967} identified the foundational island constraints that block
long-distance wh-dependencies: embedded question constraint, Complex NP
Constraint, adjunct clause constraint, Coordinate Structure Constraint,
and subject constraint.

## Vocabulary types

The descriptive vocabulary for island constraints is defined here at its
point of origin. Source and strength classifications are NOT stipulated —
each study derives its own from its theoretical commitments. See:
- `MannerOfSpeaking.lean`: `mosIslandSources`, `mosIslandStrength`
- `ShenHuang2026.lean`: `definiteNominalSources`, `definiteNominalStrength`
- `Adger2025.lean`: `alDerivedSource`, `subjectIslandStrength`
- `CartnerEtAl2026.lean`: `subjectIslandSource`
-/

-- ============================================================================
-- Island Constraint Vocabulary
-- ============================================================================

/-- Types of island constraints (descriptive labels) -/
inductive ConstraintType where
  | embeddedQuestion  -- Wh-word blocks further wh-dependency
  | complexNP         -- Complex NP blocks dependency
  | adjunct           -- Adjunct clause blocks dependency
  | coordinate        -- Coordination blocks asymmetric dependency
  | subject           -- Subject position blocks dependency
  | sententialSubject -- Sentential subject blocks dependency
  | mannerOfSpeaking  -- MoS verb complement backgrounds content (@cite{lu-pan-degen-2025})
  | definiteNominal   -- Definite/specific DP blocks dependency (@cite{chomsky-1973},
                       -- @cite{fiengo-higginbotham-1981}, @cite{shen-huang-2026})
  deriving Repr, DecidableEq

/-- Constraint strength classification -/
inductive ConstraintStrength where
  | strong  -- Consistently blocks the dependency
  | weak    -- Ameliorated in some contexts (e.g., D-linked wh-phrases)
  deriving Repr, DecidableEq

/-- Source of an island constraint: what mechanism produces it.
Distinguishes structural accounts (subjacency), processing accounts
(memory load), semantic accounts (binding restrictions), and discourse
accounts (information structure).

These are descriptive labels for the mechanism — the classification of
which source applies to which island type is a theoretical claim, derived
in individual study files from their theoretical commitments. -/
inductive IslandSource where
  /-- Syntactic: island follows from structural configuration (PIC, subjacency) -/
  | syntactic
  /-- Semantic: island follows from a binding restriction (Specificity Condition) -/
  | semantic
  /-- Processing: island is an artifact of memory/retrieval difficulty -/
  | processing
  /-- Discourse: island arises from information-structural backgroundedness (@cite{goldberg-2006}, 2013;
  @cite{lu-pan-degen-2025}) -/
  | discourse
  deriving Repr, DecidableEq

namespace Ross1967

-- ============================================================================
-- §1. Lexical entries for example sentences
-- ============================================================================

private def what : Word := ⟨"what", .PRON, { wh := true }⟩
private def did : Word := ⟨"did", .AUX, {}⟩
private def john : Word := ⟨"John", .DET, { number := some .sg, person := some .third }⟩
private def buy : Word := ⟨"buy", .VERB, { valence := some .transitive, number := some .pl }⟩
private def you : Word := ⟨"you", .DET, { person := some .second, case_ := some .nom }⟩
private def wonder : Word := ⟨"wonder", .VERB, { valence := some .transitive, number := some .pl }⟩
private def who : Word := ⟨"who", .PRON, { wh := true }⟩
private def bought : Word := ⟨"bought", .VERB, { valence := some .transitive, vform := some .finite }⟩
private def see : Word := ⟨"see", .VERB, { valence := some .transitive, number := some .pl }⟩
private def met : Word := ⟨"met", .VERB, { valence := some .transitive, vform := some .finite }⟩
private def man : Word := ⟨"man", .NOUN, { number := some .sg, countable := some .count }⟩
private def that : Word := ⟨"that", .DET, { number := some .sg }⟩
private def saw : Word := ⟨"saw", .VERB, { valence := some .transitive, vform := some .finite }⟩
private def leave : Word := ⟨"leave", .VERB, { valence := some .intransitive, number := some .pl }⟩
private def before : Word := ⟨"before", .ADP, {}⟩
private def because : Word := ⟨"because", .SCONJ, {}⟩
private def books : Word := ⟨"books", .NOUN, { number := some .pl, countable := some .count }⟩
private def and_ : Word := ⟨"and", .CCONJ, {}⟩
private def sell : Word := ⟨"sell", .VERB, { valence := some .transitive, number := some .pl }⟩
private def do_ : Word := ⟨"do", .AUX, { number := some .pl }⟩
private def the : Word := ⟨"the", .DET, {}⟩
private def sees : Word := ⟨"sees", .VERB, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def mary : Word := ⟨"Mary", .DET, { number := some .sg, person := some .third }⟩

-- ============================================================================
-- §2. Island constraint examples
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

    { grammatical := [what, did, john, buy, and_, sell]
      ungrammatical := [what, did, john, buy, and_, sell, books]
      clauseType := .matrixQuestion
      description := "Symmetric (ATB) ok; asymmetric blocked" }
  ]
}

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

/-- All island constraint data -/
def islandData : List PhenomenonData := [
  embeddedQuestionConstraint,
  complexNPConstraint,
  adjunctClauseConstraint,
  coordinateStructureConstraint,
  subjectConstraint
]

-- ============================================================================
-- §3. Sanity checks
-- ============================================================================

#guard wordsToString [what, did, john, buy] == "what did John buy"
#guard wordsToString [what, do_, you, wonder, who, bought] == "what do you wonder who bought"
#guard wordsToString [what, did, john, buy, and_, sell] == "what did John buy and sell"

end Ross1967
