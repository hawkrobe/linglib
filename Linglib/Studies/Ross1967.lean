import Linglib.Features.MinimalPairs

open Morphology (Word wordsToString)

open Features.MinimalPairs

set_option autoImplicit false

/-!
# Constraints on Variables in Syntax
[ross-1967]

[ross-1967] identified the foundational island constraints that block
long-distance wh-dependencies: embedded question constraint, Complex NP
Constraint, adjunct clause constraint, Coordinate Structure Constraint,
and subject constraint.

## Vocabulary types

`ConstraintType` / `ConstraintStrength` / `IslandSource` are the
descriptive labels island studies classify with. The constraint
inventory is Ross's five plus the later extensions the enum must carry
because consumers share one type (manner-of-speaking, definite nominal).
Source and strength classifications are NOT stipulated globally — each
study derives its own from its theoretical commitments. See:
- `LuPanDegen2025.lean`: `mosIslandSources`, `mosIslandStrength`
- `ShenHuang2026.lean`: `definiteNominalSources`, `definiteNominalStrength`
- `Adger2025.lean`: `adgerSubjectIslandSource`, `adgerDefiniteNominalSources`
- `CartnerEtAl2026.lean`: `subjectIslandSource`
-/

/-- Types of island constraints (descriptive labels). Ross's foundational
    five plus later additions (MoS verbs, definite nominals). -/
inductive ConstraintType where
  /-- Wh-word blocks further wh-dependency. -/
  | embeddedQuestion
  /-- Complex NP blocks dependency (Ross 1967). -/
  | complexNP
  /-- Adjunct clause blocks dependency. -/
  | adjunct
  /-- Coordination blocks asymmetric dependency (CSC). -/
  | coordinate
  /-- Subject position blocks dependency. -/
  | subject
  /-- Sentential subject blocks dependency. -/
  | sententialSubject
  /-- MoS verb complement backgrounds content ([lu-pan-degen-2025]). -/
  | mannerOfSpeaking
  /-- Definite/specific DP blocks dependency
      ([chomsky-1973], [shen-huang-2026]). -/
  | definiteNominal
  deriving Repr, DecidableEq

/-- Constraint strength classification. -/
inductive ConstraintStrength where
  /-- Consistently blocks the dependency. -/
  | strong
  /-- Ameliorated in some contexts (D-linking, processing facilitation,
      stage-level subjects, etc.). -/
  | weak
  deriving Repr, DecidableEq

/-- Source of an island constraint: what mechanism produces it.
Distinguishes structural accounts (subjacency, PIC, Angular Locality),
processing accounts (memory load), semantic accounts (binding restrictions),
and discourse accounts (information structure).

These are descriptive labels for the mechanism — the classification of
which source applies to which island type is a theoretical claim, derived
in individual study files from their theoretical commitments. -/
inductive IslandSource where
  /-- Syntactic: island follows from structural configuration
      (PIC, subjacency, Angular Locality). -/
  | syntactic
  /-- Semantic: island follows from a binding restriction
      (Specificity Condition). -/
  | semantic
  /-- Processing: island is an artifact of memory/retrieval difficulty. -/
  | processing
  /-- Discourse: island arises from information-structural backgroundedness
      ([goldberg-2006], [lu-pan-degen-2025]). -/
  | discourse
  deriving Repr, DecidableEq

namespace Ross1967


-- ============================================================================
-- §1. Lexical entries for example sentences
-- ============================================================================

private def what : Word := { form :="what", cat := .PRON, features := { pronType := some .Int }}
private def did : Word := { form :="did", cat := .AUX, features := {}}
private def john : Word := { form :="John", cat := .DET, features := { number := some .Sing, person := some .third }}
private def buy : Word := { form :="buy", cat := .VERB, features := { number := some .Plur }}
private def you : Word := { form :="you", cat := .DET, features := { person := some .second, case_ := some .Nom }}
private def wonder : Word := { form :="wonder", cat := .VERB, features := { number := some .Plur }}
private def who : Word := { form :="who", cat := .PRON, features := { pronType := some .Int }}
private def bought : Word := { form :="bought", cat := .VERB, features := { verbForm := some .Fin }}
private def see : Word := { form :="see", cat := .VERB, features := { number := some .Plur }}
private def met : Word := { form :="met", cat := .VERB, features := { verbForm := some .Fin }}
private def man : Word := { form :="man", cat := .NOUN, features := { number := some .Sing }}
private def that : Word := { form :="that", cat := .DET, features := { number := some .Sing }}
private def saw : Word := { form :="saw", cat := .VERB, features := { verbForm := some .Fin }}
private def leave : Word := { form :="leave", cat := .VERB, features := { number := some .Plur }}
private def before : Word := { form :="before", cat := .ADP, features := {}}
private def because : Word := { form :="because", cat := .SCONJ, features := {}}
private def books : Word := { form :="books", cat := .NOUN, features := { number := some .Plur }}
private def and_ : Word := { form :="and", cat := .CCONJ, features := {}}
private def sell : Word := { form :="sell", cat := .VERB, features := { number := some .Plur }}
private def do_ : Word := { form :="do", cat := .AUX, features := { number := some .Plur }}
private def the : Word := { form :="the", cat := .DET, features := {}}
private def sees : Word := { form :="sees", cat := .VERB, features := { number := some .Sing, person := some .third }}
private def mary : Word := { form :="Mary", cat := .DET, features := { number := some .Sing, person := some .third }}

-- ============================================================================
-- §2. Island constraint examples
-- ============================================================================

/-- Embedded question constraint: wh-dependencies blocked across intervening wh-phrase -/
def embeddedQuestionConstraint : PhenomenonData := {
  name := "Embedded Question Constraint"
  generalization := "A wh-word cannot be associated with a position inside an embedded question"
  pairs := [
    { lhs := [what, did, john, buy]
      rhs := [what, do_, you, wonder, who, bought]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked by intervening wh-word"
      citation := "Ross (1967)" },

    { lhs := [who, did, john, see]
      rhs := [who, do_, you, wonder, what, saw]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked across embedded question" }
  ]
}

/-- CNPC: wh-dependencies blocked into relative clauses and noun complements -/
def complexNPConstraint : PhenomenonData := {
  name := "Complex NP Constraint"
  generalization := "A wh-word cannot be associated with a position inside a complex NP"
  pairs := [
    { lhs := [who, did, you, see]
      rhs := [who, did, you, met, the, man, that, saw]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked into relative clause"
      citation := "Ross (1967)" }
  ]
}

/-- Adjunct constraint: wh-dependencies blocked into adjunct clauses -/
def adjunctClauseConstraint : PhenomenonData := {
  name := "Adjunct Clause Constraint"
  generalization := "A wh-word cannot be associated with a position inside an adjunct clause"
  pairs := [
    { lhs := [what, did, john, buy]
      rhs := [what, did, john, leave, before, buy]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked into temporal adjunct"
      citation := "Huang (1982)" },

    { lhs := [what, did, john, buy]
      rhs := [what, did, john, leave, because, mary, bought]
      clauseType := .matrixQuestion
      description := "Wh-dependency blocked into causal adjunct" }
  ]
}

/-- CSC: asymmetric wh-dependencies blocked in coordination -/
def coordinateStructureConstraint : PhenomenonData := {
  name := "Coordinate Structure Constraint"
  generalization := "A wh-word cannot be associated with a position in just one conjunct"
  pairs := [
    { lhs := [what, did, john, buy]
      rhs := [what, did, john, buy, books, and_]
      clauseType := .matrixQuestion
      description := "Wh-dependency into single conjunct blocked"
      citation := "Ross (1967)" },

    { lhs := [what, did, john, buy, and_, sell]
      rhs := [what, did, john, buy, and_, sell, books]
      clauseType := .matrixQuestion
      description := "Symmetric (ATB) ok; asymmetric blocked" }
  ]
}

/-- Subject constraint: wh-dependencies into subjects degraded -/
def subjectConstraint : PhenomenonData := {
  name := "Subject Constraint"
  generalization := "Wh-dependencies into subject position are blocked or degraded"
  pairs := [
    { lhs := [who, did, you, see]
      rhs := [who, did, sees, john]
      clauseType := .matrixQuestion
      description := "Wh-dependency into subject blocked"
      citation := "Ross (1967)" }
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
