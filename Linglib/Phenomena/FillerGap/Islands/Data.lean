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

import Linglib.Core.Grammar

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
private def man : Word := ⟨"man", .NOUN, { number := some .sg, countable := some true }⟩
private def that : Word := ⟨"that", .DET, { number := some .sg }⟩
private def saw : Word := ⟨"saw", .VERB, { valence := some .transitive, vform := some .finite }⟩
private def leave : Word := ⟨"leave", .VERB, { valence := some .intransitive, number := some .pl }⟩
private def before : Word := ⟨"before", .ADP, {}⟩
private def because : Word := ⟨"because", .SCONJ, {}⟩
private def books : Word := ⟨"books", .NOUN, { number := some .pl, countable := some true }⟩
private def and_ : Word := ⟨"and", .CCONJ, {}⟩
private def sell : Word := ⟨"sell", .VERB, { valence := some .transitive, number := some .pl }⟩
private def do_ : Word := ⟨"do", .AUX, { number := some .pl }⟩
private def the : Word := ⟨"the", .DET, {}⟩
private def sees : Word := ⟨"sees", .VERB, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def mary : Word := ⟨"Mary", .DET, { number := some .sg, person := some .third }⟩

-- Embedded Question Constraint (Wh-Islands)

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

-- Complex NP Constraint (CNPC)

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

-- Adjunct Clause Constraint

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

-- Coordinate Structure Constraint (CSC)

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

-- Subject Constraint

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

-- Combined Island Data

/-- All island constraint data -/
def islandData : List PhenomenonData := [
  embeddedQuestionConstraint,
  complexNPConstraint,
  adjunctClauseConstraint,
  coordinateStructureConstraint,
  subjectConstraint
]

-- Constraint Types (for categorization)

/-- Types of island constraints (descriptive labels) -/
inductive ConstraintType where
  | embeddedQuestion  -- Wh-word blocks further wh-dependency
  | complexNP         -- Complex NP blocks dependency
  | adjunct           -- Adjunct clause blocks dependency
  | coordinate        -- Coordination blocks asymmetric dependency
  | subject           -- Subject position blocks dependency
  | sententialSubject -- Sentential subject blocks dependency
  | mannerOfSpeaking  -- MoS verb complement backgrounds content (Lu, Pan & Degen 2025)
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
  | .mannerOfSpeaking => .weak      -- Ameliorated by prosodic focus (Lu et al. 2025)

/-- Source of an island constraint: what mechanism produces it.
Distinguishes structural accounts (subjacency), processing accounts
(memory load), and discourse accounts (information structure). -/
inductive IslandSource where
  /-- Syntactic: island follows from structural configuration (Ross 1967, Chomsky 1973) -/
  | syntactic
  /-- Processing: island is an artifact of memory/retrieval difficulty (Hofmeister & Sag 2010) -/
  | processing
  /-- Discourse: island arises from information-structural backgroundedness (Goldberg 2006, 2013;
  Lu, Pan & Degen 2025) -/
  | discourse
  deriving Repr, DecidableEq, BEq

/-- Classification of island constraints by source.
Traditional islands are syntactic; MoS islands are discourse-based.
Note: this classification is itself debated — Hofmeister & Sag (2010) argue that many
"syntactic" islands are actually processing-based. See `Comparisons/Islands.lean`. -/
def constraintSource : ConstraintType → IslandSource
  | .embeddedQuestion  => .syntactic  -- but see H&S 2010 for processing account
  | .complexNP         => .syntactic  -- but see H&S 2010 for processing account
  | .adjunct           => .syntactic
  | .coordinate        => .syntactic
  | .subject           => .syntactic
  | .sententialSubject => .syntactic
  | .mannerOfSpeaking  => .discourse  -- Lu, Pan & Degen 2025

/-- MoS islands are the only discourse-sourced island type currently formalized. -/
theorem mos_is_discourse_island :
    constraintSource .mannerOfSpeaking = .discourse := rfl

/-- MoS islands are weak (ameliorable). -/
theorem mos_is_weak :
    constraintStrength .mannerOfSpeaking = .weak := rfl

-- ============================================================================
-- Processing Factors (Hofmeister & Sag 2010, §3)
-- ============================================================================

/-!
## Gradience in Island Effects

Hofmeister & Sag (2010) argue that the binary strong/weak classification
(Szabolcsi 2006) is insufficient. Island effects are **gradient** along multiple
dimensions, and acceptability varies systematically with nonstructural
manipulations that leave island configurations intact.

This challenges every categorical island constraint proposed:
- Subjacency (Chomsky 1973)
- Complex NP Constraint (Ross 1967)
- Barriers (Chomsky 1986)
- Minimal Link Condition (Chomsky 1995)

See `Phenomena.FillerGap.Compare` for the competence vs. performance comparison.
-/

/-- Processing factors that independently contribute to the difficulty of
filler-gap dependencies inside islands (Hofmeister & Sag 2010, §3). -/
inductive ProcessingFactor where
  /-- Distance between filler and gap increases memory load (§3.1).
  Confirmed by: Gibson 1998, 2000; Hawkins 1999; Grodner & Gibson 2005. -/
  | locality
  /-- Referential processing of intervening constituents depletes resources (§3.2).
  Definites trigger referent search; proper names > definites > indefinites > pronouns
  in processing cost (Warren & Gibson 2002, 2005; Ariel 1990). -/
  | referentialLoad
  /-- Clause boundaries impose processing cost independent of extraction (§3.3).
  Even in yes-no questions, different complementizers elicit different neurological
  responses and acceptability (Kluender & Kutas 1993b). -/
  | clauseBoundary
  /-- Syntactic/semantic complexity of the filler phrase affects retrieval (§3.4).
  Counterintuitively, MORE complex fillers REDUCE processing difficulty
  because richer representations resist interference and aid retrieval
  (Hofmeister 2007). -/
  | fillerComplexity
  deriving Repr, DecidableEq, BEq

/-- Complexity of the displaced wh-phrase.

Hofmeister & Sag's central manipulation across all three experiments.
More complex fillers (*which*-N phrases) facilitate processing inside islands,
because richer representations aid memory retrieval (§3.4). -/
inductive FillerType where
  /-- Bare wh-word: *who*, *what* -/
  | bare
  /-- Complex wh-phrase: *which convict*, *which employee* -/
  | whichN
  deriving Repr, DecidableEq, BEq

/-- Type of the island-forming NP (Experiment 1 only).

Definite NPs trigger referent search and presupposition accommodation,
consuming resources needed for dependency resolution (§3.2). -/
inductive IslandNPType where
  /-- Definite singular: *the report* -/
  | definite
  /-- Indefinite plural: *reports* -/
  | plural
  /-- Indefinite singular: *a report* -/
  | indefinite
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Experimental Acceptability Data (Hofmeister & Sag 2010)
-- ============================================================================

/-- An experimental condition from Hofmeister & Sag 2010.
Acceptability stored as Nat (judgment ratio × 100, so 78 means 0.78). -/
structure IslandCondition where
  island : ConstraintType
  filler : FillerType
  npType : Option IslandNPType
  /-- Mean judgment ratio × 100 -/
  acceptability : Nat
  citation : String
  deriving Repr

/-- Experiment 1: CNPC violations (§5). 36 items, (2 × 3) + 1 design.
Acceptability ratings on 1–8 scale, normalized as ratio of subject mean.
Data from Figure 3 (p. 393). -/
def cnpcAcceptability : List IslandCondition := [
  { island := .complexNP, filler := .bare, npType := some .definite,
    acceptability := 60, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .bare, npType := some .indefinite,
    acceptability := 65, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .bare, npType := some .plural,
    acceptability := 62, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .whichN, npType := some .definite,
    acceptability := 78, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .whichN, npType := some .indefinite,
    acceptability := 82, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .whichN, npType := some .plural,
    acceptability := 85, citation := "H&S 2010, Exp 1, Fig. 3" }
]

/-- Experiment 2: Wh-island violations (§6). 24 items, 2 + 1 design.
Acceptability on 1–7 scale, normalized.
Data from Figure 5 (p. 397).
Key finding: F1(1,15)=15.964, p=0.001; F2(1,19)=14.428, p=0.001. -/
def whIslandAcceptability : List IslandCondition := [
  { island := .embeddedQuestion, filler := .bare, npType := none,
    acceptability := 57, citation := "H&S 2010, Exp 2, Fig. 5" },
  { island := .embeddedQuestion, filler := .whichN, npType := none,
    acceptability := 76, citation := "H&S 2010, Exp 2, Fig. 5" }
]

/-- Non-island baseline acceptability (CNPC experiment, Figure 3). -/
def cnpcBaseline : Nat := 108

-- ============================================================================
-- Key Empirical Generalizations
-- ============================================================================

/-- Average acceptability for a filler type across a set of conditions. -/
def avgAcceptability (conditions : List IslandCondition) (f : FillerType) : Nat :=
  let filtered := conditions.filter (·.filler == f)
  if filtered.isEmpty then 0
  else filtered.foldl (· + ·.acceptability) 0 / filtered.length

/-- **Filler complexity effect in CNPC**: which-N > bare wh (§5.2).
F1(1,20)=48.741, p<0.0001; F2(1,35)=39.494, p<0.0001.
The structure is identical — only the filler changes. -/
theorem cnpc_whichN_gt_bare :
    avgAcceptability cnpcAcceptability .whichN >
    avgAcceptability cnpcAcceptability .bare := by native_decide

/-- **Filler complexity effect in wh-islands**: which-N > bare wh (§6.2).
F1(1,15)=15.964, p=0.001. -/
theorem whIsland_whichN_gt_bare :
    avgAcceptability whIslandAcceptability .whichN >
    avgAcceptability whIslandAcceptability .bare := by native_decide

/-- **NP type effect**: indefinite > definite across both filler types (§5.2).
Consistent with lower referential processing cost for indefinites. -/
theorem cnpc_indefinite_gt_definite :
    let indef := cnpcAcceptability.filter (·.npType == some .indefinite)
    let def_ := cnpcAcceptability.filter (·.npType == some .definite)
    indef.foldl (· + ·.acceptability) 0 >
    def_.foldl (· + ·.acceptability) 0 := by native_decide

/-- Even the best island condition (which-PL, 85) remains below the
non-island baseline (108). Islands are ameliorated, not eliminated. -/
theorem best_island_lt_baseline :
    (85 : Nat) < cnpcBaseline := by native_decide

-- Tests

#eval wordsToString [what, did, john, buy]                    -- "what did John buy"
#eval wordsToString [what, do_, you, wonder, who, bought]    -- "*what do you wonder who bought"
#eval wordsToString [what, did, john, buy, and_, sell]       -- "what did John buy and sell" (ATB)
