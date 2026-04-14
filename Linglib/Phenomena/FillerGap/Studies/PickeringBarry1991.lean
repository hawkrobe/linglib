import Linglib.Core.ProcessingModel
import Linglib.Phenomena.WordOrder.CrossSerial

/-!
# Pickering & Barry (1991)
@cite{pickering-barry-1991}

Sentence Processing without Empty Categories.
*Language and Cognitive Processes*, 6(3), 229–259.

## Core Thesis

Processing of unbounded dependencies does not involve empty categories
(traces). Fillers associate directly with their subcategorizing verbs —
**filler-verb association** — without intermediary gap sites. Processing
difficulty is determined by the **nesting pattern** of filler-verb associations:

- **Nested** (abba): must hold first filler while processing inner pairs → hard
- **Disjoint** (aabb): each pair completed before the next begins → easy

This single distinction correctly predicts processing difficulty across four
sentence types (Table 2), where the trace-based account (requiring separate
filler-gap and gap-verb association patterns) makes incorrect predictions
for multiple pied-piping constructions.

## Connection to CCG

The gap-free account is made possible by CCG's forward composition (the B
combinator), which allows partial constituents like S/NP for "John saw"
without positing a gap after "saw." In the derivation of "Sue wonders whom
John saw" (ex 84):

- John : NP type-raises to S/(S\NP) via T
- saw : (S\NP)/NP
- T(John) >B saw yields S/NP — a sentence missing an object
- whom : Q/(S/NP) combines with S/NP to form Q

No empty category is needed because composition creates the filler-verb
association directly. This is the `subject_verb_composition` theorem in
`CCG.Combinators`.

## Sections

- §1: Association patterns and the two competing analyses
- §2: The four sentence types with empirical difficulty
- §3: Table 2 — the gap-free classification and its processing predictions
- §4: Contrast with the trace-based analysis (Table 1)
- §5: Bridges to ProcessingProfile, CrossSerial, and CCG
-/

namespace Phenomena.FillerGap.Studies.PickeringBarry1991

open ProcessingModel

-- ============================================================================
-- §1: Association Patterns
-- ============================================================================

/-- Nesting pattern of associations in a sentence.

Two concurrent associations can be nested (abba: the second pair is
enclosed within the first) or disjoint (aabb: each pair completed
before the next begins).

This is the central formal object of @cite{pickering-barry-1991}. -/
inductive NestingPattern where
  | nested   -- abba: hard (must hold unfinished association in memory)
  | disjoint -- aabb: easy (each association completed sequentially)
  deriving DecidableEq, Repr

/-- Under the gap-free account, there is only one type of association:
filler-verb. Under the trace account, there are two: filler-gap and gap-verb.

The trace account must classify both patterns independently, while the
gap-free account needs only one. -/
inductive AnalysisType where
  | gapFree    -- 1 association type: filler-verb
  | traceBased -- 2 association types: filler-gap + gap-verb
  deriving DecidableEq, Repr

/-- Number of independent association types required by each analysis. -/
def AnalysisType.associationTypes : AnalysisType → Nat
  | .gapFree => 1
  | .traceBased => 2

/-- The gap-free analysis is simpler: fewer association types to track. -/
theorem gapFree_simpler :
    AnalysisType.gapFree.associationTypes <
    AnalysisType.traceBased.associationTypes := by native_decide

-- ============================================================================
-- §2: The Four Sentence Types
-- ============================================================================

/-- The four sentence types classified in Tables 1 and 2 (p. 242, 246).

Each involves multiple extractions and exhibits characteristic processing
difficulty that discriminates between the two analyses. -/
inductive SentenceType where
  /-- "I saw the farmer who owned the dog which chased the cat." (ex 44)
  Subject extracted from each relative clause. -/
  | engMultiSubjRel
  /-- "The cat which the dog which the farmer owned chased fled." (ex 45)
  Object extracted from each relative clause (center-embedded). -/
  | engMultiObjRel
  /-- "Der Bauer der das Mädchen das den Jungen küßte schlug ging." (ex 48)
  German: subject extracted, verb-final order creates nesting. -/
  | gerMultiSubjRel
  /-- "John found the saucer on which Mary put the cup into which
  I poured the tea." (ex 42) Pied-piped PPs, successive relatives. -/
  | engMultiPiedPiping
  deriving DecidableEq, Repr

/-- Observed processing difficulty. -/
inductive Difficulty where
  | easy -- Extensible without processing cost increase
  | hard -- Difficulty increases with each additional embedding
  deriving DecidableEq, Repr

/-- Empirical processing difficulty for each sentence type.

Subject relatives and pied-piping are easy to extend with further
relative clauses (exx 51, 54–55); object relatives and German subject
relatives become rapidly incomprehensible (exx 52–53). -/
def observedDifficulty : SentenceType → Difficulty
  | .engMultiSubjRel   => .easy
  | .engMultiObjRel    => .hard
  | .gerMultiSubjRel   => .hard
  | .engMultiPiedPiping => .easy

-- ============================================================================
-- §3: Table 2 — Gap-Free Analysis
-- ============================================================================

/-- Filler-verb association pattern under the gap-free analysis (Table 2).

This is the ONLY association type needed. The annotation scheme from
p. 245:
- Subject relative (ex 56): [who]₁ [owned]₁ ... [which]₂ [chased]₂
  → disjoint (1122)
- Object relative (ex 57): [which]₁ ... [which]₂ [owned]₂ [chased]₁
  → nested (1221)
- German subj rel (ex 58): [der]₁ [das]₂ [küßte]₂ [schlug]₁
  → nested (1221)
- Pied-piping (ex 59): [on which]₁ [put]₁ [into which]₂ [poured]₂
  → disjoint (1122) -/
def fillerVerbPattern : SentenceType → NestingPattern
  | .engMultiSubjRel    => .disjoint
  | .engMultiObjRel     => .nested
  | .gerMultiSubjRel    => .nested
  | .engMultiPiedPiping => .disjoint

/-- Is the construction nested in Chomsky's (1965) sense?

Under the gap-free analysis (no empty categories), the definition
simplifies: a construction is nested iff its filler-verb associations
are nested. This collapse is the central result. -/
def isNestedConstruction : SentenceType → Bool
  | .engMultiSubjRel    => false
  | .engMultiObjRel     => true
  | .gerMultiSubjRel    => true
  | .engMultiPiedPiping => false

/-- **Table 2 correspondence** (p. 246): under the gap-free analysis,
the filler-verb pattern directly determines construction nestedness.

Table 1 (trace-based) has three independent columns (filler-gap pattern,
gap-verb pattern, construction type) with no systematic relationship.
Table 2 collapses to two identical columns. -/
theorem table2_correspondence :
    ∀ s : SentenceType,
    (fillerVerbPattern s = .nested) ↔ (isNestedConstruction s = true) := by
  intro s; cases s <;> simp [fillerVerbPattern, isNestedConstruction]

/-- Gap-free processing prediction: nested filler-verb associations are
hard, disjoint are easy. -/
def gapFreePrediction (s : SentenceType) : Difficulty :=
  match fillerVerbPattern s with
  | .nested => .hard
  | .disjoint => .easy

/-- **The gap-free analysis correctly predicts all four observations.** -/
theorem gapFree_all_correct :
    ∀ s : SentenceType, gapFreePrediction s = observedDifficulty s := by
  intro s; cases s <;> rfl

-- ============================================================================
-- §4: Contrast with Trace-Based Analysis (Table 1)
-- ============================================================================

/-- Filler-gap pattern under the trace-based analysis (Table 1). -/
def fillerGapPattern : SentenceType → NestingPattern
  | .engMultiSubjRel    => .disjoint
  | .engMultiObjRel     => .nested
  | .gerMultiSubjRel    => .disjoint  -- filler-gap is disjoint!
  | .engMultiPiedPiping => .nested

/-- Gap-verb pattern under the trace-based analysis (Table 1). -/
def gapVerbPattern : SentenceType → NestingPattern
  | .engMultiSubjRel    => .disjoint
  | .engMultiObjRel     => .disjoint
  | .gerMultiSubjRel    => .nested
  | .engMultiPiedPiping => .nested

/-- Trace-based prediction: a construction is hard if EITHER filler-gap
or gap-verb associations are nested. -/
def traceBasedPrediction (s : SentenceType) : Difficulty :=
  if fillerGapPattern s == .nested || gapVerbPattern s == .nested
  then .hard else .easy

/-- The trace-based analysis incorrectly predicts pied-piping is hard.
It has nested filler-gap AND nested gap-verb (Table 1), yet the
construction is easy to process and easily extensible (exx 54–55). -/
theorem traceBased_piedPiping_wrong :
    traceBasedPrediction .engMultiPiedPiping ≠
    observedDifficulty .engMultiPiedPiping := by native_decide

/-- The gap-free analysis correctly predicts pied-piping is easy —
the critical case where it outperforms the trace-based account. -/
theorem gapFree_piedPiping_correct :
    gapFreePrediction .engMultiPiedPiping =
    observedDifficulty .engMultiPiedPiping := rfl

/-- Table 1 has no systematic relationship between its three columns.
The filler-gap pattern, gap-verb pattern, and construction type are
all independent. German subject relatives are nested constructions
with disjoint filler-gap associations — the columns disagree. -/
theorem table1_columns_disagree :
    fillerGapPattern .gerMultiSubjRel = .disjoint ∧
    gapVerbPattern .gerMultiSubjRel = .nested ∧
    isNestedConstruction .gerMultiSubjRel = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §5: Bridges
-- ============================================================================

/-! ### Bridge to ProcessingProfile -/

/-- Map nesting pattern to ProcessingProfile.

Nested associations require holding unfinished fillers in working memory
while forming inner associations — higher locality (longer dependency span)
and referential load (more intervening material to track). -/
def nestingProfile : NestingPattern → ProcessingProfile
  | .nested =>
    { locality := 4, boundaries := 2, referentialLoad := 2, ease := 0 }
  | .disjoint =>
    { locality := 2, boundaries := 0, referentialLoad := 0, ease := 1 }

instance : HasProcessingProfile SentenceType where
  profile s := nestingProfile (fillerVerbPattern s)

/-- Nested associations are Pareto-harder than disjoint. -/
theorem nested_harder_than_disjoint :
    (nestingProfile .nested).compare (nestingProfile .disjoint) =
    .harder := by native_decide

/-- Processing ordering predictions verified via Pareto dominance. -/
def orderingPredictions : List (OrderingPrediction SentenceType) := [
  { harder := .engMultiObjRel
    easier := .engMultiSubjRel
    description := "Object relatives harder than subject relatives" },
  { harder := .gerMultiSubjRel
    easier := .engMultiPiedPiping
    description := "German subject relatives harder than pied-piping" },
  { harder := .engMultiObjRel
    easier := .engMultiPiedPiping
    description := "Object relatives harder than pied-piping" },
  { harder := .gerMultiSubjRel
    easier := .engMultiSubjRel
    description := "German subject relatives harder than English" }
]

theorem all_orderings_verified :
    orderingPredictions.all verifyOrdering = true := by native_decide

/-! ### Bridge to CrossSerial dependencies -/

/-- German verb-final order produces nested filler-verb associations,
consistent with the nested dependency pattern in German verb clusters
(`CrossSerial.german_3np_3v`). Both German constructions — subject
relatives and verb clusters — exhibit nesting because the verb that
closes each dependency comes in reverse order.

@cite{bach-brown-marslen-wilson-1986} confirms the processing prediction:
German nested constructions are hard, like their Dutch cross-serial
counterparts (though for different structural reasons). -/
theorem german_nested_consistent :
    fillerVerbPattern .gerMultiSubjRel = .nested ∧
    Phenomena.WordOrder.CrossSerial.german_3np_3v.binding.pattern = .nested :=
  ⟨rfl, by decide⟩

/-! ### Bridge to CCG combinators

The gap-free account requires a grammar that can establish filler-verb
associations without positing gap positions. CCG achieves this via forward
composition (B) and type-raising (T):

  `subject_verb_composition` in `CCG.Combinators` proves:
    B (T subj) verb obj = verb obj subj

This is exactly derivation (84) in the paper: "John saw" becomes
a constituent S/NP via rule (80a) (type-raising + composition), and
"whom" : Q/(S/NP) combines with S/NP to form Q — no trace needed. The variable-free semantics
(`ccgVariableFree` in `CCG.Combinators`) guarantees that all semantic
operations use combinators rather than bound variables, which is the
formal counterpart of "no empty categories." -/

end Phenomena.FillerGap.Studies.PickeringBarry1991
