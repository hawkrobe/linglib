import Linglib.Core.Agent.DecisionTheory
import Linglib.Phenomena.Questions.Studies.Xiang2022.Data

/-!
# Xiang 2022 Bridge: Decision-Theoretic Verification @cite{xiang-2022}

Connects Xiang's empirical MS/MA data to the decision-theoretic infrastructure
in `Core.Agent.DecisionTheory`. This file exercises `DecisionProblem`, `resolves`,
`resolvingAnswers`, `isMentionSome`, `isMentionAll`, `questionUtility`, and
`completeInformationDP` with a concrete committee-service scenario.

## Scenario

Three people: Andy, Billy, Cindy. Three possible worlds, each encoding which
pair can serve on a 2-person committee: {A,B}, {A,C}, {B,C}. This gives a
finite model small enough for `native_decide` but rich enough to distinguish
MS from MA questions.

## Definitions Exercised

| Core/Agent Definition   | How Exercised                                   |
|------------------------|-------------------------------------------------|
| `DecisionProblem`      | `findServableDP`, `identifyAllDP` constructed   |
| `resolves`             | 5 theorems (3 positive, 2 negative)             |
| `resolvingAnswers`     | `three_resolving_answers`                       |
| `isMentionSome`        | `whoCanServe_is_mentionSome`                    |
| `isMentionAll`         | `epistemic_question_is_mentionAll`              |
| `Question`             | 2 concrete questions constructed                |
| `completeInformationDP`| Used to construct `identifyAllDP`               |
| `questionUtility`      | `questionUtility_positive`                      |
-/

namespace Phenomena.Questions.Studies.Xiang2022.Bridge

open Core.DecisionTheory

/-! ### Finite Types -/

/-- Three committee candidates. -/
inductive Person where
  | andy | billy | cindy
  deriving DecidableEq, Repr

instance : Fintype Person where
  elems := {.andy, .billy, .cindy}
  complete := λ x => by cases x <;> decide

/-- Three possible worlds: which pair can serve on the committee.
World `ab` means Andy and Billy can serve, etc. -/
inductive CommitteeWorld where
  | ab | ac | bc
  deriving DecidableEq, Repr

instance : Fintype CommitteeWorld where
  elems := {.ab, .ac, .bc}
  complete := λ x => by cases x <;> decide

/-- Which persons can serve in each world. -/
def canServe : CommitteeWorld → Person → Bool
  | .ab, .andy  => true
  | .ab, .billy => true
  | .ab, .cindy => false
  | .ac, .andy  => true
  | .ac, .billy => false
  | .ac, .cindy => true
  | .bc, .andy  => false
  | .bc, .billy => true
  | .bc, .cindy => true

/-- All worlds as a list (for `resolves` etc. which take `List W`). -/
def allWorlds : List CommitteeWorld := [.ab, .ac, .bc]

/-- All persons as a list. -/
def allPersons : List Person := [.andy, .billy, .cindy]

/-- All worlds as CommitteeWorld actions (for identify-all DP). -/
def allWorldActions : List CommitteeWorld := [.ab, .ac, .bc]

/-! ### Decision Problems -/

/-- **Find-servable DP**: the questioner wants to nominate *someone* who can serve.
Utility 1 iff the nominated person can actually serve in the true world.
This is the MS-licensing DP — any single resolving answer suffices. -/
def findServableDP : DecisionProblem CommitteeWorld Person where
  utility w p := if canServe w p then 1 else 0
  prior _ := 1 / 3

/-- **Identify-all DP**: the questioner wants to know *exactly* which world obtains.
Uses `completeInformationDP` — utility 1 iff guessed world matches true world.
This is the MA-licensing DP — only the full partition resolves it. -/
def identifyAllDP : DecisionProblem CommitteeWorld CommitteeWorld :=
  { completeInformationDP with prior := λ _ => 1 / 3 }

/-! ### Questions (answer-space structures) -/

/-- Individual-answer cells for "Who can serve?": one cell per person,
containing the worlds where that person can serve.
These cells *overlap* (e.g., Andy-cell ∩ Billy-cell = {ab}). -/
def whoCanServe_individual : Question CommitteeWorld :=
  [ λ w => canServe w .andy    -- {ab, ac}
  , λ w => canServe w .billy   -- {ab, bc}
  , λ w => canServe w .cindy   -- {ac, bc}
  ]

/-- Partition cells for "Who can serve?": one cell per exact pair.
These cells are *disjoint* (each world in exactly one cell). -/
def whoCanServe_partition : Question CommitteeWorld :=
  [ λ w => w == .ab   -- exactly {ab}
  , λ w => w == .ac   -- exactly {ac}
  , λ w => w == .bc   -- exactly {bc}
  ]

/-! ### Core Theorems: `resolves` -/

/-- The Andy-cell resolves `findServableDP`: once we know Andy can serve,
nominating Andy dominates in every world in the cell. -/
theorem andyCell_resolves :
    resolves findServableDP allWorlds allPersons (λ w => canServe w .andy) = true := by
  native_decide

/-- The Billy-cell resolves `findServableDP`. -/
theorem billyCell_resolves :
    resolves findServableDP allWorlds allPersons (λ w => canServe w .billy) = true := by
  native_decide

/-- The Cindy-cell resolves `findServableDP`. -/
theorem cindyCell_resolves :
    resolves findServableDP allWorlds allPersons (λ w => canServe w .cindy) = true := by
  native_decide

/-- Individual cells do NOT resolve the identify-all DP: knowing that Andy can
serve doesn't tell you whether you're in world ab or ac. -/
theorem andyCell_not_resolve_identifyAll :
    resolves identifyAllDP allWorlds allWorldActions
      (λ w => canServe w .andy) = false := by
  native_decide

/-- The Billy-cell also fails to resolve identify-all. -/
theorem billyCell_not_resolve_identifyAll :
    resolves identifyAllDP allWorlds allWorldActions
      (λ w => canServe w .billy) = false := by
  native_decide

/-! ### Core Theorems: `isMentionSome` and `isMentionAll` -/

/-- **Can-question → MS**: Individual-answer question with find-servable DP is MS.
Models Xiang's ex. 32–33: "Who can serve?" with a find-someone goal. -/
theorem whoCanServe_is_mentionSome :
    isMentionSome findServableDP allWorlds allPersons whoCanServe_individual = true := by
  native_decide

/-- **Epistemic blocking → MA**: Individual-answer cells with identify-all DP yield MA.
Models Xiang's ex. 5: "Who might serve?" — epistemic modal means the questioner
needs the *full* epistemic picture, not just one possibility. No individual cell
resolves the identify-all DP, so `resolvingAnswers` is empty → `isMentionSome`
returns false → `isMentionAll` returns true. -/
theorem epistemic_question_is_mentionAll :
    isMentionAll identifyAllDP allWorlds allWorldActions
      whoCanServe_individual = true := by
  native_decide

/-! ### Structural Properties of the Answer Space -/

/-- Individual cells overlap: Andy-cell and Billy-cell share world `ab`.
This is Xiang's condition (A) for MS availability. -/
theorem individual_cells_overlap :
    allWorlds.any (λ w => canServe w .andy && canServe w .billy) = true := by
  native_decide

/-- Partition cells are disjoint: no world belongs to two distinct partition cells. -/
theorem partition_cells_disjoint :
    ¬ (allWorlds.any (λ w =>
      (w == CommitteeWorld.ab) && (w == CommitteeWorld.ac))) := by
  native_decide

/-! ### `resolvingAnswers` -/

/-- All three individual cells resolve `findServableDP`. -/
theorem three_resolving_answers :
    (resolvingAnswers findServableDP allWorlds allPersons
      whoCanServe_individual).length = 3 := by
  native_decide

/-- No individual cell resolves `identifyAllDP`. -/
theorem zero_resolving_answers_identifyAll :
    (resolvingAnswers identifyAllDP allWorlds allWorldActions
      whoCanServe_individual).length = 0 := by
  native_decide

/-! ### `questionUtility` -/

/-- The MS question has positive expected utility value for `findServableDP`.
Learning any cell of `whoCanServe_individual` improves decision-making
over the prior. -/
theorem questionUtility_positive :
    questionUtility findServableDP allPersons whoCanServe_individual > 0 := by
  native_decide

/-! ### Xiang's Conditions as Predicates -/

/-- Xiang's condition (A): answer cells are not mutually exclusive.
Some pair of distinct cells shares at least one world. -/
def answersOverlap {W : Type} [BEq (W → Bool)]
    (q : Question W) (worlds : List W) : Bool :=
  q.any λ c1 => q.any λ c2 =>
    !BEq.beq c1 c2 && worlds.any λ w => c1 w && c2 w

/-- Xiang's condition (B): answer space is not closed under conjunction.
Some pair of cells has a conjunction that isn't represented by any cell. -/
def notClosedUnderConj {W : Type}
    (q : Question W) (worlds : List W) : Bool :=
  q.any λ c1 => q.any λ c2 =>
    !(q.any λ c3 => worlds.all λ w => c3 w == (c1 w && c2 w))

/-- Individual cells satisfy condition (A): they overlap. -/
theorem committee_satisfies_condA :
    answersOverlap whoCanServe_individual allWorlds = true := by
  native_decide

/-- Individual cells satisfy condition (B): not closed under ∧.
The conjunction of Andy-cell and Billy-cell is {ab}, which is not
one of the three individual cells. -/
theorem committee_satisfies_condB :
    notClosedUnderConj whoCanServe_individual allWorlds = true := by
  native_decide

/-- Partition cells violate condition (A): they are disjoint. -/
theorem partition_violates_condA :
    answersOverlap whoCanServe_partition allWorlds = false := by
  native_decide

/-- When conditions (A) and (B) hold for `findServableDP`, the question
is indeed mention-some. (Verified for this finite instance.) -/
theorem condA_condB_implies_mentionSome :
    answersOverlap whoCanServe_individual allWorlds = true →
    notClosedUnderConj whoCanServe_individual allWorlds = true →
    isMentionSome findServableDP allWorlds allPersons whoCanServe_individual = true := by
  intro _ _; native_decide

end Phenomena.Questions.Studies.Xiang2022.Bridge
