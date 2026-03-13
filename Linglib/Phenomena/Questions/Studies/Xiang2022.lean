import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Semantics.Questions.Answerhood.Exhaustivity

/-!
# @cite{xiang-2022}: Relativized Exhaustivity @cite{xiang-2022}

Empirical data on mention-some and uniqueness from:
@cite{xiang-2022}. Relativized Exhaustivity: mention-some and uniqueness.
*Natural Language Semantics* 30:311–362.

## Overview

@cite{xiang-2022} makes three contributions:

1. MS answers are subject to a "mention-one-only" constraint: they must name
   a single individual, not a disjunction (ex. 3–4).
2. MS is primarily *grammatically* licensed by ability *can* inside the
   question nucleus, not pragmatically by decision problems. The MS/MA
   ambiguity in *can*-questions reflects structural scope ambiguity of
   the wh-trace relative to the modal (first-order vs higher-order).
3. The RelExh presupposition (91) — exhaustivity evaluated relative to
   singleton modal bases — unifies MS licensing, avoids over-generation
   for non-*can* questions, and derives local-uniqueness effects in
   modalized singular wh-questions.

## Data points

Empirical generalizations from the paper, with exact example numbers:
1. "Who can chair the committee?" — MS available (ex. 2)
2. "Who called?" — MA required (ex. 1)
3. Mention-one-only constraint (ex. 3–4)
4. Non-*can* modals block MS: *should*, *might* (ex. 6)
5. Same question, different contexts → MS vs MA (Section 2.2)
6. Singular uniqueness effects (Section 4.3, Section 6.3)
7. Table 3 summary: RelExh vs Dayal's EP predictions
-/

namespace Phenomena.Questions.Studies.Xiang2022

/-- Whether a question receives mention-some, mention-all, or is ambiguous
between the two readings. -/
inductive MSMAJudgment where
  | mentionSome
  | mentionAll
  | ambiguous
  deriving DecidableEq, Repr

/-- Type of modal in the question, which affects MS/MA availability.
Xiang's key claim: only ability *can* grammatically licenses MS. -/
inductive ModalType where
  | none
  | abilityCan
  | epistemicMight
  | deonticShould
  deriving DecidableEq, Repr

/-- A single empirical datum from @cite{xiang-2022}. -/
structure Xiang2022Datum where
  /-- The question under study -/
  question : String
  /-- What modal (if any) appears in the question -/
  modalType : ModalType
  /-- Observed MS/MA judgment -/
  judgment : MSMAJudgment
  /-- An example answer or context -/
  exampleAnswer : String
  /-- Source reference within the paper -/
  source : String
  deriving Repr

/-! ### Core data: MS licensing by modal type -/

/-- Ability *can* licenses mention-some (@cite{xiang-2022}, ex. 2).

"Who can chair the committee?" — naming a single individual is a
sufficient answer. This is the paper's central empirical observation:
MS is grammatically licensed by *can*. -/
def canQuestionMS : Xiang2022Datum :=
  { question := "Who can chair the committee?"
  , modalType := .abilityCan
  , judgment := .mentionSome
  , exampleAnswer := "Anne can. (sufficient answer)"
  , source := "Xiang 2022, ex. 2"
  }

/-- Bare wh-question requires mention-all (@cite{xiang-2022}, ex. 1).

"Who called?" — without a modal, the question demands exhaustive listing.
Non-modalized questions uniformly receive MA. -/
def bareQuestionMA : Xiang2022Datum :=
  { question := "Who called?"
  , modalType := .none
  , judgment := .mentionAll
  , exampleAnswer := "Anne and Bill called. (#Anne called, as a complete answer)"
  , source := "Xiang 2022, ex. 1"
  }

/-- Deontic *should* blocks mention-some (@cite{xiang-2022}, ex. 6b).

"Which students should pass the test?" — even though modal, deontic
modals pattern with MA. Only ability *can* licenses MS. -/
def deonticBlocksMS : Xiang2022Datum :=
  { question := "Which students should pass the test?"
  , modalType := .deonticShould
  , judgment := .mentionAll
  , exampleAnswer := "All students who should. (#Anne should, as a complete answer)"
  , source := "Xiang 2022, ex. 6b"
  }

/-- Epistemic *might* blocks mention-some (@cite{xiang-2022}, ex. 6c).

"Which students might pass the test?" — epistemics pattern with MA,
not MS. The question demands the full epistemic picture. -/
def epistemicBlocksMS : Xiang2022Datum :=
  { question := "Which students might pass the test?"
  , modalType := .epistemicMight
  , judgment := .mentionAll
  , exampleAnswer := "All students who might. (#Anne might, as a complete answer)"
  , source := "Xiang 2022, ex. 6c"
  }

/-- Non-modalized question requires MA (@cite{xiang-2022}, ex. 6a).

"Which students passed the test?" — without a modal, exhaustive. -/
def nonModalMA : Xiang2022Datum :=
  { question := "Which students passed the test?"
  , modalType := .none
  , judgment := .mentionAll
  , exampleAnswer := "All students who passed."
  , source := "Xiang 2022, ex. 6a"
  }

/-! ### Context sensitivity (Section 2.2) -/

/-- Goal-driven MS: same question, recruit-one goal (@cite{xiang-2022}, Section 2.2).

"Who can chair the committee?" with the goal of recruiting *one* person.
@cite{van-rooij-2003} models this via a decision problem where any single
committee member resolves the DP. -/
def goalDrivenMS : Xiang2022Datum :=
  { question := "Who can chair the committee?"
  , modalType := .abilityCan
  , judgment := .mentionSome
  , exampleAnswer := "Context: We need to recruit one more member. → Anne can."
  , source := "Xiang 2022, Section 2.2 (cf. van Rooij 2003)"
  }

/-- Goal-driven MA: same question, know-all goal (@cite{xiang-2022}, Section 2.2).

Same question as above, but the goal of knowing the *full* candidate list.
The DP requires complete information, so all candidates must be named. -/
def goalDrivenMA : Xiang2022Datum :=
  { question := "Who can chair the committee?"
  , modalType := .abilityCan
  , judgment := .mentionAll
  , exampleAnswer := "Context: We want a complete roster. → Anne and Bill can."
  , source := "Xiang 2022, Section 2.2 (cf. van Rooij 2003)"
  }

/-! ### Mention-one-only constraint (ex. 3–4) -/

/-- Whether an MS answer obeys the mention-one-only constraint. -/
structure MentionOneOnlyDatum where
  /-- The question -/
  question : String
  /-- The proposed MS answer -/
  answer : String
  /-- Is this answer acceptable as an MS answer? -/
  acceptable : Bool
  /-- Source -/
  source : String
  deriving Repr

/-- Valid MS answer: single individual (@cite{xiang-2022}, ex. 3a).

"Anne can." — a single-individual MS answer is acceptable. -/
def mentionOneValid : MentionOneOnlyDatum :=
  { question := "Who can chair the committee?"
  , answer := "Anne can."
  , acceptable := true
  , source := "Xiang 2022, ex. 3a"
  }

/-- Invalid MS answer: disjunction (@cite{xiang-2022}, ex. 3b).

"#Anne or Bill can." — a disjunctive MS answer is blocked by
the mention-one-only constraint. This is NOT predicted by
van Rooij's decision-theoretic account but IS predicted by
Xiang's semantic analysis. -/
def mentionOneInvalid : MentionOneOnlyDatum :=
  { question := "Who can chair the committee?"
  , answer := "#Anne or Bill can."
  , acceptable := false
  , source := "Xiang 2022, ex. 3b"
  }

/-! ### Uniqueness effects (Section 4.3, Section 6.3) -/

/-- Types of uniqueness inference observed in singular wh-questions.
Xiang distinguishes global vs local uniqueness (Table 3). -/
inductive UniquenessType where
  | global       -- exactly one individual satisfies P in every accessible world
  | local        -- in each accessible world, at most one individual satisfies P
  | existLocal   -- "existential" local uniqueness (weaker, via existential closure)
  | none
  deriving DecidableEq, Repr

/-- A datum about uniqueness effects in singular wh-questions. -/
structure UniquenessDatum where
  /-- The question -/
  question : String
  /-- Modal type -/
  modalType : ModalType
  /-- Type of uniqueness inference -/
  uniqueness : UniquenessType
  /-- Whether Dayal's EP predicts this -/
  dayalEPPredicts : Bool
  /-- Whether RelExh predicts this -/
  relExhPredicts : Bool
  /-- Source -/
  source : String
  deriving Repr

/-- Non-modalized singular: global uniqueness.
"Which child came?" — presupposes exactly one child came.
Both Dayal's EP and RelExh predict this. (Table 3, row 1) -/
def nonModalUniqueness : UniquenessDatum :=
  { question := "Which child came?"
  , modalType := .none
  , uniqueness := .global
  , dayalEPPredicts := true
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 64"
  }

/-- □-modal singular (have-to), global uniqueness.
"Which chapter do we have to assign?" — global uniqueness reading.
Both Dayal's EP and RelExh predict. (Table 3, row 3) -/
def boxModalGlobalUniq : UniquenessDatum :=
  { question := "Which chapter do we have to assign?"
  , modalType := .deonticShould
  , uniqueness := .global
  , dayalEPPredicts := true
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 99/102"
  }

/-- □-modal singular (have-to), local uniqueness.
"Which chapter do we have to assign?" — local uniqueness reading.
Dayal's EP does NOT predict this; RelExh DOES. This is a key
advantage of RelExh over Dayal's EP. (Table 3, row 4) -/
def boxModalLocalUniq : UniquenessDatum :=
  { question := "Which chapter do we have to assign?"
  , modalType := .deonticShould
  , uniqueness := .local
  , dayalEPPredicts := false
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 99/103"
  }

/-- ◇-modal singular (can), local uniqueness in MS.
"Which chapter can we assign?" — existential local uniqueness.
Dayal's EP does NOT predict; RelExh DOES. (Table 3, row 8) -/
def canModalLocalUniqMS : UniquenessDatum :=
  { question := "Which chapter can we assign?"
  , modalType := .abilityCan
  , uniqueness := .existLocal
  , dayalEPPredicts := false
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 100–101/105b"
  }

/-- ◇-modal singular (can), global uniqueness.
"Which chapter can we assign?" — global uniqueness.
Dayal's EP predicts this but RelExh does NOT — the only cell in
Table 3 where Dayal's EP has coverage that RelExh lacks. (Table 3, row 7) -/
def canModalGlobalUniq : UniquenessDatum :=
  { question := "Which chapter can we assign?"
  , modalType := .abilityCan
  , uniqueness := .global
  , dayalEPPredicts := true
  , relExhPredicts := false
  , source := "Xiang 2022, Table 3, row 7"
  }

def uniquenessData : List UniquenessDatum :=
  [ nonModalUniqueness, boxModalGlobalUniq, boxModalLocalUniq
  , canModalLocalUniqMS, canModalGlobalUniq ]

/-! ### Aggregation -/

/-- All MS/MA judgment data points from the paper. -/
def allData : List Xiang2022Datum :=
  [ canQuestionMS, bareQuestionMA, deonticBlocksMS, epistemicBlocksMS
  , nonModalMA, goalDrivenMS, goalDrivenMA ]

/-- Data points classified as mention-some. -/
def msCount : Nat :=
  allData.filter (λ d => d.judgment == .mentionSome) |>.length

/-- Data points classified as mention-all. -/
def maCount : Nat :=
  allData.filter (λ d => d.judgment == .mentionAll) |>.length

/-- Table 3 cells where RelExh has coverage that Dayal's EP lacks. -/
def relExhAdvantages : Nat :=
  uniquenessData.filter (λ d => d.relExhPredicts && !d.dayalEPPredicts) |>.length

/-- Table 3 cells where Dayal's EP has coverage that RelExh lacks. -/
def dayalAdvantages : Nat :=
  uniquenessData.filter (λ d => d.dayalEPPredicts && !d.relExhPredicts) |>.length

/-! ## Bridge: RelExh Derivation + Decision-Theoretic Agreement

Formalizes the derivation chain from @cite{xiang-2022}, Section 5.2 (ex. 93):

1. Define the paper's own scenario (3 worlds, 2 individuals, ability modal base)
2. Show EP fails for the FO can-question (overlapping answer propositions)
3. Show RelExh passes (each singleton modal base has a strongest answer)
4. Show DecisionTheory independently classifies this as mention-some
5. Prove both frameworks agree on the same finite model
6. Contrast with partition reading: EP holds → MA

This connects Xiang's semantic theory (`Theories.Semantics.Questions.Exhaustivity`)
to the decision-theoretic infrastructure (`Core.Agent.DecisionTheory`) through
a shared concrete scenario, exercising both and proving agreement.

### Scenario (ex. 93)

- Worlds: w0 (utterance world), w1, w2
- Individuals: a, b
- Base predicate: chairs(w1, a) = true, chairs(w2, b) = true, else false
- Ability modal base: mb(w0) = [w1, w2], mb(w1) = [w1], mb(w2) = [w2]

Under the FO interpretation, "Who can chair?" gets overlapping cells:
- ◇chair(a) = {w0, w1} (a can chair at w0 via w1, and trivially at w1)
- ◇chair(b) = {w0, w2} (b can chair at w0 via w2, and trivially at w2)

These overlap at w0 → EP fails → but RelExh passes → MS licensed.

### Definitions Exercised

| Definition              | Source                      | How Exercised                    |
|-------------------------|-----------------------------|----------------------------------|
| `dayalEP`               | Exhaustivity.lean           | 2 theorems (fails FO, holds partition) |
| `relExh`                | Exhaustivity.lean           | 2 theorems (passes FO, holds partition) |
| `foQDen`                | Exhaustivity.lean           | Used throughout scenario         |
| `propEntails`           | Exhaustivity.lean           | 2 theorems (incomparability)     |
| `DecisionProblem`       | Core.Agent.DecisionTheory   | findChairDP, identifyAllDP       |
| `isMentionSome`         | Core.Agent.DecisionTheory   | canQ_mentionSome                 |
| `isMentionAll`          | Core.Agent.DecisionTheory   | foQ_identifyAll_mentionAll       |
| `questionUtility`       | Core.Agent.DecisionTheory   | questionUtility_positive         |
| `completeInformationDP` | Core.Agent.DecisionTheory   | identifyAllDP                    |
-/

open Core.DecisionTheory
open Theories.Semantics.Questions.Exhaustivity

/-! ### Finite Types (ex. 93 scenario) -/

/-- Three worlds: w0 is the utterance world, w1 and w2 are accessible. -/
inductive XW where
  | w0 | w1 | w2
  deriving DecidableEq, Repr, BEq

instance : Fintype XW where
  elems := {.w0, .w1, .w2}
  complete := λ x => by cases x <;> decide

/-- Two individuals who might chair the committee. -/
inductive XP where
  | a | b
  deriving DecidableEq, Repr, BEq

instance : Fintype XP where
  elems := {.a, .b}
  complete := λ x => by cases x <;> decide

/-! ### Base Predicate and Modal Base -/

/-- Base predicate: who actually chairs in each world.
In w1, individual a chairs; in w2, individual b chairs; w0 is the
utterance world where no one directly chairs. -/
def chairs : XW → XP → Bool
  | .w1, .a => true
  | .w2, .b => true
  | _,   _  => false

/-- Ability modal base: from w0, both w1 and w2 are accessible
(representing what is possible). From w1/w2, only the world itself
is accessible (the abilities are settled). -/
def abilityMB : XW → List XW
  | .w0 => [.w1, .w2]
  | .w1 => [.w1]
  | .w2 => [.w2]

/-- All worlds in the scenario. -/
def allWorlds : List XW := [.w0, .w1, .w2]

/-- All individuals. -/
def allIndividuals : List XP := [.a, .b]

/-! ### FO Question Denotation (can-question, wh below modal)

Under the FO interpretation, the question "Who can chair?" has denotation:
  ⟦who can chair⟧(mb)(α)(w) = ∃v ∈ mb(w). chairs(v, α)

This gives overlapping cells at w0:
- ◇chair(a) at w0: w1 ∈ mb(w0) and chairs(w1,a) → true
- ◇chair(b) at w0: w2 ∈ mb(w0) and chairs(w2,b) → true
-/

/-- The FO cells as explicit propositions, for use with DecisionTheory. -/
def foCells : Question XW :=
  [ foQDen chairs abilityMB .a
  , foQDen chairs abilityMB .b
  ]

/-! ### Partition Question Denotation (HO reading / non-modal)

Under the partition interpretation, each cell identifies a single world.
This models the higher-order reading where the questioner wants to know
exactly which world obtains. -/

/-- Partition qden: ignores modal base, directly tests world identity. -/
def partQDen : (XW → List XW) → XW → XW → Bool :=
  λ _ target w => w == target

/-- Partition cells: one cell per world. -/
def partCells : Question XW :=
  [ λ w => w == XW.w0
  , λ w => w == XW.w1
  , λ w => w == XW.w2
  ]

/-! ### Decision Problems -/

/-- Find-chair DP: utility 1 iff the nominated person can chair in some
accessible world. Models the "recruit one committee member" context. -/
def findChairDP : DecisionProblem XW XP where
  utility w p := if (abilityMB w).any (chairs · p) then 1 else 0
  prior _ := 1 / 3

/-- Identify-all DP: utility 1 iff guessed world matches true world.
Models the "complete roster" context. -/
def identifyAllDP : DecisionProblem XW XW :=
  { completeInformationDP with prior := λ _ => 1 / 3 }

/-! ## Part I: EP/RelExh Derivation Chain (@cite{xiang-2022}, Section 5.2)

The derivation follows ex. 93 exactly:
1. Both a and b are true answers at w0 under FO interpretation
2. Their propositions are incomparable (neither entails the other)
3. Therefore EP fails at w0 (no strongest true answer)
4. But RelExh passes: each singleton {w1}, {w2} has EP
5. Therefore MS is semantically licensed
-/

/-! ### Step 1: True answers at w0 -/

/-- ◇chair(a) holds at w0: there exists v ∈ mb(w0) where a chairs (namely w1). -/
theorem foAnswer_true_a : foQDen chairs abilityMB .a .w0 = true := by native_decide

/-- ◇chair(b) holds at w0: there exists v ∈ mb(w0) where b chairs (namely w2). -/
theorem foAnswer_true_b : foQDen chairs abilityMB .b .w0 = true := by native_decide

/-! ### Step 2: Propositions are incomparable -/

/-- The a-proposition does not entail the b-proposition.
◇chair(a) = {w0, w1} and ◇chair(b) = {w0, w2}: w1 ∈ ◇chair(a) but w1 ∉ ◇chair(b). -/
theorem propExt_a_not_entails_b :
    propEntails (foQDen chairs abilityMB .a) (foQDen chairs abilityMB .b) allWorlds = false := by
  native_decide

/-- The b-proposition does not entail the a-proposition.
w2 ∈ ◇chair(b) but w2 ∉ ◇chair(a). -/
theorem propExt_b_not_entails_a :
    propEntails (foQDen chairs abilityMB .b) (foQDen chairs abilityMB .a) allWorlds = false := by
  native_decide

/-! ### Step 3: EP fails -/

/-- **EP fails for the FO can-question at w0** (@cite{xiang-2022}, ex. 93).

Both a and b are true answers at w0, but neither proposition entails the other
(they overlap at w0 but diverge at w1 vs w2). So there is no strongest true
answer, and Dayal's exhaustivity presupposition is not met. -/
theorem canQ_ep_fails :
    dayalEP (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = false := by
  native_decide

/-! ### Step 4: RelExh passes -/

/-- **RelExh passes for the FO can-question at w0** (@cite{xiang-2022}, ex. 93).

For each v ∈ mb(w0) = {w1, w2}:
- Singleton {w1}: only a chairs → ◇chair(a) is the unique true answer → EP holds
- Singleton {w2}: only b chairs → ◇chair(b) is the unique true answer → EP holds

Since EP holds for every singleton subbase, RelExh is satisfied. -/
theorem canQ_relExh_passes :
    relExh (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = true := by
  native_decide

/-! ### Step 5: DecisionTheory agrees -/

/-- DecisionTheory independently classifies the FO can-question as mention-some.
Both FO cells resolve `findChairDP` (learning that a can chair → nominate a;
learning that b can chair → nominate b), and the cells overlap at w0. -/
theorem canQ_mentionSome :
    isMentionSome findChairDP {.w0, .w1, .w2} {.a, .b} foCells = true := by
  native_decide

/-- **Semantic–pragmatic agreement on MS**: RelExh passes AND DecisionTheory
says mention-some, on the same finite model. -/
theorem canQ_semantic_pragmatic_agree :
    relExh (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = true ∧
    isMentionSome findChairDP {.w0, .w1, .w2} {.a, .b} foCells = true := by
  exact ⟨canQ_relExh_passes, canQ_mentionSome⟩

/-! ### Structural link: cells are qden -/

/-- The FO cells used for DecisionTheory are structurally identical to the
foQDen-derived propositions. This makes the agreement non-accidental:
both frameworks operate on the same answer-space structure. -/
theorem foCells_eq_qden :
    foCells = [foQDen chairs abilityMB .a, foQDen chairs abilityMB .b] := rfl

/-! ## Part II: Partition Contrast (MA reading)

Under the partition interpretation, each cell identifies exactly one world.
EP trivially holds (the unique true cell entails itself), and DecisionTheory
classifies this as mention-all (no resolving answers for identify-all DP,
since individual cells don't tell you the exact world). -/

/-- EP holds for the partition reading at w0.
Under partQDen, only the w0-cell is true at w0, so it trivially entails
all other true cells (there are none). -/
theorem partQ_ep_holds :
    dayalEP partQDen abilityMB [.w0, .w1, .w2] allWorlds .w0 = true := by
  native_decide

/-- RelExh holds for the partition reading at w0.
EP holds for the full question, so a fortiori it holds for each singleton
modal base. -/
theorem partQ_relExh_holds :
    relExh partQDen abilityMB [.w0, .w1, .w2] allWorlds .w0 = true := by
  native_decide

/-- DecisionTheory classifies the FO can-question as mention-all when the
goal is complete identification. FO cells don't resolve identifyAllDP:
knowing that a can chair (= being in {w0, w1}) doesn't identify whether
you're in w0 or w1. -/
theorem foQ_identifyAll_mentionAll :
    isMentionAll identifyAllDP {.w0, .w1, .w2} {XW.w0, .w1, .w2} foCells = true := by
  native_decide

/-! ## Part III: Preserved from Prior Bridge

Structural properties of the answer space and questionUtility. -/

/-- The MS question has positive expected utility value for `findChairDP`.
Learning any FO cell improves decision-making over the prior. -/
theorem questionUtility_positive :
    questionUtility findChairDP {.a, .b} (questionToFinset foCells) > 0 := by
  native_decide

/-! ### Answer space structure (van Rooij–inspired predicates) -/

/-- Answer cells are not mutually exclusive: some pair of distinct cells
shares at least one world. -/
def answersOverlap {W : Type} [BEq (W → Bool)]
    (q : Question W) (worlds : List W) : Bool :=
  q.any λ c1 => q.any λ c2 =>
    !BEq.beq c1 c2 && worlds.any λ w => c1 w && c2 w

/-- Answer space is not closed under conjunction: some pair of cells has
a conjunction that isn't represented by any cell. -/
def notClosedUnderConj {W : Type}
    (q : Question W) (worlds : List W) : Bool :=
  q.any λ c1 => q.any λ c2 =>
    !(q.any λ c3 => worlds.all λ w => c3 w == (c1 w && c2 w))

/-- FO cells overlap: the a-cell and b-cell share world w0. -/
theorem foCells_overlap :
    answersOverlap foCells allWorlds = true := by
  native_decide

/-- FO cells are not closed under ∧.
The conjunction of the a-cell and b-cell is {w0}, which is not
one of the two FO cells. -/
theorem foCells_not_closed :
    notClosedUnderConj foCells allWorlds = true := by
  native_decide

/-- Partition cells don't overlap: they are disjoint. -/
theorem partCells_no_overlap :
    answersOverlap partCells allWorlds = false := by
  native_decide

/-! ## Part IV: @cite{fox-2018} Exhaustification @cite{fox-2018}

@cite{fox-2018} "Partition by Exhaustification" derives Dayal's EP from the
exhaustification operator Exh. We exercise the Bool-valued Exh/IE/MC-set
machinery from Questions.Exhaustivity on three question denotations:

1. **FO cells** {◇a, ◇b}: Exh identifies {w1} and {w2} but not {w0}.
   No unique cell-identifier at w0 → `foxAns` undefined → FO alone
   cannot derive MS (consistent with Fox's argument that higher-order
   quantification is needed).

2. **HO cells** {◇a, ◇b, ◇a∨◇b}: Fox's higher-order reading (Section 4.3).
   Exh(◇a∨◇b) = ◇a∨◇b (IE = ∅ since the two MC-sets {◇a} and {◇b}
   have empty intersection). At w0, this is the unique Exh-true cell, and
   both ◇a and ◇b entail ◇a∨◇b, so `foxAns = 3` → **MS**.

3. **Partition cells**: trivially `foxAns = 1` → **MA**.
-/

/-! ### Higher-order question denotation (@cite{fox-2018}, Section 4.3) -/

/-- Higher-order question denotation: adds the disjunctive cell ◇a∨◇b
to the FO cells. Under Spector's analysis, the wh-variable ranges over
generalized quantifiers, generating compound cells including disjunctions. -/
def hoCells : List (XW → Bool) :=
  [ foQDen chairs abilityMB .a
  , foQDen chairs abilityMB .b
  , λ w => foQDen chairs abilityMB .a w || foQDen chairs abilityMB .b w
  ]

/-! ### Exh on FO cells -/

/-- Exh(◇chair(a)) is false at w0: both a and b can chair, so a's
exhaustified answer (= only a can chair) doesn't hold at w0. -/
theorem canQ_foxExh_a_w0 :
    foxExh foCells 0 allWorlds .w0 = false := by native_decide

/-- Exh(◇chair(a)) is true at w1: at w1 only a can chair. -/
theorem canQ_foxExh_a_w1 :
    foxExh foCells 0 allWorlds .w1 = true := by native_decide

/-- Exh(◇chair(b)) is true at w2: at w2 only b can chair. -/
theorem canQ_foxExh_b_w2 :
    foxExh foCells 1 allWorlds .w2 = true := by native_decide

/-- Exh(◇chair(a)) is satisfiable: true at w1. -/
theorem canQ_foxNV_a :
    foxNV foCells 0 allWorlds = true := by native_decide

/-- Exh(◇chair(b)) is satisfiable: true at w2. -/
theorem canQ_foxNV_b :
    foxNV foCells 1 allWorlds = true := by native_decide

/-- No Exh-true FO cell at w0: neither exclusive reading holds where
both individuals can chair. This is why Fox needs higher-order Q. -/
theorem canQ_exhTrueCount_w0 :
    exhTrueCount foCells allWorlds .w0 = 0 := by native_decide

/-- FO cells don't partition: w0 has no Exh-true cell (Schwarzschild
test fails). -/
theorem canQ_fo_no_partition :
    foxPartition foCells allWorlds = false := by native_decide

/-- `foxAns` is undefined for FO cells at w0: no unique cell-identifier
(zero Exh-true cells). FO alone cannot derive Fox's MS prediction. -/
theorem canQ_fo_foxAns_w0 :
    foxAns foCells allWorlds .w0 = 0 := by native_decide

/-! ### Exh on HO cells (Fox's Section 4.3) -/

/-- Exh(◇a∨◇b) at w0 under hoQ: the disjunctive cell's IE is empty
(MC-sets {◇a} and {◇b} have empty intersection), so Exh(◇a∨◇b) = ◇a∨◇b.
True at w0 since both can chair. -/
theorem canQ_ho_exh_disj_w0 :
    foxExh hoCells 2 allWorlds .w0 = true := by native_decide

/-- At w0 under hoQ, exactly one Exh is true: the disjunctive cell.
The individual cells' Exh (= only-a, only-b) are false at w0. -/
theorem canQ_ho_exhTrueCount_w0 :
    exhTrueCount hoCells allWorlds .w0 = 1 := by native_decide

/-- **Fox's Ans gives MS for HO cells at w0.** The unique cell-identifier
is Exh(◇a∨◇b) = ◇a∨◇b. All three Q-members are true at w0 and entail
◇a∨◇b (trivially, since ◇a → ◇a∨◇b and ◇b → ◇a∨◇b).
|Ans| = 3 > 1 → mention-some.

This is Fox's key result: the cell-identifier is weaker than the individual
true answers, so multiple answers are licensed. -/
theorem canQ_ho_foxAns_w0 :
    foxAns hoCells allWorlds .w0 = 3 := by native_decide

/-- HO cells don't partition: at w1 both Exh(◇a) and Exh(◇a∨◇b)
are true (Exh(◇a) = {w1}, Exh(◇a∨◇b) = {w0,w1,w2}), so the
Schwarzschild test fails. Fox's Ans requires a unique cell-identifier
per world; the HO cells with ◇a∨◇b violate this outside w0.
This reflects the gap between Fox's conceptual argument for MS
and the formal QPM condition. -/
theorem canQ_ho_no_partition :
    foxPartition hoCells allWorlds = false := by native_decide

/-- `foxAns` is undefined at w1 under HO cells: two Exh-true cells
(Exh(◇a) and Exh(◇a∨◇b)), so no unique cell-identifier. -/
theorem canQ_ho_foxAns_w1 :
    foxAns hoCells allWorlds .w1 = 0 := by native_decide

/-! ### Partition question -/

/-- Partition cells form a proper partition: every world has exactly
one Exh-true cell (Schwarzschild test passes). -/
theorem partQ_partition :
    foxPartition partCells allWorlds = true := by native_decide

/-- Fox's Ans = 1 for partition cells at w0 → mention-all. The unique
true cell is the w0-cell; its Exh is itself. -/
theorem partQ_foxAns :
    foxAns partCells allWorlds .w0 = 1 := by native_decide

/-! ### Pointwise NV -/

/-- Pointwise NV holds for FO cells at w0: each true cell's Exh is
satisfiable (though not true at w0 itself). -/
theorem canQ_pointwiseNV :
    pointwiseNV foCells allWorlds .w0 = true := by native_decide

/-! ### Cross-framework agreement -/

/-- **Dayal EP and Fox Exh agree on the FO can-question**: EP fails
(no strongest answer) and Exh identifies no cell at w0 (no unique
cell-identifier). Both frameworks flag that the FO denotation alone
cannot resolve the question at w0. -/
theorem canQ_ep_exh_agree_fo :
    dayalEP (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = false ∧
    foxAns foCells allWorlds .w0 = 0 := by
  exact ⟨canQ_ep_fails, canQ_fo_foxAns_w0⟩

/-- **Dayal EP and Fox Ans agree on MA for partition**: EP holds
(unique strongest answer) and Fox's |Ans| = 1. -/
theorem partQ_ep_fox_agree :
    dayalEP partQDen abilityMB [.w0, .w1, .w2] allWorlds .w0 = true ∧
    foxAns partCells allWorlds .w0 = 1 := by
  exact ⟨partQ_ep_holds, partQ_foxAns⟩

/-- **Fox's HO reading derives MS**: with the higher-order Q (including
◇a∨◇b), `foxAns = 3` at w0 — the exhaustification framework predicts
mention-some. This agrees with RelExh (which passes for the FO reading)
and DecisionTheory. -/
theorem canQ_ho_ms_agree :
    foxAns hoCells allWorlds .w0 = 3 ∧
    relExh (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = true ∧
    isMentionSome findChairDP {.w0, .w1, .w2} {.a, .b} foCells = true := by
  exact ⟨canQ_ho_foxAns_w0, canQ_relExh_passes, canQ_mentionSome⟩

end Phenomena.Questions.Studies.Xiang2022
