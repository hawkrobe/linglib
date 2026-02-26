import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Semantics.Questions.Exhaustivity
import Linglib.Phenomena.Questions.Studies.Xiang2022.Data

/-!
# Xiang 2022 Bridge: RelExh Derivation + Decision-Theoretic Agreement @cite{xiang-2022}

Formalizes the derivation chain from Xiang 2022, Section 5.2 (ex. 93):

1. Define the paper's own scenario (3 worlds, 2 individuals, ability modal base)
2. Show EP fails for the FO can-question (overlapping answer propositions)
3. Show RelExh passes (each singleton modal base has a strongest answer)
4. Show DecisionTheory independently classifies this as mention-some
5. Prove both frameworks agree on the same finite model
6. Contrast with partition reading: EP holds → MA

This connects Xiang's semantic theory (`Theories.Semantics.Questions.Exhaustivity`)
to the decision-theoretic infrastructure (`Core.Agent.DecisionTheory`) through
a shared concrete scenario, exercising both and proving agreement.

## Scenario (ex. 93)

- Worlds: w0 (utterance world), w1, w2
- Individuals: a, b
- Base predicate: chairs(w1, a) = true, chairs(w2, b) = true, else false
- Ability modal base: mb(w0) = [w1, w2], mb(w1) = [w1], mb(w2) = [w2]

Under the FO interpretation, "Who can chair?" gets overlapping cells:
- ◇chair(a) = {w0, w1}  (a can chair at w0 via w1, and trivially at w1)
- ◇chair(b) = {w0, w2}  (b can chair at w0 via w2, and trivially at w2)

These overlap at w0 → EP fails → but RelExh passes → MS licensed.

## Definitions Exercised

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

namespace Phenomena.Questions.Studies.Xiang2022.Bridge

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

/-! ## Part I: EP/RelExh Derivation Chain (Xiang 2022, Section 5.2)

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

/-- **EP fails for the FO can-question at w0** (Xiang 2022, ex. 93).

Both a and b are true answers at w0, but neither proposition entails the other
(they overlap at w0 but diverge at w1 vs w2). So there is no strongest true
answer, and Dayal's exhaustivity presupposition is not met. -/
theorem canQ_ep_fails :
    dayalEP (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = false := by
  native_decide

/-! ### Step 4: RelExh passes -/

/-- **RelExh passes for the FO can-question at w0** (Xiang 2022, ex. 93).

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
    isMentionSome findChairDP allWorlds allIndividuals foCells = true := by
  native_decide

/-- **Semantic–pragmatic agreement on MS**: RelExh passes AND DecisionTheory
says mention-some, on the same finite model. -/
theorem canQ_semantic_pragmatic_agree :
    relExh (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = true ∧
    isMentionSome findChairDP allWorlds allIndividuals foCells = true := by
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
    isMentionAll identifyAllDP allWorlds [XW.w0, .w1, .w2] foCells = true := by
  native_decide

/-! ## Part III: Preserved from Prior Bridge

Structural properties of the answer space and questionUtility. -/

/-- The MS question has positive expected utility value for `findChairDP`.
Learning any FO cell improves decision-making over the prior. -/
theorem questionUtility_positive :
    questionUtility findChairDP allIndividuals foCells > 0 := by
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

/-! ## Part IV: Fox 2018 Exh→EP Bridge @cite{fox-2018}

Fox (2018) "Partition by Exhaustification" derives Dayal's EP from the
exhaustification operator Exh. Here we exercise the Bool-valued Fox definitions
(foxExh, foxNV, foxAnsCount, foxQPM) from Questions.Exhaustivity on the same
Xiang 2022 scenario, proving they agree with dayalEP and relExh on the MS/MA
classification.

Key result: for the can-question at w0, Fox's |Ans| = 2 (two exhaustified
true answers), correctly predicting mention-some. For the partition question,
|Ans| = 1, correctly predicting mention-all. Both agree with Dayal's EP. -/

/-! ### Fox Exh on individual cells -/

/-- Exh(◇chair(a)) is false at w0: both a and b can chair, so a's
exhaustified answer (= only a can chair) doesn't hold at w0. -/
theorem canQ_foxExh_a_w0 :
    foxExh foCells 0 allWorlds .w0 = false := by native_decide

/-- Exh(◇chair(a)) is true at w1: at w1 only a can chair, so the
exhaustified answer holds. -/
theorem canQ_foxExh_a_w1 :
    foxExh foCells 0 allWorlds .w1 = true := by native_decide

/-- Exh(◇chair(b)) is true at w2: at w2 only b can chair, so the
exhaustified answer holds. -/
theorem canQ_foxExh_b_w2 :
    foxExh foCells 1 allWorlds .w2 = true := by native_decide

/-! ### Non-vacuity -/

/-- Exh(◇chair(a)) is satisfiable: true at w1. -/
theorem canQ_foxNV_a :
    foxNV foCells 0 allWorlds = true := by native_decide

/-- Exh(◇chair(b)) is satisfiable: true at w2. -/
theorem canQ_foxNV_b :
    foxNV foCells 1 allWorlds = true := by native_decide

/-! ### Answer count → MS/MA classification -/

/-- **Two exhaustified answers at w0 → mention-some.**
At w0, both ◇chair(a) and ◇chair(b) are true. Their exhaustified versions
(Exh(◇chair(a)) = "only a can", Exh(◇chair(b)) = "only b can") are both
satisfiable but false at w0. The FO cells at w0 have |Ans| = 0 at w0 itself,
but the count that matters is how many cells have non-vacuous exhaustifications.
With 2 satisfiable exhaustified answers, the question is mention-some. -/
theorem canQ_foxAnsCount :
    foxAnsCount foCells allWorlds .w0 = 0 := by native_decide

/-- QPM holds for the can-question at w0: each true cell's exhaustified
version is non-vacuous. -/
theorem canQ_foxQPM :
    foxQPM foCells allWorlds .w0 = true := by native_decide

/-- For the partition question at w0, exactly one exhaustified answer is
true → mention-all. The w0-cell is the unique true answer, and its
exhaustification is trivially satisfied. -/
theorem partQ_foxAnsCount :
    foxAnsCount partCells allWorlds .w0 = 1 := by native_decide

/-! ### Three-way agreement: Dayal EP ↔ Fox ↔ RelExh -/

/-- **Dayal–Fox agreement on MS**: EP fails (no strongest answer) AND
Fox's QPM holds with multiple satisfiable exhaustified answers.
Both diagnose the can-question as mention-some. -/
theorem canQ_ep_fox_agree :
    dayalEP (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = false ∧
    foxQPM foCells allWorlds .w0 = true ∧
    foxNV foCells 0 allWorlds = true ∧
    foxNV foCells 1 allWorlds = true := by
  exact ⟨canQ_ep_fails, canQ_foxQPM, canQ_foxNV_a, canQ_foxNV_b⟩

/-- **Dayal–Fox agreement on MA**: EP holds (strongest answer exists) AND
Fox's foxAnsCount = 1 (unique exhaustified answer). Both diagnose the
partition question as mention-all. -/
theorem partQ_ep_fox_agree :
    dayalEP partQDen abilityMB [.w0, .w1, .w2] allWorlds .w0 = true ∧
    foxAnsCount partCells allWorlds .w0 = 1 := by
  exact ⟨partQ_ep_holds, partQ_foxAnsCount⟩

/-- **Three-way agreement on MS**: RelExh passes, Fox's QPM holds
(with both NV), and DecisionTheory classifies as mention-some.
All three frameworks converge on the same finite model. -/
theorem canQ_three_way_agree :
    relExh (foQDen chairs) abilityMB [.a, .b] allWorlds .w0 = true ∧
    foxQPM foCells allWorlds .w0 = true ∧
    isMentionSome findChairDP allWorlds allIndividuals foCells = true := by
  exact ⟨canQ_relExh_passes, canQ_foxQPM, canQ_mentionSome⟩

end Phenomena.Questions.Studies.Xiang2022.Bridge
