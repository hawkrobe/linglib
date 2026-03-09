import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Semantics.Questions.Partition
import Linglib.Theories.Semantics.Questions.MentionSome

/-!
# Van Rooy (2003): Questioning to Resolve Decision Problems
@cite{van-rooy-2003}

Robert van Rooy. Questioning to Resolve Decision Problems.
Linguistics and Philosophy 26(6): 727–763.

## Key Contributions

Van Rooy proposes that question interpretation is driven by the questioner's
**decision problem**: the question is asked to help the questioner decide
what to do. This yields:

1. **Op(P)(w)**: The relevance-maximal groups of P-satisfiers in world w
2. **⟦?xPx⟧^R**: An underspecified question denotation that unifies
   mention-all and mention-some readings
3. **>_Q ordering on answers**: Relevance-based answer preference
4. **Q > Q' ordering on questions**: When one question is better than another
5. **Domain selection**: The wh-domain contains exactly decision-relevant
   individuals
6. **Scalar questions**: Preference-based orderings not reducible to
   entailment

## Connection to G&S

Van Rooy's theory extends Groenendijk & Stokhof's partition semantics.
G&S's exhaustive partition is the limiting case when the questioner's
decision problem requires complete information. Van Rooy shows that
when partial information suffices, the question denotation naturally
produces mention-some readings.

## Connection to Existing Infrastructure

- `Core.Agent.DecisionTheory`: Decision problems, EUV, VSI, question utility
- `Theories.Semantics.Questions.Partition`: G&S partition semantics
- `Theories.Semantics.Questions.MentionSome`: G&S mention-some (§5)
- `Theories.Semantics.Questions.GSVanRooyBridge`: Blackwell's theorem
-/

namespace Phenomena.Questions.Studies.VanRooy2003

open Core.DecisionTheory
open Semantics.Questions hiding Question
open Semantics.Questions.MentionSome


/-! ## Op(P): Relevance-Maximal Satisfiers

@cite{van-rooy-2003}, §5 (p. 752): Op(P)(w) selects the group(s) of
P-satisfiers in world w that are maximally relevant to the agent's
decision problem. The standard mention-all denotation partitions by
the full extension of P; Op(P) partitions only by the decision-relevant
part of the extension.

For a simple "find one" goal, Op(P)(w) = {{a} : P(a)(w)} — any single
satisfier is a maximally relevant group.

For a "list all" goal, Op(P)(w) = {ext(P)(w)} — only the complete
extension is maximally relevant.
-/

/-- A relevance function assigns to each world a set of "optimal groups"
of entities — those groups that are maximally relevant to the agent's
decision problem. -/
structure RelevanceFunction (W E : Type*) where
  /-- The predicate (e.g., "sells Italian newspapers") -/
  predicate : W → E → Bool
  /-- The optimal groups in each world: subsets of satisfiers that are
      maximally relevant to the decision problem -/
  optimalGroups : W → List (List E)

/-- Standard mention-all: Op(P)(w) = {ext(P)(w)}, the full extension.
Only one group per world: all satisfiers together. -/
def mentionAllRelevance {W E : Type*} [DecidableEq E]
    (predicate : W → E → Bool) (domain : List E) : RelevanceFunction W E where
  predicate := predicate
  optimalGroups := λ w => [domain.filter (predicate w)]

/-- Mention-some relevance: Op(P)(w) = {{a} : P(a)(w)}, each satisfier
is its own optimal group. Any single satisfier suffices. -/
def mentionSomeRelevance {W E : Type*}
    (predicate : W → E → Bool) (domain : List E) : RelevanceFunction W E where
  predicate := predicate
  optimalGroups := λ w => domain.filter (predicate w) |>.map (·::[])


/-! ## ⟦?xPx⟧^R: The Underspecified Question Denotation

@cite{van-rooy-2003}, §5 (p. 753): The relevance-parameterized question
denotation:

  ⟦?xPx⟧^R = {λv[g ∈ Op(P)(v)] : w ∈ W & g ∈ Op(P)(w)}

Each "answer" is a proposition saying "group g is among the optimal
groups." The set of such propositions is the question denotation.

When Op = mention-all, this reduces to the standard G&S partition.
When Op = mention-some, this produces {λv[{a} ∈ Op(P)(v)] : P(a)(w)},
i.e., one answer per satisfier, each saying "a is a satisfier."
-/

/-- The relevance-parameterized question denotation ⟦?xPx⟧^R.

Each cell says "group g is among the optimal groups in this world."
The question is the collection of such propositions across all
groups that appear in some world.

@cite{van-rooy-2003}, p. 753. -/
def underspecifiedDenotation {W E : Type*} [BEq E] [BEq (List E)]
    (rf : RelevanceFunction W E) (worlds : List W) : Question W :=
  -- Collect all optimal groups that appear in any world
  let allGroups := worlds.flatMap rf.optimalGroups |>.eraseDups
  -- Each group induces a proposition: "this group is optimal here"
  allGroups.map λ g => λ v => rf.optimalGroups v |>.any (· == g)


/-! ## Examples

### Italian Newspaper Example

@cite{van-rooy-2003}, p. 739, 753–754: "Where can I buy an Italian newspaper?"

The questioner wants to buy an Italian newspaper. Any shop that sells
one suffices. Op(P)(w) = {{s} : sells-Italian(s)(w)}, making each shop
a separate answer. The question gets a mention-some reading. -/

/-- Worlds for the Italian newspaper scenario: which shops sell Italian papers. -/
inductive NewspaperWorld
  | shopA_only      -- only shop A sells Italian newspapers
  | shopB_only      -- only shop B
  | both            -- both A and B sell
  deriving DecidableEq, BEq, Repr

instance : Fintype NewspaperWorld :=
  ⟨{.shopA_only, .shopB_only, .both}, by intro x; cases x <;> simp⟩

/-- Shops in the domain. -/
inductive Shop
  | A | B
  deriving DecidableEq, BEq, Repr

/-- "x sells Italian newspapers" in world w. -/
def sellsItalian : NewspaperWorld → Shop → Bool
  | .shopA_only, .A => true
  | .shopA_only, .B => false
  | .shopB_only, .A => false
  | .shopB_only, .B => true
  | .both,       .A => true
  | .both,       .B => true

/-- Mention-some relevance for the newspaper scenario. -/
def newspaperRelevance : RelevanceFunction NewspaperWorld Shop :=
  mentionSomeRelevance sellsItalian [.A, .B]

/-- The underspecified denotation produces mention-some answers:
"Shop A sells Italian papers" and "Shop B sells Italian papers."
In the both-world, both answers are true. -/
def newspaperQuestion : Question NewspaperWorld :=
  underspecifiedDenotation newspaperRelevance [.shopA_only, .shopB_only, .both]

/-- The newspaper question has exactly 2 cells (one per shop). -/
theorem newspaper_has_two_cells :
    newspaperQuestion.length = 2 := by native_decide

/-- In the shopA_only world, only the "Shop A" answer is true. -/
theorem newspaper_shopA_only_resolved :
    (newspaperQuestion.filter (· .shopA_only)).length = 1 := by native_decide

/-- In the both world, both answers are true — either suffices. -/
theorem newspaper_both_world_two_true :
    (newspaperQuestion.filter (· .both)).length = 2 := by native_decide

/-- The newspaper scenario decision problem: go to shop A or shop B.
Utility 1 if you go to a shop that sells Italian papers, 0 otherwise. -/
def newspaperDP : DecisionProblem NewspaperWorld Shop where
  utility w a := if sellsItalian w a then 1 else 0
  prior _ := 1/3

/-- The newspaper DP has mention-some structure: both cells resolve it. -/
theorem newspaper_mentionSome :
    isMentionSome newspaperDP
      [.shopA_only, .shopB_only, .both] [.A, .B]
      [λ w => sellsItalian w .A, λ w => sellsItalian w .B] = true := by
  native_decide


/-! ### "Where do you live?" Example

@cite{van-rooy-2003}, p. 754–755: "Where do you live?"

The granularity of the answer depends on the decision problem:
- Taxi driver: needs exact address
- Census worker: needs city/state
- Casual conversation: city suffices

This is modeled by different decision problems inducing different
optimal partitions. -/

/-- Granularity levels for the "where do you live" example. -/
inductive Granularity
  | city     -- e.g., "Amsterdam"
  | district -- e.g., "Amsterdam Centrum"
  | address  -- e.g., "123 Keizersgracht"
  deriving DecidableEq, BEq, Repr

/-- Different decision problems require different granularity.
The required granularity determines the question interpretation. -/
structure GranularityDatum where
  /-- Who is asking? -/
  asker : String
  /-- What decision problem do they face? -/
  decisionProblem : String
  /-- What granularity is needed? -/
  requiredGranularity : Granularity
  /-- Natural language form of the question -/
  question : String := "Where do you live?"
  deriving Repr

def taxiDriver : GranularityDatum :=
  { asker := "Taxi driver"
  , decisionProblem := "Navigate to the destination"
  , requiredGranularity := .address }

def censusWorker : GranularityDatum :=
  { asker := "Census worker"
  , decisionProblem := "Record residential district"
  , requiredGranularity := .district }

def casualConversation : GranularityDatum :=
  { asker := "Acquaintance at a party"
  , decisionProblem := "Make conversation / establish common ground"
  , requiredGranularity := .city }

def granularityExamples : List GranularityDatum :=
  [taxiDriver, censusWorker, casualConversation]

/-- Different askers need different granularity. -/
theorem granularity_varies :
    (taxiDriver.requiredGranularity != censusWorker.requiredGranularity) ∧
    (censusWorker.requiredGranularity != casualConversation.requiredGranularity) := by
  exact ⟨by native_decide, by native_decide⟩


/-! ### The Beatle Hierarchy: Scalar Questions

@cite{van-rooy-2003}, p. 759–760: "Which Beatle records do you have?"

Consider a collector who values Beatles records differently:
  John > Paul > George > Ringo

The questioner (a record shop owner) wants to sell records. The
ordering on answers is preference-based, not entailment-based:
knowing the collector has John records is more useful than knowing
they have Ringo records (because John records are more valuable to sell).

This shows that Van Rooy's relevance ordering goes beyond standard
partition refinement: it can produce scale-like orderings that don't
reduce to set-containment/entailment. -/

/-- Beatles for the collector example. -/
inductive Beatle
  | john | paul | george | ringo
  deriving DecidableEq, BEq, Repr

/-- Preference ranking over Beatles records (higher = more valuable). -/
def beatleValue : Beatle → ℚ
  | .john   => 4
  | .paul   => 3
  | .george => 2
  | .ringo  => 1

/-- Worlds: which Beatle's records the collector has.
Simplified to single-record worlds. -/
inductive BeatleWorld
  | hasJohn | hasPaul | hasGeorge | hasRingo
  deriving DecidableEq, BEq, Repr

instance : Fintype BeatleWorld :=
  ⟨{.hasJohn, .hasPaul, .hasGeorge, .hasRingo}, by intro x; cases x <;> simp⟩

/-- Which Beatle the collector has in each world. -/
def collectorHas : BeatleWorld → Beatle
  | .hasJohn   => .john
  | .hasPaul   => .paul
  | .hasGeorge => .george
  | .hasRingo  => .ringo

/-- The record shop DP: utility of selling Beatle b's records to the collector.
Utility equals the value of the Beatle if the collector actually has that Beatle's
records (and thus would want related merchandise). -/
def recordShopDP : DecisionProblem BeatleWorld Beatle where
  utility w a := if collectorHas w == a then beatleValue a else 0
  prior _ := 1/4

/-- Learning "has John" is more useful than "has Ringo" for the record shop.

This is the scalar ordering: UV({hasJohn}) > UV({hasRingo}). -/
theorem john_more_useful_than_ringo :
    utilityValue recordShopDP [.john, .paul, .george, .ringo]
      (Finset.univ.filter (· == BeatleWorld.hasJohn)) >
    utilityValue recordShopDP [.john, .paul, .george, .ringo]
      (Finset.univ.filter (· == BeatleWorld.hasRingo)) := by
  native_decide

/-- The full scalar ordering: John > Paul > George > Ringo in utility value. -/
theorem beatle_utility_ordering :
    let uv := λ w : BeatleWorld =>
      utilityValue recordShopDP [.john, .paul, .george, .ringo]
        (Finset.univ.filter (· == w))
    uv .hasJohn > uv .hasPaul ∧
    uv .hasPaul > uv .hasGeorge ∧
    uv .hasGeorge > uv .hasRingo := by
  native_decide


/-! ## Domain Selection

@cite{van-rooy-2003}, §4.2 (p. 745–746): The wh-domain of a question
contains exactly those individuals that are decision-relevant. An
individual d is decision-relevant if knowing whether P(d) holds has
positive expected utility value.

This explains why "Where can I buy an Italian newspaper?" doesn't
range over non-shops (e.g., hospitals, parks): those locations have
zero utility value for the buy-newspaper decision problem. -/

/-- An individual d is decision-relevant for question ?xP(x) given DP
if learning whether P(d) holds has positive utility value. -/
def isDecisionRelevant {W : Type*} [Fintype W] [DecidableEq W]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (predicate : W → Bool) : Bool :=
  let yesCell := Finset.univ.filter (λ w => predicate w = true)
  utilityValue dp actions yesCell > 0

/-- The decision-relevant domain: entities whose P-status matters. -/
def decisionRelevantDomain {W E : Type*} [Fintype W] [DecidableEq W]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (predicate : W → E → Bool) (domain : List E) : List E :=
  domain.filter λ d => isDecisionRelevant dp actions (predicate · d)

/-- In the newspaper example, both shops are decision-relevant. -/
theorem newspaper_shops_relevant :
    decisionRelevantDomain newspaperDP [Shop.A, Shop.B]
      sellsItalian [Shop.A, Shop.B] = [Shop.A, Shop.B] := by
  native_decide


/-! ## Summary Theorems

Structural properties connecting the examples back to the core theory. -/

/-- Mention-some reading arises when the decision problem is goal-directed:
any satisfier achieves the goal. This connects Van Rooy's Op(P) analysis
to the `isMentionSome` predicate from `Core.Agent.DecisionTheory`.

We use the newspaper DP directly (not `mentionSomeDP` which takes a unary
predicate). The newspaper DP has utility 1 for going to a shop that sells
Italian papers, so each shop-cell resolves it. -/
theorem mentionSome_from_goal_dp :
    let worlds := [NewspaperWorld.shopA_only, .shopB_only, .both]
    let q : Question NewspaperWorld :=
      [λ w => sellsItalian w Shop.A, λ w => sellsItalian w Shop.B]
    isMentionSome newspaperDP worlds [Shop.A, Shop.B] q = true := by
  native_decide

/-- Mention-all reading arises when the decision problem requires
complete information (e.g., the complete information DP). -/
theorem mentionAll_from_complete_dp :
    let dp := completeInformationDP (W := NewspaperWorld)
    let worlds := [NewspaperWorld.shopA_only, .shopB_only, .both]
    let q : Question NewspaperWorld :=
      [λ w => sellsItalian w Shop.A, λ w => sellsItalian w Shop.B]
    isMentionAll dp worlds [.shopA_only, .shopB_only, .both] q = true := by
  native_decide

/-- The newspaper question utility is positive: asking is worthwhile. -/
theorem newspaper_question_has_value :
    questionUtility newspaperDP [Shop.A, Shop.B]
      [λ w => sellsItalian w Shop.A, λ w => sellsItalian w Shop.B] > 0 := by
  native_decide

end Phenomena.Questions.Studies.VanRooy2003
