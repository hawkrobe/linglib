import Linglib.Core.Agent.DecisionTheory
import Linglib.Core.Agent.PartitionDT
import Linglib.Theories.Semantics.Questions.Denotation.Partition
import Linglib.Theories.Semantics.Questions.Answerhood.MentionSome
import Linglib.Theories.Semantics.Questions.Utility.Relevance

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

namespace VanRooy2003

open Core.DecisionTheory
open Semantics.Questions
open Semantics.Questions.MentionSome
open Semantics.Questions.Relevance


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
  deriving DecidableEq, Repr

instance : LawfulBEq NewspaperWorld where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl := by intro a; cases a <;> decide

instance : Fintype NewspaperWorld :=
  ⟨{.shopA_only, .shopB_only, .both}, by intro x; cases x <;> simp⟩

/-- Shops in the domain. -/
inductive Shop
  | A | B
  deriving DecidableEq, Repr

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
      {NewspaperWorld.shopA_only, .shopB_only, .both} {Shop.A, .B}
      [(Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w .A),
       (Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w .B)] = true := by
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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
    utilityValue recordShopDP {Beatle.john, .paul, .george, .ringo}
      (Finset.univ.filter (· == BeatleWorld.hasJohn)) >
    utilityValue recordShopDP {Beatle.john, .paul, .george, .ringo}
      (Finset.univ.filter (· == BeatleWorld.hasRingo)) := by
  native_decide

/-- The full scalar ordering: John > Paul > George > Ringo in utility value. -/
theorem beatle_utility_ordering :
    let uv := λ w : BeatleWorld =>
      utilityValue recordShopDP {Beatle.john, .paul, .george, .ringo}
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

/-- In the newspaper example, both shops are decision-relevant. -/
theorem newspaper_shops_relevant :
    decisionRelevantDomain newspaperDP {Shop.A, .B}
      sellsItalian [Shop.A, Shop.B] = {Shop.A, .B} := by
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
    let worlds : Finset NewspaperWorld := {.shopA_only, .shopB_only, .both}
    let q : List (Finset NewspaperWorld) :=
      [(Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w Shop.A),
       (Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w Shop.B)]
    isMentionSome newspaperDP worlds {Shop.A, .B} q = true := by
  native_decide

/-- Mention-all reading arises when the decision problem requires
complete information (e.g., the complete information DP). -/
theorem mentionAll_from_complete_dp :
    let dp := completeInformationDP (W := NewspaperWorld)
    let worlds : Finset NewspaperWorld := {.shopA_only, .shopB_only, .both}
    let q : List (Finset NewspaperWorld) :=
      [(Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w Shop.A),
       (Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w Shop.B)]
    isMentionAll dp worlds {NewspaperWorld.shopA_only, .shopB_only, .both} q = true := by
  native_decide

/-- The newspaper question utility is positive: asking is worthwhile. -/
theorem newspaper_question_has_value :
    questionUtility newspaperDP {Shop.A, .B}
      (questionToFinset
        [(Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w Shop.A),
         (Finset.univ : Finset NewspaperWorld).filter (fun w => sellsItalian w Shop.B)]) > 0 := by
  native_decide


/-! ## Resolution–Value Saturation

The deepest mathematical connection between @cite{van-rooy-2003} and
@cite{groenendijk-stokhof-1984}: **resolution of a question by a decision
problem implies value saturation** — the question extracts all
decision-relevant information, and coarsening from the G&S partition to
Van Rooy's underspecified denotation is decision-theoretically free.

### The algebraic heart

Blackwell's theorem (proved in `Core.Partition`) uses sub-additivity of max:

    max_a [Σ_w f(w,a)] ≤ Σ_w [max_a f(w,a)]

This gives: finer partitions have higher `partitionValue`. But the
inequality can be **tight**: if cell C has a dominant action a_dom
(∀b, ∀w∈C: U(w,a_dom) ≥ U(w,b)), then a_dom achieves the pointwise
maximum at every world, so max-of-sums = sum-of-maxes:

    max_a [Σ_{w∈C} π(w)·U(w,a)]
      ≥ Σ_{w∈C} π(w)·U(w,a_dom)          — choosing a = a_dom
      = Σ_{w∈C} π(w)·max_b U(w,b)         — a_dom achieves max at each w
      = Σ_{w∈C} [max_a π(w)·U(w,a)]       — when π ≥ 0
      ≥ max_a [Σ_{w∈C} π(w)·U(w,a)]       — sub-additivity (Blackwell)

The squeeze gives equality. Summing over cells:

    partitionValue(Q) = partitionValue(Q_exact)

**Resolution is exactly when Blackwell's sub-additivity inequality is
tight at every cell.** This characterizes the "plateau" in the Blackwell
ordering: all resolving partitions achieve the same maximal value.

### Connection to Van Rooy's underspecified denotation

Van Rooy's ⟦?xPx⟧^R with mention-some relevance produces cells that
each resolve the questioner's DP. So the coarsening from G&S's three-cell
partition (only-A, only-B, both) to Van Rooy's two-cell denotation
(A-sells, B-sells) is decision-theoretically free: no information of
value to the questioner is lost.

This is the formal sense in which "Where can I buy an Italian newspaper?"
need only mention one shop. -/


/-! ### The G&S partition for the newspaper scenario -/

/-- The G&S partition for "where can I buy an Italian newspaper?":
two worlds are equivalent iff they have the same extension for
"sells Italian newspapers." This gives three cells:
{shopA_only}, {shopB_only}, {both}. -/
def newspaperGS : QUD NewspaperWorld :=
  QUD.ofProject (λ w => (sellsItalian w Shop.A, sellsItalian w Shop.B))

/-- The mention-some partition: two worlds are equivalent iff they give
the same answer to "does SOME shop sell Italian newspapers?"
This gives two cells: {shopA_only, shopB_only, both} vs ∅ (but all our
worlds have a satisfier, so there's just one cell — trivial partition).

For a non-trivial mention-some partition, we use a coarser grouping:
worlds are equivalent iff they agree on whether shop A sells.
This gives two cells: {shopA_only, both} and {shopB_only}. -/
def newspaperMS_A : QUD NewspaperWorld :=
  QUD.ofProject (λ w => sellsItalian w Shop.A)

/-- The mention-some partition based on shop B. -/
def newspaperMS_B : QUD NewspaperWorld :=
  QUD.ofProject (λ w => sellsItalian w Shop.B)


/-! ### Value saturation: concrete verification -/

/-- The G&S partition (3 cells) and the mention-some-A partition (2 cells)
achieve the **same** partitionValue for the newspaper DP.

This is the concrete instance of value saturation: coarsening from the
exhaustive partition to the mention-some partition loses nothing,
because both resolve the DP. -/
theorem newspaper_value_saturation_A :
    QUD.partitionValue newspaperDP newspaperGS Finset.univ {Shop.A, .B} =
    QUD.partitionValue newspaperDP newspaperMS_A Finset.univ {Shop.A, .B} := by
  native_decide

/-- Same for the shop-B mention-some partition. -/
theorem newspaper_value_saturation_B :
    QUD.partitionValue newspaperDP newspaperGS Finset.univ {Shop.A, .B} =
    QUD.partitionValue newspaperDP newspaperMS_B Finset.univ {Shop.A, .B} := by
  native_decide

/-- Both mention-some partitions achieve the same value as the exact
(identity) partition. This is the full value saturation: even the
coarsest resolving partition extracts all decision-relevant information. -/
theorem newspaper_value_saturation_exact :
    QUD.partitionValue newspaperDP (QUD.exact (M := NewspaperWorld))
      Finset.univ {Shop.A, .B} =
    QUD.partitionValue newspaperDP newspaperMS_A Finset.univ {Shop.A, .B} := by
  native_decide

/-- Verification: the G&S partition also equals the exact partition's value.
(Follows from the previous two, but verified independently.) -/
theorem newspaper_GS_eq_exact :
    QUD.partitionValue newspaperDP newspaperGS Finset.univ {Shop.A, .B} =
    QUD.partitionValue newspaperDP (QUD.exact (M := NewspaperWorld))
      Finset.univ {Shop.A, .B} := by
  native_decide


/-! ### Value saturation FAILS for the complete-information DP -/

/-- For the complete-information DP (where knowing the exact world matters),
the mention-some partition achieves STRICTLY LESS value than the G&S
partition. Coarsening is no longer free — information is lost. -/
theorem complete_info_value_NOT_saturated :
    QUD.partitionValue (completeInformationDP (W := NewspaperWorld))
      newspaperMS_A Finset.univ {NewspaperWorld.shopA_only, .shopB_only, .both} <
    QUD.partitionValue (completeInformationDP (W := NewspaperWorld))
      newspaperGS Finset.univ {NewspaperWorld.shopA_only, .shopB_only, .both} := by
  native_decide


/-! ### The underspecified denotation achieves value saturation -/

/-- The cells of the underspecified denotation for the newspaper scenario. -/
def newspaperUnderspecCells :=
  underspecifiedDenotation
    (mentionSomeRelevance sellsItalian [Shop.A, Shop.B])
    [NewspaperWorld.shopA_only, .shopB_only, .both]

/-- Every cell of the underspecified denotation (mention-some relevance)
resolves the newspaper DP: after learning any answer, the questioner
can act optimally.

This is the bridge from Van Rooy's Op(P) construction to value saturation:
Op(P) produces cells → cells resolve → value is saturated. -/
theorem underspecified_all_cells_resolve :
    (newspaperUnderspecCells.map fun c =>
        (Finset.univ : Finset NewspaperWorld).filter (fun w => c w = true)).all
      (resolves newspaperDP
        {NewspaperWorld.shopA_only, .shopB_only, .both} {Shop.A, .B})
      = true := by
  native_decide


/-! ### The General Theorem

The concrete verifications above are instances of a general principle.
We state it here; the proof combines Blackwell (one direction) with
the resolution lower bound (the other direction). -/

/-- **Resolution–Value Saturation Theorem** (general form).

For a decision problem D with non-negative priors and utilities, and a
partition Q where every cell resolves D:

    partitionValue(Q, D) = partitionValue(Q_exact, D)

Resolution marks the **plateau** in the Blackwell ordering: all resolving
partitions achieve the maximal value, regardless of their granularity.

**Proof sketch** (both directions):

**(≤)** Blackwell: Q_exact refines Q, so partitionValue(Q_exact) ≥ partitionValue(Q).

**(≥)** For each cell C of Q with dominant action a_dom:
  - `max_a [Σ_{w∈C} π(w)·U(w,a)] ≥ Σ_{w∈C} π(w)·U(w,a_dom)` (choosing a_dom)
  - `= Σ_{w∈C} π(w)·max_b U(w,b)` (a_dom achieves max at every w)
  - `= Σ_{w∈C} max_a [π(w)·U(w,a)]` (when π ≥ 0, U ≥ 0)
  - Summing over cells: partitionValue(Q) ≥ partitionValue(Q_exact)

Combined: equality.

Delegates to `QUD.resolution_value_eq_exact` (proved in `Core.Partition`). -/
theorem resolution_value_saturation
    {W : Type*} [Fintype W] [DecidableEq W]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (q : QUD W) (actions : Finset A)
    (hResolves : ∀ cell ∈ q.toCellsFinset Finset.univ,
      ∃ a ∈ actions, ∀ b ∈ actions, ∀ w ∈ cell,
        dp.utility w a ≥ dp.utility w b)
    (hPrior : ∀ w, dp.prior w ≥ 0) :
    QUD.partitionValue dp q Finset.univ actions =
    QUD.partitionValue dp QUD.exact Finset.univ actions :=
  QUD.resolution_value_eq_exact dp q actions hResolves hPrior

/-- **Corollary**: For a mention-some DP, the underspecified denotation
(coarsened to a partition) achieves the same value as the full G&S
partition. The mention-some question is decision-theoretically
equivalent to the mention-all question.

This is the mathematical core of Van Rooy's theory: the partition
structure of a question should match the decision problem's resolution
structure, and coarser-than-necessary partitions that still resolve
lose nothing. -/
theorem mentionSome_value_eq_mentionAll :
    QUD.partitionValue newspaperDP newspaperMS_A Finset.univ {Shop.A, .B} =
    QUD.partitionValue newspaperDP newspaperGS Finset.univ {Shop.A, .B} :=
  newspaper_value_saturation_A.symm

end VanRooy2003
