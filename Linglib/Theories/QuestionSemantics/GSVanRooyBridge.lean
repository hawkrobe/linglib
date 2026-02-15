import Linglib.Core.DecisionTheory
import Linglib.Theories.QuestionSemantics.PragmaticAnswerhood
import Linglib.Theories.QuestionSemantics.MentionSome
import Linglib.Theories.QuestionSemantics.Polarity

/-!
# Questions/GSVanRooyBridge.lean

Bridging Theorems between Groenendijk & Stokhof (1984) and Van Rooy (2003).

## Overview

G&S and Van Rooy approach question semantics from different angles:
- **G&S**: Partition semantics (equivalence relations on worlds)
- **Van Rooy**: Decision-theoretic semantics (questions resolve decision problems)

This file establishes the formal connections between these approaches.

## Results

1. **Blackwell's Theorem**: Semantic refinement = pragmatic dominance
2. **Mention-Some Characterization**: Decision-theoretic <-> goal-based licensing
3. **Pragmatic Answerhood <-> Utility**: G&S's J-relative answerhood = positive UV
4. **Exhaustivity Characterization**: When complete information is required
5. **Polar Question Optimality**: PPQ/NPQ/Alt choice maximizes utility

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Van Rooy (2003). Questioning to Resolve Decision Problems. L&P 26.
- Van Rooy (2003). Quality and Quantity of Information Exchange. JoLLI.
- Van Rooy & Šafářová (2003). On Polar Questions. SALT 13.
- Blackwell (1953). Equivalent Comparisons of Experiments.
-/

namespace QuestionSemantics.Bridge

open Core.DecisionTheory
open QuestionSemantics
open QuestionSemantics.MentionSome
open QuestionSemantics.Polarity
open scoped GSQuestion  -- For ⊑ notation


/-!
## Blackwell's Theorem

The fundamental bridge: G&S's semantic refinement ordering on questions
is *exactly* the universal pragmatic dominance ordering.

```
Q ⊑ Q'  ⟺  ∀DP: EUV_DP(Q) ≥ EUV_DP(Q')
```

This is remarkable: the partition structure isn't arbitrary—it's the unique
structure that respects decision-theoretic usefulness across ALL possible goals.

**Proof sketch (→)**: If Q refines Q', its cells are subsets. More information
can only help (or not hurt) any decision. By convexity of max.

**Proof sketch (←)**: Contrapositive. If Q doesn't refine Q', find w,v that are
Q-equivalent but Q'-inequivalent. Construct a DP where distinguishing w from v
matters. Then Q' beats Q on this DP.
-/

/-- Blackwell's Theorem: Refinement implies dominance for expected utility.

If Q refines Q', then Q is at least as useful as Q' for ANY decision problem.
This is the "easy direction" of Blackwell. -/
theorem blackwell_refinement_dominance_EU {W A : Type*} [DecidableEq A]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (hRefines : q ⊑ q') :
    ∀ dp : DecisionProblem W A,
      questionUtility dp worlds actions (q.toQuestion worlds) >=
      questionUtility dp worlds actions (q'.toQuestion worlds) := by
  sorry

/-- Blackwell's Theorem: Dominance implies refinement.

If Q dominates Q' for ALL decision problems, then Q refines Q'.
This is the "hard direction"—proved by contraposition. -/
theorem blackwell_dominance_refinement {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (hDominates : ∀ dp : DecisionProblem W A,
      questionUtility dp worlds actions (q.toQuestion worlds) >=
      questionUtility dp worlds actions (q'.toQuestion worlds)) :
    q ⊑ q' := by
  sorry

/-- Blackwell's Theorem (full characterization).

Semantic refinement <-> Universal pragmatic dominance. -/
theorem blackwell_full {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (hWorlds : worlds.length > 0) (hActions : actions.length > 0) :
    q ⊑ q' <->
    ∀ dp : DecisionProblem W A,
      questionUtility dp worlds actions (q.toQuestion worlds) >=
      questionUtility dp worlds actions (q'.toQuestion worlds) := by
  constructor
  · exact blackwell_refinement_dominance_EU q q' worlds actions
  · exact blackwell_dominance_refinement q q' worlds actions

/-- Blackwell generalizes to maximin (pessimistic) criterion.

The theorem holds not just for expected utility but for ANY "reasonable"
decision criterion. This shows G&S semantics is robust. -/
theorem blackwell_maximin {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (hWorlds : worlds.length > 0) (hActions : actions.length > 0) :
    q ⊑ q' <->
    ∀ dp : DecisionProblem W A,
      questionMaximin dp worlds actions (q.toQuestion worlds) >=
      questionMaximin dp worlds actions (q'.toQuestion worlds) := by
  sorry


/-!
## Mention-Some: G&S <-> Van Rooy

G&S (Section 5): Mention-some is licensed by "human concerns"—practical goals
where partial information suffices.

Van Rooy: Mention-some arises when multiple cells of the partition resolve
the decision problem (i.e., make one action dominant).

**Conjecture**: These characterizations are equivalent.

The G&S "human concern" licensing corresponds exactly to the existence of
a decision problem with the mention-some structure.
-/

/-- A decision problem has mention-some structure if multiple cells resolve it.

Van Rooy's characterization: mention-some <-> |resolving cells| > 1 -/
def hasMentionSomeStructure {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : Bool :=
  (resolvingAnswers dp worlds actions q).length > 1

/-- G&S's human-concern licensing implies Van Rooy's mention-some structure.

If a question is licensed for mention-some by a human concern (practical goal),
then there exists a decision problem where multiple cells resolve. -/
theorem humanConcern_implies_mentionSomeDP {W E : Type*} [DecidableEq E]
    (msi : MentionSomeInterrogative W E)
    (goal : String)
    (_hLicensed : MentionSomeLicensor.humanConcern goal = MentionSomeLicensor.humanConcern goal) :
    -- There exists a DP with mention-some structure
    ∃ (A : Type) (_ : DecidableEq A) (dp : DecisionProblem W A) (actions : List A) (worlds : List W),
      hasMentionSomeStructure dp worlds actions (msi.whDomain.map λ x => λ w => msi.abstract w x) := by
  sorry

/-- Van Rooy's mention-some structure implies G&S mention-some is appropriate.

If a DP has multiple resolving cells, then mention-some answers are pragmatically
appropriate (complete information is not required). -/
theorem mentionSomeDP_implies_partialOK {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W)
    (_hMS : hasMentionSomeStructure dp worlds actions q = true) :
    -- Any resolving cell gives an appropriate answer
    ∀ cell ∈ resolvingAnswers dp worlds actions q,
      resolves dp worlds actions cell = true := by
  -- By definition of resolvingAnswers, each cell in it satisfies resolves
  intro cell hMem
  simp only [resolvingAnswers, List.mem_filter] at hMem
  exact hMem.2

/-- The canonical mention-some DP: "any satisfier achieves the goal".

This is the decision-theoretic encoding of G&S's "Where can I buy coffee?"
The action is "go/don't go", utility is 1 iff you go to a coffee place. -/
def canonicalMentionSomeDP {W : Type*} (satisfies : W -> Bool) : DecisionProblem W Bool :=
  mentionSomeDP satisfies

/-- The canonical mention-some DP has mention-some structure.

For "Where can I buy coffee?", each coffee shop is a resolving cell. -/
theorem canonicalMentionSomeDP_has_structure {W : Type*} [DecidableEq W]
    (satisfies : W -> Bool) (worlds : List W)
    (hMultiple : (worlds.filter satisfies).length > 1) :
    let dp := canonicalMentionSomeDP satisfies
    let q : Question W := worlds.filter satisfies |>.map λ w => (· == w)
    hasMentionSomeStructure dp worlds [true, false] q = true := by
  sorry


/-!
## Pragmatic Answerhood and Utility

G&S Ch.IV: P "gives a pragmatic answer" to Q in J iff P∩J ⊆ some cell of J/Q.

Van Rooy: An answer has positive utility value iff learning it improves
expected decision quality.

**Conjecture**: These notions coincide under the right correspondence
between information sets J and decision problems.

The information set J encodes what the questioner knows. This constrains
the relevant decision problems to those consistent with J.
-/

/-- A decision problem is consistent with information set J if the prior
assigns positive probability only to worlds in J. -/
def dpConsistentWithInfoSet {W A : Type*}
    (dp : DecisionProblem W A) (j : InfoSet W) (worlds : List W) : Bool :=
  worlds.all λ w => dp.prior w > 0 → j w

/-- Pragmatic answerhood implies positive utility for consistent DPs.

If P gives a pragmatic answer to Q in J, then for any DP consistent with J,
learning P has non-negative utility value. -/
theorem pragmaticAnswer_implies_nonnegUtility {W A : Type*} [DecidableEq A]
    (p : W -> Bool) (q : GSQuestion W) (j : InfoSet W)
    (worlds : List W) (actions : List A)
    (hAnswer : givesPragmaticAnswer p q j worlds = true)
    (dp : DecisionProblem W A)
    (hConsistent : dpConsistentWithInfoSet dp j worlds = true) :
    utilityValue dp worlds actions p >= 0 := by
  sorry

/-- Positive utility implies pragmatic answerhood (converse direction).

If learning P has positive utility for some DP consistent with J,
then P gives a pragmatic answer to Q in J. -/
theorem positiveUtility_implies_pragmaticAnswer {W A : Type*} [DecidableEq A]
    (p : W -> Bool) (q : GSQuestion W) (j : InfoSet W)
    (worlds : List W) (actions : List A)
    (dp : DecisionProblem W A)
    (hConsistent : dpConsistentWithInfoSet dp j worlds = true)
    (hPositive : utilityValue dp worlds actions p > 0) :
    givesPragmaticAnswer p q j worlds = true := by
  sorry

/-- Full characterization: Pragmatic answerhood <-> Non-trivial utility.

P gives a pragmatic answer in J iff P has positive utility for some
DP consistent with J (and doesn't have negative utility for any). -/
theorem pragmaticAnswer_iff_utility {W A : Type*} [DecidableEq A]
    (p : W -> Bool) (q : GSQuestion W) (j : InfoSet W)
    (worlds : List W) (actions : List A) :
    givesPragmaticAnswer p q j worlds = true <->
    (∃ dp : DecisionProblem W A,
      dpConsistentWithInfoSet dp j worlds = true ∧
      utilityValue dp worlds actions p > 0) ∧
    (∀ dp : DecisionProblem W A,
      dpConsistentWithInfoSet dp j worlds = true →
      utilityValue dp worlds actions p >= 0) := by
  sorry


/-!
## When is Exhaustive Information Required?

G&S: Mention-all (exhaustive) reading is the default; mention-some requires
special licensing.

Van Rooy: Exhaustive information is required when NO proper subset of cells
resolves ALL relevant decision problems.

**Conjecture**: A question requires exhaustive answers iff the questioner's
goal requires complete information to optimize.
-/

/-- A question requires exhaustive answers for a DP if only the complete
partition resolves it (no single cell suffices). -/
def requiresExhaustive {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : Bool :=
  -- No single cell resolves the DP
  q.all λ cell => !resolves dp worlds actions cell

/-- Complete information DP always requires exhaustive answers.

When the goal is to know the exact world state, no partial answer suffices. -/
theorem completeInfoDP_requires_exhaustive {W : Type*} [DecidableEq W]
    (worlds : List W) (hMultiple : worlds.length > 1) :
    let dp := completeInformationDP (W := W)
    let q := exactQuestion worlds
    requiresExhaustive dp worlds worlds q = true := by
  sorry

/-- Mention-some DPs don't require exhaustive answers.

When any satisfier achieves the goal, partial answers work. -/
theorem mentionSomeDP_not_exhaustive {W : Type*} [DecidableEq W]
    (satisfies : W -> Bool) (worlds : List W)
    (_hExists : worlds.any satisfies = true) :
    let dp := canonicalMentionSomeDP satisfies
    let q : Question W := [satisfies, λ w => !satisfies w]
    requiresExhaustive dp worlds [true, false] q = false := by
  -- The satisfies cell resolves the DP (true dominates false in satisfying worlds)
  -- so not all cells fail to resolve, hence requiresExhaustive = false
  sorry

/-- Exhaustivity is monotone in refinement.

If Q requires exhaustive answers and Q' refines Q, then Q' also requires
exhaustive answers. Finer questions are at least as demanding. -/
theorem exhaustive_monotone {W A : Type*} [DecidableEq A]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (dp : DecisionProblem W A)
    (hRefines : q' ⊑ q)
    (hExh : requiresExhaustive dp worlds actions (q.toQuestion worlds) = true) :
    requiresExhaustive dp worlds actions (q'.toQuestion worlds) = true := by
  sorry


/-!
## Polar Question Choice is Utility-Maximizing

Van Rooy & Šafářová (2003): The choice between PPQ, NPQ, and Alt-Q depends
on the relative utility of positive vs negative answers.

- PPQ (?p): Choose when UV(p) > UV(¬p)
- NPQ (?¬p): Choose when UV(¬p) > UV(p)
- Alt (?p∨¬p): Choose when UV(p) ≈ UV(¬p)

**Conjecture**: This choice rule is optimal—it maximizes expected communicative
success given the speaker's goals.
-/

/-- Utility of positive answer exceeds negative. -/
def positiveMoreUseful {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) : Bool :=
  utilityValue dp worlds actions p > utilityValue dp worlds actions (λ w => !p w)

/-- Utility of negative answer exceeds positive. -/
def negativeMoreUseful {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) : Bool :=
  utilityValue dp worlds actions (λ w => !p w) > utilityValue dp worlds actions p

/-- Utilities are approximately equal. -/
def utilitiesBalanced {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) (epsilon : ℚ) : Bool :=
  let uvPos := utilityValue dp worlds actions p
  let uvNeg := utilityValue dp worlds actions (λ w => !p w)
  let diff := uvPos - uvNeg
  ((-epsilon) ≤ diff) && (diff ≤ epsilon)

/-- Optimal question type given utility structure. -/
def optimalPolarType {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) : PolarQuestionType :=
  if positiveMoreUseful dp worlds actions p then .positive
  else if negativeMoreUseful dp worlds actions p then .negative
  else .alternative

/-- PPQ is optimal when positive answer is more useful.

Van Rooy & Šafářová: Use PPQ (?p) when UV(p) > UV(¬p). -/
theorem ppq_optimal_when_positive_useful {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool)
    (hPos : positiveMoreUseful dp worlds actions p = true) :
    optimalPolarType dp worlds actions p = .positive := by
  simp [optimalPolarType, hPos]

/-- NPQ is optimal when negative answer is more useful.

Van Rooy & Šafářová: Use NPQ (?¬p) when UV(¬p) > UV(p). -/
theorem npq_optimal_when_negative_useful {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool)
    (hNeg : negativeMoreUseful dp worlds actions p = true)
    (hNotPos : positiveMoreUseful dp worlds actions p = false) :
    optimalPolarType dp worlds actions p = .negative := by
  simp [optimalPolarType, hNotPos, hNeg]

/-- Alt-Q is optimal when utilities are balanced.

Van Rooy & Šafářová: Use Alt (?p∨¬p) when UV(p) ≈ UV(¬p). -/
theorem alt_optimal_when_balanced {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool)
    (hNotPos : positiveMoreUseful dp worlds actions p = false)
    (hNotNeg : negativeMoreUseful dp worlds actions p = false) :
    optimalPolarType dp worlds actions p = .alternative := by
  simp [optimalPolarType, hNotPos, hNotNeg]


/-!
## Refinement and Resolution

A key property: if a coarser question resolves a decision problem,
then any finer question also resolves it.

This follows from Blackwell but is useful to state directly.
-/

/-- A question resolves a DP if learning its answer determines optimal action. -/
def questionResolves {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : Bool :=
  q.all λ cell => resolves dp worlds actions cell

/-- Helper: If action a dominates in a superset, it dominates in any subset.

Key lemma for refinement_preserves_resolution: dominance on a set S
implies dominance on any subset S' ⊆ S. -/
theorem resolves_subset {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c c' : W -> Bool)
    (hSubset : ∀ w, c' w = true → c w = true)
    (hResolves : resolves dp worlds actions c = true) :
    resolves dp worlds actions c' = true := by
  unfold resolves at *
  cases actions with
  | nil => rfl
  | cons a rest =>
    -- Need to show: rest.all (λ b => (worlds.filter c').all (λ w => ...))
    simp only [List.all_eq_true] at *
    intro b hb w hw
    -- w ∈ worlds.filter c' means w ∈ worlds ∧ c' w = true
    simp only [List.mem_filter] at hw
    -- Since c' w = true and hSubset, we have c w = true
    have hcw : c w = true := hSubset w hw.2
    -- So w ∈ worlds.filter c
    have hw_in_c : w ∈ worlds.filter c := by
      simp only [List.mem_filter]
      exact ⟨hw.1, hcw⟩
    -- Apply hResolves
    exact hResolves b hb w hw_in_c

/-- Refinement preserves resolution.

If Q resolves DP and Q' refines Q, then Q' also resolves DP.
(More information never hurts.) -/
theorem refinement_preserves_resolution {W A : Type*} [DecidableEq A]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (dp : DecisionProblem W A)
    (_hRefines : q' ⊑ q)
    (_hResolves : questionResolves dp worlds actions (q.toQuestion worlds) = true) :
    questionResolves dp worlds actions (q'.toQuestion worlds) = true := by
  -- Each cell c' of q' is contained in some cell c of q.
  -- Connect refinement to cell inclusion via resolves_subset.
  sorry -- Need to show cell inclusion from refinement, then apply resolves_subset

/-- The trivial question resolves only trivial DPs.

If the trivial question (one cell) resolves DP, the DP is trivial
(one action dominates regardless of world). -/
theorem trivial_resolves_only_trivial {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (_hResolves : questionResolves dp worlds actions [λ _ => true] = true) :
    -- One action dominates unconditionally
    ∃ a ∈ actions, actions.all λ b =>
      worlds.all λ w => dp.utility w a >= dp.utility w b := by
  -- The trivial cell (λ _ => true) covers all worlds.
  -- If it resolves, the first action dominates all others unconditionally.
  -- This follows from: worlds.filter (λ _ => true) = worlds
  sorry

/-- The exact question resolves all DPs.

The maximally fine partition always determines optimal action
(assuming actions are world-indexed). -/
theorem exact_resolves_all {W : Type*} [DecidableEq W]
    (worlds : List W) (hNonempty : worlds.length > 0) :
    let dp := completeInformationDP (W := W)
    questionResolves dp worlds worlds (exactQuestion worlds) = true := by
  sorry

end QuestionSemantics.Bridge
