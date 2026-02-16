import Linglib.Core.DecisionTheory
import Linglib.Theories.Semantics.Questions.PragmaticAnswerhood
import Linglib.Theories.Semantics.Questions.MentionSome
import Linglib.Theories.Semantics.Questions.Polarity

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

If Q refines Q', then Q is at least as useful as Q' for ANY decision problem
with non-negative priors. This is the "easy direction" of Blackwell.

Proved via `QUD.questionUtility_refinement_ge` from `Core.Partition`. -/
theorem blackwell_refinement_dominance_EU {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (q q' : GSQuestion W) (actions : List A)
    (hRefines : q ⊑ q') :
    ∀ dp : DecisionProblem W A, (∀ w, dp.prior w ≥ 0) →
      questionUtility dp actions (q.toQuestion (Finset.univ.val.toList)) >=
      questionUtility dp actions (q'.toQuestion (Finset.univ.val.toList)) := by
  intro dp hprior
  exact QUD.questionUtility_refinement_ge dp q q' actions hRefines hprior

/-- Blackwell's Theorem: Dominance implies refinement.

If Q dominates Q' for ALL decision problems (varying action type, action set,
and utility function, with non-negative priors), then Q refines Q'.

The hypothesis must quantify over all action types `A`, not a fixed one:
with a fixed `A` of cardinality < 2, the hypothesis is vacuously true
(questionUtility with one action is partition-independent) but the
conclusion may be false.

Proved via three bridges: `partitionValue_ge_of_questionUtility_ge` converts
`questionUtility` ordering to `partitionValue` on `Finset.univ`;
`partitionValue_restrict_support` restricts to arbitrary `worlds`;
`partitionValue_congr_on_worlds` transfers between the zeroed-out DP
and the original. -/
theorem blackwell_dominance_refinement {W : Type*} [Fintype W] [DecidableEq W]
    (q q' : GSQuestion W)
    (hDominates : ∀ (A : Type) [DecidableEq A] (dp : DecisionProblem W A) (actions : List A),
      (∀ w, dp.prior w ≥ 0) →
      questionUtility dp actions (q.toQuestion (Finset.univ.val.toList)) >=
      questionUtility dp actions (q'.toQuestion (Finset.univ.val.toList))) :
    q ⊑ q' := by
  apply QUD.blackwell_characterizes_refinement
  intro worlds A dp actions hprior
  letI : DecidableEq A := Classical.decEq A
  -- Construct dp' with prior zeroed outside worlds
  let dp' : DecisionProblem W A :=
    { prior := fun w => if w ∈ worlds then dp.prior w else 0
      utility := dp.utility }
  have hprior' : ∀ w, dp'.prior w ≥ 0 := by
    intro w; simp only [dp']; split_ifs <;> [exact hprior w; linarith]
  have hsupp : ∀ w, w ∉ worlds → dp'.prior w = 0 := by
    intro w hw; simp only [dp']; simp [hw]
  -- Step 1: questionUtility ordering for dp' (from hypothesis)
  have hQU := hDominates A dp' actions hprior'
  -- Step 2: Convert to partitionValue ordering on Finset.univ
  have hPV_univ := QUD.partitionValue_ge_of_questionUtility_ge dp' q q' actions hprior' hQU
  -- Step 3: Restrict from Finset.univ to worlds
  rw [QUD.partitionValue_restrict_support dp' q worlds actions hsupp,
      QUD.partitionValue_restrict_support dp' q' worlds actions hsupp] at hPV_univ
  -- Step 4: dp' agrees with dp on worlds, so partitionValue is the same
  rw [QUD.partitionValue_congr_on_worlds dp' dp q worlds actions
        (fun w hw => ⟨by simp [dp', hw], fun _ => rfl⟩),
      QUD.partitionValue_congr_on_worlds dp' dp q' worlds actions
        (fun w hw => ⟨by simp [dp', hw], fun _ => rfl⟩)] at hPV_univ
  exact hPV_univ

/-- Blackwell's Theorem (full characterization).

Semantic refinement ↔ universal pragmatic dominance (for non-negative priors).
The RHS quantifies over ALL action types and action sets. -/
theorem blackwell_full {W : Type*} [Fintype W] [DecidableEq W]
    (q q' : GSQuestion W) :
    q ⊑ q' ↔
    ∀ (A : Type) [DecidableEq A] (dp : DecisionProblem W A) (actions : List A),
      (∀ w, dp.prior w ≥ 0) →
      questionUtility dp actions (q.toQuestion (Finset.univ.val.toList)) >=
      questionUtility dp actions (q'.toQuestion (Finset.univ.val.toList)) := by
  constructor
  · intro hRefines A _ dp actions hprior
    exact blackwell_refinement_dominance_EU q q' actions hRefines dp hprior
  · intro hDom
    exact blackwell_dominance_refinement q q' hDom

/-- Blackwell forward direction for maximin: refinement implies maximin dominance.

The biconditional is FALSE with fixed action type `A`: if `|A| < 2`,
`questionMaximin` is partition-independent so dominance holds vacuously
but refinement may fail. Only the forward direction is correct for fixed `A`.

TODO: Each fine cell c' ⊆ c (coarse). The maximin over c' considers
fewer worst cases → min over subset ≥ min over superset. -/
theorem blackwell_maximin_forward {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (hRefines : q ⊑ q') :
    ∀ dp : DecisionProblem W A,
      questionMaximin dp worlds actions (q.toQuestion worlds) >=
      questionMaximin dp worlds actions (q'.toQuestion worlds) := by
  intro dp
  simp only [GSQuestion.toQuestion]
  -- Key: for each fine cell, MUV ≥ questionMaximin of coarse partition
  have key : ∀ cell ∈ q.toCells worlds,
      maximinUtilityValue dp worlds actions cell ≥
      questionMaximin dp worlds actions (q'.toCells worlds) := by
    intro cell hcell
    -- 1. Find containing coarse cell
    obtain ⟨cell', hcell', hcontains⟩ :=
      QUD.toCells_fine_sub_coarse q q' worlds hRefines cell hcell
    -- 2. Filter nonemptiness: cell has a representative
    obtain ⟨w, hw, hcw⟩ := QUD.toCells_cell_nonempty q worlds cell hcell
    have hne : worlds.filter cell ≠ [] :=
      List.ne_nil_of_mem (List.mem_filter.mpr ⟨hw, hcw⟩)
    -- 3. MUV(fine) ≥ MUV(coarse) ≥ questionMaximin(coarse)
    calc maximinUtilityValue dp worlds actions cell
        ≥ maximinUtilityValue dp worlds actions cell' :=
          maximinUtilityValue_monotone_cell dp worlds actions cell cell' hcontains hne
      _ ≥ questionMaximin dp worlds actions (q'.toCells worlds) :=
          questionMaximin_le_muv dp worlds actions (q'.toCells worlds) cell' hcell'
  -- Case split on worlds to handle empty case
  cases worlds with
  | nil => simp [QUD.toCells, questionMaximin]
  | cons w ws =>
    -- toCells of nonempty worlds is nonempty
    obtain ⟨c, cs, hq⟩ : ∃ c cs, q.toCells (w :: ws) = c :: cs := by
      match hne : q.toCells (w :: ws) with
      | c :: cs => exact ⟨c, cs, rfl⟩
      | [] => exact absurd hne (QUD.toCells_nonempty q w ws)
    simp only [questionMaximin, hq]
    exact le_foldl_min _ _ _ _
      (key c (hq ▸ List.mem_cons_self))
      (fun cell hcell => key cell (hq ▸ List.mem_cons_of_mem c hcell))


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
  simp only [hasMentionSomeStructure, canonicalMentionSomeDP]
  -- All cells resolve, so resolvingAnswers = q
  have hAllResolve : ∀ c ∈ (worlds.filter satisfies |>.map λ w => (· == w)),
      resolves (mentionSomeDP satisfies) worlds [true, false] c = true := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨w, hw, rfl⟩ := hc
    have hsat := (List.mem_filter.mp hw).2
    unfold resolves
    simp only [List.any_eq_true, List.all_eq_true, List.mem_filter, decide_eq_true_eq]
    -- Witness: action true dominates
    refine ⟨true, by simp, fun b _ v ⟨_, hv⟩ => ?_⟩
    have := beq_iff_eq.mp hv; subst this
    simp only [mentionSomeDP, hsat, Bool.true_and]
    cases b <;> simp
  simp only [resolvingAnswers, List.filter_eq_self.mpr hAllResolve,
    List.length_map, decide_eq_true_eq]
  exact hMultiple

/-- Any mention-some interrogative with multiple satisfiers has mention-some structure.

This is the substantive bridge: when multiple entities satisfy the wh-restriction,
the canonical mention-some DP (go/don't-go with utility for reaching any satisfier)
has mention-some structure. This replaces the vacuous `humanConcern_implies_mentionSomeDP`
whose hypothesis (`rfl`) carried no content.

The key insight is that G&S's "human concern" licensing boils down to the
existence of a satisfier-based DP with mention-some structure. -/
theorem mentionSome_multiple_satisfiers {W : Type*} [DecidableEq W]
    (satisfies : W → Bool) (worlds : List W)
    (hMultiple : (worlds.filter satisfies).length > 1) :
    hasMentionSomeStructure (canonicalMentionSomeDP satisfies) worlds [true, false]
      (worlds.filter satisfies |>.map fun w => (· == w)) = true :=
  canonicalMentionSomeDP_has_structure satisfies worlds hMultiple


/-!
## Question Utility Non-negativity from Blackwell

Any QUD-derived question has non-negative `questionUtility`. This follows
from Blackwell: every QUD refines `QUD.trivial` (which has utility 0),
so by `questionUtility_refinement_ge`, the utility is ≥ 0.

This is the correct replacement for the false pragmatic answerhood ↔ utility
theorems that were here previously. Those theorems claimed an equivalence between
G&S's `givesPragmaticAnswer` and `utilityValue` for consistent DPs, but
`utilityValue` on an arbitrary `Finset.filter` doesn't connect to
`givesPragmaticAnswer` (which tests partition cell containment, not utility).
-/

/-- Question utility is non-negative for QUD-derived questions with proper priors.

Corollary of `QUD.questionUtility_qud_nonneg` proved in `Core.Partition`. -/
theorem questionUtility_nonneg_from_blackwell {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (q : QUD W) (actions : List A)
    (hprior : ∀ w, dp.prior w ≥ 0)
    (hsum : Finset.univ.sum dp.prior ≤ 1) :
    questionUtility dp actions (q.toCells (Finset.univ.val.toList)) ≥ 0 :=
  QUD.questionUtility_qud_nonneg dp q actions hprior hsum


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
  show requiresExhaustive (mentionSomeDP satisfies) worlds [true, false]
    [satisfies, fun w => !satisfies w] = false
  -- Key: the `satisfies` cell resolves because action `true` dominates.
  -- For w with satisfies w = true: utility(w, true) = 1 >= utility(w, b) for any b.
  -- So !resolves ... satisfies = false, making the List.all false.
  simp only [requiresExhaustive, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_false_iff]
  left
  simp only [Bool.not_eq_false']
  simp only [resolves, List.any_cons, List.any_nil, Bool.or_false,
    List.all_cons, List.all_nil, Bool.and_true]
  simp only [Bool.or_eq_true_iff]
  left
  simp only [Bool.and_eq_true_iff, List.all_eq_true, List.mem_filter, and_imp]
  exact ⟨fun w _ hw => by simp [mentionSomeDP, hw],
         fun w _ hw => by simp [mentionSomeDP, hw]⟩

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
def positiveMoreUseful {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (p : W -> Bool) : Bool :=
  utilityValue dp actions (Finset.univ.filter (fun w => p w = true)) >
    utilityValue dp actions (Finset.univ.filter (fun w => (!p w) = true))

/-- Utility of negative answer exceeds positive. -/
def negativeMoreUseful {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (p : W -> Bool) : Bool :=
  utilityValue dp actions (Finset.univ.filter (fun w => (!p w) = true)) >
    utilityValue dp actions (Finset.univ.filter (fun w => p w = true))

/-- Utilities are approximately equal. -/
def utilitiesBalanced {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (p : W -> Bool) (epsilon : ℚ) : Bool :=
  let uvPos := utilityValue dp actions (Finset.univ.filter (fun w => p w = true))
  let uvNeg := utilityValue dp actions (Finset.univ.filter (fun w => (!p w) = true))
  let diff := uvPos - uvNeg
  ((-epsilon) ≤ diff) && (diff ≤ epsilon)

/-- Optimal question type given utility structure. -/
def optimalPolarType {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (p : W -> Bool) : PolarQuestionType :=
  if positiveMoreUseful dp actions p then .positive
  else if negativeMoreUseful dp actions p then .negative
  else .alternative

/-- PPQ is optimal when positive answer is more useful.

Van Rooy & Šafářová: Use PPQ (?p) when UV(p) > UV(¬p). -/
theorem ppq_optimal_when_positive_useful {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (p : W -> Bool)
    (hPos : positiveMoreUseful dp actions p = true) :
    optimalPolarType dp actions p = .positive := by
  simp [optimalPolarType, hPos]

/-- NPQ is optimal when negative answer is more useful.

Van Rooy & Šafářová: Use NPQ (?¬p) when UV(¬p) > UV(p). -/
theorem npq_optimal_when_negative_useful {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (p : W -> Bool)
    (hNeg : negativeMoreUseful dp actions p = true)
    (hNotPos : positiveMoreUseful dp actions p = false) :
    optimalPolarType dp actions p = .negative := by
  simp [optimalPolarType, hNotPos, hNeg]

/-- Alt-Q is optimal when utilities are balanced.

Van Rooy & Šafářová: Use Alt (?p∨¬p) when UV(p) ≈ UV(¬p). -/
theorem alt_optimal_when_balanced {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (p : W -> Bool)
    (hNotPos : positiveMoreUseful dp actions p = false)
    (hNotNeg : negativeMoreUseful dp actions p = false) :
    optimalPolarType dp actions p = .alternative := by
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

/-- Helper: If some action dominates in a superset, it dominates in any subset.

Key lemma for refinement_preserves_resolution: if C resolves DP (some action
dominates on C) and C' ⊆ C, then C' also resolves DP (same witness). -/
theorem resolves_subset {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c c' : W -> Bool)
    (hSubset : ∀ w, c' w = true → c w = true)
    (hResolves : resolves dp worlds actions c = true) :
    resolves dp worlds actions c' = true := by
  unfold resolves at *
  cases actions with
  | nil => rfl
  | cons _ _ =>
    -- hResolves: ∃ a ∈ actions, a dominates all others on worlds.filter c
    -- Goal: ∃ a ∈ actions, a dominates all others on worlds.filter c'
    -- Same witness works: c' ⊆ c means fewer worlds to check
    simp only [List.any_eq_true, List.all_eq_true] at *
    obtain ⟨dom, hdom_mem, hdom⟩ := hResolves
    refine ⟨dom, hdom_mem, λ b hb w hw => ?_⟩
    simp only [List.mem_filter] at hw
    have hcw : c w = true := hSubset w hw.2
    have hw_in_c : w ∈ worlds.filter c := by
      simp only [List.mem_filter]
      exact ⟨hw.1, hcw⟩
    exact hdom b hb w hw_in_c

/-- Refinement preserves resolution.

If Q resolves DP and Q' refines Q, then Q' also resolves DP.
(More information never hurts.) -/
theorem refinement_preserves_resolution {W A : Type*} [DecidableEq A]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (dp : DecisionProblem W A)
    (hRefines : q' ⊑ q)
    (hResolves : questionResolves dp worlds actions (q.toQuestion worlds) = true) :
    questionResolves dp worlds actions (q'.toQuestion worlds) = true := by
  -- Each fine cell c' of q' is contained in some coarse cell c of q.
  -- c resolves (hResolves), so c' resolves (resolves_subset).
  simp only [questionResolves, GSQuestion.toQuestion] at *
  simp only [List.all_eq_true] at *
  intro c' hc'
  obtain ⟨c, hc_mem, hc_sub⟩ := QUD.toCells_fine_sub_coarse q' q worlds hRefines c' hc'
  exact resolves_subset dp worlds actions c c' hc_sub (hResolves c hc_mem)

/-- Exhaustivity is anti-monotone in refinement.

If Q' refines Q and Q' requires exhaustive answers (no fine cell resolves),
then Q also requires exhaustive answers (no coarse cell resolves).

Proof idea: For each coarse cell c of Q, pick any fine cell c' ⊆ c (exists
by refinement). c' doesn't resolve (by hypothesis). By contrapositive of
`resolves_subset` (smaller doesn't resolve → bigger doesn't resolve), c
doesn't resolve either.

The converse is FALSE. Counterexample: W = {w1, w2}, actions = {a, b},
U(w1,a)=1, U(w1,b)=0, U(w2,a)=0, U(w2,b)=1. Coarse cell {w1,w2} doesn't resolve
(neither dominates), but fine cells {w1}, {w2} each resolve. -/
theorem exhaustive_antimonotone {W A : Type*} [DecidableEq A]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (dp : DecisionProblem W A)
    (hRefines : q' ⊑ q)
    (hExh : requiresExhaustive dp worlds actions (q'.toQuestion worlds) = true) :
    requiresExhaustive dp worlds actions (q.toQuestion worlds) = true := by
  simp only [requiresExhaustive, GSQuestion.toQuestion] at *
  simp only [List.all_eq_true, Bool.not_eq_true'] at *
  intro c hc
  obtain ⟨c', hc'_mem, hc'_sub⟩ := QUD.toCells_coarse_contains_fine q q' worlds hRefines c hc
  have hc'_nr := hExh c' hc'_mem
  by_contra habs
  have hrc : resolves dp worlds actions c = true := by
    cases h : resolves dp worlds actions c with
    | true => rfl
    | false => exact absurd h habs
  have h_contra := resolves_subset dp worlds actions c c' hc'_sub hrc
  simp [hc'_nr] at h_contra

/-- The converse of `exhaustive_antimonotone` is FALSE.

Counterexample: W = {w1, w2}, actions = {go, stay},
U(w1, go)=1, U(w1, stay)=0, U(w2, go)=0, U(w2, stay)=1.
Coarse cell {w1, w2} doesn't resolve (neither action dominates),
but fine cells {w1}, {w2} each resolve. -/
private inductive ExhW | w1 | w2 deriving DecidableEq, Repr

private def exhaustiveCounterexDP : DecisionProblem ExhW Bool where
  utility w a := match w, a with
    | .w1, true  => 1 | .w1, false => 0
    | .w2, true  => 0 | .w2, false => 1
  prior _ := 1

/-- Coarse (trivial) question requires exhaustive for the counterex DP. -/
example : requiresExhaustive exhaustiveCounterexDP [.w1, .w2] [true, false]
    [fun _ => true] = true := by native_decide

/-- Fine (exact) question does NOT require exhaustive — each cell resolves. -/
example : requiresExhaustive exhaustiveCounterexDP [.w1, .w2] [true, false]
    [fun w => w == ExhW.w1, fun w => w == ExhW.w2] = false := by native_decide

/-- The trivial question resolves only trivial DPs.

If the trivial question (one cell = all worlds) resolves DP, the DP is trivial:
some action dominates all others on all worlds. -/
theorem trivial_resolves_only_trivial {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (hNonempty : actions ≠ [])
    (hResolves : questionResolves dp worlds actions [λ _ => true] = true) :
    ∃ a ∈ actions, actions.all λ b =>
      worlds.all λ w => dp.utility w a >= dp.utility w b := by
  simp only [questionResolves, List.all_cons, List.all_nil, Bool.and_true] at hResolves
  unfold resolves at hResolves
  have hfilt : worlds.filter (fun (_ : W) => true) = worlds :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  rw [hfilt] at hResolves
  cases h : actions with
  | nil => exact absurd h hNonempty
  | cons a rest =>
    rw [h] at hResolves
    exact List.any_eq_true.mp hResolves

/-- The exact question resolves all DPs (with world-indexed actions).

The maximally fine partition always determines optimal action: in each
singleton cell {wᵢ}, action wᵢ dominates all others (utility 1 vs 0).

Now correct after fixing `resolves` to existential (Van Rooy 2003, p.736). -/
theorem exact_resolves_all {W : Type*} [DecidableEq W]
    (worlds : List W) (hNonempty : worlds.length > 0) :
    let dp := completeInformationDP (W := W)
    questionResolves dp worlds worlds (exactQuestion worlds) = true := by
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, worlds = x :: xs := by
    cases worlds with | nil => simp at hNonempty | cons x xs => exact ⟨x, xs, rfl⟩
  simp only [questionResolves, exactQuestion, List.all_eq_true, List.mem_map]
  rintro _ ⟨w, hw, rfl⟩
  -- Each singleton cell resolves: action w dominates
  unfold resolves completeInformationDP
  simp only [List.any_eq_true, List.all_eq_true, List.mem_filter, decide_eq_true_eq]
  refine ⟨w, hw, fun b _ v ⟨_, hv⟩ => ?_⟩
  have := (beq_iff_eq.mp hv).symm; subst this
  simp only [beq_self_eq_true, ite_true]
  split <;> norm_num

/-- The trivial question doesn't resolve the complete information DP.

When the goal is to know the exact world state, a single cell covering all
worlds cannot resolve the DP: for any candidate action a, there exists
w ≠ a with U(w, a) = 0 < 1 = U(w, w). Requires ≥2 distinct worlds. -/
theorem completeInfoDP_requires_exhaustive {W : Type*} [DecidableEq W]
    (worlds : List W) (hMultiple : worlds.length > 1) (hNodup : worlds.Nodup) :
    requiresExhaustive completeInformationDP worlds worlds [fun _ => true] = true := by
  -- Suffices to show the trivial cell doesn't resolve
  suffices h : resolves completeInformationDP worlds worlds (fun _ => true) = false by
    simp [requiresExhaustive, h]
  -- By contradiction: if it resolves, some action dominates on all worlds
  by_contra habs
  have hres : resolves completeInformationDP worlds worlds (fun _ => true) = true := by
    cases h : resolves completeInformationDP worlds worlds (fun _ => true) with
    | true => rfl
    | false => exact absurd h habs
  have hne : worlds ≠ [] := by intro h; rw [h] at hMultiple; simp at hMultiple
  have hqr : questionResolves completeInformationDP worlds worlds [fun _ => true] = true := by
    simp [questionResolves, hres]
  obtain ⟨a, ha, hdom⟩ := trivial_resolves_only_trivial
    completeInformationDP worlds worlds hne hqr
  simp only [List.all_eq_true, decide_eq_true_eq] at hdom
  -- Find w ∈ worlds with w ≠ a
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, worlds = x :: xs := by
    cases worlds with | nil => simp at hMultiple | cons x xs => exact ⟨x, xs, rfl⟩
  have hxs_ne : xs ≠ [] := by intro h; rw [h] at hMultiple; simp at hMultiple
  have hxne : x ∉ xs := (List.nodup_cons.mp hNodup).1
  obtain ⟨w, hw, hwne⟩ : ∃ w ∈ (x :: xs), w ≠ a := by
    by_cases hax : a = x
    · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil xs hxs_ne
      exact ⟨y, .tail x hy, by rintro rfl; exact hxne (hax ▸ hy)⟩
    · exact ⟨x, List.Mem.head xs, fun h => hax h.symm⟩
  -- At w: utility(w, a) = 0 but utility(w, w) = 1
  have h1 := hdom w hw w hw
  simp only [completeInformationDP, beq_iff_eq] at h1
  simp [hwne.symm] at h1
  norm_num at h1

end QuestionSemantics.Bridge
