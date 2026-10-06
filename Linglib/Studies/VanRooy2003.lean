module

public import Linglib.Core.Probability.Decision.Duality
public import Linglib.Data.Examples.VanRooy2003
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Setoid.Partition

/-!
# van Rooy (2003): Questioning to Resolve Decision Problems

Van Rooy grounds the meaning of questions in the questioner's decision problem, a prior over
worlds and a utility for each action in each world. Information resolves the problem when some
action is optimal in every world it leaves open. A question, a partition of the worlds, is worth
the average gain in decision value from learning its answer; this value equals the expected value
of sample information and is never negative (`DecisionProblem.questionUtility_parts_nonneg`), and
one question refines another exactly when it is at least as useful in every decision problem
(`DecisionProblem.le_iff_forall_questionUtility_le`). A wh-question denotes the propositions that
some value is among the optimal true values of its predicate, those with no more relevant true
value, and this one rule yields both mention-all and mention-some readings.

## Main statements

* `isResolved_iff_exists_subset_optimalityRegion`: information resolves the problem exactly
  when it lies within the worlds where one action is optimal.
* `newspaper_station_resolves`, `newspaper_betterAnswer`: in the Italian newspaper example the
  partial answer *at least at the station* resolves the problem and is a better answer than the
  complete one.
* `betterQuestion_whQuestion`: of two equally useful wh-domains the smaller gives the better
  question.
* `questionR_entailment`: when relevance is informativity the rule gives the partition by the
  predicate's extension, the mention-all reading.
* `bestPlace_questionR`, `bestPlace_overlapCells`, `bestPlace_hamblin`: the newspaper question has
  a mention-some meaning, which the rule of footnote 28 and Hamblin's rule both miss.
* `optimalValues_le`, `optimalValues_gt_eq_empty`: ranking numbers by size gives the maximum for
  *How many meters can you jump?* and nothing for *How many meters can't you jump?*.
* `killer_byName`, `killer_byMask`, `beatles_questionR`: which concepts resolve the questioner's
  problem decides the partition of *Who killed spiderman?*, and an autograph hierarchy gives
  *Which Beatles' autograph do you have?* three answers.

## Implementation notes

Decision problems are real-valued, and questions over a finite set of worlds are `Finpartition`s.
The relevance of a value in a world is a utility into a preorder; the paper's relation `>` orders
answers, which for the newspaper example of section 5.2 is world-relative, the best place
differing between worlds. Section 5.3 assumes the questioner most wants to resolve her problem, so
for *Who killed spiderman?* a concept is more relevant when it resolves the problem. The examples
are rows of `Data.Examples.VanRooy2003`.

## TODO

* The group-valued domain example of section 5.3, the questions (21), (23) and (25), the
  relevance condition on wh-domains of section 4.2, the answer ordering of section 3.1, and the
  argumentative value of section 5.4.

## References

* [van-rooy-2003]
* [blackwell-1953]
* [raiffa-schlaifer-1961]
* [groenendijk-stokhof-1984]
* [hamblin-1973b]
* [rullmann-1995]
* [aloni-2001]
* [merin-1999-relevance]
-/

@[expose] public section

namespace VanRooy2003

open Core.DecisionTheory Core.DecisionTheory.DecisionProblem

variable {W A G R : Type*}

/-! ### Resolving a decision problem -/

/-- The proposition an action induces is the set of worlds where no action is strictly
better. -/
def optimalityRegion (dp : DecisionProblem ℝ W A) (acts : Set A) (a : A) : Set W :=
  {w | ∀ b ∈ acts, dp.utility w b ≤ dp.utility w a}

/-- The propositions the actions induce. -/
def optimalityRegions (dp : DecisionProblem ℝ W A) (acts : Set A) : Set (Set W) :=
  optimalityRegion dp acts '' acts

/-- Information resolves the decision problem exactly when it lies within the optimality
region of some action. -/
theorem isResolved_iff_exists_subset_optimalityRegion (dp : DecisionProblem ℝ W A)
    (acts : Set A) (C : Set W) :
    IsResolved dp acts C ↔ ∃ a ∈ acts, C ⊆ optimalityRegion dp acts a :=
  ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, fun _ hw b hb ↦ h b hb _ hw⟩,
    fun ⟨a, ha, h⟩ ↦ ⟨a, ha, fun _ hb _ hw ↦ h hw _ hb⟩⟩

/-- Over finitely many actions every world has an optimal one, so the regions cover the
worlds. -/
theorem iUnion_optimalityRegion (dp : DecisionProblem ℝ W A) (acts : Finset A)
    (hne : acts.Nonempty) : ⋃ a ∈ acts, optimalityRegion dp acts a = Set.univ :=
  Set.eq_univ_of_forall fun w ↦
    let ⟨a, ha, hmax⟩ := acts.exists_max_image (dp.utility w) hne
    Set.mem_iUnion₂.2 ⟨a, ha, hmax⟩

/-- When every world has a strictly best action the regions are pairwise disjoint, and the
actions induce a partition. -/
theorem pairwiseDisjoint_optimalityRegion (dp : DecisionProblem ℝ W A) (acts : Set A)
    (hstrict : ∀ w, ∃ a ∈ acts, ∀ b ∈ acts, b ≠ a → dp.utility w b < dp.utility w a) :
    acts.PairwiseDisjoint (optimalityRegion dp acts) := by
  intro a ha a' ha' hne
  refine Set.disjoint_left.2 fun w hw hw' ↦ ?_
  obtain ⟨c, hc, hbest⟩ := hstrict w
  by_cases hac : a = c
  · subst hac
    exact (hw' a ha).not_gt (hbest a' ha' (Ne.symm hne))
  · exact (hw c hc).not_gt (hbest a ha hac)

/-- An answer is better than another when it has a higher utility value, or the same value and
is strictly less informative. -/
def BetterAnswer [Fintype W] (dp : DecisionProblem ℝ W A) (acts : Finset A) (C D : Finset W) :
    Prop :=
  toLex (dp.utilityValue acts D, D) < toLex (dp.utilityValue acts C, C)

theorem betterAnswer_iff [Fintype W] {dp : DecisionProblem ℝ W A} {acts : Finset A}
    {C D : Finset W} :
    BetterAnswer dp acts C D ↔ dp.utilityValue acts D < dp.utilityValue acts C ∨
      dp.utilityValue acts C = dp.utilityValue acts D ∧ D ⊂ C := by
  simp [BetterAnswer, Prod.Lex.toLex_lt_toLex, eq_comm]

/-! ### The Italian newspaper -/

/-- The worlds of the newspaper examples are named by where to go, only the station, only the
palace, or either (the paper's `u`, `v` and `w`). -/
inductive NewsW where
  | station
  | palace
  | both
  deriving DecidableEq, Fintype, Inhabited

/-- The actions of the newspaper example are walking to the station and walking to the
palace. -/
inductive Walk where
  | station
  | palace
  deriving DecidableEq, Fintype, Inhabited

private theorem forall_walk {p : Walk → Prop} : (∀ a, p a) ↔ p .station ∧ p .palace :=
  ⟨fun h ↦ ⟨h _, h _⟩, fun h a ↦ a.casesOn h.1 h.2⟩

private theorem sum_newsW {M : Type*} [AddCommMonoid M] (f : NewsW → M) :
    ∑ x, f x = f .station + f .palace + f .both := by
  rw [show (Finset.univ : Finset NewsW) = {.station, .palace, .both} by decide]
  simp [add_assoc]

/-- Walking to a place is worth 1 where the newspaper is sold there (`Examples.ex_12`). -/
noncomputable def newspaper : DecisionProblem ℝ NewsW Walk where
  utility
    | .station, .station | .both, .station | .palace, .palace | .both, .palace => 1
    | .palace, .station | .station, .palace => 0
  prior _ := 1 / 3

/-- The actions induce overlapping propositions, not a partition. -/
theorem newspaper_optimalityRegions :
    optimalityRegion newspaper Set.univ .station = {.station, .both} ∧
      optimalityRegion newspaper Set.univ .palace = {.palace, .both} := by
  constructor <;> ext w <;> cases w <;> norm_num [optimalityRegion, forall_walk, newspaper]

/-- The mention-some answer *at least at the station* resolves the problem although it is only
a partial answer to the partition question. -/
theorem newspaper_station_resolves :
    IsResolved newspaper Set.univ ({.station, .both} : Set NewsW) :=
  (isResolved_iff_exists_subset_optimalityRegion _ _ _).2
    ⟨.station, trivial, newspaper_optimalityRegions.1.ge⟩

private theorem newspaper_value : newspaper.value Finset.univ = 2 / 3 := by
  have h (a : Walk) : newspaper.expectedUtility a = 2 / 3 := by
    cases a <;> norm_num [expectedUtility, sum_newsW, newspaper]
  rw [value_eq_of_forall_le (Finset.mem_univ .station) fun b _ ↦ ((h b).trans (h _).symm).le, h]

/-- Any answer that leaves the palace out resolves the problem and is worth `1 / 3`. -/
private theorem newspaper_utilityValue {C : Finset NewsW} (hC : C.Nonempty) (hs : .palace ∉ C) :
    newspaper.utilityValue Finset.univ C = 1 / 3 := by
  have hprior (w : NewsW) : 0 ≤ newspaper.prior w := by norm_num [newspaper]
  have hpos : 0 < newspaper.cellProbability C :=
    Finset.sum_pos (fun _ _ ↦ by norm_num [newspaper]) hC
  have hstation : newspaper.condExpectedUtility C .station = 1 := by
    have h := cellProbability_mul_condExpectedUtility (cell := C) hprior .station
    rw [Finset.sum_congr rfl fun w hw ↦ show newspaper.prior w * newspaper.utility w .station =
      newspaper.prior w by cases w <;> simp_all [newspaper]] at h
    exact mul_left_cancel₀ hpos.ne' (h.trans (mul_one _).symm)
  have hle (b : Walk) : newspaper.condExpectedUtility C b ≤ 1 := by
    refine le_of_mul_le_mul_left ?_ hpos
    rw [cellProbability_mul_condExpectedUtility hprior, mul_one]
    exact Finset.sum_le_sum fun w _ ↦ by cases w <;> cases b <;> norm_num [newspaper]
  rw [utilityValue, condValue_eq_of_forall_le (Finset.mem_univ .station)
    fun b _ ↦ hstation ▸ hle b, hstation, newspaper_value]
  norm_num

/-- Taking effort into account, the mention-some answer *at least at the station* is a better
answer than the complete answer *only at the station*, since both resolve the problem and the
first says less. -/
theorem newspaper_betterAnswer :
    BetterAnswer newspaper Finset.univ {.station, .both} {.station} := by
  refine betterAnswer_iff.2 (.inr ⟨?_, by decide⟩)
  rw [newspaper_utilityValue (by simp) (by decide), newspaper_utilityValue (by simp) (by decide)]

/-! ### The utility of questions -/

section Utility

variable [Fintype W] [DecidableEq W]

/-- No question is worth more than the finest one, what the world is like, whose value is the
expected value of perfect information of [raiffa-schlaifer-1961]. -/
theorem questionUtility_le_bot (dp : DecisionProblem ℝ W A) (acts : Finset A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (Q : Finpartition (Finset.univ : Finset W)) :
    dp.questionUtility acts Q.parts ≤
      dp.questionUtility acts (⊥ : Finpartition (Finset.univ : Finset W)).parts :=
  questionUtility_anti_of_le dp acts bot_le hprior

/-- Relative to a decision problem, a question is better than another when it is more useful, or
as useful and strictly coarser, since one should not ask for irrelevant information. -/
def BetterQuestion (dp : DecisionProblem ℝ W A) (acts : Finset A)
    (Q Q' : Finpartition (Finset.univ : Finset W)) : Prop :=
  toLex (dp.questionUtility acts Q'.parts, Q') < toLex (dp.questionUtility acts Q.parts, Q)

theorem betterQuestion_iff {dp : DecisionProblem ℝ W A} {acts : Finset A}
    {Q Q' : Finpartition (Finset.univ : Finset W)} :
    BetterQuestion dp acts Q Q' ↔
      dp.questionUtility acts Q'.parts < dp.questionUtility acts Q.parts ∨
        dp.questionUtility acts Q.parts = dp.questionUtility acts Q'.parts ∧ Q' < Q := by
  simp [BetterQuestion, Prod.Lex.toLex_lt_toLex, eq_comm]

/-! ### The domain of a wh-phrase -/

variable {D : Type*} [DecidableEq D]

/-- The partition a wh-question induces over a domain puts two worlds together when the
predicate's extension agrees on the domain. -/
def whQuestion (P : W → Finset D) (dom : Finset D) : Finpartition (Finset.univ : Finset W) :=
  Finpartition.ofFun fun w ↦ dom ∩ P w

/-- Enlarging the domain refines the question, since more individuals give more specific
answers. -/
theorem whQuestion_anti (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom') :
    whQuestion P dom' ≤ whQuestion P dom :=
  Finpartition.ofFun_le_ofFun_iff.2 fun w v hwv ↦ by
    rw [← Finset.inter_eq_left.2 h, Finset.inter_assoc, Finset.inter_assoc, hwv]

/-- Enlarging the domain cannot lower the value of the question, so the domain should contain
every individual that could matter. -/
theorem questionUtility_whQuestion_mono (dp : DecisionProblem ℝ W A) (acts : Finset A)
    (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom') (hprior : ∀ w, 0 ≤ dp.prior w) :
    dp.questionUtility acts (whQuestion P dom).parts ≤
      dp.questionUtility acts (whQuestion P dom').parts :=
  questionUtility_anti_of_le dp acts (whQuestion_anti P h) hprior

/-- Of two domains yielding equally useful but different questions, the smaller gives the better
question, so the domain relevance selects contains only individuals that could affect the
decision. -/
theorem betterQuestion_whQuestion (dp : DecisionProblem ℝ W A) (acts : Finset A)
    (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom')
    (heq : dp.questionUtility acts (whQuestion P dom).parts =
      dp.questionUtility acts (whQuestion P dom').parts)
    (hne : whQuestion P dom' ≠ whQuestion P dom) :
    BetterQuestion dp acts (whQuestion P dom) (whQuestion P dom') :=
  betterQuestion_iff.2 (.inr ⟨heq, (whQuestion_anti P h).lt_of_ne hne⟩)

end Utility

/-! ### Mention-some and mention-all from one rule -/

/-- The optimal values of `P` in `w` are its true values for which no true value is more
relevant. -/
def optimalValues [Preorder R] (P : W → Set G) (u : W → G → R) (w : W) : Set G :=
  {g ∈ P w | ∀ g' ∈ P w, ¬ u w g < u w g'}

theorem mem_optimalValues [LinearOrder R] {P : W → Set G} {u : W → G → R} {w : W} {g : G} :
    g ∈ optimalValues P u w ↔ g ∈ P w ∧ ∀ g' ∈ P w, u w g' ≤ u w g := by
  simp only [optimalValues, Set.mem_ofPred_eq, not_lt]

/-- Hamblin's rule makes the answers the propositions that a value satisfies the predicate, one
for each value satisfying it somewhere. -/
def whAnswers (P : W → Set G) : Set (Set W) := {p | ∃ w, ∃ g ∈ P w, p = {v | g ∈ P v}}

/-- The paper's rule is Hamblin's rule applied to the optimal values, whose answers are the
propositions that a value is among the optimal ones. -/
def questionR [Preorder R] (P : W → Set G) (u : W → G → R) : Set (Set W) :=
  whAnswers (optimalValues P u)

/-- The rule of footnote 28 puts two worlds together whenever their optimal values overlap. -/
def overlapCells (op : W → Set G) : Set (Set W) := {p | ∃ w, p = {v | (op w ∩ op v).Nonempty}}

/-- Hamblin's rule collects, for each value true somewhere, the worlds where it is true. -/
theorem whAnswers_eq_image (P : W → Set G) :
    whAnswers P = (fun g ↦ {v | g ∈ P v}) '' ⋃ w, P w := by
  ext p
  simp only [whAnswers, Set.mem_image, Set.mem_iUnion]
  exact ⟨fun ⟨w, g, hg, hp⟩ ↦ ⟨g, ⟨w, hg⟩, hp.symm⟩, fun ⟨g, ⟨w, hg⟩, hp⟩ ↦ ⟨w, g, hg, hp.symm⟩⟩

/-- When the optimal value is unique in every world the rule gives the partition by that
value. -/
theorem whAnswers_singleton (f : W → G) :
    whAnswers (fun w ↦ {f w}) = (Setoid.ker f).classes := by
  ext p
  simp only [whAnswers, Set.mem_singleton_iff, exists_eq_left, Setoid.classes,
    Set.mem_ofPred_eq]
  exact exists_congr fun w ↦ by
    rw [show {v | f w = f v} = {x | Setoid.ker f x w} from Set.ext fun v ↦ eq_comm]

/-- When every value is equally relevant, the rule is Hamblin's. -/
theorem questionR_const [Preorder R] (P : W → Set G) (r : R) :
    questionR P (fun _ _ ↦ r) = whAnswers P :=
  congrArg whAnswers <| funext fun w ↦ Set.ext fun g ↦ by simp [optimalValues]

/-- Asking which action is optimal, the rule yields the nonempty propositions the actions
induce. -/
theorem questionR_actions (dp : DecisionProblem ℝ W A) (acts : Set A) :
    questionR (fun _ ↦ acts) dp.utility = {r ∈ optimalityRegions dp acts | r.Nonempty} := by
  ext p
  simp only [questionR, whAnswers, optimalityRegions, Set.mem_ofPred_eq, Set.mem_image,
    mem_optimalValues]
  constructor
  · rintro ⟨w, a, ⟨ha, hw⟩, rfl⟩
    exact ⟨⟨a, ha, Set.ext fun v ↦ by simp [optimalityRegion, ha]⟩, w, ha, hw⟩
  · rintro ⟨⟨a, ha, rfl⟩, w, hw⟩
    exact ⟨w, a, ⟨ha, hw⟩, Set.ext fun v ↦ by simp [optimalityRegion, ha]⟩

/-- When an answer is more relevant the more informative it is, the rule asks for the most
informative true answer, and for a distributive predicate it gives the partition by the
predicate's extension, the mention-all reading of [groenendijk-stokhof-1984]. -/
theorem questionR_entailment {D : Type*} (ext : W → Set D) :
    questionR (fun w ↦ {g | g ⊆ ext w}) (fun _ g ↦ OrderDual.toDual {v | g ⊆ ext v}) =
      (Setoid.ker ext).classes := by
  set op := optimalValues (fun w ↦ {g : Set D | g ⊆ ext w})
    (fun _ g ↦ OrderDual.toDual {v | g ⊆ ext v})
  have hopt (w : W) (g : Set D) :
      g ∈ op w ↔ g ⊆ ext w ∧ {v | g ⊆ ext v} = {v | ext w ⊆ ext v} := by
    simp only [op, optimalValues, Set.mem_ofPred_eq, OrderDual.toDual_lt_toDual]
    refine ⟨fun ⟨hg, h⟩ ↦ ⟨hg, by_contra fun hne ↦ h (ext w) subset_rfl
      (lt_of_le_of_ne (fun v hv ↦ hg.trans hv) (Ne.symm hne))⟩,
      fun ⟨hg, heq⟩ ↦ ⟨hg, fun g' hg' hlt ↦ (heq ▸ hlt).not_ge fun v hv ↦ hg'.trans hv⟩⟩
  have hcell (w : W) (g : Set D) (hg : g ∈ op w) :
      {v | g ∈ op v} = {v | Setoid.ker ext v w} := by
    obtain ⟨hgw, hgeq⟩ := (hopt w g).1 hg
    ext v
    simp only [Set.mem_ofPred_eq, hopt]
    refine ⟨fun ⟨_, hgv⟩ ↦ ?_, fun h ↦ ⟨h ▸ hgw, h ▸ hgeq⟩⟩
    have h := hgv.symm.trans hgeq
    exact ((Set.ext_iff.1 h w).2 (show ext w ⊆ ext w from subset_rfl)).antisymm
      ((Set.ext_iff.1 h v).1 (show ext v ⊆ ext v from subset_rfl))
  ext p
  simp only [questionR, whAnswers, Setoid.classes, Set.mem_ofPred_eq]
  refine ⟨fun ⟨w, g, hg, hp⟩ ↦ ⟨w, hp.trans (hcell w g hg)⟩, fun ⟨w, hp⟩ ↦ ?_⟩
  have hw : ext w ∈ op w := (hopt w _).2 ⟨subset_rfl, rfl⟩
  exact ⟨w, ext w, hw, hp.trans (hcell w _ hw).symm⟩

/-! #### The best place to buy the newspaper -/

/-- In the second newspaper example the paper is sold at both places in every world, and each
world is named by its best place (`Examples.ex_20`). -/
noncomputable def bestPlace : DecisionProblem ℝ NewsW Walk where
  utility
    | .station, .station | .palace, .palace => 2
    | .station, .palace | .palace, .station | .both, _ => 1
  prior _ := 1 / 3

/-- The optimal places are the best place of each world. -/
theorem bestPlace_optimalValues :
    optimalValues (fun _ ↦ Set.univ) bestPlace.utility .station = {.station} ∧
      optimalValues (fun _ ↦ Set.univ) bestPlace.utility .palace = {.palace} ∧
      optimalValues (fun _ ↦ Set.univ) bestPlace.utility .both = Set.univ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext a <;> cases a <;>
    norm_num [mem_optimalValues, forall_walk, bestPlace]

/-- The rule yields the overlapping mention-some answers. -/
theorem bestPlace_questionR :
    questionR (fun _ ↦ Set.univ) bestPlace.utility = {{.station, .both}, {.palace, .both}} := by
  have h (a : Walk) : optimalityRegion bestPlace Set.univ a =
      if a = .station then {.station, .both} else {.palace, .both} := by
    ext w; cases a <;> cases w <;> norm_num [optimalityRegion, forall_walk, bestPlace]
  rw [questionR_actions, optimalityRegions, Set.image_univ]
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, h]
  constructor
  · rintro ⟨⟨a, rfl⟩, -⟩
    cases a <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨.station, by simp⟩, .station, by simp⟩
    · exact ⟨⟨.palace, by simp⟩, .palace, by simp⟩

/-- The rule of footnote 28 adds the trivial answer, which is why the paper rejects it. -/
theorem bestPlace_overlapCells :
    overlapCells (optimalValues (fun _ ↦ Set.univ) bestPlace.utility) =
      {{.station, .both}, {.palace, .both}, Set.univ} := by
  obtain ⟨hs, hp, hb⟩ := bestPlace_optimalValues
  have cell (w : NewsW) (S : Set NewsW)
      (h : ∀ v, (optimalValues (fun _ ↦ Set.univ) bestPlace.utility w ∩
        optimalValues (fun _ ↦ Set.univ) bestPlace.utility v).Nonempty ↔ v ∈ S) :
      S ∈ overlapCells (optimalValues (fun _ ↦ Set.univ) bestPlace.utility) :=
    ⟨w, (Set.ext h).symm⟩
  ext p
  constructor
  · rintro ⟨w, rfl⟩
    cases w <;> [left; (right; left); (right; right)] <;> ext v <;> cases v <;>
      simp [hs, hp, hb]
  · rintro (rfl | rfl | rfl)
    · exact cell .station _ fun v ↦ by cases v <;> simp [hs, hp, hb]
    · exact cell .palace _ fun v ↦ by cases v <;> simp [hs, hp, hb]
    · exact cell .both _ fun v ↦ by cases v <;> simp [hs, hp, hb]

/-- Hamblin's rule, which ignores which places are best, yields only the trivial answer. -/
theorem bestPlace_hamblin : whAnswers (fun _ : NewsW ↦ (Set.univ : Set Walk)) = {Set.univ} := by
  rw [whAnswers_eq_image]
  simp

/-! #### Degree questions -/

/-- Ranking the numbers by size, the optimal answer to *How many meters can you jump?* is
[rullmann-1995]'s maximum, the height you can jump (`Examples.ex_18b`). -/
theorem optimalValues_le (jump : W → ℕ) (w : W) :
    optimalValues (fun w ↦ {n | n ≤ jump w}) (fun _ ↦ id) w = {jump w} := by
  ext n
  simp only [mem_optimalValues, Set.mem_ofPred_eq, Set.mem_singleton_iff, id]
  exact ⟨fun ⟨hn, h⟩ ↦ le_antisymm hn (h _ le_rfl), fun h ↦ ⟨h.le, fun m hm ↦ h ▸ hm⟩⟩

/-- Ranking the numbers in reverse, the optimal answer to *In how many seconds can you run the
100 meters?* is the minimum (`Examples.ex_19`). -/
theorem optimalValues_ge (time : W → ℕ) (w : W) :
    optimalValues (fun w ↦ {n | time w ≤ n}) (fun _ ↦ OrderDual.toDual) w = {time w} := by
  ext n
  simp only [mem_optimalValues, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    OrderDual.toDual_le_toDual]
  exact ⟨fun ⟨hn, h⟩ ↦ le_antisymm (h _ le_rfl) hn, fun h ↦ ⟨h.ge, fun m hm ↦ h ▸ hm⟩⟩

/-- When jumping high is better there is no best number of meters you cannot jump, so *How many
meters can't you jump?* is undefined (`Examples.ex_24`). -/
theorem optimalValues_gt_eq_empty (jump : W → ℕ) (w : W) :
    optimalValues (fun w ↦ {n | jump w < n}) (fun _ ↦ id) w = ∅ :=
  Set.eq_empty_of_forall_notMem fun n ⟨hn, h⟩ ↦ h (n + 1) (by grind) (Nat.lt_succ_self n)

/-- With the preferences reversed, the unique optimal answer to *How many meters can't you jump?*
is the first number of meters you cannot jump. -/
theorem optimalValues_gt_toDual (jump : W → ℕ) (w : W) :
    optimalValues (fun w ↦ {n | jump w < n}) (fun _ ↦ OrderDual.toDual) w = {jump w + 1} := by
  ext n
  simp only [mem_optimalValues, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    OrderDual.toDual_le_toDual]
  exact ⟨fun ⟨hn, h⟩ ↦ le_antisymm (h _ (Nat.lt_succ_self _)) hn,
    fun h ↦ ⟨h ▸ Nat.lt_succ_self _, fun m hm ↦ h ▸ hm⟩⟩

/-! #### Conceptual covers -/

/-- In the worlds of *Who killed spiderman?* John or Bill did it, wearing a blue or a green
mask (`Examples.ex_22`). -/
inductive SpiderW where
  | johnBlue
  | johnGreen
  | billBlue
  | billGreen
  deriving DecidableEq, Fintype

/-- The concepts that may identify the killer are two names and two masks. -/
inductive Concept where
  | john
  | bill
  | blue
  | green
  deriving DecidableEq, Fintype

/-- The concepts true of the killer in each world. -/
def killer : SpiderW → Set Concept
  | .johnBlue => {.john, .blue}
  | .johnGreen => {.john, .green}
  | .billBlue => {.bill, .blue}
  | .billGreen => {.bill, .green}

/-- A questioner who has to know the culprit's name decides whom to accuse. -/
noncomputable def byName : DecisionProblem ℝ SpiderW Concept where
  utility
    | .johnBlue, .john | .johnGreen, .john | .billBlue, .bill | .billGreen, .bill => 1
    | _, _ => 0
  prior _ := 1 / 4

/-- A questioner who has to know what the culprit looks like decides which mask to look for. -/
noncomputable def byMask : DecisionProblem ℝ SpiderW Concept where
  utility
    | .johnBlue, .blue | .johnGreen, .green | .billBlue, .blue | .billGreen, .green => 1
    | _, _ => 0
  prior _ := 1 / 4

private theorem prop_lt_iff {p q : Prop} : p < q ↔ ¬ p ∧ q := by
  simp only [lt_iff_le_not_ge, le_Prop_eq]
  tauto

private theorem forall_concept {p : Concept → Prop} :
    (∀ c, p c) ↔ p .john ∧ p .bill ∧ p .blue ∧ p .green :=
  ⟨fun h ↦ ⟨h _, h _, h _, h _⟩, fun ⟨h₁, h₂, h₃, h₄⟩ c ↦ by cases c <;> assumption⟩

/-- A concept is optimal when its proposition resolves the problem or no true concept's does. -/
private theorem mem_optimalValues_resolves {dp : DecisionProblem ℝ SpiderW Concept}
    {w : SpiderW} {c : Concept} :
    c ∈ optimalValues killer (fun _ c ↦ IsResolved dp Set.univ {v | c ∈ killer v}) w ↔
      c ∈ killer w ∧ ((∃ c' ∈ killer w, IsResolved dp Set.univ {v | c' ∈ killer v}) →
        IsResolved dp Set.univ {v | c ∈ killer v}) := by
  simp only [optimalValues, Set.mem_ofPred_eq, prop_lt_iff]
  exact and_congr_right fun _ ↦ ⟨fun h ⟨c', hc', hr⟩ ↦ by_contra fun hn ↦ h c' hc' ⟨hn, hr⟩,
    fun h c' hc' ⟨hn, hr⟩ ↦ hn (h ⟨c', hc', hr⟩)⟩

private theorem killer_johnBlue : killer .johnBlue = {.john, .blue} := rfl
private theorem killer_johnGreen : killer .johnGreen = {.john, .green} := rfl
private theorem killer_billBlue : killer .billBlue = {.bill, .blue} := rfl
private theorem killer_billGreen : killer .billGreen = {.bill, .green} := rfl

/-- The culprit's name in each world. -/
def nameOf : SpiderW → Concept
  | .johnBlue | .johnGreen => .john
  | .billBlue | .billGreen => .bill

/-- The culprit's mask in each world. -/
def maskOf : SpiderW → Concept
  | .johnBlue | .billBlue => .blue
  | .johnGreen | .billGreen => .green

private theorem whAnswers_pair {f : SpiderW → Concept} {c₁ c₂ : Concept} {S₁ S₂ : Set SpiderW}
    (hU : ⋃ w, ({f w} : Set Concept) = {c₁, c₂}) (h₁ : ∀ v, f v = c₁ ↔ v ∈ S₁)
    (h₂ : ∀ v, f v = c₂ ↔ v ∈ S₂) : whAnswers (fun w ↦ {f w}) = {S₁, S₂} := by
  rw [whAnswers_eq_image, hU, Set.image_pair]
  simp only [Set.mem_singleton_iff, eq_comm (a := c₁), eq_comm (a := c₂)]
  rw [show {v | f v = c₁} = S₁ from Set.ext h₁, show {v | f v = c₂} = S₂ from Set.ext h₂]

/-- For a questioner who has to know the culprit's name, *Who killed spiderman?* denotes the
partition by name, as if quantifying over the cover {John, Bill}. -/
theorem killer_byName :
    questionR killer (fun _ c ↦ IsResolved byName Set.univ {v | c ∈ killer v}) =
      {{.johnBlue, .johnGreen}, {.billBlue, .billGreen}} := by
  have hjohn : IsResolved byName Set.univ {v | .john ∈ killer v} :=
    ⟨.john, trivial, fun b _ v hv ↦ by cases v <;> cases b <;> simp_all [killer, byName]⟩
  have hbill : IsResolved byName Set.univ {v | .bill ∈ killer v} :=
    ⟨.bill, trivial, fun b _ v hv ↦ by cases v <;> cases b <;> simp_all [killer, byName]⟩
  have hblue : ¬ IsResolved byName Set.univ {v | .blue ∈ killer v} := fun ⟨a, _, h⟩ ↦ by
    have h₁ := h .john trivial .johnBlue (by simp [killer])
    have h₂ := h .bill trivial .billBlue (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byName]
  have hgreen : ¬ IsResolved byName Set.univ {v | .green ∈ killer v} := fun ⟨a, _, h⟩ ↦ by
    have h₁ := h .john trivial .johnGreen (by simp [killer])
    have h₂ := h .bill trivial .billGreen (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byName]
  have hop : optimalValues killer (fun _ c ↦ IsResolved byName Set.univ {v | c ∈ killer v}) =
      fun w ↦ {nameOf w} := funext fun w ↦ Set.ext fun c ↦ by
    rw [mem_optimalValues_resolves]
    cases w <;> cases c <;> simp [killer_johnBlue, killer_johnGreen, killer_billBlue,
      killer_billGreen, nameOf, hjohn, hbill, hblue, hgreen]
  rw [questionR, hop]
  refine whAnswers_pair (c₁ := .john) (c₂ := .bill) ?_ (fun v ↦ ?_) (fun v ↦ ?_)
  · ext c
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_insert_iff]
    refine ⟨by rintro ⟨w, rfl⟩; cases w <;> simp [nameOf], ?_⟩
    exact (by
      rintro (rfl | rfl)
      exacts [⟨.johnBlue, rfl⟩, ⟨.billBlue, rfl⟩])
  all_goals cases v <;> simp [nameOf]

/-- For a questioner who has to know what the culprit looks like, *Who killed spiderman?*
denotes the partition by mask, as if quantifying over the cover {blue, green}. -/
theorem killer_byMask :
    questionR killer (fun _ c ↦ IsResolved byMask Set.univ {v | c ∈ killer v}) =
      {{.johnBlue, .billBlue}, {.johnGreen, .billGreen}} := by
  have hblue : IsResolved byMask Set.univ {v | .blue ∈ killer v} :=
    ⟨.blue, trivial, fun b _ v hv ↦ by cases v <;> cases b <;> simp_all [killer, byMask]⟩
  have hgreen : IsResolved byMask Set.univ {v | .green ∈ killer v} :=
    ⟨.green, trivial, fun b _ v hv ↦ by cases v <;> cases b <;> simp_all [killer, byMask]⟩
  have hjohn : ¬ IsResolved byMask Set.univ {v | .john ∈ killer v} := fun ⟨a, _, h⟩ ↦ by
    have h₁ := h .blue trivial .johnBlue (by simp [killer])
    have h₂ := h .green trivial .johnGreen (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byMask]
  have hbill : ¬ IsResolved byMask Set.univ {v | .bill ∈ killer v} := fun ⟨a, _, h⟩ ↦ by
    have h₁ := h .blue trivial .billBlue (by simp [killer])
    have h₂ := h .green trivial .billGreen (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byMask]
  have hop : optimalValues killer (fun _ c ↦ IsResolved byMask Set.univ {v | c ∈ killer v}) =
      fun w ↦ {maskOf w} := funext fun w ↦ Set.ext fun c ↦ by
    rw [mem_optimalValues_resolves]
    cases w <;> cases c <;> simp [killer_johnBlue, killer_johnGreen, killer_billBlue,
      killer_billGreen, maskOf, hjohn, hbill, hblue, hgreen]
  rw [questionR, hop]
  refine whAnswers_pair (c₁ := .blue) (c₂ := .green) ?_ (fun v ↦ ?_) (fun v ↦ ?_)
  · ext c
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_insert_iff]
    refine ⟨by rintro ⟨w, rfl⟩; cases w <;> simp [maskOf], ?_⟩
    exact (by
      rintro (rfl | rfl)
      exacts [⟨.johnBlue, rfl⟩, ⟨.johnGreen, rfl⟩])
  all_goals cases v <;> simp [maskOf]

/-- When any one concept resolves the problem every true concept is optimal, and *Who killed
spiderman?* denotes four overlapping answers, one per concept. -/
theorem killer_anyConcept :
    questionR killer (fun _ _ ↦ True) = {{.johnBlue, .johnGreen}, {.billBlue, .billGreen},
      {.johnBlue, .billBlue}, {.johnGreen, .billGreen}} := by
  have hU : ⋃ w, killer w = {.john, .bill, .blue, .green} := by
    ext c
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun _ ↦ by cases c <;> simp, fun _ ↦ ?_⟩
    cases c
    exacts [⟨.johnBlue, by simp [killer]⟩, ⟨.billBlue, by simp [killer]⟩,
      ⟨.johnBlue, by simp [killer]⟩, ⟨.johnGreen, by simp [killer]⟩]
  have h (c : Concept) (S : Set SpiderW) (hS : ∀ w, c ∈ killer w ↔ w ∈ S) :
      {w | c ∈ killer w} = S := Set.ext hS
  rw [questionR_const, whAnswers_eq_image, hU, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton, h .john {.johnBlue, .johnGreen},
    h .bill {.billBlue, .billGreen}, h .blue {.johnBlue, .billBlue},
    h .green {.johnGreen, .billGreen}] <;> intro w <;> cases w <;> simp [killer]

/-! #### Scalar questions -/

/-- The Beatles whose autographs one might have (`Examples.ex_26`). -/
inductive Beatle where
  | lennon
  | mccartney
  | harrison
  | starr
  deriving DecidableEq, Fintype

/-- The autographic hierarchy ranks Lennon over Harrison over Starr. -/
def autographRank : Beatle → ℕ
  | .lennon => 3
  | .harrison => 2
  | .starr => 1
  | .mccartney => 0

/-- The autographs that count, McCartney's ignored. -/
def counted (w : Finset Beatle) : Set Beatle := ↑(w.erase .mccartney)

/-- Ranked by the hierarchy, *Which Beatles' autograph do you have?* has just three resolving
answers, at least a Lennon autograph, Harrison but not Lennon, and only Starr. -/
theorem beatles_questionR :
    questionR counted (fun _ ↦ autographRank) =
      {{w | .lennon ∈ w}, {w | .harrison ∈ w ∧ .lennon ∉ w},
        {w | .starr ∈ w ∧ .harrison ∉ w ∧ .lennon ∉ w}} := by
  have hop (b : Beatle) (w : Finset Beatle) :
      b ∈ optimalValues counted (fun _ ↦ autographRank) w ↔
        b ∈ w.erase .mccartney ∧ ∀ b' ∈ w.erase .mccartney, autographRank b' ≤ autographRank b := by
    rw [mem_optimalValues]; simp only [counted, Finset.mem_coe]
  have hU : ⋃ w, optimalValues counted (fun _ ↦ autographRank) w =
      {.lennon, .harrison, .starr} := by
    ext b
    simp only [Set.mem_iUnion, hop, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert b
    decide
  have h (b : Beatle) (S : Set (Finset Beatle))
      (hS : ∀ w, (b ∈ w.erase .mccartney ∧
        ∀ b' ∈ w.erase .mccartney, autographRank b' ≤ autographRank b) ↔ w ∈ S) :
      {w | b ∈ optimalValues counted (fun _ ↦ autographRank) w} = S :=
    Set.ext fun w ↦ (hop b w).trans (hS w)
  rw [questionR, whAnswers_eq_image, hU, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, h .lennon {w | .lennon ∈ w}, h .harrison {w | .harrison ∈ w ∧ .lennon ∉ w},
    h .starr {w | .starr ∈ w ∧ .harrison ∉ w ∧ .lennon ∉ w}] <;>
    simp only [Set.mem_ofPred_eq] <;> decide

end VanRooy2003
