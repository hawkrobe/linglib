module

public import Linglib.Core.Order.Partition.Finpartition
public import Linglib.Semantics.Questions.Value
public import Linglib.Data.Examples.VanRooy2003
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Setoid.Partition

/-!
# van Rooy (2003): Questioning to Resolve Decision Problems

Van Rooy grounds the meaning of questions in the questioner's decision problem, a prior over
worlds and a utility for each action in each world. Information resolves the problem when some
action is optimal in every world it leaves open. A question, a partition of the worlds, is worth
the average gain in decision value from learning its answer; that theory of question value,
consumed beyond this paper, is `Semantics/Questions/Value.lean`. A wh-question denotes the
propositions that some value is among the optimal true values of its predicate, those with no
more relevant true value, and this one rule yields both mention-all and mention-some readings.

## Main statements

* `isResolved_iff_exists_subset_optimalityRegion`: information resolves the problem exactly
  when it lies within the worlds where one action is optimal.
* `newspaper_station_resolves`, `newspaper_betterAnswer`: in the Italian newspaper example the
  partial answer *at least at the station* resolves the problem and is a better answer than the
  complete one.
* `questionR_entailment`, `bestPlace_questionR`: when relevance is informativity the rule gives the
  mention-all partition, and the newspaper question has a mention-some meaning that Hamblin's rule
  misses.
* `killer_byName`, `killer_byMask`, `beatles_questionR`: which concepts resolve the questioner's
  problem decides the partition of *Who killed spiderman?*, and an autograph hierarchy gives
  *Which Beatles' autograph do you have?* three answers.

## Implementation notes

A decision problem is a real utility on worlds and actions together with a prior measure, the
actions forming a type, and questions over a finite set of worlds are `Finpartition`s.
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

open MeasureTheory ProbabilityTheory

universe u

variable {W : Type u} {A G R : Type*}

/-! ### Resolving a decision problem -/

/-- Information `C` resolves the decision problem with utility `U` when some action is at least
as good as every other in every world of `C`. -/
def IsResolved (U : W → A → ℝ) (C : Set W) : Prop := ∃ a, ∀ b, ∀ w ∈ C, U w b ≤ U w a

/-- The proposition an action induces is the set of worlds where no action is strictly
better. -/
def optimalityRegion (U : W → A → ℝ) (a : A) : Set W := {w | ∀ b, U w b ≤ U w a}

/-- Information resolves the decision problem exactly when it lies within the optimality
region of some action. -/
theorem isResolved_iff_exists_subset_optimalityRegion (U : W → A → ℝ) (C : Set W) :
    IsResolved U C ↔ ∃ a, C ⊆ optimalityRegion U a :=
  ⟨fun ⟨a, h⟩ ↦ ⟨a, fun _ hw b ↦ h b _ hw⟩, fun ⟨a, h⟩ ↦ ⟨a, fun _ _ hw ↦ h hw _⟩⟩

/-- Over finitely many actions every world has an optimal one, so the regions cover the
worlds. -/
theorem iUnion_optimalityRegion [Finite A] [Nonempty A] (U : W → A → ℝ) :
    ⋃ a, optimalityRegion U a = Set.univ :=
  Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion.2 (Finite.exists_max (U w))

/-- When every world has a strictly best action the regions are pairwise disjoint, and the
actions induce a partition. -/
theorem pairwise_disjoint_optimalityRegion (U : W → A → ℝ)
    (hstrict : ∀ w, ∃ a, ∀ b, b ≠ a → U w b < U w a) :
    Pairwise (Function.onFun Disjoint (optimalityRegion U)) := by
  intro a a' hne
  refine Set.disjoint_left.2 fun w hw hw' ↦ ?_
  obtain ⟨c, hbest⟩ := hstrict w
  by_cases hac : a = c
  · subst hac
    exact (hw' a).not_gt (hbest a' (Ne.symm hne))
  · exact (hw c).not_gt (hbest a hac)

section Value

variable [MeasurableSpace W]

/-! ### The Italian newspaper -/

/-- The worlds of the newspaper examples are named by where to go, only the station, only the
palace, or either (the paper's `u`, `v` and `w`). -/
inductive NewsW where
  | station
  | palace
  | both
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace NewsW := ⊤

instance : DiscreteMeasurableSpace NewsW := ⟨fun _ ↦ trivial⟩

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
def newspaper : NewsW → Walk → ℝ
  | .station, .station | .both, .station | .palace, .palace | .both, .palace => 1
  | .palace, .station | .station, .palace => 0

/-- The worlds of the newspaper example are equiprobable. -/
noncomputable abbrev newsPrior : Measure NewsW := uniformOn Set.univ

/-- The actions induce overlapping propositions, not a partition. -/
theorem newspaper_optimalityRegions :
    optimalityRegion newspaper .station = {.station, .both} ∧
      optimalityRegion newspaper .palace = {.palace, .both} := by
  constructor <;> ext w <;> cases w <;> norm_num [optimalityRegion, forall_walk, newspaper]

/-- The mention-some answer *at least at the station* resolves the problem although it is only
a partial answer to the partition question. -/
theorem newspaper_station_resolves : IsResolved newspaper ({.station, .both} : Set NewsW) :=
  (isResolved_iff_exists_subset_optimalityRegion _ _).2
    ⟨.station, newspaper_optimalityRegions.1.ge⟩

private theorem newspaper_value : decisionValue newspaper newsPrior = 2 / 3 := by
  have h (a : Walk) : ∫ w, newspaper w a ∂newsPrior = 2 / 3 := by
    rw [integral_fintype .of_finite, sum_newsW]
    cases a <;>
      simp [uniformOn_univ_real_singleton, newspaper, show Fintype.card NewsW = 3 from rfl] <;>
      norm_num
  simp only [decisionValue, h, ciSup_const]

/-- Any answer that leaves the palace out resolves the problem and is worth `1 / 3`. -/
private theorem newspaper_utilityValue {C : Set NewsW} (hC : C.Nonempty) (hs : .palace ∉ C) :
    Question.utilityValue newspaper newsPrior C = 1 / 3 := by
  obtain ⟨w₀, hw₀⟩ := hC
  have hpos : newsPrior C ≠ 0 := fun h ↦ uniformOn_univ_singleton_ne_zero w₀
    (measure_mono_null (Set.singleton_subset_iff.2 hw₀) h)
  have := cond_isProbabilityMeasure (μ := newsPrior) hpos
  have hstation : ∫ w, newspaper w .station ∂newsPrior[|C] = 1 := by
    rw [integral_congr_ae (g := fun _ ↦ (1 : ℝ)) (ae_iff_of_countable.2 fun w hw ↦ ?_)]
    · simp
    · cases w <;> simp_all [newspaper, cond_apply' (measurableSet_singleton _),
        Set.inter_singleton_eq_empty.2 hs]
  have hval : decisionValue newspaper newsPrior[|C] = 1 :=
    le_antisymm (ciSup_le fun a ↦ (integral_mono .of_finite (integrable_const 1) fun w ↦ by
      cases w <;> cases a <;> simp [newspaper]).trans (by simp))
      (hstation ▸ integral_le_decisionValue _ Walk.station)
  rw [Question.utilityValue, hval, newspaper_value]
  norm_num

/-- Taking effort into account, the mention-some answer *at least at the station* is a better
answer than the complete answer *only at the station*, since both resolve the problem and the
first says less. -/
theorem newspaper_betterAnswer :
    Question.BetterAnswer newspaper newsPrior {.station, .both} {.station} := by
  refine Question.betterAnswer_iff.2 (.inr ⟨?_, ?_⟩)
  · rw [newspaper_utilityValue (by simp) (by simp), newspaper_utilityValue (by simp) (by simp)]
  · refine Set.ssubset_iff_subset_ne.2 ⟨by simp, fun h ↦ ?_⟩
    have hb : NewsW.both ∈ ({NewsW.station} : Set NewsW) := by rw [h]; simp
    simp at hb

end Value

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
theorem questionR_actions (U : W → A → ℝ) :
    questionR (fun _ ↦ Set.univ) U = {r ∈ Set.range (optimalityRegion U) | r.Nonempty} := by
  ext p
  simp only [questionR, whAnswers, Set.mem_ofPred_eq, Set.mem_range, mem_optimalValues,
    Set.mem_univ, true_and, forall_const]
  constructor
  · rintro ⟨w, a, hw, rfl⟩
    exact ⟨⟨a, rfl⟩, w, hw⟩
  · rintro ⟨⟨a, rfl⟩, w, hw⟩
    exact ⟨w, a, hw, rfl⟩

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
def bestPlace : NewsW → Walk → ℝ
  | .station, .station | .palace, .palace => 2
  | .station, .palace | .palace, .station | .both, _ => 1

/-- The optimal places are the best place of each world. -/
theorem bestPlace_optimalValues :
    optimalValues (fun _ ↦ Set.univ) bestPlace .station = {.station} ∧
      optimalValues (fun _ ↦ Set.univ) bestPlace .palace = {.palace} ∧
      optimalValues (fun _ ↦ Set.univ) bestPlace .both = Set.univ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext a <;> cases a <;>
    norm_num [mem_optimalValues, forall_walk, bestPlace]

/-- The rule yields the overlapping mention-some answers. -/
theorem bestPlace_questionR :
    questionR (fun _ ↦ Set.univ) bestPlace = {{.station, .both}, {.palace, .both}} := by
  have h (a : Walk) : optimalityRegion bestPlace a =
      if a = .station then {.station, .both} else {.palace, .both} := by
    ext w; cases a <;> cases w <;> norm_num [optimalityRegion, forall_walk, bestPlace]
  rw [questionR_actions]
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
    overlapCells (optimalValues (fun _ ↦ Set.univ) bestPlace) =
      {{.station, .both}, {.palace, .both}, Set.univ} := by
  obtain ⟨hs, hp, hb⟩ := bestPlace_optimalValues
  have cell (w : NewsW) (S : Set NewsW)
      (h : ∀ v, (optimalValues (fun _ ↦ Set.univ) bestPlace w ∩
        optimalValues (fun _ ↦ Set.univ) bestPlace v).Nonempty ↔ v ∈ S) :
      S ∈ overlapCells (optimalValues (fun _ ↦ Set.univ) bestPlace) :=
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
def byName : SpiderW → Concept → ℝ
  | .johnBlue, .john | .johnGreen, .john | .billBlue, .bill | .billGreen, .bill => 1
  | _, _ => 0

/-- A questioner who has to know what the culprit looks like decides which mask to look for. -/
def byMask : SpiderW → Concept → ℝ
  | .johnBlue, .blue | .johnGreen, .green | .billBlue, .blue | .billGreen, .green => 1
  | _, _ => 0

private theorem prop_lt_iff {p q : Prop} : p < q ↔ ¬ p ∧ q := by
  simp only [lt_iff_le_not_ge, le_Prop_eq]
  tauto

private theorem forall_concept {p : Concept → Prop} :
    (∀ c, p c) ↔ p .john ∧ p .bill ∧ p .blue ∧ p .green :=
  ⟨fun h ↦ ⟨h _, h _, h _, h _⟩, fun ⟨h₁, h₂, h₃, h₄⟩ c ↦ by cases c <;> assumption⟩

/-- A concept is optimal when its proposition resolves the problem or no true concept's does. -/
private theorem mem_optimalValues_resolves {U : SpiderW → Concept → ℝ}
    {w : SpiderW} {c : Concept} :
    c ∈ optimalValues killer (fun _ c ↦ IsResolved U {v | c ∈ killer v}) w ↔
      c ∈ killer w ∧ ((∃ c' ∈ killer w, IsResolved U {v | c' ∈ killer v}) →
        IsResolved U {v | c ∈ killer v}) := by
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
    questionR killer (fun _ c ↦ IsResolved byName {v | c ∈ killer v}) =
      {{.johnBlue, .johnGreen}, {.billBlue, .billGreen}} := by
  have hjohn : IsResolved byName {v | .john ∈ killer v} :=
    ⟨.john, fun b v hv ↦ by cases v <;> cases b <;> simp_all [killer, byName]⟩
  have hbill : IsResolved byName {v | .bill ∈ killer v} :=
    ⟨.bill, fun b v hv ↦ by cases v <;> cases b <;> simp_all [killer, byName]⟩
  have hblue : ¬ IsResolved byName {v | .blue ∈ killer v} := fun ⟨a, h⟩ ↦ by
    have h₁ := h .john .johnBlue (by simp [killer])
    have h₂ := h .bill .billBlue (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byName]
  have hgreen : ¬ IsResolved byName {v | .green ∈ killer v} := fun ⟨a, h⟩ ↦ by
    have h₁ := h .john .johnGreen (by simp [killer])
    have h₂ := h .bill .billGreen (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byName]
  have hop : optimalValues killer (fun _ c ↦ IsResolved byName {v | c ∈ killer v}) =
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
    questionR killer (fun _ c ↦ IsResolved byMask {v | c ∈ killer v}) =
      {{.johnBlue, .billBlue}, {.johnGreen, .billGreen}} := by
  have hblue : IsResolved byMask {v | .blue ∈ killer v} :=
    ⟨.blue, fun b v hv ↦ by cases v <;> cases b <;> simp_all [killer, byMask]⟩
  have hgreen : IsResolved byMask {v | .green ∈ killer v} :=
    ⟨.green, fun b v hv ↦ by cases v <;> cases b <;> simp_all [killer, byMask]⟩
  have hjohn : ¬ IsResolved byMask {v | .john ∈ killer v} := fun ⟨a, h⟩ ↦ by
    have h₁ := h .blue .johnBlue (by simp [killer])
    have h₂ := h .green .johnGreen (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byMask]
  have hbill : ¬ IsResolved byMask {v | .bill ∈ killer v} := fun ⟨a, h⟩ ↦ by
    have h₁ := h .blue .billBlue (by simp [killer])
    have h₂ := h .green .billGreen (by simp [killer])
    revert h₁ h₂
    cases a <;> norm_num [byMask]
  have hop : optimalValues killer (fun _ c ↦ IsResolved byMask {v | c ∈ killer v}) =
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
