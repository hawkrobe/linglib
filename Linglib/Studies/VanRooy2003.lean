import Linglib.Core.Probability.Decision.Basic
import Linglib.Data.Examples.VanRooy2003
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.Linarith

/-!
# van Rooy (2003): Questioning to Resolve Decision Problems

This file formalizes [van-rooy-2003], which grounds the semantics and pragmatics of questions
in the questioner's decision problem, a probability function, a utility function and a set of
actions, the substrate's `Core.DecisionTheory.DecisionProblem`. Information `C` resolves the
problem when after learning it some action weakly dominates the others,
`DecisionProblem.IsResolved`; the actions themselves induce propositions, the worlds where an
action is optimal, `optimalityRegion`, which cover the worlds, `iUnion_optimalityRegion`, and
partition them when every world has a strictly best action, `pairwise_disjoint_optimalityRegion`;
`C` resolves the problem exactly when it lies in one of them,
`isResolved_iff_exists_subset_optimalityRegion`. The Italian newspaper, (12), where two actions
are optimal in one world, is the case of overlapping regions, `newspaper_optimalityRegions`, in
which a partial mention-some answer resolves the problem, `newspaper_station_resolves`. The
expected utility value of a question, `EUV`, is the average utility value of its answers, the
substrate's `DecisionProblem.questionUtility` over the parts of a `Finpartition`; it never
exceeds the value of the finest question, what the world is like, `questionUtility_le_bot`, and
a question is at least as good as another for every decision problem exactly when it refines it,
the paper's special case of [blackwell-1953], `le_iff_forall_questionUtility_le`. Relative to a
fixed decision problem questions are ordered by utility and then by coarseness, `Better`, which
selects the domain of a wh-phrase, `whQuestion`: enlarging the domain refines the question,
`whQuestion_anti`, so of two domains giving the same utility the smaller yields the better
question, `better_whQuestion_of_subset`. Finally the mention-some and mention-all readings are
derived from one rule: a question denotes the propositions that some group is among the optimal
values of the predicate in a world, `questionR`, which is a partition when the optimal value is
unique, `questionR_eq_range_fiber`, and gives the mention-some denotation of (20),
`newspaper_questionR`, where the rule of footnote 28 over-generates, `newspaper_questionS`.

## Implementation notes

Questions are `Finpartition`s of the finite set of worlds, whose refinement order is the paper's
entailment ⊑, and the Blackwell fact is stated over them, its converse by the paper's argument
that two incomparable partitions are told apart by a two-world identification problem. The
scalar questions of section 5.4 and the argumentative value of [merin-1999-relevance] are not
formalized. The examples are the rows of `Data.Examples.VanRooy2003`.

## References

* [van-rooy-2003]
* [groenendijk-stokhof-1984]
* [blackwell-1953]
* [raiffa-schlaifer-1961]
* [karttunen-1977]
* [hamblin-1973b]
* [merin-1999-relevance]
-/

namespace VanRooy2003

open Core.DecisionTheory Core.DecisionTheory.DecisionProblem

variable {W A : Type*}

/-! ### Resolving a decision problem -/

/-- The proposition an action induces: the worlds where no other action is strictly better. -/
def optimalityRegion (dp : DecisionProblem ℚ W A) (acts : Set A) (a : A) : Set W :=
  {w | ∀ b ∈ acts, dp.utility w b ≤ dp.utility w a}

/-- The propositions the actions induce. -/
def optimalityRegions (dp : DecisionProblem ℚ W A) (acts : Set A) : Set (Set W) :=
  optimalityRegion dp acts '' acts

/-- Information resolves the decision problem exactly when it lies within the optimality
region of some action. -/
theorem isResolved_iff_exists_subset_optimalityRegion (dp : DecisionProblem ℚ W A)
    (acts : Set A) (C : Set W) :
    IsResolved dp acts C ↔ ∃ a ∈ acts, C ⊆ optimalityRegion dp acts a := by
  simp only [IsResolved, optimalityRegion, Set.subset_def, Set.mem_ofPred_eq]
  exact ⟨λ ⟨a, ha, h⟩ => ⟨a, ha, λ w hw b hb => h b hb w hw⟩,
    λ ⟨a, ha, h⟩ => ⟨a, ha, λ b hb w hw => h w hw b hb⟩⟩

/-- Over finitely many actions every world has an optimal one: the regions cover the worlds. -/
theorem iUnion_optimalityRegion (dp : DecisionProblem ℚ W A) (acts : Finset A)
    (hne : acts.Nonempty) : ⋃ a ∈ acts, optimalityRegion dp (acts : Set A) a = Set.univ := by
  refine Set.eq_univ_of_forall λ w => ?_
  obtain ⟨a, ha, hmax⟩ := acts.exists_max_image (dp.utility w) hne
  exact Set.mem_iUnion₂.2 ⟨a, ha, λ b hb => hmax b hb⟩

/-- When every world has a strictly best action the regions are pairwise disjoint, and the
actions induce a partition. -/
theorem pairwise_disjoint_optimalityRegion (dp : DecisionProblem ℚ W A) (acts : Set A)
    (hstrict : ∀ w, ∃ a ∈ acts, ∀ b ∈ acts, b ≠ a → dp.utility w b < dp.utility w a) :
    (acts).PairwiseDisjoint (optimalityRegion dp acts) := by
  intro a ha a' ha' hne
  refine Set.disjoint_left.2 λ w hw hw' => ?_
  obtain ⟨c, hc, hbest⟩ := hstrict w
  by_cases hac : a = c
  · subst hac
    exact absurd (hw' a ha) (not_le.2 (hbest a' ha' (Ne.symm hne)))
  · exact absurd (hw c hc) (not_le.2 (hbest a ha hac))

/-! ### The Italian newspaper, (12) -/

/-- The worlds of (12): the newspaper is sold only at the station, only at the palace, or at
both. -/
inductive NewsW where
  | station
  | palace
  | both
  deriving DecidableEq, Repr, Fintype

/-- The actions: walk to the station or to the palace. -/
inductive Walk where
  | station
  | palace
  deriving DecidableEq, Repr, Fintype

/-- The newspaper problem: walking to a place is worth 1 where the newspaper is sold there. -/
def newspaper : DecisionProblem ℚ NewsW Walk where
  utility
    | .station, .station | .both, .station | .palace, .palace | .both, .palace => 1
    | .palace, .station | .station, .palace => 0
  prior _ := 1/3

/-- The actions induce the overlapping propositions {u, w} and {v, w}, not a partition. -/
theorem newspaper_optimalityRegions :
    optimalityRegion newspaper Set.univ .station = {.station, .both} ∧
      optimalityRegion newspaper Set.univ .palace = {.palace, .both} := by
  refine ⟨Set.ext λ w => ?_, Set.ext λ w => ?_⟩ <;> cases w <;>
    simp only [optimalityRegion, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_univ, true_implies] <;> decide

/-- The mention-some answer *at least at the station*, {u, w}, resolves the problem although
it is only a partial answer to the partition question. -/
theorem newspaper_station_resolves :
    IsResolved newspaper Set.univ ({.station, .both} : Set NewsW) :=
  ⟨.station, Set.mem_univ _, λ b _ w hw => by
    rcases hw with rfl | rfl <;> cases b <;> decide⟩

/-! ### The utility of questions -/

section Utility

variable [Fintype W] [DecidableEq W]

/-- The expected utility value of a question, the average utility value of its answers. -/
abbrev EUV (dp : DecisionProblem ℚ W A) (acts : Finset A)
    (Q : Finpartition (Finset.univ : Finset W)) : ℚ :=
  questionUtility dp acts Q.parts

/-- No question is worth more than the finest one, what the world is like, whose value is the
expected value of perfect information of [raiffa-schlaifer-1961]. -/
theorem questionUtility_le_bot (dp : DecisionProblem ℚ W A) (acts : Finset A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (Q : Finpartition (Finset.univ : Finset W)) :
    EUV dp acts Q ≤ EUV dp acts ⊥ :=
  questionUtility_anti_of_le dp acts bot_le hprior

/-- The special case of [blackwell-1953]'s theorem: a question refines another exactly when it
is at least as useful for every decision problem with a non-negative prior. The converse holds
because a part of the finer question meeting two parts of the coarser one is told apart by the
problem of identifying which of two of its worlds obtains. -/
theorem le_iff_forall_questionUtility_le [DecidableEq A] [Nontrivial A] [Nonempty W]
    (P Q : Finpartition (Finset.univ : Finset W)) :
    P ≤ Q ↔ ∀ (dp : DecisionProblem ℚ W A) (acts : Finset A), (∀ w, 0 ≤ dp.prior w) →
      EUV dp acts Q ≤ EUV dp acts P := by
  refine ⟨λ h dp acts hprior => questionUtility_anti_of_le dp acts h hprior, λ hdom => ?_⟩
  by_contra hnref
  simp only [LE.le, not_forall, not_exists, not_and] at hnref
  obtain ⟨f₀, hf₀, hf₀_uncov⟩ := hnref
  obtain ⟨w_wit⟩ := ‹Nonempty W›
  obtain ⟨c₀, hc₀, _⟩ := Q.exists_mem (Finset.mem_univ w_wit)
  obtain ⟨v, hv_f₀, hv_nc₀⟩ := hf₀_uncov c₀ hc₀
  obtain ⟨c_v, hc_v, hv_c_v⟩ := Q.exists_mem (Finset.mem_univ v)
  obtain ⟨w, hw_f₀, hw_nc_v⟩ := hf₀_uncov c_v hc_v
  obtain ⟨c_w, hc_w, hw_c_w⟩ := Q.exists_mem (Finset.mem_univ w)
  have hc_w_ne_c_v : c_w ≠ c_v := λ heq => hw_nc_v (heq ▸ hw_c_w)
  have hwv_ne : w ≠ v := λ heq =>
    Finset.disjoint_left.1 (Q.disjoint hc_w hc_v hc_w_ne_c_v) hw_c_w (heq ▸ hv_c_v)
  obtain ⟨a₁, a₂, ha_ne⟩ := exists_pair_ne A
  let dp : DecisionProblem ℚ W A :=
    { prior := λ w' => if w' = w then 1 else if w' = v then 1 else 0
      utility := λ w' a => if w' = w ∧ a = a₁ then 1 else if w' = v ∧ a = a₂ then 1 else 0 }
  have hprior_nn : ∀ w' : W, 0 ≤ dp.prior w' := λ w' => by
    show 0 ≤ if w' = w then (1 : ℚ) else if w' = v then 1 else 0
    split_ifs <;> norm_num
  have hyp := hdom dp {a₁, a₂} hprior_nn
  have hsum_a₁ : ∀ S : Finset W,
      ∑ w' ∈ S, dp.prior w' * dp.utility w' a₁ = if w ∈ S then (1 : ℚ) else 0 := by
    intro S
    have hpt : ∀ w' : W, dp.prior w' * dp.utility w' a₁ = if w' = w then (1 : ℚ) else 0 := by
      intro w'
      show (if w' = w then (1 : ℚ) else if w' = v then 1 else 0) *
        (if w' = w ∧ a₁ = a₁ then 1 else if w' = v ∧ a₁ = a₂ then 1 else 0) =
        if w' = w then 1 else 0
      by_cases hw : w' = w
      · subst hw; simp
      · by_cases hv : w' = v
        · subst hv; simp [hw, ha_ne]
        · simp [hw, hv]
    rw [Finset.sum_congr rfl λ w' _ => hpt w', Finset.sum_ite_eq' S w λ _ => (1 : ℚ)]
  have hsum_a₂ : ∀ S : Finset W,
      ∑ w' ∈ S, dp.prior w' * dp.utility w' a₂ = if v ∈ S then (1 : ℚ) else 0 := by
    intro S
    have hpt : ∀ w' : W, dp.prior w' * dp.utility w' a₂ = if w' = v then (1 : ℚ) else 0 := by
      intro w'
      show (if w' = w then (1 : ℚ) else if w' = v then 1 else 0) *
        (if w' = w ∧ a₂ = a₁ then 1 else if w' = v ∧ a₂ = a₂ then 1 else 0) =
        if w' = v then 1 else 0
      by_cases hw : w' = w
      · subst hw; simp [hwv_ne, ha_ne.symm]
      · by_cases hv : w' = v
        · subst hv; simp [hwv_ne.symm]
        · simp [hw, hv]
    rw [Finset.sum_congr rfl λ w' _ => hpt w', Finset.sum_ite_eq' S v λ _ => (1 : ℚ)]
  have hcpcv : ∀ (S : Finset W) (acts : Finset A) (hne : acts.Nonempty),
      dp.cellProbability S * dp.condValue acts S =
        acts.sup' hne λ a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a := by
    intro S acts hne
    rw [condValue_of_nonempty hne]
    have hpsum_nn : 0 ≤ dp.cellProbability S := Finset.sum_nonneg λ w' _ => hprior_nn w'
    by_cases hcp : dp.cellProbability S = 0
    · rw [hcp, zero_mul]
      have hprior_zero : ∀ w' ∈ S, dp.prior w' = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg λ w' _ => hprior_nn w').1 hcp
      exact (Finset.sup'_eq_of_forall (s := acts) (H := hne) (a := (0 : ℚ))
        (f := λ a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a)
        λ a _ => Finset.sum_eq_zero λ w' hw' => by rw [hprior_zero w' hw', zero_mul]).symm
    · have hS : S.sum dp.prior ≠ 0 := hcp
      rw [Finset.mul₀_sup' hpsum_nn _ acts hne]
      refine Finset.sup'_congr hne rfl λ a _ => ?_
      show S.sum dp.prior * dp.condExpectedUtility S a = ∑ w' ∈ S, dp.prior w' * dp.utility w' a
      rw [condExpectedUtility_of_ne_zero hS, Finset.mul_sum]
      refine Finset.sum_congr rfl λ w' _ => ?_
      rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hS]
  have hcpcv_max : ∀ S : Finset W,
      dp.cellProbability S * dp.condValue {a₁, a₂} S =
        max (if w ∈ S then (1 : ℚ) else 0) (if v ∈ S then 1 else 0) := by
    intro S
    rw [hcpcv S {a₁, a₂} (Finset.insert_nonempty _ _)]
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ λ a ha => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · rw [hsum_a₁]; exact le_max_left _ _
      · rw [hsum_a₂]; exact le_max_right _ _
    · refine max_le ?_ ?_
      · rw [← hsum_a₁ S]
        exact Finset.le_sup' (s := ({a₁, a₂} : Finset A))
          (f := λ a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a) (by simp)
      · rw [← hsum_a₂ S]
        exact Finset.le_sup' (s := ({a₁, a₂} : Finset A))
          (f := λ a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a) (by simp)
  have hpart_w : ∀ {R : Finpartition (Finset.univ : Finset W)} {c : Finset W} (hc : c ∈ R.parts)
      (hwc : w ∈ c), R.parts.filter (w ∈ ·) = {c} := by
    intro R c hc hwc
    ext c'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨λ ⟨hc', hw'⟩ => ?_, λ heq => heq ▸ ⟨hc, hwc⟩⟩
    by_contra hne
    exact Finset.disjoint_left.1 (R.disjoint hc' hc hne) hw' hwc
  have hpart_v : ∀ {R : Finpartition (Finset.univ : Finset W)} {c : Finset W} (hc : c ∈ R.parts)
      (hvc : v ∈ c), R.parts.filter (v ∈ ·) = {c} := by
    intro R c hc hvc
    ext c'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨λ ⟨hc', hv'⟩ => ?_, λ heq => heq ▸ ⟨hc, hvc⟩⟩
    by_contra hne
    exact Finset.disjoint_left.1 (R.disjoint hc' hc hne) hv' hvc
  have hcoarse_filter : Q.parts.filter (λ c => w ∈ c ∨ v ∈ c) = {c_w, c_v} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨λ ⟨hc, hor⟩ => ?_, ?_⟩
    · rcases hor with hw | hv
      · exact Or.inl (by_contra λ hne => Finset.disjoint_left.1 (Q.disjoint hc hc_w hne) hw hw_c_w)
      · exact Or.inr (by_contra λ hne => Finset.disjoint_left.1 (Q.disjoint hc hc_v hne) hv hv_c_v)
    · rintro (rfl | rfl)
      · exact ⟨hc_w, Or.inl hw_c_w⟩
      · exact ⟨hc_v, Or.inr hv_c_v⟩
  have hfine_filter : P.parts.filter (λ f => w ∈ f ∨ v ∈ f) = {f₀} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨λ ⟨hf, hor⟩ => ?_, λ heq => heq ▸ ⟨hf₀, Or.inl hw_f₀⟩⟩
    rcases hor with hw | hv
    · exact by_contra λ hne => Finset.disjoint_left.1 (P.disjoint hf hf₀ hne) hw hw_f₀
    · exact by_contra λ hne => Finset.disjoint_left.1 (P.disjoint hf hf₀ hne) hv hv_f₀
  have hcp_eq : ∀ S : Finset W,
      dp.cellProbability S = (if w ∈ S then (1 : ℚ) else 0) + (if v ∈ S then 1 else 0) := by
    intro S
    show ∑ w' ∈ S, (if w' = w then (1 : ℚ) else if w' = v then 1 else 0) =
      (if w ∈ S then 1 else 0) + (if v ∈ S then 1 else 0)
    have hpt : ∀ w' : W, (if w' = w then (1 : ℚ) else if w' = v then 1 else 0) =
        (if w' = w then 1 else 0) + (if w' = v then 1 else 0) := by
      intro w'
      by_cases hw : w' = w
      · subst hw; simp [hwv_ne]
      · by_cases hv : w' = v
        · subst hv; simp [hwv_ne.symm]
        · simp [hw, hv]
    rw [Finset.sum_congr rfl λ w' _ => hpt w', Finset.sum_add_distrib,
      Finset.sum_ite_eq' S w λ _ => (1 : ℚ), Finset.sum_ite_eq' S v λ _ => (1 : ℚ)]
  have hswap : ∀ c : Finset W, max (if w ∈ c then (1 : ℚ) else 0) (if v ∈ c then 1 else 0) =
      if w ∈ c ∨ v ∈ c then (1 : ℚ) else 0 := by
    intro c
    by_cases hw : w ∈ c <;> by_cases hv : v ∈ c <;> simp [hw, hv]
  have hmax_coarse :
      (∑ c ∈ Q.parts, max (if w ∈ c then (1 : ℚ) else 0) (if v ∈ c then 1 else 0)) = 2 := by
    rw [Finset.sum_congr rfl λ c _ => hswap c, ← Finset.sum_filter, hcoarse_filter,
      Finset.sum_insert (by simp [hc_w_ne_c_v]), Finset.sum_singleton]
    norm_num
  have hmax_fine :
      (∑ f ∈ P.parts, max (if w ∈ f then (1 : ℚ) else 0) (if v ∈ f then 1 else 0)) = 1 := by
    rw [Finset.sum_congr rfl λ f _ => hswap f, ← Finset.sum_filter, hfine_filter,
      Finset.sum_singleton]
  have hcpP : ∀ (R : Finpartition (Finset.univ : Finset W)) {c d : Finset W} (hc : c ∈ R.parts)
      (hwc : w ∈ c) (hd : d ∈ R.parts) (hvd : v ∈ d), ∑ c ∈ R.parts, dp.cellProbability c = 2 := by
    intro R c d hc hwc hd hvd
    simp_rw [hcp_eq]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, hpart_w hc hwc,
      hpart_v hd hvd, Finset.sum_singleton, Finset.sum_singleton]
    norm_num
  have hqu_eq : ∀ (cells : Finset (Finset W)), questionUtility dp {a₁, a₂} cells =
      (∑ c ∈ cells, dp.cellProbability c * dp.condValue {a₁, a₂} c) -
        dp.value {a₁, a₂} * (∑ c ∈ cells, dp.cellProbability c) := by
    intro cells
    unfold DecisionProblem.questionUtility DecisionProblem.utilityValue
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl λ c _ => mul_comm _ _
  have hX_coarse : ∑ c ∈ Q.parts, dp.cellProbability c * dp.condValue {a₁, a₂} c = 2 := by
    simp_rw [hcpcv_max]; exact hmax_coarse
  have hX_fine : ∑ f ∈ P.parts, dp.cellProbability f * dp.condValue {a₁, a₂} f = 1 := by
    simp_rw [hcpcv_max]; exact hmax_fine
  simp only [EUV] at hyp
  rw [hqu_eq Q.parts, hqu_eq P.parts, hX_coarse, hX_fine, hcpP Q hc_w hw_c_w hc_v hv_c_v,
    hcpP P hf₀ hw_f₀ hf₀ hv_f₀] at hyp
  linarith

/-- Relative to a decision problem, a question is better than another when it is more useful,
or as useful and less fine-grained: one should not ask for irrelevant information. -/
def Better (dp : DecisionProblem ℚ W A) (acts : Finset A)
    (Q Q' : Finpartition (Finset.univ : Finset W)) : Prop :=
  EUV dp acts Q' < EUV dp acts Q ∨ (EUV dp acts Q = EUV dp acts Q' ∧ Q' ≤ Q)

/-! ### The domain of a wh-phrase -/

variable {D : Type*} [DecidableEq D]

instance (f : W → Finset D) : DecidableRel (Setoid.ker f).r :=
  λ a b => inferInstanceAs (Decidable (f a = f b))

/-- The partition a wh-question induces over a domain: two worlds fall together when the
predicate's extension agrees on the domain. -/
def whQuestion (P : W → Finset D) (dom : Finset D) : Finpartition (Finset.univ : Finset W) :=
  Finpartition.ofSetoid (Setoid.ker λ w => dom ∩ P w)

/-- Enlarging the domain refines the question: more individuals, more specific answers. -/
theorem whQuestion_anti (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom') :
    whQuestion P dom' ≤ whQuestion P dom := by
  unfold whQuestion
  intro b hb
  obtain ⟨w, hw⟩ := Finpartition.nonempty_of_mem_parts _ hb
  refine ⟨_, (Finpartition.part_mem _).2 (Finset.mem_univ w), λ v hv => ?_⟩
  have hrel : dom' ∩ P w = dom' ∩ P v :=
    Finpartition.mem_part_ofSetoid_iff_rel.1
      ((Finpartition.mem_part_iff_exists _).2 ⟨b, hb, hv, hw⟩)
  refine Finpartition.mem_part_ofSetoid_iff_rel.2 ?_
  show dom ∩ P w = dom ∩ P v
  have := hrel
  ext d
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hd, hdw⟩
    have : d ∈ dom' ∩ P v := this ▸ Finset.mem_inter.2 ⟨h hd, hdw⟩
    exact ⟨hd, (Finset.mem_inter.1 this).2⟩
  · rintro ⟨hd, hdv⟩
    have : d ∈ dom' ∩ P w := this.symm ▸ Finset.mem_inter.2 ⟨h hd, hdv⟩
    exact ⟨hd, (Finset.mem_inter.1 this).2⟩

/-- Of two domains yielding equally useful questions, the smaller gives the better question:
the domain selected by relevance contains only the individuals that could affect the
decision. -/
theorem better_whQuestion_of_subset (dp : DecisionProblem ℚ W A) (acts : Finset A)
    (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom')
    (heq : EUV dp acts (whQuestion P dom) = EUV dp acts (whQuestion P dom')) :
    Better dp acts (whQuestion P dom) (whQuestion P dom') :=
  Or.inr ⟨heq, whQuestion_anti P h⟩

end Utility

/-! ### Mention-some and mention-all from one rule -/

variable {G : Type*}

/-- The paper's rule: the answers are the propositions that a group is among the optimal values
of the predicate, one for each group optimal somewhere. -/
def questionR (op : W → Set G) : Set (Set W) := {p | ∃ w, ∃ g ∈ op w, p = {v | g ∈ op v}}

/-- The rule of footnote 28, which puts two worlds together whenever their optimal values
overlap. -/
def questionS (op : W → Set G) : Set (Set W) := {p | ∃ w, p = {v | (op w ∩ op v).Nonempty}}

/-- When the optimal value is unique in every world the rule gives the partition by that value,
the mention-all reading. -/
theorem questionR_eq_range_fiber (f : W → G) :
    questionR (λ w => {f w}) = {p | ∃ w, p = f ⁻¹' {f w}} := by
  ext p
  simp only [questionR, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq, Set.preimage,
    eq_comm]

/-- The newspaper worlds of (20) and the places optimal in each: the station in `u`, the palace
in `v`, both in `w`. -/
def newspaperOp : NewsW → Set Walk
  | .station => {.station}
  | .palace => {.palace}
  | .both => Set.univ

/-- The rule yields the mention-some denotation {{u, w}, {v, w}}. -/
theorem newspaper_questionR :
    questionR newspaperOp = {{.station, .both}, {.palace, .both}} := by
  ext p
  simp only [questionR, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, g, hg, rfl⟩
    cases g
    · left; ext v; cases v <;> simp [newspaperOp]
    · right; ext v; cases v <;> simp [newspaperOp]
  · rintro (rfl | rfl)
    · exact ⟨.station, .station, by simp [newspaperOp], by ext v; cases v <;> simp [newspaperOp]⟩
    · exact ⟨.palace, .palace, by simp [newspaperOp], by ext v; cases v <;> simp [newspaperOp]⟩

/-- The rule of footnote 28 adds the trivial answer {u, v, w}, which is why the paper rejects
it. -/
theorem newspaper_questionS : Set.univ ∈ questionS newspaperOp :=
  ⟨.both, by ext v; cases v <;> simp [newspaperOp]; exact ⟨.station, trivial⟩⟩

end VanRooy2003
