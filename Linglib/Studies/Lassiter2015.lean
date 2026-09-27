module

public import Linglib.Logic.ComparativeProbability.Patterns
public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Core.Order.Probability.Content
public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Semantics.Attitudes.EpistemicThreshold
public import Linglib.Studies.HollidayIcard2013
public import Linglib.Data.Examples.Lassiter2015
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Lassiter (2015): Epistemic comparison, models of uncertainty, and the disjunction puzzle

[lassiter-2015] traces the disjunction puzzle, that *φ is as likely as ψ* and *φ is as likely
as χ* entail *φ is as likely as ψ or χ* under [kratzer-1991]'s comparative possibility, to the
lift [lewis-1973] uses: a proposition sits in the likelihood order by its highest worlds alone,
so the likelihood of a disjunction is that of its likeliest disjunct. Iterated over a fair
lottery in which nobody holds more than two tickets, the puzzle makes Sam as likely to win as
not (`lottery_collapse`). Section 1.4 shows that [kratzer-2012]'s revised lift, which compares
only the worlds in exactly one of the two propositions, escapes Yalcin's special case but
validates the puzzle whenever the alternatives are disjoint, as in the lottery
(`revised_escapes_collapse`, `revised_disjoint_puzzle`); every countermodel has a world in the
overlap (`revised_countermodel_overlap`). Section 1.5 shows that [holliday-icard-2013]'s
m-lifting avoids the puzzle but, under Kratzer's *must*, makes a necessary proposition no
likelier than its negation as soon as the best worlds are fewer than half
(`mLift_must_not_probably`, `best_not_probably_of_ncard_lt`).

Section 2 replaces the lift by a scale. Finitely additive probability refutes the puzzle
(`prob_refutes_rightUnion`) while allowing it when the first proposition holds at least half
the mass (`prob_rightUnion_of_half`), and gives Sam the right odds (`lottery_bound`).
Symmetric fuzzy measures also refute it, but let *Sam goes to the movies* be exactly as
likely as *Sam goes to school or to the movies* although school is possible
(`fuzzy_counterexample`); the equal-shares axiom, [holliday-icard-2013]'s qualitative
additivity, forbids this (`QualAddMeasure.eq_zero_of_union_le`). Section 3 examines three
bridges from Kratzer's *must* to a probabilistic *likely*: BR1 reimports the disjoint puzzle
(`bridge1_disjoint_puzzle`) and permits a necessary proposition to be barely likelier than
not (`bridge1_thin_margin`); BR2 and BR3 permit it to be less likely than not
(`bridge2_must_not_probably`, `bridge3_must_not_probably`). Section 4 states the three
replacements for the auxiliaries, quantificational, strong and weak, and the inference from
*more likely than* to *might* that separates them (`moreLikely_might`,
`weak_refutes_moreLikely_might`).

## Implementation notes

* Kratzer's *must* is `humanNecessity` over the empty base, and Kratzer 2012's revised lift is
  `KratzerLift` in `Logic/ComparativeProbability/WorldOrdering`, whose disjoint right-union is
  the observation this paper reports through [holliday-icard-2013].
* The three world-ordering countermodels share one model: three worlds, the first alone best,
  masses `0.4`, `0.3`, `0.3`; BR3 holds in it by [holliday-icard-2013]'s footnote-13 lemma,
  since the order agrees with the measure on singletons.
* The strong and weak probabilistic auxiliaries are `EpistemicThreshold.meetsThreshold`, the
  positive-form threshold semantics, with thresholds `1` and `θ < 1`.
* The ratio-modifier argument of §2.2 and the open problems of §4 are recorded as examples
  only.

## References

* [lassiter-2015]
* [kratzer-1991]
* [kratzer-2012]
* [lewis-1973]
* [halpern-1997]
* [halpern-2003]
* [holliday-icard-2013]
* [yalcin-2010]
* [hamblin-1959]
* [von-fintel-gillies-2010]
-/

@[expose] public section

namespace Lassiter2015

open ComparativeProbability Modality

variable {W : Type*}

/-! ### §1.1 The disjunction puzzle and the lottery -/

/-- The puzzle (11) is the right-union property, which [lewis-1973]'s lift has
([halpern-1997]). -/
theorem disjunction_puzzle (r : W → W → Prop) : RightUnion (LewisLift r) :=
  rightUnion_lewisLift

/-- (13)–(14): iterating the puzzle over the other ticket holders, whose winnings exhaust Sam's
losing, makes Sam as likely to win as not. -/
theorem lottery_collapse {r : Set W → Set W → Prop} (hJ : RightUnion r) {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) {win : Set W} {wins : ι → Set W}
    (hcover : (⋃ i ∈ s, wins i) = winᶜ) (h : ∀ i ∈ s, r win (wins i)) : r win winᶜ :=
  hcover ▸ hJ.biUnion hs h

/-! ### §1.4 Kratzer's revised comparative possibility -/

section Revised

variable (r : W → W → Prop)

/-- (30): the revised lift lets a proposition be as likely as its negation without being as
likely as everything, escaping Yalcin's collapse, since it is as likely as the whole space only
when the space is exhausted. -/
theorem kratzerLift_univ_iff (A : Set W) : KratzerLift r A Set.univ ↔ A = Set.univ :=
  kratzerLift_univ_iff' r A

/-- Two indiscriminate worlds: `{0}` is as likely as its complement but not as everything. -/
theorem revised_escapes_collapse :
    ¬EquiprobabilityCollapse (KratzerLift fun _ _ : Fin 2 ↦ True) := by
  intro h
  have := h {0} Set.univ fun ⟨_, _, hall⟩ ↦ (hall 0 ⟨rfl, fun h ↦ h rfl⟩).2 trivial
  rw [kratzerLift_univ_iff] at this
  exact absurd (this ▸ Set.mem_univ 1) (by simp)

/-- (31), Appendix B: in a countermodel to the puzzle for the revised lift, a world of one
alternative outside the first proposition fails to dominate a world the first proposition shares
with the other alternative. -/
theorem revised_countermodel_overlap {A B C : Set W} (hB : KratzerLift r A B)
    (hC : KratzerLift r A C) (hn : ¬KratzerLift r A (B ∪ C)) :
    (∃ u ∈ B \ A, ∃ v ∈ A ∩ C, ¬(r u v ∧ ¬r v u)) ∨
      ∃ u ∈ C \ A, ∃ v ∈ A ∩ B, ¬(r u v ∧ ¬r v u) := by
  simp only [KratzerLift, not_not] at hn
  obtain ⟨u, ⟨huBC, huA⟩, hall⟩ := hn
  rcases huBC with huB | huC
  · left
    refine ⟨u, ⟨huB, huA⟩, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hB ⟨u, ⟨huB, huA⟩, fun v ⟨hvA, hvB⟩ ↦ by
      by_cases hvC : v ∈ C
      · exact hnone v ⟨hvA, hvC⟩
      · exact hall v ⟨hvA, fun h ↦ h.elim hvB hvC⟩⟩
  · right
    refine ⟨u, ⟨huC, huA⟩, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hC ⟨u, ⟨huC, huA⟩, fun v ⟨hvA, hvC⟩ ↦ by
      by_cases hvB : v ∈ B
      · exact hnone v ⟨hvA, hvB⟩
      · exact hall v ⟨hvA, fun h ↦ h.elim hvB hvC⟩⟩

/-- (32), Appendix C: with the alternatives made disjoint, as in the lottery, the puzzle is
valid for the revised lift. -/
theorem revised_disjoint_puzzle {A B C : Set W} (hB : Disjoint A B) (hC : Disjoint A C)
    (hAB : KratzerLift r A B) (hAC : KratzerLift r A C) : KratzerLift r A (B ∪ C) :=
  kratzerLift_rightUnion_of_disjoint r hB hC hAB hAC

end Revised

/-! ### §1.5 The m-lifting under Kratzer's *must* -/

/-- A proposition fewer than half of whose worlds it contains cannot be probable under the
m-lifting: no injection matches its complement into it. -/
theorem best_not_probably_of_ncard_lt [Finite W] (r : W → W → Prop) {A : Set W}
    (h : A.ncard < Aᶜ.ncard) : ¬Probably (MatchingLift r) A :=
  fun hp ↦ absurd hp.1.ncard_le (not_le.2 h)

/-- The ordering source of §1.5 and §3: the first of three worlds is the sole best world. -/
def bestFirst : List (Fin 3 → Prop) := [(· = 0)]

theorem bestFirst_le (v u : Fin 3) : (v ≤[bestFirst] u) ↔ (u = 0 → v = 0) := by
  simp [bestFirst, atLeastAsGoodAs_iff]

/-- Kratzer's *must* of the sole best world holds, yet under the m-lifting that world is not
likelier than its complement, since one world matches no injection from two. -/
theorem mLift_must_not_probably :
    humanNecessity emptyBackground (fun _ ↦ bestFirst) (· ∈ ({0} : Set (Fin 3))) 0 ∧
      ¬Probably (MatchingLift (atLeastAsGoodAs bestFirst)) {0} := by
  refine ⟨?_, best_not_probably_of_ncard_lt _ ?_⟩
  · intro u _
    refine ⟨0, by rw [accessibleWorlds_emptyBackground]; exact Set.mem_univ _, ?_, fun z _ hz ↦ ?_⟩
    · rw [bestFirst_le]; exact fun _ ↦ rfl
    · rw [bestFirst_le] at hz; exact hz rfl
  · have : ({0} : Set (Fin 3))ᶜ = {1, 2} := by ext x; fin_cases x <;> simp
    rw [this, Set.ncard_singleton, Set.ncard_pair (by decide)]; decide

/-! ### §2.1 Scales of probability -/

section Probability

variable (P : FinAddMeasure ℚ W)

/-- (46): three disjoint alternatives with masses `0.4`, `0.3`, `0.3` refute the puzzle for
probability. -/
noncomputable def skewed : FinAddMeasure ℚ (Fin 3) :=
  .ofFintype ![4 / 10, 3 / 10, 3 / 10] (fun i ↦ by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)

theorem prob_refutes_rightUnion : ¬RightUnion skewed.inducedGe := by
  intro h
  have h12 : skewed ({1} ∪ {2}) = 6 / 10 := by
    rw [skewed.additive (Set.disjoint_singleton.2 (by decide))]
    simp [skewed]; norm_num
  have := h {0} {1} {2} (by simp [FinAddMeasure.inducedGe, skewed]; norm_num)
    (by simp [FinAddMeasure.inducedGe, skewed]; norm_num)
  simp only [FinAddMeasure.inducedGe, Set.sup_eq_union, h12] at this
  simp [skewed] at this
  norm_num at this

/-- The premises are compatible with the conclusion: when the first proposition holds at least
half the mass, any alternatives outside it together weigh no more. -/
theorem prob_rightUnion_of_half {A B C : Set W} (hA : 1 / 2 ≤ P A) (hB : B ⊆ Aᶜ) (hC : C ⊆ Aᶜ) :
    P (B ∪ C) ≤ P A := by
  have h1 := P.mu_compl A
  have h2 := P.mu_mono (Set.union_subset hB hC)
  linarith

/-- The fair lottery: a holder of at most `k` of `n` tickets wins with probability at most
`k / n`, and loses with probability at least `(n - k) / n`. -/
theorem lottery_bound {n k : ℕ} [NeZero n] {A : Set (Fin n)} (h : A.ncard ≤ k) :
    FinAddMeasure.uniform (K := ℚ) (Fin n) A ≤ k / n ∧
      ((n : ℚ) - k) / n ≤ FinAddMeasure.uniform (K := ℚ) (Fin n) Aᶜ := by
  have hn : (0 : ℚ) < n := by exact_mod_cast NeZero.pos n
  have hk : (A.ncard : ℚ) ≤ k := by exact_mod_cast h
  constructor
  · rw [FinAddMeasure.uniform_apply, Fintype.card_fin]
    exact div_le_div_of_nonneg_right hk hn.le
  · have := (FinAddMeasure.uniform (K := ℚ) (Fin n)).mu_compl A
    rw [FinAddMeasure.uniform_apply, Fintype.card_fin] at this
    have h1 : (A.ncard : ℚ) / n ≤ k / n := div_le_div_of_nonneg_right hk hn.le
    have h2 : ((n : ℚ) - k) / n = 1 - k / n := by rw [sub_div, div_self hn.ne']
    linarith

end Probability

/-! ### §2.2 Symmetric fuzzy measures and equal shares -/

/-- (47): a symmetric fuzzy measure, normalized, symmetric under complement, and monotone. -/
structure SymmetricFuzzyMeasure (W : Type*) where
  /-- The measure. -/
  mu : Set W → ℚ
  mu_univ : mu Set.univ = 1
  symm : ∀ A, mu A + mu Aᶜ = 1
  mono : ∀ ⦃A B⦄, A ⊆ B → mu A ≤ mu B

/-- Every probability measure is a symmetric fuzzy measure. -/
def FinAddMeasure.toSymmetricFuzzy (P : FinAddMeasure ℚ W) : SymmetricFuzzyMeasure W :=
  ⟨P, P.total, P.mu_compl, fun _ _ h ↦ P.mu_mono h⟩

open scoped Classical in
/-- (48)'s scenario: Sam may go to school (`1`), more likely to the movies (`0`), or elsewhere
(`2`); the movies alone measure `0.6`, as much as the movies or school. -/
noncomputable def wax : SymmetricFuzzyMeasure (Fin 3) where
  mu A := if 0 ∈ A then (if 1 ∈ A then (if 2 ∈ A then 1 else 6 / 10) else
      (if 2 ∈ A then 8 / 10 else 6 / 10))
    else (if 1 ∈ A then (if 2 ∈ A then 4 / 10 else 2 / 10) else (if 2 ∈ A then 4 / 10 else 0))
  mu_univ := by simp
  symm A := by
    by_cases h0 : 0 ∈ A <;> by_cases h1 : 1 ∈ A <;> by_cases h2 : 2 ∈ A <;>
      simp [h0, h1, h2] <;> norm_num
  mono A B h := by
    by_cases a0 : 0 ∈ A <;> by_cases a1 : 1 ∈ A <;> by_cases a2 : 2 ∈ A <;>
      by_cases b0 : 0 ∈ B <;> by_cases b1 : 1 ∈ B <;> by_cases b2 : 2 ∈ B <;>
      simp only [a0, a1, a2, b0, b1, b2, ite_true, ite_false] <;>
      first
        | exact absurd (h a0) b0
        | exact absurd (h a1) b1
        | exact absurd (h a2) b2
        | norm_num

/-- (48): under `wax`, going to the movies is exactly as likely as going to school or to the
movies, although going to school is possible; the measure is not qualitatively additive. -/
theorem fuzzy_counterexample :
    wax.mu {0} = wax.mu ({1} ∪ {0}) ∧ 0 < wax.mu {1} ∧
      ¬(wax.mu ({1} ∪ {0}) ≤ wax.mu {0} ↔
        wax.mu (({1} ∪ {0}) \ {0}) ≤ wax.mu ({0} \ ({1} ∪ {0}))) := by
  have h1 : ({1} ∪ {0} : Set (Fin 3)) \ {0} = {1} := by ext x; fin_cases x <;> simp
  have h2 : ({0} : Set (Fin 3)) \ ({1} ∪ {0}) = ∅ := by ext x; fin_cases x <;> simp
  rw [h1, h2]
  norm_num [wax]

/-- (49) with (47): under a qualitatively additive measure, a proposition as likely as a
disjunction it is part of leaves the other disjunct no mass, so (48) forces school out. -/
theorem QualAddMeasure.eq_zero_of_union_le (m : QualAddMeasure ℚ W) {A B : Set W}
    (h : m (A ∪ B) ≤ m A) : m (B \ A) = 0 := by
  have := (m.qualAdd (A ∪ B) A).1 h
  rw [Set.union_sdiff_left, Set.sdiff_eq_empty.2 Set.subset_union_left, m.mu_empty] at this
  exact le_antisymm this (m.nonneg _)

/-! ### §3 Bridging rules -/

section Bridges

variable (r : W → W → Prop) (P : FinAddMeasure ℚ W)

/-- (57) BR1: the revised lift constrains probability. -/
def Bridge1 : Prop := ∀ A B, KratzerLift r A B → P B ≤ P A

/-- (59) BR2: the world order constrains probability on singletons. -/
def Bridge2 : Prop := ∀ u v, r u v → P {v} ≤ P {u}

/-- (61) BR3: the m-lifting constrains probability. -/
def Bridge3 : Prop := ∀ A B, MatchingLift r A B → P B ≤ P A

/-- (58): BR1 reimports the puzzle for disjoint alternatives ordered by the revised lift. -/
theorem bridge1_disjoint_puzzle (h : Bridge1 r P) {A B C : Set W} (hB : Disjoint A B)
    (hC : Disjoint A C) (hAB : KratzerLift r A B) (hAC : KratzerLift r A C) :
    P (B ∪ C) ≤ P A :=
  h _ _ (kratzerLift_rightUnion_of_disjoint r hB hC hAB hAC)

/-- BR2 makes the m-lifting sound for the measure ([holliday-icard-2013], footnote 13), so
BR3 follows from BR2 when the order agrees with the measure. -/
theorem bridge3_of_agree [Fintype W] (h : ∀ v u, r v u ↔ P {u} ≤ P {v}) : Bridge3 r P :=
  fun _ _ hAB ↦ HollidayIcard2013.measure_le_of_matchingLift P r h hAB

end Bridges

/-- The three-world model of §3 with masses `0.4`, `0.3`, `0.3`: BR2 holds, Kratzer's *must*
of the best world holds, yet the best world is less likely than its complement. -/
theorem bridge2_must_not_probably :
    Bridge2 (atLeastAsGoodAs bestFirst) skewed ∧
      humanNecessity emptyBackground (fun _ ↦ bestFirst) (· ∈ ({0} : Set (Fin 3))) 0 ∧
      ¬Probably skewed.inducedGe {0} := by
  refine ⟨fun u v huv ↦ ?_, mLift_must_not_probably.1, fun ⟨h, _⟩ ↦ ?_⟩
  · rw [bestFirst_le] at huv
    fin_cases u <;> fin_cases v <;> simp [skewed] at huv ⊢ <;> norm_num
  · have hc : ({0} : Set (Fin 3))ᶜ = {1} ∪ {2} := by ext x; fin_cases x <;> simp
    rw [FinAddMeasure.inducedGe, hc, skewed.additive (Set.disjoint_singleton.2 (by decide))] at h
    simp [skewed] at h
    norm_num at h

/-- The same model satisfies BR3, since the order agrees with the measure on singletons, so
BR3 too allows a necessary proposition to be less likely than its negation. -/
theorem bridge3_must_not_probably :
    Bridge3 (atLeastAsGoodAs bestFirst) skewed ∧
      humanNecessity emptyBackground (fun _ ↦ bestFirst) (· ∈ ({0} : Set (Fin 3))) 0 ∧
      ¬Probably skewed.inducedGe {0} :=
  ⟨bridge3_of_agree _ _ fun v u ↦ by
      rw [bestFirst_le]; fin_cases u <;> fin_cases v <;> simp [skewed] <;> norm_num,
    bridge2_must_not_probably.2.1, bridge2_must_not_probably.2.2⟩

/-- The two-world model of §3 with masses `0.5001` and `0.4999`: BR1 holds, the sole best world
is necessary, yet it is only barely likelier than its negation, so BR1 cannot deliver *much
more likely*. -/
noncomputable def thin : FinAddMeasure ℚ (Fin 2) :=
  .ofFintype ![5001 / 10000, 4999 / 10000] (fun i ↦ by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)

/-- The ordering source with the first of two worlds best. -/
def bestFirst₂ : List (Fin 2 → Prop) := [(· = 0)]

theorem bridge1_thin_margin :
    Bridge1 (atLeastAsGoodAs bestFirst₂) thin ∧
      humanNecessity emptyBackground (fun _ ↦ bestFirst₂) (· ∈ ({0} : Set (Fin 2))) 0 ∧
      thin {0} < 5002 / 10000 := by
  have hle : ∀ v u : Fin 2, (v ≤[bestFirst₂] u) ↔ (u = 0 → v = 0) := fun v u ↦ by
    simp [bestFirst₂, atLeastAsGoodAs_iff]
  have hsets : ∀ A : Set (Fin 2), A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Set.univ := fun A ↦ by
    by_cases h0 : 0 ∈ A <;> by_cases h1 : 1 ∈ A
    · right; right; right; ext x; fin_cases x <;> simp [h0, h1]
    · right; left; ext x; fin_cases x <;> simp [h0, h1]
    · right; right; left; ext x; fin_cases x <;> simp [h0, h1]
    · left; ext x; fin_cases x <;> simp [h0, h1]
  refine ⟨fun A B hAB ↦ ?_, ?_, by simp [thin]; norm_num⟩
  · rcases hsets A with rfl | rfl | rfl | rfl <;> rcases hsets B with rfl | rfl | rfl | rfl <;>
      simp [KratzerLift, hle, thin] at hAB ⊢ <;> norm_num at hAB ⊢
  · intro u _
    refine ⟨0, by rw [accessibleWorlds_emptyBackground]; exact Set.mem_univ _, ?_, fun z _ hz ↦ ?_⟩
    · rw [hle]; exact fun _ ↦ rfl
    · rw [hle] at hz; exact hz rfl

/-! ### §4 Probability and the epistemic auxiliaries -/

section Auxiliaries

variable (P : FinAddMeasure ℚ W)

/-- *Must* as a quantifier over the epistemic space, Kratzer's auxiliary with an empty ordering
source: the whole space. -/
def quantMust (A : Set W) : Prop := A = Set.univ

/-- The probabilistic *must* with threshold `θ`, strong at `θ = 1` and weak below. -/
def probMust (θ : ℚ) (A : Set W) : Prop :=
  EpistemicThreshold.meetsThreshold (fun _ : Unit ↦ (P : Set W → ℚ)) θ () A

/-- The dual *might*: `Pr(A) > 1 - θ`. -/
def probMight (θ : ℚ) (A : Set W) : Prop := 1 - θ < P A

/-- (56) under the quantificational auxiliaries: a necessary proposition has all the mass, the
largest possible margin over its negation. -/
theorem quantMust_prob {A : Set W} (h : quantMust A) : P A = 1 ∧ P Aᶜ = 0 := by
  subst h; simp

/-- The strong probabilistic *must* agrees with the quantificational one on the mass. -/
theorem probMust_one_iff (A : Set W) : probMust P 1 A ↔ P A = 1 := by
  unfold probMust EpistemicThreshold.meetsThreshold
  constructor
  · intro h
    have h' : 1 ≤ P A := h
    exact le_antisymm (by have := P.mu_compl A; have := P.nonneg Aᶜ; linarith) h'
  · intro h
    show 1 ≤ P A
    rw [h]

/-- (64): under the strong auxiliaries, what is more likely than something might be. -/
theorem moreLikely_might {A B : Set W} (h : Strict P.inducedGe A B) : probMight P 1 A := by
  obtain ⟨hle, hnot⟩ := h
  simp only [FinAddMeasure.inducedGe, ge_iff_le, not_le] at hle hnot
  have := P.nonneg B
  unfold probMight; linarith

/-- (65): under a weak *might*, two astronomically unlikely teams can be ordered without either
being a live possibility. -/
theorem weak_refutes_moreLikely_might :
    ∃ (P : FinAddMeasure ℚ (Fin 100)) (A B : Set (Fin 100)),
      Strict P.inducedGe A B ∧ ¬probMight P (9 / 10) A := by
  refine ⟨FinAddMeasure.uniform (K := ℚ) (Fin 100), {0, 1}, {0}, ⟨?_, ?_⟩, ?_⟩
  · simp only [FinAddMeasure.inducedGe, ge_iff_le]
    exact (FinAddMeasure.uniform (K := ℚ) (Fin 100)).mu_mono (Set.singleton_subset_iff.2 (by simp))
  · simp only [FinAddMeasure.inducedGe, ge_iff_le, not_le, FinAddMeasure.uniform_apply,
      Set.ncard_singleton, Set.ncard_pair (show (0 : Fin 100) ≠ 1 by decide), Fintype.card_fin]
    norm_num
  · simp only [probMight, FinAddMeasure.uniform_apply,
      Set.ncard_pair (show (0 : Fin 100) ≠ 1 by decide), Fintype.card_fin, not_lt]
    norm_num

end Auxiliaries

end Lassiter2015
