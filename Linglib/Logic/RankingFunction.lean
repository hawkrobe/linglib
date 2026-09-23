module

public import Linglib.Logic.Nonmonotonic.Preferential
public import Mathlib.Data.ENat.Lattice

/-!
# Ranking functions

This file defines ranking functions, Spohn's ordinal conditional functions with natural-number
grades, together with his conditionalization of them and the consequence relation they induce.

A ranking function grades the disbelief in each world, and some world has grade `0`. The rank
of a proposition is the least rank of its worlds, and `⊤` for the contradiction, so of a
proposition and its negation one has rank `0`, and the rank of a disjunction is the smaller of
the two ranks. Conditionalization on a proposition at a firmness keeps the ranking within the
proposition and within its negation, each shifted to start at `0`, and lifts the negation by the
firmness. Revision conditionalizes at the firmness that just makes the proposition believed;
`Logic/BeliefRevision/Iterated.lean` proves the iterated-revision postulates of Darwiche and
Pearl for it. A ranking function orders the worlds by rank, which makes it a ranked model in
the sense of Lehmann and Magidor. A proposition `B` follows from `A` when the `A`-worlds of least
rank are `B`-worlds, which Halpern characterizes as `A` being impossible or `A ∩ B` being less
disbelieved than `A \ B`. This consequence relation is rational, and the beliefs of the ranking
function are the consequences of the tautology. The L-conditioning of Goldszmidt and Pearl
shifts the worlds outside a proposition by a fixed strength and, unlike conditionalization,
commutes.

## Main definitions

* `RankingFunction W`: a grading of disbelief `W → ℕ` with a world of grade `0`.
* `RankingFunction.rankSet`: the rank of a proposition, in `ℕ∞`.
* `RankingFunction.aPart`: the A-part of a ranking, the ranking within `A` shifted to `0`.
* `RankingFunction.conditionα`, `RankingFunction.revise`: A,α-conditionalization, and revision
  as conditionalization at the canonical firmness.
* `RankingFunction.lCondition`: the L-conditioning of Goldszmidt and Pearl, at a ranking that
  holds the evidence possible.
* `RankingFunction.beliefSet`: the propositions true at every world of rank `0`.
* `RankingFunction.toPreorder`, `RankingFunction.Entails`: the normality order on worlds and
  its consequence relation.

## Main results

* `RankingFunction.rankSet_eq_zero_or_compl`, `RankingFunction.rankSet_union`: of a proposition
  and its negation one has rank `0`, and the rank of a disjunction is the smaller rank.
* `RankingFunction.revise_success`: the revised ranking believes the evidence.
* `RankingFunction.entails_iff_exists_lt`, `RankingFunction.entails_iff_rankSet`: a consequent
  follows when each world falsifying it is outranked by one verifying it, equivalently when the
  premise is impossible or verifying it is less disbelieved than falsifying it.
* `RankingFunction.lCondition_comm`: L-conditionings commute.
* `RankingFunction.isRational_entails`: the consequence relation is rational.
* `RankingFunction.mem_beliefSet_iff_entails_univ`: belief is consequence from the tautology.

## References

* [W. Spohn, *Ordinal Conditional Functions: A Dynamic Theory of Epistemic States*
  (1988)][spohn-1988]
* [M. Goldszmidt and J. Pearl, *Qualitative Probabilities for Default Reasoning, Belief
  Revision, and Causal Modeling* (1996)][goldszmidt-pearl-1996]
* [D. Lehmann and M. Magidor, *What Does a Conditional Knowledge Base Entail?*
  (1992)][lehmann-magidor-1992]
* [A. Darwiche and J. Pearl, *On the Logic of Iterated Belief Revision*
  (1997)][darwiche-pearl-1997]
* [J. Y. Halpern, *Reasoning about Uncertainty* (2003)][halpern-2003]
-/

@[expose] public section

/-- A ranking function is a grading of disbelief in worlds under which some world has grade
`0`. -/
structure RankingFunction (W : Type*) where
  /-- The grade of disbelief in each world. -/
  rank : W → ℕ
  /-- Some world is not disbelieved. -/
  normalized : ∃ w, rank w = 0

namespace RankingFunction

variable {W : Type*} (κ : RankingFunction W) {A B : Set W} {w : W}

@[ext] theorem ext {κ κ' : RankingFunction W} (h : ∀ w, κ.rank w = κ'.rank w) : κ = κ' := by
  cases κ; cases κ'; congr; exact funext h

/-! ### Ranks of propositions -/

/-- The rank of a proposition is the least rank of its worlds, and `⊤` for the contradiction. -/
noncomputable def rankSet (A : Set W) : ℕ∞ := ⨅ w ∈ A, (κ.rank w : ℕ∞)

theorem rankSet_le (hw : w ∈ A) : κ.rankSet A ≤ κ.rank w := iInf₂_le w hw

theorem le_rankSet_iff {n : ℕ∞} : n ≤ κ.rankSet A ↔ ∀ w ∈ A, n ≤ κ.rank w := le_iInf₂_iff

theorem rankSet_anti (h : A ⊆ B) : κ.rankSet B ≤ κ.rankSet A :=
  κ.le_rankSet_iff.2 fun _ hw ↦ κ.rankSet_le (h hw)

@[simp] theorem rankSet_empty : κ.rankSet ∅ = ⊤ := by simp [rankSet]

/-- The rank of a satisfiable proposition is attained. -/
theorem exists_rank_eq_rankSet (hA : A.Nonempty) : ∃ w ∈ A, (κ.rank w : ℕ∞) = κ.rankSet A := by
  have hmem := csInf_mem (hA.image fun w ↦ (κ.rank w : ℕ∞))
  rw [sInf_image] at hmem
  exact hmem

theorem rankSet_eq_top_iff : κ.rankSet A = ⊤ ↔ A = ∅ := by
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun h ↦ h ▸ κ.rankSet_empty⟩
  obtain ⟨w, -, e⟩ := κ.exists_rank_eq_rankSet (Set.nonempty_iff_ne_empty.2 hne)
  exact ENat.natCast_ne_top _ (e.trans h)

theorem rankSet_ne_top (hA : A.Nonempty) : κ.rankSet A ≠ ⊤ :=
  mt κ.rankSet_eq_top_iff.1 hA.ne_empty

/-- The rank of a disjunction is the smaller rank. -/
theorem rankSet_union (A B : Set W) : κ.rankSet (A ∪ B) = min (κ.rankSet A) (κ.rankSet B) :=
  iInf_union

theorem rankSet_eq_zero_iff : κ.rankSet A = 0 ↔ ∃ w ∈ A, κ.rank w = 0 := by
  constructor
  · intro h
    rcases A.eq_empty_or_nonempty with rfl | hA
    · simp at h
    · obtain ⟨w, hw, e⟩ := κ.exists_rank_eq_rankSet hA
      exact ⟨w, hw, by exact_mod_cast e.trans h⟩
  · rintro ⟨w, hw, h0⟩
    exact le_antisymm ((κ.rankSet_le hw).trans (by simp [h0])) bot_le

@[simp] theorem rankSet_univ : κ.rankSet Set.univ = 0 :=
  κ.rankSet_eq_zero_iff.2 (let ⟨w, hw⟩ := κ.normalized; ⟨w, trivial, hw⟩)

/-- Of a proposition and its negation, one has rank `0`. -/
theorem rankSet_eq_zero_or_compl (A : Set W) : κ.rankSet A = 0 ∨ κ.rankSet Aᶜ = 0 := by
  have h := κ.rankSet_univ
  rw [← Set.union_compl_self A, rankSet_union] at h
  exact (min_eq_iff.1 h).imp And.left And.left

theorem toNat_rankSet_le (hw : w ∈ A) : (κ.rankSet A).toNat ≤ κ.rank w :=
  ENat.toNat_le_of_le_natCast (κ.rankSet_le hw)

/-! ### Conditionalization -/

/-- The A-part `κ(w | A) = κ(w) − κ(A)` of a ranking is the ranking within `A`, shifted so that
its best world has rank `0`. -/
noncomputable def aPart (A : Set W) (w : W) : ℕ := κ.rank w - (κ.rankSet A).toNat

theorem exists_aPart_eq_zero (hA : A.Nonempty) : ∃ w ∈ A, κ.aPart A w = 0 := by
  obtain ⟨w, hw, e⟩ := κ.exists_rank_eq_rankSet hA
  exact ⟨w, hw, by simp [aPart, ← e]⟩

theorem aPart_le (A : Set W) (w : W) : κ.aPart A w ≤ κ.rank w := Nat.sub_le _ _

open Classical in
/-- The A,α-conditionalization of `κ` is its A-part on `A` and its Aᶜ-part lifted by the firmness
`α` on `Aᶜ`, so that `A` comes to be believed with firmness `α`. -/
noncomputable def conditionα (A : Set W) (hA : A.Nonempty) (α : ℕ) : RankingFunction W where
  rank w := if w ∈ A then κ.aPart A w else α + κ.aPart Aᶜ w
  normalized := let ⟨w, hw, h0⟩ := κ.exists_aPart_eq_zero hA; ⟨w, by simp [hw, h0]⟩

theorem conditionα_of_mem (hA : A.Nonempty) (α : ℕ) (hw : w ∈ A) :
    (κ.conditionα A hA α).rank w = κ.aPart A w := by
  simp [conditionα, hw]

theorem conditionα_of_notMem (hA : A.Nonempty) (α : ℕ) (hw : w ∉ A) :
    (κ.conditionα A hA α).rank w = α + κ.aPart Aᶜ w := by
  simp [conditionα, hw]

/-- The conditionalized ranking holds `A` possible. -/
@[simp] theorem rankSet_conditionα (hA : A.Nonempty) (α : ℕ) :
    (κ.conditionα A hA α).rankSet A = 0 := by
  obtain ⟨w, hw, h0⟩ := κ.exists_aPart_eq_zero hA
  exact (rankSet_eq_zero_iff _).2 ⟨w, hw, by rw [conditionα_of_mem _ _ _ hw, h0]⟩

/-- The conditionalized ranking believes `A` with firmness `α`. -/
theorem rankSet_conditionα_compl (hA : A.Nonempty) (hA' : Aᶜ.Nonempty) (α : ℕ) :
    (κ.conditionα A hA α).rankSet Aᶜ = α := by
  obtain ⟨w, hw, h0⟩ := κ.exists_aPart_eq_zero hA'
  refine le_antisymm (((κ.conditionα A hA α).rankSet_le hw).trans ?_) ?_
  · rw [conditionα_of_notMem _ _ _ hw, h0, add_zero]
  · exact (le_rankSet_iff _).2 fun v hv ↦ by
      rw [conditionα_of_notMem _ _ _ hv]
      exact_mod_cast Nat.le_add_right _ _

/-- Revision by `A` is conditionalization at the firmness `κ(Aᶜ) + 1`, just enough to make `A`
believed. -/
noncomputable def revise (A : Set W) (hA : A.Nonempty) : RankingFunction W :=
  κ.conditionα A hA ((κ.rankSet Aᶜ).toNat + 1)

/-- The belief set of a ranking function consists of the propositions true at every world of
rank `0`. -/
def beliefSet : Set (Set W) := {A | ∀ w, κ.rank w = 0 → w ∈ A}

theorem mem_beliefSet : A ∈ κ.beliefSet ↔ ∀ w, κ.rank w = 0 → w ∈ A := Iff.rfl

/-- The revised ranking believes the evidence, the AGM success postulate. -/
theorem revise_success (hA : A.Nonempty) : A ∈ (κ.revise A hA).beliefSet := fun w hw ↦ by
  by_contra hnot
  rw [revise, conditionα_of_notMem _ _ _ hnot] at hw
  omega

open Classical in
/-- L-conditioning on `A` with strength `l`, at a ranking holding `A` possible, lifts the worlds
outside `A` by `l`. -/
noncomputable def lCondition (A : Set W) (h0 : ∃ w ∈ A, κ.rank w = 0) (l : ℕ) :
    RankingFunction W where
  rank w := if w ∈ A then κ.rank w else κ.rank w + l
  normalized := let ⟨w, hw, hr⟩ := h0; ⟨w, by simp [hw, hr]⟩

/-- L-conditionings commute, where two conditionalizations commute only on independent
propositions. -/
theorem lCondition_comm (hA : ∃ w ∈ A, κ.rank w = 0) (hB : ∃ w ∈ B, κ.rank w = 0) (l m : ℕ)
    (hAB : ∃ w ∈ B, (κ.lCondition A hA l).rank w = 0)
    (hBA : ∃ w ∈ A, (κ.lCondition B hB m).rank w = 0) :
    (κ.lCondition A hA l).lCondition B hAB m = (κ.lCondition B hB m).lCondition A hBA l := by
  ext w
  simp only [lCondition]
  split_ifs <;> omega

/-! ### The induced consequence relation -/

/-- In the normality order of a ranking function, `w` is at least as normal as `v` when its rank
is at most that of `v`. -/
@[reducible] def toPreorder : Preorder W := Preorder.lift κ.rank

theorem toPreorder_le {v : W} : κ.toPreorder.le w v ↔ κ.rank w ≤ κ.rank v := Iff.rfl

theorem wellFounded_toPreorder_lt : WellFounded κ.toPreorder.lt := InvImage.wf κ.rank wellFounded_lt

theorem total_toPreorder : Std.Total κ.toPreorder.le := ⟨fun w v ↦ le_total (κ.rank w) (κ.rank v)⟩

/-- The minimal worlds of a proposition are its worlds of least rank. -/
theorem mem_minimals_toPreorder :
    w ∈ κ.toPreorder.minimals A ↔ w ∈ A ∧ ∀ v ∈ A, κ.rank w ≤ κ.rank v :=
  Preorder.mem_minimals_iff_forall_le κ.total_toPreorder

/-- `B` follows from `A` in `κ` when the `A`-worlds of least rank are `B`-worlds. This is the
consequence relation of the ranked model `κ.toPreorder`. -/
def Entails (A B : Set W) : Prop := Nonmonotonic.Entails κ.toPreorder A B

theorem entails_iff_forall_least :
    κ.Entails A B ↔ ∀ w ∈ A, (∀ v ∈ A, κ.rank w ≤ κ.rank v) → w ∈ B :=
  ⟨fun h _ hw hmin ↦ h (κ.mem_minimals_toPreorder.2 ⟨hw, hmin⟩),
    fun h w hw ↦ have := κ.mem_minimals_toPreorder.1 hw; h w this.1 this.2⟩

/-- `B` follows from `A` exactly when every `A`-world outside `B` is outranked by an `A`-world
in `B`. -/
theorem entails_iff_exists_lt :
    κ.Entails A B ↔ ∀ x ∈ A, x ∉ B → ∃ y ∈ A, y ∈ B ∧ κ.rank y < κ.rank x := by
  refine ⟨fun h x hx hxB ↦ ?_, fun h w hw ↦ by_contra fun hwB ↦ ?_⟩
  · obtain ⟨y, hy, hyx⟩ := Preorder.exists_le_mem_minimals κ.wellFounded_toPreorder_lt hx
    refine ⟨y, hy.1, h hy, lt_of_le_of_ne hyx fun e ↦ hxB (h ?_)⟩
    exact κ.mem_minimals_toPreorder.2
      ⟨hx, fun v hv ↦ e ▸ (κ.mem_minimals_toPreorder.1 hy).2 v hv⟩
  · obtain ⟨y, hy, -, hlt⟩ := h w hw.1 hwB
    exact absurd ((κ.mem_minimals_toPreorder.1 hw).2 y hy) (not_le.2 hlt)

/-- `B` follows from `A` exactly when `A` is impossible or `A ∩ B` is less disbelieved than
`A \ B`. -/
theorem entails_iff_rankSet :
    κ.Entails A B ↔ κ.rankSet A = ⊤ ∨ κ.rankSet (A ∩ B) < κ.rankSet (A \ B) := by
  rw [entails_iff_exists_lt]
  constructor
  · intro h
    rcases A.eq_empty_or_nonempty with rfl | hA
    · exact Or.inl κ.rankSet_empty
    rcases (A \ B).eq_empty_or_nonempty with he | hne
    · have hAB : A ∩ B = A := Set.inter_eq_left.2 (Set.sdiff_eq_empty.1 he)
      exact Or.inr (by rw [he, hAB, rankSet_empty]; exact (κ.rankSet_ne_top hA).lt_top)
    · obtain ⟨x, hx, e⟩ := κ.exists_rank_eq_rankSet hne
      obtain ⟨y, hyA, hyB, hlt⟩ := h x hx.1 hx.2
      refine Or.inr ((κ.rankSet_le (A := A ∩ B) ⟨hyA, hyB⟩).trans_lt ?_)
      rw [← e]
      exact_mod_cast hlt
  · rintro (hA | hlt) x hx hxB
    · exact absurd (κ.rankSet_eq_top_iff.1 hA ▸ hx) (Set.notMem_empty x)
    · have hne : (A ∩ B).Nonempty := Set.nonempty_iff_ne_empty.2 fun he ↦ by simp [he] at hlt
      obtain ⟨y, hy, e⟩ := κ.exists_rank_eq_rankSet hne
      have hxr := κ.rankSet_le (A := A \ B) ⟨hx, hxB⟩
      exact ⟨y, hy.1, hy.2, by exact_mod_cast e ▸ hlt.trans_le hxr⟩

instance [Fintype W] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    Decidable (κ.Entails A B) :=
  decidable_of_iff _ κ.entails_iff_exists_lt.symm

/-- The consequence relation of a ranking function is rational. -/
theorem isRational_entails : Nonmonotonic.IsRational κ.Entails :=
  Nonmonotonic.isRational_entails κ.wellFounded_toPreorder_lt κ.total_toPreorder

/-- The beliefs are the consequences of the tautology. -/
theorem mem_beliefSet_iff_entails_univ : A ∈ κ.beliefSet ↔ κ.Entails Set.univ A := by
  rw [entails_iff_forall_least]
  refine ⟨fun h w _ hmin ↦ h w ?_, fun h w hw ↦ h w trivial fun v _ ↦ hw ▸ Nat.zero_le _⟩
  obtain ⟨w₀, hw₀⟩ := κ.normalized
  exact Nat.le_zero.1 (hw₀ ▸ hmin w₀ trivial)

end RankingFunction
