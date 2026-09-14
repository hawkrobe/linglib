import Linglib.Core.Order.Plausibility
import Mathlib.Data.ENat.Lattice

/-!
# Ranking functions

This file defines ranking functions, the ordinal conditional functions of [spohn-1988] with
natural-number grades, and Spohn's conditionalization on them. A ranking function grades the
disbelief in each world, some world having grade `0`; the rank of a proposition is the least
rank of its worlds, `⊤` for the contradiction, so that of a proposition and its negation one
has rank `0` and the rank of a disjunction is the smaller rank. Conditionalization on a
proposition at a firmness keeps the ranking within the proposition and within its negation,
each shifted to start at `0`, and lifts the negation by the firmness; revision conditionalizes
at the firmness that just makes the proposition believed, the operator whose iterated-revision
postulates `Logic/BeliefRevision/Iterated.lean` proves. A ranking function induces a
plausibility order, hence a preferential consequence relation, and the order is connected, so
the relation satisfies rational monotonicity ([halpern-2003]).

## Main definitions

* `RankingFunction W` — a grading of disbelief `W → ℕ` with a world of grade `0`.
* `RankingFunction.rankSet` — the rank of a proposition, in `ℕ∞`.
* `RankingFunction.aPart` — the A-part of a ranking, the ranking within `A` shifted to `0`.
* `RankingFunction.conditionα` — A,α-conditionalization; `RankingFunction.revise` — revision
  at the canonical firmness; `RankingFunction.lCondition` — the L-conditioning of
  [goldszmidt-pearl-1996].
* `RankingFunction.beliefSet` — the propositions true at every world of rank `0`.
* `RankingFunction.toPlausibilityOrder`, `RankingFunction.toPreferential` — the induced
  plausibility order and preferential consequence relation.

## Main results

* `RankingFunction.rankSet_eq_zero_or_compl`, `RankingFunction.rankSet_union` — of a
  proposition and its negation one has rank `0`; the rank of a disjunction is the smaller rank.
* `RankingFunction.revise_success` — the revised ranking believes the evidence.
* `RankingFunction.ranking_connected`, `RankingFunction.ranking_rationalMonotonicity` — the
  induced order is connected, so rational monotonicity holds.

## References

* [spohn-1988]
* [goldszmidt-pearl-1996]
* [halpern-2003]
* [darwiche-pearl-1997]
-/

open Core.Order (PlausibilityOrder PreferentialConsequence rationalMonotonicity)

/-- A ranking function: a grading of disbelief in worlds with a world of grade `0`. -/
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

/-- The rank of a proposition: the least rank of its worlds, `⊤` for the contradiction. -/
noncomputable def rankSet (A : Set W) : ℕ∞ := ⨅ w ∈ A, (κ.rank w : ℕ∞)

theorem rankSet_le (hw : w ∈ A) : κ.rankSet A ≤ κ.rank w := iInf₂_le w hw

theorem le_rankSet_iff {n : ℕ∞} : n ≤ κ.rankSet A ↔ ∀ w ∈ A, n ≤ κ.rank w := le_iInf₂_iff

theorem rankSet_anti (h : A ⊆ B) : κ.rankSet B ≤ κ.rankSet A :=
  κ.le_rankSet_iff.2 λ _ hw => κ.rankSet_le (h hw)

@[simp] theorem rankSet_empty : κ.rankSet ∅ = ⊤ := by simp [rankSet]

/-- The rank of a satisfiable proposition is attained. -/
theorem exists_rank_eq_rankSet (hA : A.Nonempty) : ∃ w ∈ A, (κ.rank w : ℕ∞) = κ.rankSet A := by
  have hmem := csInf_mem (hA.image λ w => (κ.rank w : ℕ∞))
  rw [sInf_image] at hmem
  exact hmem

theorem rankSet_eq_top_iff : κ.rankSet A = ⊤ ↔ A = ∅ := by
  refine ⟨λ h => by_contra λ hne => ?_, λ h => h ▸ κ.rankSet_empty⟩
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

/-- The A-part `κ(w | A) = κ(w) − κ(A)`: the ranking within `A` shifted so that its best world
has rank `0`. -/
noncomputable def aPart (A : Set W) (w : W) : ℕ := κ.rank w - (κ.rankSet A).toNat

theorem exists_aPart_eq_zero (hA : A.Nonempty) : ∃ w ∈ A, κ.aPart A w = 0 := by
  obtain ⟨w, hw, e⟩ := κ.exists_rank_eq_rankSet hA
  exact ⟨w, hw, by simp [aPart, ← e]⟩

theorem aPart_le (A : Set W) (w : W) : κ.aPart A w ≤ κ.rank w := Nat.sub_le _ _

open Classical in
/-- A,α-conditionalization: the A-part of `κ` on `A` and the Aᶜ-part lifted by the firmness
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
  · exact (le_rankSet_iff _).2 λ v hv => by
      rw [conditionα_of_notMem _ _ _ hv]
      exact_mod_cast Nat.le_add_right _ _

/-- Revision: conditionalization at the firmness `κ(Aᶜ) + 1`, just enough to make `A`
believed; on a contingent proposition it is the operator `BeliefRevision.spohn` of
[darwiche-pearl-1997] (`RankingFunction.revise_rank`). -/
noncomputable def revise (A : Set W) (hA : A.Nonempty) : RankingFunction W :=
  κ.conditionα A hA ((κ.rankSet Aᶜ).toNat + 1)

/-- The belief set: the propositions true at every world of rank `0`. -/
def beliefSet : Set (Set W) := {A | ∀ w, κ.rank w = 0 → w ∈ A}

theorem mem_beliefSet : A ∈ κ.beliefSet ↔ ∀ w, κ.rank w = 0 → w ∈ A := Iff.rfl

/-- The revised ranking believes the evidence, the AGM success postulate. -/
theorem revise_success (hA : A.Nonempty) : A ∈ (κ.revise A hA).beliefSet := λ w hw => by
  by_contra hnot
  rw [revise, conditionα_of_notMem _ _ _ hnot] at hw
  omega

open Classical in
/-- L-conditioning ([goldszmidt-pearl-1996]): lift the worlds outside `A` by `l`, at a ranking
holding `A` possible. Unlike `conditionα`, it commutes. -/
noncomputable def lCondition (A : Set W) (h0 : ∃ w ∈ A, κ.rank w = 0) (l : ℕ) :
    RankingFunction W where
  rank w := if w ∈ A then κ.rank w else κ.rank w + l
  normalized := let ⟨w, hw, hr⟩ := h0; ⟨w, by simp [hw, hr]⟩

/-! ### The induced plausibility order -/

/-- The plausibility order of a ranking function: `w` is at least as plausible as `v` when its
rank is at most that of `v`. Smoothness holds because `ℕ` is well-ordered. -/
def toPlausibilityOrder : PlausibilityOrder W where
  toPreorder := Preorder.lift κ.rank
  smooth := λ φ w hφw => by
    classical
    show ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧
      ∀ u, φ u → κ.rank u ≤ κ.rank v → κ.rank v ≤ κ.rank u
    have hex : ∃ n, ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧ κ.rank v = n := ⟨_, w, hφw, le_rfl, rfl⟩
    obtain ⟨v, hφv, hvw, hvrank⟩ := Nat.find_spec hex
    refine ⟨v, hφv, hvw, λ u hφu huv => ?_⟩
    by_contra h
    push Not at h
    exact Nat.find_min hex (hvrank ▸ h) ⟨u, hφu, huv.trans hvw, rfl⟩

/-- The preferential consequence relation of a ranking function. -/
def toPreferential : PreferentialConsequence W := κ.toPlausibilityOrder.toPreferential

/-- The plausibility order of a ranking function is connected: any two worlds are comparable,
because `ℕ` is linearly ordered. -/
theorem ranking_connected : Core.Order.Normality.connected κ.toPlausibilityOrder.toPreorder :=
  λ w v => le_total (κ.rank w) (κ.rank v)

/-- Ranking functions satisfy rational monotonicity: the connected order makes every minimal
`φ ∧ ψ`-world minimal among the `φ`-worlds once some minimal `φ`-world satisfies `ψ`. -/
theorem ranking_rationalMonotonicity : rationalMonotonicity κ.toPreferential := by
  intro φ ψ χ hφχ hnotφψ w ⟨⟨hφw, hψw⟩, hmin⟩
  refine hφχ w ⟨hφw, λ v hφv hvw => ?_⟩
  obtain ⟨u, hu⟩ := Classical.not_forall.mp hnotφψ
  obtain ⟨⟨hφu, hminu⟩, hψu⟩ := Classical.not_imp.mp hu
  have hψu : ψ u := Classical.not_not.mp hψu
  have hvw' : κ.rank v ≤ κ.rank w := hvw
  have huv : κ.rank u ≤ κ.rank v := by
    by_contra h
    exact h (hminu v hφv (Nat.le_of_lt (not_le.mp h)))
  have hwu : κ.rank w ≤ κ.rank u := hmin u ⟨hφu, hψu⟩ (huv.trans hvw')
  exact hwu.trans huv

end RankingFunction
