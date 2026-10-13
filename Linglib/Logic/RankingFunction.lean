module

public import Linglib.Logic.Nonmonotonic.Preferential
public import Mathlib.Data.ENat.Lattice

/-!
# Ranking functions

This file defines ranking functions, Spohn's ordinal conditional functions with natural-number
grades, their conditionalization, and the consequence relation they induce.

A ranking function grades the disbelief in each world, and some world has grade `0`. The rank of
a proposition is the least rank of its worlds, and `⊤` for the contradiction, so of a proposition
and its negation one has rank `0`, and the rank of a disjunction is the smaller of the two ranks.
The rank of `B` given `A` is `κ(A ∩ B) − κ(A)`, and `⊤` when `A` is impossible, so the rank
of an intersection is a rank plus a conditional rank, which gives the chain rule and Bayes' rule
for ranks. Conditionalization on a proposition at a firmness keeps the ranking within the
proposition and within its negation, each shifted to start at `0`, and lifts the negation by the
firmness. It keeps the ranks given the proposition and given its negation, so it ranks every
proposition by Jeffrey's rule.

A ranking function orders the worlds by rank, which makes it a ranked model in the sense of
Lehmann and Magidor. A proposition `B` follows from `A` when the `A`-worlds of least rank are
`B`-worlds, equivalently when `Bᶜ` has positive rank given `A`. This consequence relation is
rational, and the beliefs of the ranking function, the propositions true at every world of rank
`0`, are the consequences of the tautology.

## Main definitions

* `RankingFunction W`: a grading of disbelief `W → ℕ` with a world of grade `0`.
* `RankingFunction.rank`: the rank of a proposition, in `ℕ∞`.
* `RankingFunction.condRank`: the rank of a proposition given another.
* `RankingFunction.aPart`, `RankingFunction.conditionα`: the ranking within a proposition, and
  conditionalization on a proposition at a firmness.
* `RankingFunction.Entails`: the consequence relation of the ranked model.

## Main statements

* `RankingFunction.rank_eq_zero_or_compl`, `RankingFunction.rank_union`: of a proposition
  and its negation one has rank `0`, and the rank of a disjunction is the smaller rank.
* `RankingFunction.rank_conditionα_eq`: conditionalization follows Jeffrey's rule.
* `RankingFunction.entails_iff_condRank`: a consequence is a proposition whose negation has
  positive rank given the premise.
* `RankingFunction.isRational_entails`: the consequence relation is rational.

## Notation

* `κ[B | A]` for `κ.condRank A B`, the rank of `B` given `A`, in the scope `RankingFunction`.

## References

* [W. Spohn, *Ordinal Conditional Functions: A Dynamic Theory of Epistemic States*
  (1988)][spohn-1988]
* [M. Goldszmidt and J. Pearl, *Qualitative Probabilities for Default Reasoning, Belief
  Revision, and Causal Modeling* (1996)][goldszmidt-pearl-1996]
* [D. Lehmann and M. Magidor, *What Does a Conditional Knowledge Base Entail?*
  (1992)][lehmann-magidor-1992]
* [J. Y. Halpern, *Reasoning about Uncertainty* (2003)][halpern-2003]
-/

@[expose] public section

/-- A ranking function is a grading of disbelief in worlds under which some world has grade
`0`. -/
structure RankingFunction (W : Type*) where
  /-- The grade of disbelief in each world. Apply the ranking function itself, `κ w`. -/
  toFun : W → ℕ
  /-- Some world is not disbelieved. Use the lemma `exists_eq_zero`. -/
  exists_eq_zero' : ∃ w, toFun w = 0

namespace RankingFunction

variable {W : Type*}

instance : FunLike (RankingFunction W) W ℕ where
  coe := toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp] theorem coe_mk (f : W → ℕ) (h) : ⇑(⟨f, h⟩ : RankingFunction W) = f := rfl

@[ext] theorem ext {κ κ' : RankingFunction W} (h : ∀ w, κ w = κ' w) : κ = κ' :=
  DFunLike.ext κ κ' h

variable (κ : RankingFunction W) {A B : Set W} {w : W}

theorem exists_eq_zero : ∃ w, κ w = 0 := κ.exists_eq_zero'

/-- Ranking functions whose grades differ by a constant are equal. -/
theorem eq_of_forall_add_eq_add {κ κ' : RankingFunction W} {c c' : ℕ}
    (h : ∀ w, κ w + c = κ' w + c') : κ = κ' := by
  obtain ⟨w, hw⟩ := κ.exists_eq_zero
  obtain ⟨w', hw'⟩ := κ'.exists_eq_zero
  have := h w
  have := h w'
  ext v
  have := h v
  omega

/-! ### Ranks of propositions -/

/-- The rank of a proposition is the least rank of its worlds, and `⊤` for the contradiction. -/
noncomputable def rank (A : Set W) : ℕ∞ := ⨅ w ∈ A, (κ w : ℕ∞)

theorem rank_le (hw : w ∈ A) : κ.rank A ≤ κ w := iInf₂_le w hw

theorem le_rank_iff {n : ℕ∞} : n ≤ κ.rank A ↔ ∀ w ∈ A, n ≤ κ w := le_iInf₂_iff

theorem rank_eq_of_forall_le (hw : w ∈ A) (h : ∀ v ∈ A, κ w ≤ κ v) : κ.rank A = κ w :=
  le_antisymm (κ.rank_le hw) (κ.le_rank_iff.2 fun v hv ↦ by exact_mod_cast h v hv)

theorem rank_anti (h : A ⊆ B) : κ.rank B ≤ κ.rank A :=
  κ.le_rank_iff.2 fun _ hw ↦ κ.rank_le (h hw)

@[simp] theorem rank_empty : κ.rank ∅ = ⊤ := by simp [rank]

/-- The rank of a satisfiable proposition is attained. -/
theorem exists_apply_eq_rank (hA : A.Nonempty) : ∃ w ∈ A, (κ w : ℕ∞) = κ.rank A := by
  have hmem := csInf_mem (hA.image fun w ↦ (κ w : ℕ∞))
  rw [sInf_image] at hmem
  exact hmem

theorem rank_eq_top_iff : κ.rank A = ⊤ ↔ A = ∅ := by
  simp [rank, Set.eq_empty_iff_forall_notMem]

theorem rank_ne_top (hA : A.Nonempty) : κ.rank A ≠ ⊤ :=
  mt κ.rank_eq_top_iff.1 hA.ne_empty

/-- The rank of a disjunction is the smaller rank. -/
theorem rank_union (A B : Set W) : κ.rank (A ∪ B) = min (κ.rank A) (κ.rank B) :=
  iInf_union

theorem rank_eq_zero_iff : κ.rank A = 0 ↔ ∃ w ∈ A, κ w = 0 := by
  simp [rank]

@[simp] theorem rank_univ : κ.rank Set.univ = 0 :=
  κ.rank_eq_zero_iff.2 (let ⟨w, hw⟩ := κ.exists_eq_zero; ⟨w, trivial, hw⟩)

/-- Of a proposition and its negation, one has rank `0`. -/
theorem rank_eq_zero_or_compl (A : Set W) : κ.rank A = 0 ∨ κ.rank Aᶜ = 0 := by
  have h := κ.rank_univ
  rw [← Set.union_compl_self A, rank_union] at h
  exact (min_eq_iff.1 h).imp And.left And.left

theorem toNat_rank_le (hw : w ∈ A) : (κ.rank A).toNat ≤ κ w :=
  ENat.toNat_le_of_le_natCast (κ.rank_le hw)

/-! ### Conditional ranks -/

/-- The rank of `B` given `A` is `κ(B | A) = κ(A ∩ B) − κ(A)`, and `⊤` when `A` is
impossible. -/
noncomputable def condRank (A B : Set W) : ℕ∞ :=
  if κ.rank A = ⊤ then ⊤ else κ.rank (A ∩ B) - κ.rank A

@[inherit_doc condRank]
scoped macro:max κ:term noWs "[" B:term " | " A:term "]" : term =>
  `(RankingFunction.condRank $κ $A $B)

/-- Unexpander for the `κ[B | A]` notation. -/
@[app_unexpander RankingFunction.condRank]
meta def condRankUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $κ $A $B) => `($κ[$B | $A])
  | _ => throw ()

theorem condRank_of_ne_top (hA : κ.rank A ≠ ⊤) :
    κ[B | A] = κ.rank (A ∩ B) - κ.rank A := by
  simp [condRank, hA]

theorem condRank_of_eq_top (hA : κ.rank A = ⊤) : κ[B | A] = ⊤ := by
  simp [condRank, hA]

/-- The rank of `A ∩ B` is the rank of `A` plus the rank of `B` given `A`. -/
theorem condRank_add_rank (A B : Set W) :
    κ[B | A] + κ.rank A = κ.rank (A ∩ B) := by
  by_cases hA : κ.rank A = ⊤
  · rw [hA, add_top]
    exact (top_le_iff.1 (hA ▸ κ.rank_anti Set.inter_subset_left)).symm
  · rw [condRank_of_ne_top _ hA, tsub_add_cancel_of_le (κ.rank_anti Set.inter_subset_left)]

@[simp] theorem condRank_univ (B : Set W) : κ[B | Set.univ] = κ.rank B := by
  simp [condRank]

@[simp] theorem condRank_empty (A : Set W) : κ[∅ | A] = ⊤ := by
  by_cases hA : κ.rank A = ⊤ <;> simp [condRank, hA]

theorem condRank_self (hA : κ.rank A ≠ ⊤) : κ[A | A] = 0 := by
  simp [condRank_of_ne_top _ hA]

theorem condRank_eq_top_iff (hA : κ.rank A ≠ ⊤) :
    κ[B | A] = ⊤ ↔ κ.rank (A ∩ B) = ⊤ := by
  simp [condRank_of_ne_top _ hA, hA]

/-- The rank of a disjunction given `A` is the smaller of the two ranks given `A`. -/
theorem condRank_union (A B C : Set W) :
    κ[B ∪ C | A] = min κ[B | A] κ[C | A] := by
  by_cases hA : κ.rank A = ⊤
  · simp [condRank_of_eq_top _ hA]
  · simp only [condRank_of_ne_top _ hA, Set.inter_union_distrib_left, rank_union]
    exact Monotone.map_min (f := fun x : ℕ∞ ↦ x - κ.rank A) fun _ _ h ↦ tsub_le_tsub_right h _

/-- The rank of `B ∩ C` given `A` is the rank of `B` given `A` plus the rank of `C` given
`A ∩ B`. -/
theorem condRank_inter (A B C : Set W) :
    κ[B ∩ C | A] = κ[B | A] + κ[C | A ∩ B] := by
  by_cases hA : κ.rank A = ⊤
  · simp [condRank_of_eq_top _ hA]
  · have h := κ.condRank_add_rank A (B ∩ C)
    rw [← Set.inter_assoc, ← κ.condRank_add_rank (A ∩ B) C, ← κ.condRank_add_rank A B,
      ← add_assoc, add_comm κ[C | A ∩ B]] at h
    exact WithTop.add_right_cancel hA h

/-- Bayes' rule for ranks. -/
theorem condRank_eq_condRank_add_sub (hA : κ.rank A ≠ ⊤) :
    κ[B | A] = κ[A | B] + κ.rank B - κ.rank A := by
  rw [condRank_add_rank, Set.inter_comm, condRank_of_ne_top _ hA]

/-! ### Conditionalization -/

/-- The A-part `κ(w | A) = κ(w) − κ(A)` of a ranking is the ranking within `A`, shifted so that
its best world has rank `0`. -/
noncomputable def aPart (A : Set W) (w : W) : ℕ := κ w - (κ.rank A).toNat

/-- The A-part of a world of `A` is its rank given `A`. -/
theorem condRank_singleton (hw : w ∈ A) : κ[{w} | A] = κ.aPart A w := by
  have hA := κ.rank_ne_top ⟨w, hw⟩
  rw [condRank_of_ne_top _ hA, Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hw),
    κ.rank_eq_of_forall_le (Set.mem_singleton w) (by simp), ← ENat.natCast_toNat hA,
    ← ENat.natCast_sub, aPart]

theorem exists_aPart_eq_zero (hA : A.Nonempty) : ∃ w ∈ A, κ.aPart A w = 0 := by
  obtain ⟨w, hw, e⟩ := κ.exists_apply_eq_rank hA
  exact ⟨w, hw, by simp [aPart, ← e]⟩

open Classical in
/-- The A,α-conditionalization of `κ` is its A-part on `A` and its Aᶜ-part lifted by the firmness
`α` on `Aᶜ`, so that `A` comes to be believed with firmness `α`. -/
noncomputable def conditionα (A : Set W) (hA : A.Nonempty) (α : ℕ) : RankingFunction W where
  toFun w := if w ∈ A then κ.aPart A w else α + κ.aPart Aᶜ w
  exists_eq_zero' := let ⟨w, hw, h0⟩ := κ.exists_aPart_eq_zero hA; ⟨w, by simp [hw, h0]⟩

theorem conditionα_of_mem (hA : A.Nonempty) (α : ℕ) (hw : w ∈ A) :
    κ.conditionα A hA α w = κ.aPart A w := by
  simp [conditionα, hw]

theorem conditionα_of_notMem (hA : A.Nonempty) (α : ℕ) (hw : w ∉ A) :
    κ.conditionα A hA α w = α + κ.aPart Aᶜ w := by
  simp [conditionα, hw]

/-- The conditionalized ranking holds `A` possible. -/
@[simp] theorem rank_conditionα (hA : A.Nonempty) (α : ℕ) :
    (κ.conditionα A hA α).rank A = 0 := by
  obtain ⟨w, hw, h0⟩ := κ.exists_aPart_eq_zero hA
  exact (rank_eq_zero_iff _).2 ⟨w, hw, by rw [conditionα_of_mem _ _ _ hw, h0]⟩

/-- The conditionalized ranking believes `A` with firmness `α`. -/
theorem rank_conditionα_compl (hA : A.Nonempty) (hA' : Aᶜ.Nonempty) (α : ℕ) :
    (κ.conditionα A hA α).rank Aᶜ = α := by
  obtain ⟨w, hw, h0⟩ := κ.exists_aPart_eq_zero hA'
  refine le_antisymm (((κ.conditionα A hA α).rank_le hw).trans ?_) ?_
  · rw [conditionα_of_notMem _ _ _ hw, h0, add_zero]
  · exact (le_rank_iff _).2 fun v hv ↦ by
      rw [conditionα_of_notMem _ _ _ hv]
      exact_mod_cast Nat.le_add_right _ _

/-- Within `A`, the conditionalized ranking ranks each proposition by its rank given `A`. -/
theorem rank_conditionα_of_subset {S : Set W} (hA : A.Nonempty) (α : ℕ) (hS : S ⊆ A) :
    (κ.conditionα A hA α).rank S = κ.rank S - κ.rank A := by
  have hA' := κ.rank_ne_top hA
  rcases S.eq_empty_or_nonempty with rfl | hS'
  · rw [rank_empty, rank_empty]
    exact (ENat.sub_eq_top_iff.2 ⟨rfl, hA'⟩).symm
  obtain ⟨u, hu, e⟩ := κ.exists_apply_eq_rank hS'
  rw [(κ.conditionα A hA α).rank_eq_of_forall_le hu fun v hv ↦ ?_,
    conditionα_of_mem _ _ _ (hS hu), aPart, ENat.natCast_sub, e, ENat.natCast_toNat hA']
  have : (κ u : ℕ∞) ≤ κ v := e ▸ κ.rank_le hv
  rw [conditionα_of_mem _ _ _ (hS hu), conditionα_of_mem _ _ _ (hS hv)]
  exact Nat.sub_le_sub_right (by exact_mod_cast this) _

/-- Outside `A`, the conditionalized ranking ranks each proposition by the firmness plus its
rank given `Aᶜ`. -/
theorem rank_conditionα_of_subset_compl {S : Set W} (hA : A.Nonempty) (hA' : Aᶜ.Nonempty)
    (α : ℕ) (hS : S ⊆ Aᶜ) :
    (κ.conditionα A hA α).rank S = α + (κ.rank S - κ.rank Aᶜ) := by
  have hA'' := κ.rank_ne_top hA'
  rcases S.eq_empty_or_nonempty with rfl | hS'
  · rw [rank_empty, rank_empty, ENat.sub_eq_top_iff.2 ⟨rfl, hA''⟩, add_top]
  obtain ⟨u, hu, e⟩ := κ.exists_apply_eq_rank hS'
  rw [(κ.conditionα A hA α).rank_eq_of_forall_le hu fun v hv ↦ ?_,
    conditionα_of_notMem _ _ _ (hS hu), aPart, Nat.cast_add, ENat.natCast_sub, e,
    ENat.natCast_toNat hA'']
  have : (κ u : ℕ∞) ≤ κ v := e ▸ κ.rank_le hv
  rw [conditionα_of_notMem _ _ _ (hS hu), conditionα_of_notMem _ _ _ (hS hv)]
  exact Nat.add_le_add_left (Nat.sub_le_sub_right (by exact_mod_cast this) _) _

/-- Conditionalization on `A` leaves the ranks given `A` unchanged. -/
theorem condRank_conditionα (hA : A.Nonempty) (α : ℕ) (B : Set W) :
    (κ.conditionα A hA α)[B | A] = κ[B | A] := by
  rw [condRank_of_ne_top _ (by simp), rank_conditionα, tsub_zero,
    rank_conditionα_of_subset _ _ _ Set.inter_subset_left,
    condRank_of_ne_top _ (κ.rank_ne_top hA)]

/-- Conditionalization on `A` leaves the ranks given `Aᶜ` unchanged. -/
theorem condRank_conditionα_compl (hA : A.Nonempty) (hA' : Aᶜ.Nonempty) (α : ℕ) (B : Set W) :
    (κ.conditionα A hA α)[B | Aᶜ] = κ[B | Aᶜ] := by
  rw [condRank_of_ne_top _ (by rw [rank_conditionα_compl _ hA hA']; exact ENat.natCast_ne_top α),
    rank_conditionα_compl _ hA hA', rank_conditionα_of_subset_compl _ hA hA' _
      Set.inter_subset_left, (ENat.addLECancellable_natCast α).add_tsub_cancel_left,
    condRank_of_ne_top _ (κ.rank_ne_top hA')]

/-- After conditionalization on `A` at firmness `α`, a proposition's rank is the smaller of its
rank given `A` and its rank given `Aᶜ` plus `α`, which is Jeffrey's rule in ranks. -/
theorem rank_conditionα_eq (hA : A.Nonempty) (hA' : Aᶜ.Nonempty) (α : ℕ) (B : Set W) :
    (κ.conditionα A hA α).rank B = min κ[B | A] (κ[B | Aᶜ] + α) := by
  have h₁ := (κ.conditionα A hA α).condRank_add_rank A B
  have h₂ := (κ.conditionα A hA α).condRank_add_rank Aᶜ B
  rw [condRank_conditionα, rank_conditionα, add_zero] at h₁
  rw [condRank_conditionα_compl _ hA hA', rank_conditionα_compl _ hA hA'] at h₂
  rw [h₁, h₂, ← rank_union, ← Set.union_inter_distrib_right, Set.union_compl_self,
    Set.univ_inter]

/-! ### The induced consequence relation -/

/-- In the normality order of a ranking function, `w` is at least as normal as `v` when its rank
is at most that of `v`. -/
@[reducible] def toPreorder : Preorder W := Preorder.lift κ

theorem wellFounded_toPreorder_lt : WellFounded κ.toPreorder.lt := InvImage.wf κ wellFounded_lt

theorem total_toPreorder : Std.Total κ.toPreorder.le := ⟨fun w v ↦ le_total (κ w) (κ v)⟩

/-- The minimal worlds of a proposition are its worlds of least rank. -/
theorem mem_minimals_toPreorder :
    w ∈ κ.toPreorder.minimals A ↔ w ∈ A ∧ ∀ v ∈ A, κ w ≤ κ v :=
  Preorder.mem_minimals_iff_forall_le κ.total_toPreorder

/-- `B` follows from `A` in `κ` when the `A`-worlds of least rank are `B`-worlds. This is the
consequence relation of the ranked model `κ.toPreorder`. -/
def Entails (A B : Set W) : Prop := Nonmonotonic.Entails κ.toPreorder A B

theorem entails_iff_forall_least :
    κ.Entails A B ↔ ∀ w ∈ A, (∀ v ∈ A, κ w ≤ κ v) → w ∈ B :=
  ⟨fun h _ hw hmin ↦ h (κ.mem_minimals_toPreorder.2 ⟨hw, hmin⟩),
    fun h w hw ↦ have := κ.mem_minimals_toPreorder.1 hw; h w this.1 this.2⟩

/-- `B` follows from `A` exactly when every `A`-world outside `B` is outranked by an `A`-world
in `B`. -/
theorem entails_iff_exists_lt :
    κ.Entails A B ↔ ∀ x ∈ A, x ∉ B → ∃ y ∈ A, y ∈ B ∧ κ y < κ x := by
  refine ⟨fun h x hx hxB ↦ ?_, fun h w hw ↦ by_contra fun hwB ↦ ?_⟩
  · obtain ⟨y, hy, hyx⟩ := Preorder.exists_le_mem_minimals κ.wellFounded_toPreorder_lt hx
    refine ⟨y, hy.1, h hy, lt_of_le_of_ne hyx fun e ↦ hxB (h ?_)⟩
    exact κ.mem_minimals_toPreorder.2
      ⟨hx, fun v hv ↦ e ▸ (κ.mem_minimals_toPreorder.1 hy).2 v hv⟩
  · obtain ⟨y, hy, -, hlt⟩ := h w hw.1 hwB
    exact absurd ((κ.mem_minimals_toPreorder.1 hw).2 y hy) (not_le.2 hlt)

/-- `B` follows from `A` exactly when `A` is impossible or `A ∩ B` is less disbelieved than
`A \ B`. -/
theorem entails_iff_rank :
    κ.Entails A B ↔ κ.rank A = ⊤ ∨ κ.rank (A ∩ B) < κ.rank (A \ B) := by
  rw [entails_iff_exists_lt]
  constructor
  · intro h
    rcases A.eq_empty_or_nonempty with rfl | hA
    · exact Or.inl κ.rank_empty
    rcases (A \ B).eq_empty_or_nonempty with he | hne
    · have hAB : A ∩ B = A := Set.inter_eq_left.2 (Set.sdiff_eq_empty.1 he)
      exact Or.inr (by rw [he, hAB, rank_empty]; exact (κ.rank_ne_top hA).lt_top)
    · obtain ⟨x, hx, e⟩ := κ.exists_apply_eq_rank hne
      obtain ⟨y, hyA, hyB, hlt⟩ := h x hx.1 hx.2
      refine Or.inr ((κ.rank_le (A := A ∩ B) ⟨hyA, hyB⟩).trans_lt ?_)
      rw [← e]
      exact_mod_cast hlt
  · rintro (hA | hlt) x hx hxB
    · exact absurd (κ.rank_eq_top_iff.1 hA ▸ hx) (Set.notMem_empty x)
    · have hne : (A ∩ B).Nonempty := Set.nonempty_iff_ne_empty.2 fun he ↦ by simp [he] at hlt
      obtain ⟨y, hy, e⟩ := κ.exists_apply_eq_rank hne
      have hxr := κ.rank_le (A := A \ B) ⟨hx, hxB⟩
      exact ⟨y, hy.1, hy.2, by exact_mod_cast e ▸ hlt.trans_le hxr⟩

/-- `B` follows from `A` exactly when `Bᶜ` has positive rank given `A`. -/
theorem entails_iff_condRank : κ.Entails A B ↔ 0 < κ[Bᶜ | A] := by
  rw [entails_iff_rank]
  by_cases hA : κ.rank A = ⊤
  · simp [hA, condRank_of_eq_top _ hA]
  · have h := κ.rank_union (A ∩ B) (A \ B)
    rw [Set.inter_union_sdiff] at h
    rw [condRank_of_ne_top _ hA, tsub_pos_iff_lt, ← Set.sdiff_eq, or_iff_right hA, h,
      min_lt_iff, lt_self_iff_false, or_false]

instance [Fintype W] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    Decidable (κ.Entails A B) :=
  decidable_of_iff _ κ.entails_iff_exists_lt.symm

/-- The consequence relation of a ranking function is rational. -/
theorem isRational_entails : Nonmonotonic.IsRational κ.Entails :=
  Nonmonotonic.isRational_entails κ.wellFounded_toPreorder_lt κ.total_toPreorder

/-- The beliefs, the consequences of the tautology, are the propositions true at every world of
rank `0`. -/
theorem entails_univ_iff : κ.Entails Set.univ A ↔ ∀ w, κ w = 0 → w ∈ A := by
  rw [entails_iff_forall_least]
  refine ⟨fun h w hw ↦ h w trivial fun v _ ↦ hw ▸ Nat.zero_le _, fun h w _ hmin ↦ h w ?_⟩
  obtain ⟨w₀, hw₀⟩ := κ.exists_eq_zero
  exact Nat.le_zero.1 (hw₀ ▸ hmin w₀ trivial)

end RankingFunction
