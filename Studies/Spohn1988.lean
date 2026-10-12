module

public import Linglib.Logic.RankingFunction
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Spohn (1988): Ordinal Conditional Functions: A Dynamic Theory of Epistemic States

This file formalizes the theory of ordinal conditional functions of [spohn-1988] with
natural-number grades, the paper's Note 16, on the ranking functions of
`Logic/RankingFunction.lean`. Conditionalization on a proposition at a firmness is reversible:
conditionalizing again on the proposition at the firmness with which it was believed restores
the ranking, whether the first change conditionalized on the proposition or on its negation
(`conditionα_conditionα`, `conditionα_compl_conditionα`); and two conditionalizations commute
when the three cells they distinguish other than the joint negation have rank zero
(`conditionα_comm`). Generalized conditionalization by a ranking on the atoms of a subfield,
the deterministic counterpart of Jeffrey conditionalization, has conditionalization on a
proposition as its two-atom case (`condition_firmness`) and is reversed by conditionalizing on
the coarsening of the original ranking to the subfield (`condition_condition_coarsen`).

Independence of two subfields, the rank of an intersection of atoms being the sum of the ranks,
extends from atoms to all members of the fields (`Independent.rankSet_inter`), and it is
equivalent to conditional ranks being unconditional ranks and to the ranks of one field being
invariant under generalized conditionalization on the other (`independent_iff_condRank`,
`independent_iff_condition`). Conditional independence given a subfield satisfies the
contraction law of the paper's Theorem 11 and its mirror image (`CondIndependentOn.inf`,
`CondIndependentOn.inf'`).

## Implementation notes

Complete subfields of the propositions over a set of worlds are partitions, `Setoid W`: the
atoms are the cells, the members are the propositions the partition decides, and the field two
subfields generate is their meet in the lattice of setoids. Over natural numbers every two
firmnesses commute and independence is symmetric, so the paper's two directions of
independence coincide. Simple conditional functions and well-ordered partitions with their
representation theorem, the independence of sequences of subfields, Theorem 13, whose
conclusion conditions on the intersection of two subfields, and the nonstandard-probability
homomorphism of Section 7 are not formalized.

## References

* [spohn-1988]
* [goldszmidt-pearl-1996]
-/

@[expose] public section

namespace Spohn1988

open RankingFunction Setoid

variable {W : Type*} (κ : RankingFunction W)

/-! ### Reversibility and commutativity of conditionalization -/

section Conditionalization

variable {A B : Set W} (hA : A.Nonempty) (hB : B.Nonempty)

theorem toNat_rankSet_eq_zero (h : κ.rankSet A = 0) : (κ.rankSet A).toNat = 0 := by
  rw [h]; rfl

/-- Theorem 3, first half: after conditionalizing on `A` at any firmness, conditionalizing on
`A` at the firmness with which `A` was believed restores the ranking. -/
theorem conditionα_conditionα (h0 : κ.rankSet A = 0) (α : ℕ) :
    (κ.conditionα A hA α).conditionα A hA (κ.rankSet Aᶜ).toNat = κ := by
  ext w
  by_cases hw : w ∈ A
  · rw [conditionα_of_mem _ _ _ hw, aPart, conditionα_of_mem _ _ _ hw, aPart,
      toNat_rankSet_eq_zero _ h0, toNat_rankSet_eq_zero _ (κ.rankSet_conditionα hA α)]
    rfl
  · rcases Set.eq_empty_or_nonempty Aᶜ with hA' | hA'
    · have hw' : w ∈ Aᶜ := hw
      rw [hA'] at hw'
      exact hw'.elim
    have := κ.toNat_rankSet_le (A := Aᶜ) hw
    rw [conditionα_of_notMem _ _ _ hw, aPart, conditionα_of_notMem _ _ _ hw, aPart,
      κ.rankSet_conditionα_compl hA hA', ENat.toNat_natCast]
    omega

/-- Theorem 3, second half: after conditionalizing on the negation of `A` at any firmness,
conditionalizing on `A` at the firmness with which `A` was believed restores the ranking. -/
theorem conditionα_compl_conditionα (hA' : Aᶜ.Nonempty) (h0 : κ.rankSet A = 0) (α : ℕ) :
    (κ.conditionα Aᶜ hA' α).conditionα A hA (κ.rankSet Aᶜ).toNat = κ := by
  have hAc : (κ.conditionα Aᶜ hA' α).rankSet A = α := by
    have := κ.rankSet_conditionα_compl hA' (by rwa [compl_compl]) α
    rwa [compl_compl] at this
  ext w
  by_cases hw : w ∈ A
  · have hw' : w ∉ Aᶜ := λ h => h hw
    rw [conditionα_of_mem _ _ _ hw, aPart, conditionα_of_notMem _ _ _ hw', aPart, compl_compl,
      toNat_rankSet_eq_zero _ h0, hAc, ENat.toNat_natCast]
    omega
  · have hw' : w ∈ Aᶜ := hw
    have := κ.toNat_rankSet_le (A := Aᶜ) hw'
    rw [conditionα_of_notMem _ _ _ hw, aPart, conditionα_of_mem _ _ _ hw', aPart,
      toNat_rankSet_eq_zero _ (κ.rankSet_conditionα hA' α)]
    omega

/-- Theorem 4: conditionalizations on `A` and on `B` commute when the cells `A ∩ B`,
`A ∩ Bᶜ` and `Aᶜ ∩ B` all have rank zero. -/
theorem conditionα_comm (hAB : κ.rankSet (A ∩ B) = 0) (hAB' : κ.rankSet (A ∩ Bᶜ) = 0)
    (hA'B : κ.rankSet (Aᶜ ∩ B) = 0) (α β : ℕ) :
    (κ.conditionα A hA α).conditionα B hB β = (κ.conditionα B hB β).conditionα A hA α := by
  classical
  have zero_of_le : ∀ {S T : Set W}, S ⊆ T → κ.rankSet S = 0 → κ.rankSet T = 0 := λ h hS =>
    le_antisymm (hS ▸ κ.rankSet_anti h) bot_le
  have hA0 := zero_of_le Set.inter_subset_left hAB
  have hB0 := zero_of_le Set.inter_subset_right hAB
  have hA'0 := zero_of_le Set.inter_subset_left hA'B
  have hB'0 := zero_of_le Set.inter_subset_right hAB'
  obtain ⟨u, ⟨huA, huB⟩, hu⟩ := κ.rankSet_eq_zero_iff.1 hAB
  obtain ⟨u', ⟨hu'A, hu'B⟩, hu'⟩ := κ.rankSet_eq_zero_iff.1 hAB'
  obtain ⟨u'', ⟨hu''A, hu''B⟩, hu''⟩ := κ.rankSet_eq_zero_iff.1 hA'B
  have h1 : ∀ w, (κ.conditionα A hA α).rank w = if w ∈ A then κ.rank w else α + κ.rank w :=
    λ w => by
      by_cases hw : w ∈ A
      · rw [conditionα_of_mem _ _ _ hw, aPart, toNat_rankSet_eq_zero _ hA0, ite_eq_left hw]; rfl
      · rw [conditionα_of_notMem _ _ _ hw, aPart, toNat_rankSet_eq_zero _ hA'0, ite_eq_right hw]; rfl
  have h2 : ∀ w, (κ.conditionα B hB β).rank w = if w ∈ B then κ.rank w else β + κ.rank w :=
    λ w => by
      by_cases hw : w ∈ B
      · rw [conditionα_of_mem _ _ _ hw, aPart, toNat_rankSet_eq_zero _ hB0, ite_eq_left hw]; rfl
      · rw [conditionα_of_notMem _ _ _ hw, aPart, toNat_rankSet_eq_zero _ hB'0, ite_eq_right hw]; rfl
  have h1B : (κ.conditionα A hA α).rankSet B = 0 :=
    (rankSet_eq_zero_iff _).2 ⟨u, huB, by rw [h1, ite_eq_left huA, hu]⟩
  have h1B' : (κ.conditionα A hA α).rankSet Bᶜ = 0 :=
    (rankSet_eq_zero_iff _).2 ⟨u', hu'B, by rw [h1, ite_eq_left hu'A, hu']⟩
  have h2A : (κ.conditionα B hB β).rankSet A = 0 :=
    (rankSet_eq_zero_iff _).2 ⟨u, huA, by rw [h2, ite_eq_left huB, hu]⟩
  have h2A' : (κ.conditionα B hB β).rankSet Aᶜ = 0 :=
    (rankSet_eq_zero_iff _).2 ⟨u'', hu''A, by rw [h2, ite_eq_left hu''B, hu'']⟩
  have L : ∀ w, ((κ.conditionα A hA α).conditionα B hB β).rank w =
      (if w ∈ B then 0 else β) + (if w ∈ A then 0 else α) + κ.rank w := λ w => by
    by_cases hwB : w ∈ B
    · rw [conditionα_of_mem _ _ _ hwB, aPart, h1 w, toNat_rankSet_eq_zero _ h1B, ite_eq_left hwB]
      split_ifs <;> omega
    · rw [conditionα_of_notMem _ _ _ hwB, aPart, h1 w, toNat_rankSet_eq_zero _ h1B', ite_eq_right hwB]
      split_ifs <;> omega
  have R : ∀ w, ((κ.conditionα B hB β).conditionα A hA α).rank w =
      (if w ∈ A then 0 else α) + (if w ∈ B then 0 else β) + κ.rank w := λ w => by
    by_cases hwA : w ∈ A
    · rw [conditionα_of_mem _ _ _ hwA, aPart, h2 w, toNat_rankSet_eq_zero _ h2A, ite_eq_left hwA]
      split_ifs <;> omega
    · rw [conditionα_of_notMem _ _ _ hwA, aPart, h2 w, toNat_rankSet_eq_zero _ h2A', ite_eq_right hwA]
      split_ifs <;> omega
  ext w
  rw [L, R]
  split_ifs <;> omega

end Conditionalization

/-! ### Generalized conditionalization -/

section Generalized

variable (𝔅 : Setoid W)

theorem cell_nonempty (w : W) : (𝔅.cell w).Nonempty := ⟨w, 𝔅.mem_cell_self w⟩

theorem cell_inf (ℭ : Setoid W) (w : W) : (𝔅 ⊓ ℭ).cell w = 𝔅.cell w ∩ ℭ.cell w := by
  ext v
  simp only [Set.mem_inter_iff, mem_cell]
  exact Setoid.inf_iff_and

/-- Definition 7: the conditionalization of `κ` by a ranking `l` on the atoms of a subfield,
each world's rank being the rank of its atom under `l` plus its rank within the atom. -/
noncomputable def condition (l : RankingFunction (Quotient 𝔅)) : RankingFunction W where
  rank w := l.rank (Quotient.mk 𝔅 w) + κ.aPart (𝔅.cell w) w
  normalized := by
    obtain ⟨b, hb⟩ := l.normalized
    induction b using Quotient.inductionOn with
    | h w₀ =>
      obtain ⟨w, hw, h0⟩ := κ.exists_aPart_eq_zero (cell_nonempty 𝔅 w₀)
      refine ⟨w, ?_⟩
      have hrel : 𝔅 w w₀ := 𝔅.mem_cell.1 hw
      simp only [Quotient.sound hrel, hb, cell_eq_of_rel hrel, h0]

theorem condition_rank (l : RankingFunction (Quotient 𝔅)) (w : W) :
    (condition κ 𝔅 l).rank w = l.rank (Quotient.mk 𝔅 w) + κ.aPart (𝔅.cell w) w :=
  rfl

/-- Within an atom, the conditionalized ranking starts at the atom's rank under `l`. -/
theorem rankSet_condition_cell (l : RankingFunction (Quotient 𝔅)) (w : W) :
    (condition κ 𝔅 l).rankSet (𝔅.cell w) = l.rank (Quotient.mk 𝔅 w) := by
  obtain ⟨v, hv, h0⟩ := κ.exists_aPart_eq_zero (cell_nonempty 𝔅 w)
  have hrel : 𝔅 v w := 𝔅.mem_cell.1 hv
  refine le_antisymm (((condition κ 𝔅 l).rankSet_le hv).trans ?_) ?_
  · rw [condition_rank, cell_eq_of_rel hrel, h0, Quotient.sound hrel, add_zero]
  · refine (le_rankSet_iff _).2 λ u hu => ?_
    rw [condition_rank, Quotient.sound (𝔅.mem_cell.1 hu)]
    exact_mod_cast Nat.le_add_right _ _

open Classical in
/-- The two-atom ranking that believes `A` with firmness `α`. -/
noncomputable def firmness (A : Set W) (hA : A.Nonempty) (α : ℕ) :
    RankingFunction (Quotient (polar A)) where
  rank := Quotient.lift (λ w => if w ∈ A then 0 else α) λ w v h => by
    simp only [polar_iff.1 h]
  normalized := ⟨Quotient.mk _ hA.some, by simp [hA.some_mem]⟩

theorem polar_cell_of_mem {A : Set W} {w : W} (hw : w ∈ A) : (polar A).cell w = A := by
  ext v
  simp [hw]

theorem polar_cell_of_notMem {A : Set W} {w : W} (hw : w ∉ A) : (polar A).cell w = Aᶜ := by
  ext v
  simp [hw]

/-- Theorem 5: conditionalization on `A` at firmness `α` is generalized conditionalization by
the two-atom ranking believing `A` with firmness `α`. -/
theorem condition_firmness (A : Set W) (hA : A.Nonempty) (α : ℕ) :
    condition κ (polar A) (firmness A hA α) = κ.conditionα A hA α := by
  ext w
  by_cases hw : w ∈ A
  · rw [condition_rank, conditionα_of_mem _ _ _ hw, polar_cell_of_mem hw]
    simp [firmness, hw]
  · rw [condition_rank, conditionα_of_notMem _ _ _ hw, polar_cell_of_notMem hw]
    simp [firmness, hw]

/-- The coarsening of `κ` to a subfield: each atom ranked by its rank under `κ`. -/
noncomputable def coarsen : RankingFunction (Quotient 𝔅) where
  rank := Quotient.lift (λ w => (κ.rankSet (𝔅.cell w)).toNat) λ w v h => by
    rw [cell_eq_of_rel h]
  normalized := by
    obtain ⟨w, hw⟩ := κ.normalized
    exact ⟨Quotient.mk _ w, by
      simpa using toNat_rankSet_eq_zero κ (κ.rankSet_eq_zero_iff.2 ⟨w, 𝔅.mem_cell_self w, hw⟩)⟩

/-- Theorem 6: generalized conditionalization is reversed by conditionalizing on the
coarsening of the original ranking to the subfield. -/
theorem condition_condition_coarsen (l : RankingFunction (Quotient 𝔅)) :
    condition (condition κ 𝔅 l) 𝔅 (coarsen κ 𝔅) = κ := by
  ext w
  have := κ.toNat_rankSet_le (𝔅.mem_cell_self w)
  rw [condition_rank, aPart, rankSet_condition_cell, ENat.toNat_natCast, condition_rank, aPart]
  show (κ.rankSet (𝔅.cell w)).toNat + _ = _
  omega

end Generalized

/-! ### Independence -/

section Independence

variable (𝔅 ℭ : Setoid W)

/-- Definition 8: `ℭ` is independent of `𝔅` with respect to `κ`: every atom of `𝔅` meets
every atom of `ℭ`, and the rank of their intersection is the sum of their ranks. -/
def Independent : Prop :=
  ∀ w v, (𝔅.cell w ∩ ℭ.cell v).Nonempty ∧
    κ.rankSet (𝔅.cell w ∩ ℭ.cell v) = κ.rankSet (𝔅.cell w) + κ.rankSet (ℭ.cell v)

variable {κ 𝔅 ℭ}

theorem Independent.symm (h : Independent κ 𝔅 ℭ) : Independent κ ℭ 𝔅 := λ w v => by
  obtain ⟨hne, heq⟩ := h v w
  exact ⟨by rwa [Set.inter_comm], by rw [Set.inter_comm, heq, add_comm]⟩

/-- Theorem 7: independence extends from atoms to all satisfiable members of the fields. -/
theorem Independent.rankSet_inter (h : Independent κ 𝔅 ℭ) {B C : Set W} (hB : 𝔅.Decides B)
    (hC : ℭ.Decides C) (hB' : B.Nonempty) (hC' : C.Nonempty) :
    κ.rankSet (B ∩ C) = κ.rankSet B + κ.rankSet C := by
  refine le_antisymm ?_ ?_
  · obtain ⟨b, hb, eb⟩ := κ.exists_rank_eq_rankSet hB'
    obtain ⟨c, hc, ec⟩ := κ.exists_rank_eq_rankSet hC'
    calc κ.rankSet (B ∩ C) ≤ κ.rankSet (𝔅.cell b ∩ ℭ.cell c) :=
          κ.rankSet_anti (Set.inter_subset_inter (hB.cell_subset hb) (hC.cell_subset hc))
      _ = κ.rankSet (𝔅.cell b) + κ.rankSet (ℭ.cell c) := (h b c).2
      _ ≤ κ.rank b + κ.rank c :=
          add_le_add (κ.rankSet_le (𝔅.mem_cell_self b)) (κ.rankSet_le (ℭ.mem_cell_self c))
      _ = κ.rankSet B + κ.rankSet C := by rw [eb, ec]
  · rcases Set.eq_empty_or_nonempty (B ∩ C) with hBC | hBC
    · rw [hBC, rankSet_empty]; exact le_top
    obtain ⟨w, ⟨hwB, hwC⟩, e⟩ := κ.exists_rank_eq_rankSet hBC
    calc κ.rankSet B + κ.rankSet C ≤ κ.rankSet (𝔅.cell w) + κ.rankSet (ℭ.cell w) :=
          add_le_add (κ.rankSet_anti (hB.cell_subset hwB)) (κ.rankSet_anti (hC.cell_subset hwC))
      _ = κ.rankSet (𝔅.cell w ∩ ℭ.cell w) := ((h w w).2).symm
      _ ≤ κ.rank w := κ.rankSet_le ⟨𝔅.mem_cell_self w, ℭ.mem_cell_self w⟩
      _ = κ.rankSet (B ∩ C) := e

variable (κ)

/-- The rank of `B` given `A`, `κ(B | A) = −κ(A) + κ(A ∩ B)`. -/
noncomputable def condRank (A B : Set W) : ℕ∞ := κ.rankSet (A ∩ B) - κ.rankSet A

/-- On a satisfiable intersection, the conditional rank is a difference of natural numbers. -/
theorem condRank_eq {A B : Set W} (h : (A ∩ B).Nonempty) :
    condRank κ A B = ((κ.rankSet (A ∩ B)).toNat - (κ.rankSet A).toNat : ℕ) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (h.mono Set.inter_subset_left))
  rw [condRank, ← hm, ← hn, ENat.toNat_natCast, ENat.toNat_natCast, ENat.natCast_sub]

theorem condRank_eq_top_iff {A B : Set W} (hA : A.Nonempty) :
    condRank κ A B = ⊤ ↔ A ∩ B = ∅ := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top hA)
  rw [condRank, ← hn, ← κ.rankSet_eq_top_iff]
  rcases eq_or_ne (κ.rankSet (A ∩ B)) ⊤ with h | h
  · simp [h]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
    rw [← hm, ← ENat.natCast_sub]
    simp

/-- On satisfiable intersections, `κ(X | A) = κ(Y | A) + κ(Z | A)` says that
`κ(A ∩ X) + κ(A) = κ(A ∩ Y) + κ(A ∩ Z)`. -/
theorem condRank_add_iff {A X Y Z : Set W} (hX : (A ∩ X).Nonempty) (hY : (A ∩ Y).Nonempty)
    (hZ : (A ∩ Z).Nonempty) :
    condRank κ A X = condRank κ A Y + condRank κ A Z ↔
      (κ.rankSet (A ∩ X)).toNat + (κ.rankSet A).toNat =
        (κ.rankSet (A ∩ Y)).toNat + (κ.rankSet (A ∩ Z)).toNat := by
  have hA : ∀ {S : Set W}, (A ∩ S).Nonempty →
      (κ.rankSet A).toNat ≤ (κ.rankSet (A ∩ S)).toNat := λ hS =>
    ENat.toNat_le_toNat (κ.rankSet_anti Set.inter_subset_left) (κ.rankSet_ne_top hS)
  have h1 := hA hX
  have h2 := hA hY
  have h3 := hA hZ
  rw [condRank_eq κ hX, condRank_eq κ hY, condRank_eq κ hZ, ← Nat.cast_add, Nat.cast_inj]
  omega

variable {κ}

/-- Theorem 8, (a) and (b): independence holds exactly when, for satisfiable members `B` of
`𝔅` and `C` of `ℭ`, the rank of `C` given `B` is the rank of `C`. -/
theorem independent_iff_condRank :
    Independent κ 𝔅 ℭ ↔ ∀ B C, 𝔅.Decides B → ℭ.Decides C → B.Nonempty → C.Nonempty →
      condRank κ B C = κ.rankSet C := by
  constructor
  · intro h B C hB hC hB' hC'
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top hB')
    rw [condRank, h.rankSet_inter hB hC hB' hC', ← hn]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top hC')
    rw [← hm, ← Nat.cast_add, ← ENat.natCast_sub, Nat.add_sub_cancel_left]
  · intro h w v
    have hcell := h (𝔅.cell w) (ℭ.cell v) (𝔅.decides_cell w) (ℭ.decides_cell v)
      (cell_nonempty 𝔅 w) (cell_nonempty ℭ v)
    have hne : (𝔅.cell w ∩ ℭ.cell v).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty, ← condRank_eq_top_iff κ (cell_nonempty 𝔅 w)] at hempty
      exact κ.rankSet_ne_top (cell_nonempty ℭ v) (hcell ▸ hempty)
    refine ⟨hne, ?_⟩
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (cell_nonempty 𝔅 w))
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top hne)
    rw [condRank, ← hn, ← hm, ← ENat.natCast_sub] at hcell
    have hle : n ≤ m := by
      have := κ.rankSet_anti (Set.inter_subset_left (s := 𝔅.cell w) (t := ℭ.cell v))
      rw [← hn, ← hm] at this
      exact_mod_cast this
    rw [← hn, ← hm, ← hcell, ← Nat.cast_add, Nat.add_sub_cancel' hle]

/-- Theorem 8, (a) and (c): independence holds exactly when generalized conditionalization on
any ranking of the atoms of `𝔅` leaves the ranks of the satisfiable members of `ℭ`
unchanged. -/
theorem independent_iff_condition :
    Independent κ 𝔅 ℭ ↔ ∀ (l : RankingFunction (Quotient 𝔅)) (C : Set W), ℭ.Decides C →
      C.Nonempty → (condition κ 𝔅 l).rankSet C = κ.rankSet C := by
  constructor
  · intro h l C hC hC'
    refine le_antisymm ?_ ((le_rankSet_iff _).2 λ v hvC => ?_)
    · obtain ⟨c, hc, ec⟩ := κ.exists_rank_eq_rankSet hC'
      obtain ⟨b, hb⟩ := l.normalized
      induction b using Quotient.inductionOn with
      | h b₀ =>
        obtain ⟨hne, heq⟩ := h b₀ c
        obtain ⟨v, ⟨hvb, hvc⟩, ev⟩ := κ.exists_rank_eq_rankSet hne
        obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (cell_nonempty 𝔅 b₀))
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (cell_nonempty ℭ c))
        have hv : κ.rank v = n₀ + m := by
          rw [heq, ← hn₀, ← hm, ← Nat.cast_add] at ev
          exact_mod_cast ev
        have hmc : m ≤ κ.rank c := by
          have := κ.rankSet_le (ℭ.mem_cell_self c)
          rw [← hm] at this
          exact_mod_cast this
        have hrel : 𝔅 v b₀ := 𝔅.mem_cell.1 hvb
        refine ((condition κ 𝔅 l).rankSet_le (hC.cell_subset hc hvc)).trans ?_
        rw [condition_rank, Quotient.sound hrel, hb, zero_add, aPart, cell_eq_of_rel hrel, ← hn₀,
          ENat.toNat_natCast, ← ec, Nat.cast_le]
        omega
    · obtain ⟨hne, heq⟩ := h v v
      obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (cell_nonempty 𝔅 v))
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (cell_nonempty ℭ v))
      have h1 : n₀ + m ≤ κ.rank v := by
        have := κ.rankSet_le (show v ∈ 𝔅.cell v ∩ ℭ.cell v from
          ⟨𝔅.mem_cell_self v, ℭ.mem_cell_self v⟩)
        rw [heq, ← hn₀, ← hm, ← Nat.cast_add] at this
        exact_mod_cast this
      have h2 : κ.rankSet C ≤ m := hm ▸ κ.rankSet_anti (hC.cell_subset hvC)
      refine h2.trans ?_
      rw [condition_rank, aPart, ← hn₀, ENat.toNat_natCast, Nat.cast_le]
      omega
  · intro h w v
    classical
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (cell_nonempty ℭ v))
    obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top (cell_nonempty 𝔅 w))
    let l : RankingFunction (Quotient 𝔅) :=
      { rank := Quotient.lift (λ x => if 𝔅 x w then 0 else n + 1) λ x y hxy => by
          simp only [show 𝔅 x w ↔ 𝔅 y w from ⟨λ h => 𝔅.trans (𝔅.symm hxy) h, λ h => 𝔅.trans hxy h⟩]
        normalized := ⟨Quotient.mk _ w, by simp⟩ }
    have hl : ∀ x, l.rank (Quotient.mk 𝔅 x) = if 𝔅 x w then 0 else n + 1 := λ x => rfl
    have hC := h l (ℭ.cell v) (ℭ.decides_cell v) (cell_nonempty ℭ v)
    rw [← hn] at hC
    have hgt : ∀ x ∈ ℭ.cell v, ¬ 𝔅 x w → n + 1 ≤ (condition κ 𝔅 l).rank x := λ x _ hx => by
      rw [condition_rank, hl, ite_eq_right hx]
      exact Nat.le_add_right _ _
    have hne : (𝔅.cell w ∩ ℭ.cell v).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have : (n + 1 : ℕ∞) ≤ (condition κ 𝔅 l).rankSet (ℭ.cell v) :=
        (le_rankSet_iff _).2 λ x hx => by
          exact_mod_cast hgt x hx λ hxw => Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hxw, hx⟩
      rw [hC] at this
      exact absurd (by exact_mod_cast this : n + 1 ≤ n) (by omega)
    refine ⟨hne, ?_⟩
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (κ.rankSet_ne_top hne)
    rw [← hk, ← hn₀, ← hn, ← Nat.cast_add, Nat.cast_inj]
    have hk₀ : n₀ ≤ k := by
      have := κ.rankSet_anti (Set.inter_subset_left (s := 𝔅.cell w) (t := ℭ.cell v))
      rw [← hn₀, ← hk] at this
      exact_mod_cast this
    -- the minimum over the atom of ℭ is attained at a world of the atom of 𝔅
    obtain ⟨x, ⟨hxb, hxc⟩, ex⟩ := κ.exists_rank_eq_rankSet hne
    have hx : κ.rank x = k := by rw [← hk] at ex; exact_mod_cast ex
    have hrelx : 𝔅 x w := 𝔅.mem_cell.1 hxb
    have hle : n ≤ k - n₀ := by
      have := (condition κ 𝔅 l).rankSet_le hxc
      rw [hC, condition_rank, hl, ite_eq_left hrelx, zero_add, aPart, cell_eq_of_rel hrelx, ← hn₀,
        ENat.toNat_natCast, hx] at this
      exact_mod_cast this
    obtain ⟨y, hyc, ey⟩ := (condition κ 𝔅 l).exists_rank_eq_rankSet (cell_nonempty ℭ v)
    rw [hC] at ey
    have hy : (condition κ 𝔅 l).rank y = n := by exact_mod_cast ey
    by_cases hyw : 𝔅 y w
    · have hky : k ≤ κ.rank y := by
        have := κ.rankSet_le (show y ∈ 𝔅.cell w ∩ ℭ.cell v from ⟨hyw, hyc⟩)
        rw [← hk] at this
        exact_mod_cast this
      rw [condition_rank, hl, ite_eq_left hyw, zero_add, aPart, cell_eq_of_rel hyw, ← hn₀,
        ENat.toNat_natCast] at hy
      omega
    · have := hgt y hyc hyw
      omega

end Independence

/-! ### Conditional independence -/

section CondIndependence

variable (𝔅 ℭ : Setoid W) (A : Set W)

/-- Definition 10: `ℭ` is independent of `𝔅` given `A` with respect to `κ`: for atoms `B` of
`𝔅` and `C` of `ℭ` meeting `A`, `κ(B ∩ C | A) = κ(B | A) + κ(C | A)`. -/
def CondIndependent : Prop :=
  ∀ w v, (A ∩ 𝔅.cell w ∩ ℭ.cell v).Nonempty →
    condRank κ A (𝔅.cell w ∩ ℭ.cell v) = condRank κ A (𝔅.cell w) + condRank κ A (ℭ.cell v)

/-- `ℭ` is independent of `𝔅` given the subfield `𝔇`: given each atom of `𝔇`. -/
def CondIndependentOn (𝔇 : Setoid W) : Prop := ∀ d, CondIndependent κ 𝔅 ℭ (𝔇.cell d)

variable {κ 𝔅 ℭ A}

theorem CondIndependent.symm (h : CondIndependent κ 𝔅 ℭ A) : CondIndependent κ ℭ 𝔅 A :=
  λ w v hne => by
    rw [Set.inter_right_comm] at hne
    rw [Set.inter_comm, h v w hne, add_comm]

theorem CondIndependentOn.symm {𝔇 : Setoid W} (h : CondIndependentOn κ 𝔅 ℭ 𝔇) :
    CondIndependentOn κ ℭ 𝔅 𝔇 :=
  λ d => (h d).symm

/-- Theorem 11: if `ℭ` is independent of `𝔅` given `𝔇 + 𝔈` and `𝔇` is independent of `𝔅`
given `𝔈`, then `ℭ + 𝔇` is independent of `𝔅` given `𝔈`. -/
theorem CondIndependentOn.inf {𝔇 𝔈 : Setoid W} (h₁ : CondIndependentOn κ 𝔅 ℭ (𝔇 ⊓ 𝔈))
    (h₂ : CondIndependentOn κ 𝔅 𝔇 𝔈) : CondIndependentOn κ 𝔅 (ℭ ⊓ 𝔇) 𝔈 := by
  intro e w v hne
  rw [cell_inf] at hne ⊢
  obtain ⟨x, ⟨hxE, hxB⟩, hxC, hxD⟩ := hne
  have hE : 𝔈.cell x = 𝔈.cell e := cell_eq_of_rel (𝔈.mem_cell.1 hxE)
  have hD : 𝔇.cell x = 𝔇.cell v := cell_eq_of_rel (𝔇.mem_cell.1 hxD)
  have H1 := h₁ x w v
  have H2 := h₂ e w x
  rw [cell_inf, hD, hE] at H1
  rw [hD] at H2
  specialize H1 ⟨x, ⟨⟨hxD, hxE⟩, hxB⟩, hxC⟩
  specialize H2 ⟨x, ⟨hxE, hxB⟩, hxD⟩
  have e1 : 𝔇.cell v ∩ 𝔈.cell e ∩ (𝔅.cell w ∩ ℭ.cell v) =
      𝔈.cell e ∩ (𝔅.cell w ∩ (ℭ.cell v ∩ 𝔇.cell v)) := by
    ext; simp only [Set.mem_inter_iff]; tauto
  have e2 : 𝔇.cell v ∩ 𝔈.cell e ∩ 𝔅.cell w = 𝔈.cell e ∩ (𝔅.cell w ∩ 𝔇.cell v) := by
    ext; simp only [Set.mem_inter_iff]; tauto
  have e3 : 𝔇.cell v ∩ 𝔈.cell e ∩ ℭ.cell v = 𝔈.cell e ∩ (ℭ.cell v ∩ 𝔇.cell v) := by
    ext; simp only [Set.mem_inter_iff]; tauto
  have e4 : 𝔇.cell v ∩ 𝔈.cell e = 𝔈.cell e ∩ 𝔇.cell v := Set.inter_comm _ _
  have hX1 : (𝔇.cell v ∩ 𝔈.cell e ∩ (𝔅.cell w ∩ ℭ.cell v)).Nonempty :=
    ⟨x, ⟨hxD, hxE⟩, hxB, hxC⟩
  have hY1 : (𝔇.cell v ∩ 𝔈.cell e ∩ 𝔅.cell w).Nonempty := ⟨x, ⟨hxD, hxE⟩, hxB⟩
  have hZ1 : (𝔇.cell v ∩ 𝔈.cell e ∩ ℭ.cell v).Nonempty := ⟨x, ⟨hxD, hxE⟩, hxC⟩
  have hX2 : (𝔈.cell e ∩ (𝔅.cell w ∩ 𝔇.cell v)).Nonempty := ⟨x, hxE, hxB, hxD⟩
  have hY2 : (𝔈.cell e ∩ 𝔅.cell w).Nonempty := ⟨x, hxE, hxB⟩
  have hZ2 : (𝔈.cell e ∩ 𝔇.cell v).Nonempty := ⟨x, hxE, hxD⟩
  have hX3 : (𝔈.cell e ∩ (𝔅.cell w ∩ (ℭ.cell v ∩ 𝔇.cell v))).Nonempty :=
    ⟨x, hxE, hxB, hxC, hxD⟩
  have hZ3 : (𝔈.cell e ∩ (ℭ.cell v ∩ 𝔇.cell v)).Nonempty := ⟨x, hxE, hxC, hxD⟩
  rw [condRank_add_iff κ hX1 hY1 hZ1, e1, e2, e3, e4] at H1
  rw [condRank_add_iff κ hX2 hY2 hZ2] at H2
  rw [condRank_add_iff κ hX3 hY2 hZ3]
  omega

/-- Theorem 12: if `𝔅` is independent of `ℭ` given `𝔇 + 𝔈` and of `𝔇` given `𝔈`, then it is
independent of `ℭ + 𝔇` given `𝔈`. -/
theorem CondIndependentOn.inf' {𝔇 𝔈 : Setoid W} (h₁ : CondIndependentOn κ ℭ 𝔅 (𝔇 ⊓ 𝔈))
    (h₂ : CondIndependentOn κ 𝔇 𝔅 𝔈) : CondIndependentOn κ (ℭ ⊓ 𝔇) 𝔅 𝔈 :=
  (CondIndependentOn.inf h₁.symm h₂.symm).symm

end CondIndependence

end Spohn1988
