module

public import Linglib.Logic.ComparativeProbability.Representability
public import Linglib.Logic.ComparativeProbability.CancellationFin4
public import Mathlib.Tactic.IntervalCases

/-! # Representation and completeness theorems

Kraft, Pratt and Seidenberg show that every qualitative probability order on fewer than five
atoms is represented by a finitely additive probability measure, and give an order on five
atoms that is not; padding it with null atoms gives one at every larger size. Following van
der Hoek, every order on a finite carrier is still represented by a qualitatively additive
measure.

## Main statements

* `ComparativeProbability.representable_of_card_lt_five`: below five atoms every order is
  representable.
* `ComparativeProbability.kps_not_representable`: the five-atom counterexample is not
  representable, by Scott's theorem.
* `ComparativeProbability.exists_nonrepresentable_fin`,
  `exists_nonrepresentable_of_five_le_card`: from five atoms on, some order is not
  representable.
* `ComparativeProbability.exists_qualAddMeasure_repr`: every order on a finite carrier is
  represented by a qualitatively additive measure.
* `ComparativeProbability.axiomA_iff_fa`: qualitative additivity is equivalent to invariance
  under adding a disjoint set to both sides.

## References

* [kraft-pratt-seidenberg-1959]
* [van-der-hoek-1996]
-/

@[expose] public section

namespace ComparativeProbability

/-! ### The Kraft–Pratt–Seidenberg counterexample -/

/-- `finsetIdx s` encodes a subset of `Fin 5` as a bitmask. -/
def finsetIdx (s : Finset (Fin 5)) : ℕ :=
  s.sum (fun i ↦ 2 ^ i.val)

/-- `kpsRankNat` ranks the 32 subsets of `Fin 5`, indexed by bitmask, in the
    Kraft–Pratt–Seidenberg order. With atoms `p, q, r, s, t` numbered `0, …, 4`, the lower half
    is `∅ < q < r < s < qr < qs < p < pq < rs < t < qrs < rp < ps < tq < qrp < rt`, and the
    complements follow in reverse order. -/
def kpsRankNat (idx : ℕ) : ℕ :=
  match idx with
  |  0 =>  0 |  1 =>  6 |  2 =>  1 |  3 =>  7
  |  4 =>  2 |  5 => 11 |  6 =>  4 |  7 => 14
  |  8 =>  3 |  9 => 12 | 10 =>  5 | 11 => 16
  | 12 =>  8 | 13 => 18 | 14 => 10 | 15 => 22
  | 16 =>  9 | 17 => 21 | 18 => 13 | 19 => 23
  | 20 => 15 | 21 => 26 | 22 => 19 | 23 => 28
  | 24 => 17 | 25 => 27 | 26 => 20 | 27 => 29
  | 28 => 24 | 29 => 30 | 30 => 25 | 31 => 31
  |  _ =>  0

/-- `kpsRank s` is the rank of `s` in the Kraft–Pratt–Seidenberg order. -/
def kpsRank (s : Finset (Fin 5)) : ℕ :=
  kpsRankNat (finsetIdx s)

theorem kps_mono_finset :
    ∀ (a b : Finset (Fin 5)), a ⊆ b → kpsRank b ≥ kpsRank a := by
  decide

private theorem kps_additive_finset :
    ∀ (a b : Finset (Fin 5)),
      (kpsRank a ≥ kpsRank b) ↔ (kpsRank (a \ b) ≥ kpsRank (b \ a)) := by
  decide

section KPSSystem

attribute [local instance] Classical.propDecidable

/-- `kpsRankSet A` is the Kraft–Pratt–Seidenberg rank of a set. -/
noncomputable def kpsRankSet (A : Set (Fin 5)) : ℕ := kpsRank A.toFinset

/-- `kpsLe A B` compares two sets by their Kraft–Pratt–Seidenberg rank. -/
noncomputable def kpsLe (A B : Set (Fin 5)) : Prop := kpsRankSet A ≤ kpsRankSet B

/-- `kpsSystem` is the Kraft–Pratt–Seidenberg order on the subsets of `Fin 5`. -/
noncomputable def kpsSystem : QualitativeProbability (Set (Fin 5)) where
  le := kpsLe
  mono' := fun {A B} hAB ↦ kps_mono_finset _ _ (Set.toFinset_subset_toFinset.mpr hAB)
  nonTrivial := by
    simp only [kpsLe, kpsRankSet, Set.top_eq_univ, Set.bot_eq_empty, Set.toFinset_univ,
      Set.toFinset_empty]; decide
  total := fun A B ↦ le_total (kpsRankSet A) (kpsRankSet B)
  trans' := fun {_ _ _} hab hbc ↦ le_trans hab hbc
  additive A B := by
    unfold kpsLe kpsRankSet
    rw [Set.toFinset_sdiff, Set.toFinset_sdiff]
    exact kps_additive_finset _ _

/-- `kpsFamily` lists the four comparisons of the Kraft–Pratt–Seidenberg order that cancel,
    `p ≻ qs`, `pqs ≻ rt`, `rs ≻ pq` and `qt ≻ ps`. -/
private def kpsFamily : List (Fin 5 → SignType) :=
  [![1, -1, 0, -1, 0], ![1, 1, -1, 1, -1], ![-1, -1, 1, 1, 0], ![-1, 1, 0, -1, 1]]

private theorem posSupport_eq_coe_filter (v : Fin 5 → SignType) :
    posSupport v = ↑(Finset.univ.filter fun i ↦ v i = 1) := by ext; simp

private theorem negSupport_eq_coe_filter (v : Fin 5 → SignType) :
    negSupport v = ↑(Finset.univ.filter fun i ↦ v i = -1) := by ext; simp

/-- **The Kraft–Pratt–Seidenberg order is not representable.** Its four comparisons
    `kpsFamily` hold strictly and their sign vectors cancel, so Scott's theorem
    (`representable_iff_cancellation`) would force `qs ≿ p`. -/
theorem kps_not_representable : ¬Representable kpsSystem := fun h ↦ by
  have key := (representable_iff_cancellation kpsSystem).mp h kpsFamily (fun v hv ↦ ?_)
    (by decide) ![1, -1, 0, -1, 0] (List.mem_cons_self ..)
  · revert key
    show ¬kpsRank (posSupport _).toFinset ≤ kpsRank (negSupport _).toFinset
    rw [posSupport_eq_coe_filter, negSupport_eq_coe_filter, Finset.toFinset_coe,
      Finset.toFinset_coe]
    decide
  · show kpsRank (negSupport v).toFinset ≤ kpsRank (posSupport v).toFinset
    rw [posSupport_eq_coe_filter, negSupport_eq_coe_filter, Finset.toFinset_coe,
      Finset.toFinset_coe]
    simp only [kpsFamily, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide

end KPSSystem

/-! ### Padding with null atoms -/

/-- `sys.pad` adds one null atom, deciding comparisons on `Fin (n + 1)` by their restriction
    to the first `n` atoms. -/
def QualitativeProbability.pad {n : ℕ} (sys : QualitativeProbability (Set (Fin n))) :
    QualitativeProbability (Set (Fin (n + 1))) where
  le A B := sys.le (Fin.castSucc ⁻¹' A) (Fin.castSucc ⁻¹' B)
  mono' _ _ hAB := sys.mono (Set.preimage_mono hAB)
  nonTrivial := by
    show ¬sys.le (Fin.castSucc ⁻¹' Set.univ) (Fin.castSucc ⁻¹' ∅)
    rw [Set.preimage_univ, Set.preimage_empty, ← Set.top_eq_univ, ← Set.bot_eq_empty]
    exact sys.nonTrivial
  total _ _ := sys.total _ _
  trans' _ _ _ h1 h2 := sys.trans h1 h2
  additive A B := by
    show sys.le _ _ ↔ sys.le _ _
    rw [Set.preimage_sdiff, Set.preimage_sdiff]; exact sys.additive _ _

/-- The padded atom is null. -/
theorem QualitativeProbability.pad_last_null {n : ℕ}
    (sys : QualitativeProbability (Set (Fin n))) : sys.pad.le {Fin.last n} ∅ := by
  show sys.le (Fin.castSucc ⁻¹' {Fin.last n}) (Fin.castSucc ⁻¹' ∅)
  rw [Set.preimage_empty, show Fin.castSucc ⁻¹' {Fin.last n} = (∅ : Set (Fin n)) from
    Set.eq_empty_of_forall_notMem fun i hi ↦ (Fin.castSucc_lt_last i).ne hi]; exact sys.refl ∅

/-- Padding reflects representability, since a measure for `sys.pad` gives the padded atom
    measure zero and its restriction along `Fin.castSucc` represents `sys`. -/
theorem representable_of_pad {n : ℕ} {sys : QualitativeProbability (Set (Fin n))}
    (h : Representable sys.pad) : Representable sys := by
  obtain ⟨m, hm⟩ := h
  have hinj := Fin.castSucc_injective n
  have hlast : m {Fin.last n} = 0 := by
    have h0 : m {Fin.last n} ≤ m ∅ := (hm _ _).mp sys.pad_last_null
    rw [m.mu_empty] at h0; linarith [m.nonneg {Fin.last n}]
  have hcover : Fin.castSucc '' (Set.univ : Set (Fin n)) ∪ {Fin.last n} = Set.univ := by
    rw [Set.image_univ]
    ext i
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr rfl
  have hdisj : Disjoint (Fin.castSucc '' (Set.univ : Set (Fin n))) {Fin.last n} :=
    Set.disjoint_singleton_right.mpr fun ⟨i, _, hi⟩ ↦ (Fin.castSucc_lt_last i).ne hi
  have htotal : m (Fin.castSucc '' (Set.univ : Set (Fin n))) = 1 := by
    have := m.additive hdisj
    rw [hcover, m.total, hlast, add_zero] at this; linarith
  refine ⟨{
    toFun := fun A ↦ m (Fin.castSucc '' A)
    nonneg' := fun A ↦ m.nonneg _
    additive' := fun A B hd ↦ by
      rw [Set.image_union]; exact m.additive ((Set.disjoint_image_iff hinj).mpr hd)
    total' := htotal
  }, fun A B ↦ ?_⟩
  have key := hm (Fin.castSucc '' A) (Fin.castSucc '' B)
  rwa [show sys.pad.le (Fin.castSucc '' A) (Fin.castSucc '' B) ↔ sys.le A B from by
    show sys.le (Fin.castSucc ⁻¹' (Fin.castSucc '' A)) _ ↔ _
    rw [Set.preimage_image_eq A hinj, Set.preimage_image_eq B hinj]] at key

/-- For every `n ≥ 5` some qualitative probability order on `Fin n` is not representable, as
    the Kraft–Pratt–Seidenberg counterexample padded with null atoms shows. -/
theorem exists_nonrepresentable_fin {n : ℕ} (h : 5 ≤ n) :
    ∃ sys : QualitativeProbability (Set (Fin n)), ¬Representable sys := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨kpsSystem, kps_not_representable⟩
  | succ n _ ih =>
    obtain ⟨sys, hsys⟩ := ih
    exact ⟨sys.pad, fun h ↦ hsys (representable_of_pad h)⟩

/-! ### The Kraft–Pratt–Seidenberg theorems -/

/-- **Kraft–Pratt–Seidenberg below five atoms.** Every qualitative probability order on fewer
    than five atoms is representable by a finitely additive measure. -/
theorem representable_of_card_lt_five {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (hcard : Fintype.card W < 5) :
    Representable sys := by
  have : DecidableEq W := Classical.typeDecidableEq W
  let e := Fintype.equivFin W
  set n := Fintype.card W with hn_def
  interval_cases n
  · exact (sys.transport e).elim0
  · exact perm_repr e sys (representable_fin1 (sys.transport e))
  · exact perm_repr e sys (representable_fin2 (sys.transport e))
  · exact perm_repr e sys (representable_fin3 (sys.transport e))
  · exact perm_repr e sys (representable_fin4 (sys.transport e))

/-- **Kraft–Pratt–Seidenberg from five atoms on.** Some qualitative probability order is not
    representable by any finitely additive measure. -/
theorem exists_nonrepresentable_of_five_le_card {W : Type*} [Fintype W]
    (hcard : 5 ≤ Fintype.card W) :
    ∃ sys : QualitativeProbability (Set W), ¬Representable sys := by
  have : DecidableEq W := Classical.typeDecidableEq W
  obtain ⟨sysF, hsysF⟩ := exists_nonrepresentable_fin hcard
  exact ⟨sysF.transport (Fintype.equivFin W).symm,
    fun h ↦ hsysF (perm_repr (Fintype.equivFin W).symm sysF h)⟩

/-! ### Qualitatively additive representation -/

attribute [local instance] Classical.propDecidable

/-- `belowCount sys A` counts the finsets at most as likely as `A`. -/
private noncomputable def belowCount {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A : Set W) : ℕ :=
  (Finset.univ.filter (fun S : Finset W ↦ sys.le ↑S A)).card

private theorem belowCount_univ {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) :
    belowCount sys Set.univ = Fintype.card (Finset W) := by
  unfold belowCount
  rw [Finset.filter_true_of_mem fun S _ ↦ sys.mono (Set.subset_univ _)]
  exact Finset.card_univ

private theorem belowCount_mono {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A B : Set W)
    (h : sys.le A B) : belowCount sys A ≤ belowCount sys B := by
  refine Finset.card_le_card fun S hS ↦ ?_
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, sys.trans hS.2 h⟩

private theorem belowCount_strict {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A B : Set W)
    (h : ¬sys.le A B) : belowCount sys B < belowCount sys A := by
  refine Finset.card_lt_card ⟨fun S hS ↦ ?_, fun hsub ↦ ?_⟩
  · rw [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, sys.trans hS.2 ((sys.total A B).resolve_left h)⟩
  · have : A.toFinset ∈ Finset.univ.filter (fun S : Finset W ↦ sys.le ↑S B) :=
      hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Set.coe_toFinset]; exact sys.refl A⟩)
    rw [Finset.mem_filter, Set.coe_toFinset] at this
    exact h this.2

private theorem belowCount_iff {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A B : Set W) :
    belowCount sys A ≤ belowCount sys B ↔ sys.le A B := by
  refine ⟨fun hcount ↦ by_contra fun hng ↦ ?_, belowCount_mono sys A B⟩
  have := belowCount_strict sys A B hng
  omega

/-- **Qualitatively additive representation.** Every qualitative probability order on a
    finite carrier is represented by a qualitatively additive measure, the count of dominated
    sets affinely renormalised so that `μ(∅) = 0` and `μ(Ω) = 1`. -/
theorem exists_qualAddMeasure_repr {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) :
    ∃ (m : QualAddMeasure ℚ W), ∀ A B, sys.le A B ↔ m A ≤ m B := by
  classical
  set E : ℚ := (belowCount sys ∅ : ℚ) with hE
  set N : ℚ := (Fintype.card (Finset W) : ℚ) with hN
  have hd : (0 : ℚ) < N - E := by
    have := belowCount_strict sys Set.univ ∅ (by simpa using sys.nonTrivial)
    rw [belowCount_univ] at this
    exact sub_pos.mpr (by rw [hN, hE]; exact_mod_cast this)
  -- the affine map t ↦ (t − E)/(N − E) is an order isomorphism
  have key : ∀ A B : Set W,
      ((belowCount sys A : ℚ) - E) / (N - E) ≤ ((belowCount sys B : ℚ) - E) / (N - E) ↔
      sys.le A B := fun A B ↦ by
    rw [div_le_div_iff_of_pos_right hd, sub_le_sub_iff_right, Nat.cast_le]
    exact belowCount_iff sys A B
  have hAle : ∀ A : Set W, E ≤ (belowCount sys A : ℚ) := fun A ↦ by
    rw [hE, Nat.cast_le]; exact belowCount_mono sys ∅ A (sys.mono (Set.empty_subset A))
  refine ⟨⟨fun A ↦ ((belowCount sys A : ℚ) - E) / (N - E),
    fun A ↦ div_nonneg (sub_nonneg.mpr (hAle A)) hd.le,
    by simp only [← hE, sub_self, zero_div], ?_, ?_⟩, fun A B ↦ (key A B).symm⟩
  · show ((belowCount sys Set.univ : ℚ) - E) / (N - E) = 1
    rw [belowCount_univ, ← hN]; exact div_self hd.ne'
  · intro A B
    show _ ≤ _ ↔ _ ≤ _
    rw [key A B, key (A \ B) (B \ A)]; exact sys.additive A B

/-! ### Qualitative and finite additivity -/

/-- Adding a set `C` disjoint from `A` to both sides of a difference leaves `A \ B`
    unchanged, `(A ∪ C) \ (B ∪ C) = A \ B`. -/
private theorem union_diff_union_disjoint {W : Type*} (A B C : Set W)
    (hAC : ∀ x, x ∈ A → x ∉ C) : (A ∪ C) \ (B ∪ C) = A \ B := by
  ext x; simp only [Set.mem_sdiff, Set.mem_union]
  refine ⟨fun h ↦ h.1.elim (fun hx ↦ ⟨hx, fun hb ↦ h.2 (Or.inl hb)⟩)
    (fun hx ↦ absurd (Or.inr hx) h.2), fun ⟨hxA, hxnB⟩ ↦
    ⟨Or.inl hxA, fun h ↦ h.elim hxnB (hAC x hxA)⟩⟩

/-- For any comparison on sets, qualitative additivity is equivalent to finite additivity in
    the form that adding a disjoint set to both sides preserves the comparison. -/
theorem axiomA_iff_fa {W : Type*} (ge : Set W → Set W → Prop) :
    (∀ A B : Set W, ge A B ↔ ge (A \ B) (B \ A)) ↔
    (∀ A B C : Set W, (∀ x, x ∈ A → x ∉ C) → (∀ x, x ∈ B → x ∉ C) →
      (ge A B ↔ ge (A ∪ C) (B ∪ C))) := by
  constructor
  · intro hA A B C hAC hBC
    have h2 := hA (A ∪ C) (B ∪ C)
    rw [union_diff_union_disjoint A B C hAC, union_diff_union_disjoint B A C hBC] at h2
    exact (hA A B).trans h2.symm
  · intro hFA A B
    have h := hFA (A \ B) (B \ A) (A ∩ B)
      (fun x ⟨_, hxnB⟩ ⟨_, hxB⟩ ↦ hxnB hxB) (fun x ⟨_, hxnA⟩ ⟨hxA, _⟩ ↦ hxnA hxA)
    rw [Set.sdiff_union_inter A B, Set.inter_comm A B, Set.sdiff_union_inter B A] at h
    exact h.symm

end ComparativeProbability
