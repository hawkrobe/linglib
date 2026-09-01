import Linglib.Core.Order.Probability.Representability
import Linglib.Core.Order.Probability.CancellationFin4
import Mathlib.Tactic.IntervalCases

/-! # KPS representation and completeness theorems

The top-level representation results ([kraft-pratt-seidenberg-1959]; [van-der-hoek-1996]):

* `ComparativeProbability.representable_of_card_lt_five` — for `|W| < 5`, every FA model is
  representable by a finitely additive probability measure (FA = FP∞ below
  five worlds).
* `ComparativeProbability.exists_nonrepresentable_of_five_le_card` — for `|W| ≥ 5`, FA is
  strictly weaker than FP∞ (the KPS counterexample, padded with null atoms).
* `ComparativeProbability.exists_qualAddMeasure_repr` — every order on a finite
  carrier is represented by a qualitatively additive measure ([van-der-hoek-1996]).
* `ComparativeProbability.axiomA_iff_fa` — Axiom A is equivalent to disjoint-union
  invariance (finite additivity).

`[UPSTREAM]` candidate (see the note in `Defs.lean`).
-/

namespace ComparativeProbability


-- ── Kraft–Pratt–Seidenberg ───

/-- **Kraft–Pratt–Seidenberg, below five atoms** ([kraft-pratt-seidenberg-1959]):
    every qualitative probability order on fewer than five atoms is
    representable by a finitely additive measure. -/
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

/-- **Kraft–Pratt–Seidenberg, at five or more atoms** ([kraft-pratt-seidenberg-1959]):
    some qualitative probability order is not representable by any finitely
    additive measure. -/
theorem exists_nonrepresentable_of_five_le_card {W : Type*} [Fintype W]
    (hcard : 5 ≤ Fintype.card W) :
    ∃ sys : QualitativeProbability (Set W), ¬Representable sys := by
  have : DecidableEq W := Classical.typeDecidableEq W
  obtain ⟨sysF, hsysF⟩ := exists_nonrepresentable_fin hcard
  exact ⟨sysF.transport (Fintype.equivFin W).symm,
    fun h => hsysF (perm_repr (Fintype.equivFin W).symm sysF h)⟩

-- ── Qualitatively additive representation ─────────────

attribute [local instance] Classical.propDecidable

/-- Count of finsets at most as likely as `A`. -/
private noncomputable def belowCount {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A : Set W) : ℕ :=
  (Finset.univ.filter (fun S : Finset W => sys.le ↑S A)).card

private theorem belowCount_univ {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) :
    belowCount sys Set.univ = Fintype.card (Finset W) := by
  unfold belowCount
  rw [Finset.filter_true_of_mem fun S _ => sys.mono (Set.subset_univ _)]
  exact Finset.card_univ

private theorem belowCount_mono {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A B : Set W)
    (h : sys.le A B) : belowCount sys A ≤ belowCount sys B := by
  refine Finset.card_le_card fun S hS => ?_
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, sys.trans hS.2 h⟩

private theorem belowCount_strict {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A B : Set W)
    (h : ¬sys.le A B) : belowCount sys B < belowCount sys A := by
  refine Finset.card_lt_card ⟨fun S hS => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, sys.trans hS.2 ((sys.total A B).resolve_left h)⟩
  · have : A.toFinset ∈ Finset.univ.filter (fun S : Finset W => sys.le ↑S B) :=
      hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Set.coe_toFinset]; exact sys.refl A⟩)
    rw [Finset.mem_filter, Set.coe_toFinset] at this
    exact h this.2

private theorem belowCount_iff {W : Type*} [Fintype W]
    (sys : QualitativeProbability (Set W)) (A B : Set W) :
    belowCount sys A ≤ belowCount sys B ↔ sys.le A B := by
  refine ⟨fun hcount => by_contra fun hng => ?_, belowCount_mono sys A B⟩
  have := belowCount_strict sys A B hng
  omega

/-- **Qualitatively additive representation** ([van-der-hoek-1996]): every
    qualitative probability order on a finite carrier is representable by a
    qualitatively additive measure — the dominated-set count, affinely
    renormalised so μ(∅) = 0 and μ(Ω) = 1. -/
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
      sys.le A B := fun A B => by
    rw [div_le_div_iff_of_pos_right hd, sub_le_sub_iff_right, Nat.cast_le]
    exact belowCount_iff sys A B
  have hAle : ∀ A : Set W, E ≤ (belowCount sys A : ℚ) := fun A => by
    rw [hE, Nat.cast_le]; exact belowCount_mono sys ∅ A (sys.mono (Set.empty_subset A))
  refine ⟨⟨fun A => ((belowCount sys A : ℚ) - E) / (N - E),
    fun A => div_nonneg (sub_nonneg.mpr (hAle A)) hd.le,
    by simp only [← hE, sub_self, zero_div], ?_, ?_⟩, fun A B => (key A B).symm⟩
  · show ((belowCount sys Set.univ : ℚ) - E) / (N - E) = 1
    rw [belowCount_univ, ← hN]; exact div_self hd.ne'
  · intro A B
    show _ ≤ _ ↔ _ ≤ _
    rw [key A B, key (A \ B) (B \ A)]; exact sys.additive A B

-- ── Bridge: Axiom A ↔ FA ────────────────────────

/-- Adding a set `C` disjoint from `A` to both sides of a difference leaves
    `A \ B` unchanged: `(A ∪ C) \ (B ∪ C) = A \ B`. -/
private theorem union_diff_union_disjoint {W : Type*} (A B C : Set W)
    (hAC : ∀ x, x ∈ A → x ∉ C) : (A ∪ C) \ (B ∪ C) = A \ B := by
  ext x; simp only [Set.mem_sdiff, Set.mem_union]
  refine ⟨fun h => h.1.elim (fun hx => ⟨hx, fun hb => h.2 (Or.inl hb)⟩)
    (fun hx => absurd (Or.inr hx) h.2), fun ⟨hxA, hxnB⟩ =>
    ⟨Or.inl hxA, fun h => h.elim hxnB (hAC x hxA)⟩⟩

/-- **Algebraic bridge**: Axiom A and finite additivity (disjoint augmentation
    preserves the comparison) are equivalent for any comparison on sets. -/
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
      (fun x ⟨_, hxnB⟩ ⟨_, hxB⟩ => hxnB hxB) (fun x ⟨_, hxnA⟩ ⟨hxA, _⟩ => hxnA hxA)
    rw [Set.sdiff_union_inter A B, Set.inter_comm A B, Set.sdiff_union_inter B A] at h
    exact h.symm

end ComparativeProbability
