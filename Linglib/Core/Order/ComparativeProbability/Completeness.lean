import Linglib.Core.Order.ComparativeProbability.Representability
import Linglib.Core.Order.ComparativeProbability.CancellationFin4
import Mathlib.Tactic.IntervalCases

/-! # KPS representation and completeness theorems

The top-level results of [holliday-icard-2013] / [kraft-pratt-seidenberg-1959]:

* `ComparativeProbability.representable_of_card_lt_five` — for `|W| < 5`, every FA model is
  representable by a finitely additive probability measure (FA = FP∞ below
  five worlds).
* `ComparativeProbability.exists_nonrepresentable_of_five_le_card` — for `|W| ≥ 5`, FA is
  strictly weaker than FP∞ (the KPS counterexample, padded with null atoms).
* `ComparativeProbability.exists_qualAddMeasure_repr`, `exists_dominationLift_repr` —
  qualitative completeness results ([van-der-hoek-1996]; [halpern-2003]
  Thm. 7.5.1a).
* `ComparativeProbability.axiomA_iff_fa` — Axiom A is equivalent to disjoint-union
  invariance (finite additivity).
-/

namespace ComparativeProbability


-- ── Theorem 8 (Kraft, [kraft-pratt-seidenberg-1959]) ───

/-- **Theorem 8a** ([kraft-pratt-seidenberg-1959]; [holliday-icard-2013]
    Theorem 8): below five worlds every FA system is representable —
    FA and FP∞ coincide. -/
theorem representable_of_card_lt_five {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (hcard : Fintype.card W < 5) :
    Representable sys := by
  haveI : DecidableEq W := Classical.typeDecidableEq W
  let e := Fintype.equivFin W
  set n := Fintype.card W with hn_def
  interval_cases n
  · exact (no_fa_empty (transportFA e sys)).elim
  · exact perm_repr e sys (representable_fin1 (transportFA e sys))
  · exact perm_repr e sys (representable_fin2 (transportFA e sys))
  · exact perm_repr e sys (representable_fin3 (transportFA e sys))
  · exact perm_repr e sys (representable_fin4 (transportFA e sys))

/-- **Theorem 8b** ([kraft-pratt-seidenberg-1959] Theorem 8): at every
    cardinality ≥ 5 some FA system is non-representable, so FA is strictly
    weaker than FP∞. -/
theorem exists_nonrepresentable_of_five_le_card {W : Type*} [Fintype W]
    (hcard : 5 ≤ Fintype.card W) :
    ∃ sys : EpistemicSystemFA W, ¬Representable sys := by
  haveI : DecidableEq W := Classical.typeDecidableEq W
  obtain ⟨sysF, hsysF⟩ := exists_nonrepresentable_fin hcard
  exact ⟨transportFA (Fintype.equivFin W).symm sysF,
    fun h => hsysF (perm_repr (Fintype.equivFin W).symm sysF h)⟩

-- ── Completeness (Theorems 2 and 6) ─────────────

attribute [local instance] Classical.propDecidable

/-- Count of finsets dominated by A under the ge ordering. -/
private noncomputable def belowCount {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A : Set W) : ℕ :=
  (Finset.univ.filter (fun S : Finset W => sys.ge A ↑S)).card

private theorem belowCount_univ {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) :
    belowCount sys Set.univ = Fintype.card (Finset W) := by
  unfold belowCount
  rw [Finset.filter_true_of_mem fun S _ => sys.mono _ _ (Set.subset_univ _)]
  exact Finset.card_univ

private theorem belowCount_mono {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A B : Set W)
    (h : sys.ge A B) : belowCount sys A ≥ belowCount sys B := by
  refine Finset.card_le_card fun S hS => ?_
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, sys.trans _ _ _ h hS.2⟩

private theorem belowCount_strict {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A B : Set W)
    (h : ¬sys.ge A B) : belowCount sys A < belowCount sys B := by
  refine Finset.card_lt_card ⟨fun S hS => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, sys.trans _ _ _ ((sys.total A B).resolve_left h) hS.2⟩
  · have : B.toFinset ∈ Finset.univ.filter (fun S : Finset W => sys.ge A ↑S) :=
      hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Set.coe_toFinset]; exact sys.refl B⟩)
    rw [Finset.mem_filter, Set.coe_toFinset] at this
    exact h this.2

private theorem belowCount_iff {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A B : Set W) :
    belowCount sys A ≥ belowCount sys B ↔ sys.ge A B := by
  refine ⟨fun hcount => by_contra fun hng => ?_, belowCount_mono sys A B⟩
  have := belowCount_strict sys A B hng
  omega

private theorem ge_div_iff {a b d : ℚ} (hd : 0 < d) :
    a / d ≥ b / d ↔ a ≥ b := by
  rw [ge_iff_le, ge_iff_le, div_le_div_iff_of_pos_right hd]

/-- **Theorem 6 completeness** ([holliday-icard-2013], Theorem 6; [van-der-hoek-1996]):
    every FA system is representable by a qualitatively additive measure —
    the dominated-set count, affinely renormalised so μ(∅) = 0 and μ(Ω) = 1. -/
theorem exists_qualAddMeasure_repr {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) :
    ∃ (m : QualAddMeasure ℚ W), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  classical
  set E : ℚ := (belowCount sys ∅ : ℚ) with hE
  set N : ℚ := (Fintype.card (Finset W) : ℚ) with hN
  have hd : (0 : ℚ) < N - E := by
    have := belowCount_strict sys ∅ Set.univ sys.nonTrivial
    rw [belowCount_univ] at this
    exact sub_pos.mpr (by rw [hN, hE]; exact_mod_cast this)
  -- the affine map t ↦ (t − E)/(N − E) is an order isomorphism
  have key : ∀ A B : Set W,
      ((belowCount sys A : ℚ) - E) / (N - E) ≥ ((belowCount sys B : ℚ) - E) / (N - E) ↔
      sys.ge A B := fun A B => by
    rw [ge_div_iff hd, ge_iff_le, sub_le_sub_iff_right, Nat.cast_le]; exact belowCount_iff sys A B
  have hAle : ∀ A : Set W, E ≤ (belowCount sys A : ℚ) := fun A => by
    rw [hE, Nat.cast_le]; exact belowCount_mono sys A ∅ (sys.mono ∅ A (Set.empty_subset A))
  refine ⟨⟨fun A => ((belowCount sys A : ℚ) - E) / (N - E),
    fun A => div_nonneg (sub_nonneg.mpr (hAle A)) hd.le,
    by simp only [← hE, sub_self, zero_div], ?_, ?_⟩, fun A B => (key A B).symm⟩
  · show ((belowCount sys Set.univ : ℚ) - E) / (N - E) = 1
    rw [belowCount_univ, ← hN]; exact div_self hd.ne'
  · intro A B
    show _ ≥ _ ↔ _ ≥ _
    rw [key A B, key (A \ B) (B \ A)]; exact sys.additive A B

/-- Helper: if ge A {b} for every b ∈ B, then ge A B, given monotonicity (T)
    and right-union (J). Proved by Finset induction on B.toFinset. -/
private lemma ge_of_forall_singleton {W : Type*} [Fintype W]
    {ge : Set W → Set W → Prop}
    (hT : EpistemicAxiom.T ge)
    (hJ : EpistemicAxiom.J ge)
    (A B : Set W) (h : ∀ b ∈ B, ge A {b}) : ge A B := by
  classical
  suffices ∀ (s : Finset W), (∀ b, b ∈ s → ge A {b}) → ge A (↑s) by
    rw [← Set.coe_toFinset B]
    exact this B.toFinset (fun b hb => h b (Set.mem_toFinset.mp hb))
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.coe_empty]
    exact hT ∅ A (Set.empty_subset A)
  | @insert b s hbs ih =>
    intro hsub
    rw [Finset.coe_insert]
    exact hJ A _ _ (hsub _ (Finset.mem_insert_self _ _))
      (ih (fun c hc => hsub c (Finset.mem_insert_of_mem hc)))

/-- **Theorem 2** ([halpern-2003], Thm. 7.5.1a; [holliday-icard-2013]):
    an epistemic system satisfying R, T, Tran, J (right-union),
    and DS (determination by singletons) is representable by Lewis's l-lifting
    from a reflexive preorder on worlds.

    The paper states this as a *logic* completeness theorem for **WJR**
    (K + BT + Tran + J + Mon + R). We prove the underlying per-model
    *representation* result, which is the model-theoretic core: the semantic
    hypotheses (R, T, Tran, J, DS) correspond to WJR's axioms evaluated
    on a single model, without formalizing the syntax or proof system.

    Construction: `ge_w u v := sys.ge {u} {v}`. -/
theorem exists_dominationLift_repr {W : Type*} [Fintype W]
    (sys : EpistemicSystemW W)
    (hTran : ∀ A B C : Set W, sys.ge A B → sys.ge B C → sys.ge A C)
    (hJ : EpistemicAxiom.J sys.ge)
    (hDS : EpistemicAxiom.DS sys.ge) :
    ∃ (ge_w : W → W → Prop) (_ : ∀ w, ge_w w w),
      ∀ A B, sys.ge A B ↔ dominationLift ge_w A B := by
  refine ⟨fun u v => sys.ge {u} {v}, fun w => sys.refl {w}, fun A B => ?_⟩
  constructor
  · -- Forward: sys.ge A B → dominationLift (fun u v => sys.ge {u} {v}) A B
    intro hAB b hbB
    -- {b} ⊆ B, so sys.ge B {b} by monotonicity (Axiom T)
    have hBb : sys.ge B {b} := sys.mono {b} B (Set.singleton_subset_iff.mpr hbB)
    -- Transitivity: sys.ge A B → sys.ge B {b} → sys.ge A {b}
    have hAb : sys.ge A {b} := hTran A B {b} hAB hBb
    -- DS: sys.ge A {b} → ∃ a ∈ A, sys.ge {a} {b}
    exact hDS A b hAb
  · -- Backward: dominationLift → sys.ge A B
    intro hLift
    apply ge_of_forall_singleton sys.mono hJ A B
    intro b hbB
    obtain ⟨a, haA, hab⟩ := hLift b hbB
    -- {a} ⊆ A, so sys.ge A {a} by monotonicity
    have hAa : sys.ge A {a} := sys.mono {a} A (Set.singleton_subset_iff.mpr haA)
    -- Transitivity: sys.ge A {a} → sys.ge {a} {b} → sys.ge A {b}
    exact hTran A {a} {b} hAa hab

-- ── Bridge: Axiom A ↔ FA ────────────────────────

/-- Adding a set `C` disjoint from `A` to both sides of a difference leaves
    `A \ B` unchanged: `(A ∪ C) \ (B ∪ C) = A \ B`. -/
private theorem union_diff_union_disjoint {W : Type*} (A B C : Set W)
    (hAC : ∀ x, x ∈ A → x ∉ C) : (A ∪ C) \ (B ∪ C) = A \ B := by
  ext x; simp only [Set.mem_diff, Set.mem_union]
  refine ⟨fun h => h.1.elim (fun hx => ⟨hx, fun hb => h.2 (Or.inl hb)⟩)
    (fun hx => absurd (Or.inr hx) h.2), fun ⟨hxA, hxnB⟩ =>
    ⟨Or.inl hxA, fun h => h.elim hxnB (hAC x hxA)⟩⟩

/-- **Algebraic bridge**: Axiom A and the finite additivity property
    of `AdditiveScale` are equivalent for any comparison on sets. -/
theorem axiomA_iff_fa {W : Type*} (ge : Set W → Set W → Prop) :
    EpistemicAxiom.A ge ↔
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
    rw [Set.diff_union_inter A B, Set.inter_comm A B, Set.diff_union_inter B A] at h
    exact h.symm

end ComparativeProbability
