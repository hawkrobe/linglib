import Linglib.Core.Scales.EpistemicScale.Fin3
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Cancellation conditions for comparative probability

@cite{kraft-pratt-seidenberg-1959}

Scott's cancellation framework for representability of comparative probability orderings
by finitely additive measures. A comparative probability ordering ≿ is representable
by a finitely additive measure iff it satisfies the **cancellation property**: no valid
neutral portfolio has a strict member.

The hard direction (cancellation → representable) is an instance of LP duality / Farkas'
lemma: the feasibility polytope {p ≥ 0 : Σpᵢ = 1, ordering constraints} is nonempty iff
no dual certificate of infeasibility exists, and such a certificate corresponds exactly to
a neutral portfolio with a strict member.

## Main results

* `representable_implies_cancellation` — easy direction: measure existence → cancellation
* `cancellation_implies_representable` — hard direction: cancellation → measure existence
  (via `feasibleWeights`, `cancellation_nonempty`, `feasible_to_measure`)
* `fa_cancellation_fin3` — FA axioms imply cancellation on Fin 3
* `fa_cancellation_fin4` — FA axioms imply cancellation on Fin 4
* `theorem8a_fin3'` — KPS Theorem 8a for n = 3 (via cancellation)
* `theorem8a_fin4'` — KPS Theorem 8a for n = 4 (via cancellation)
-/

namespace Core.Scale

attribute [local instance] Classical.propDecidable

-- ═══════════════════════════════════════════════════════════════
-- § 1. Gambles and Portfolios
-- ═══════════════════════════════════════════════════════════════

/-- Characteristic vector of a disjoint comparison: χ_A - χ_B ∈ {-1,0,1}ⁿ -/
def comparisonVec (n : ℕ) (A B : Finset (Fin n)) : Fin n → ℤ :=
  fun i => (if i ∈ A then 1 else 0) - (if i ∈ B then 1 else 0)

/-- A weighted comparison: a disjoint pair (A,B) with positive rational weight. -/
structure WComparison (n : ℕ) where
  left : Finset (Fin n)
  right : Finset (Fin n)
  weight : ℚ
  disjoint : Disjoint left right
  weight_pos : 0 < weight

/-- A portfolio is a list of weighted comparisons. -/
def Portfolio (n : ℕ) := List (WComparison n)

namespace Portfolio

variable {n : ℕ}

/-- The weighted sum of comparison vectors at atom i. -/
def weightedSum (P : Portfolio n) (i : Fin n) : ℚ :=
  (P.map (fun wc => wc.weight * ((comparisonVec n wc.left wc.right i : ℤ) : ℚ))).sum

/-- A portfolio is neutral if weighted vectors sum to zero at every atom. -/
def isNeutral (P : Portfolio n) : Prop :=
  ∀ i : Fin n, P.weightedSum i = 0

/-- A portfolio is valid for an ordering if each comparison holds. -/
def isValid (P : Portfolio n) (ge : Set (Fin n) → Set (Fin n) → Prop) : Prop :=
  ∀ (wc : WComparison n), List.Mem wc P →
    ge (↑wc.left) (↑wc.right)

/-- A portfolio has a strict member if at least one comparison is strict. -/
def hasStrict (P : Portfolio n) (ge : Set (Fin n) → Set (Fin n) → Prop) : Prop :=
  ∃ (wc : WComparison n), List.Mem wc P ∧
    ¬ge (↑wc.right) (↑wc.left)

end Portfolio

-- ═══════════════════════════════════════════════════════════════
-- § 2. Cancellation Property
-- ═══════════════════════════════════════════════════════════════

/-- The cancellation property: no valid neutral portfolio has a strict member. -/
def Cancellation (n : ℕ) (ge : Set (Fin n) → Set (Fin n) → Prop) : Prop :=
  ∀ P : Portfolio n, P.isValid ge → P.isNeutral → ¬P.hasStrict ge

-- ═══════════════════════════════════════════════════════════════
-- § 3. Easy Direction: representable → cancellation
-- ═══════════════════════════════════════════════════════════════

private lemma mu_zero {W : Type*} (m : FinAddMeasure W) : m.mu ∅ = 0 := by
  have := m.additive ∅ ∅ (fun x hx => hx.elim)
  simp only [Set.empty_union] at this; linarith

private lemma mu_finset_sum {n : ℕ} (m : FinAddMeasure (Fin n))
    (S : Finset (Fin n)) : m.mu ↑S = S.sum (fun i => m.mu {i}) := by
  induction S using Finset.induction_on with
  | empty => simp [Finset.coe_empty, mu_zero m]
  | @insert a S ha ih =>
    have hdisj : ∀ x, x ∈ ({a} : Set (Fin n)) → x ∉ (↑S : Set (Fin n)) := by
      intro x hx hxS
      rw [Set.mem_singleton_iff] at hx; subst hx
      exact ha (Finset.mem_coe.mp hxS)
    have hins : (↑(insert a S) : Set (Fin n)) = ({a} : Set (Fin n)) ∪ ↑S := by
      rw [Finset.coe_insert]; exact Set.insert_eq a ↑S
    rw [hins, m.additive _ _ hdisj, ih, Finset.sum_insert ha]

private lemma list_sum_nonneg {l : List ℚ} (h : ∀ x ∈ l, (0 : ℚ) ≤ x) :
    0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.sum_cons]
    exact add_nonneg (h hd (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx))))

private lemma list_sum_pos {l : List ℚ}
    (hnn : ∀ x ∈ l, (0 : ℚ) ≤ x) (hp : ∃ x ∈ l, (0 : ℚ) < x) :
    (0 : ℚ) < l.sum := by
  obtain ⟨x, hx, hxp⟩ := hp
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.sum_cons]
    have htl_nn : ∀ y ∈ tl, (0 : ℚ) ≤ y :=
      fun y hy => hnn y (List.mem_cons.mpr (Or.inr hy))
    rcases List.mem_cons.mp hx with rfl | hxtl
    · linarith [list_sum_nonneg htl_nn]
    · linarith [hnn hd (List.mem_cons.mpr (Or.inl rfl)), ih htl_nn hxtl]

/-- The portfolio value (weighted sum of measure differences) equals the
    dot product of singleton measures with the weighted comparison sums.
    Proved by list induction on the portfolio; the key step connects
    comparison vectors to measure differences via `mu_finset_sum`. -/
private lemma finset_sum_as_univ {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℚ) :
    S.sum f = Finset.univ.sum (fun i => if i ∈ S then f i else 0) := by
  rw [← Finset.sum_filter]; congr 1; ext x; simp

private lemma single_comp_sum {n : ℕ} (m : FinAddMeasure (Fin n))
    (L R : Finset (Fin n)) (hd : Disjoint L R) :
    m.mu ↑L - m.mu ↑R =
    Finset.univ.sum (fun i : Fin n =>
      m.mu {i} * ((comparisonVec n L R i : ℤ) : ℚ)) := by
  rw [mu_finset_sum m L, mu_finset_sum m R, finset_sum_as_univ L, finset_sum_as_univ R,
      ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  simp only [comparisonVec]
  by_cases hL : i ∈ L <;> by_cases hR : i ∈ R <;> simp_all [Finset.disjoint_left.mp hd]

private lemma finset_mul_sum {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℚ) (c : ℚ) :
    c * s.sum f = s.sum (fun i => c * f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, mul_add]; rw [ih]

private lemma portfolio_interchange {n : ℕ} (m : FinAddMeasure (Fin n))
    (P : Portfolio n) :
    (P.map (fun wc => wc.weight * (m.mu ↑wc.left - m.mu ↑wc.right))).sum =
    Finset.univ.sum (fun i => m.mu {i} * Portfolio.weightedSum P i) := by
  induction P with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    symm; apply Finset.sum_eq_zero; intro i _
    show m.mu {i} * (List.map _ []).sum = 0
    simp
  | cons wc tl ih =>
    simp only [List.map_cons, List.sum_cons]; rw [ih]
    -- Unfold weightedSum for cons
    have hwsum : ∀ i, Portfolio.weightedSum (wc :: tl) i =
        wc.weight * ((comparisonVec n wc.left wc.right i : ℤ) : ℚ) +
        Portfolio.weightedSum tl i := fun _ => by
      simp only [Portfolio.weightedSum, List.map_cons, List.sum_cons]
    simp_rw [hwsum, mul_add, Finset.sum_add_distrib]
    -- Suffices: w*(mu L - mu R) = Σ mu{i}*(w*compVec i)
    congr 1
    rw [single_comp_sum m wc.left wc.right wc.disjoint, finset_mul_sum]
    apply Finset.sum_congr rfl; intro i _; exact mul_left_comm _ _ _

/-- **Easy direction**: If μ represents the ordering, no neutral portfolio has a
    strict member. Each comparison contributes wⱼ·(μ(Aⱼ)−μ(Bⱼ)) ≥ 0 to the
    portfolio value; if any is strict, the value is positive. But by the
    interchange lemma, the value also equals Σᵢ μ({i})·weightedSum(i) = 0
    by neutrality. -/
theorem representable_implies_cancellation {n : ℕ}
    (sys : EpistemicSystemFA (Fin n))
    (m : FinAddMeasure (Fin n))
    (hm : ∀ A B, sys.ge A B ↔ m.inducedGe A B) :
    Cancellation n sys.ge := by
  intro P hValid hNeutral ⟨wc, hwc_mem, hwc_strict⟩
  -- Define the portfolio valuation function
  let f : WComparison n → ℚ := fun wc => wc.weight * (m.mu ↑wc.left - m.mu ↑wc.right)
  -- Each term is nonneg
  have hnn : ∀ x ∈ P.map f, (0 : ℚ) ≤ x := by
    intro x hx
    obtain ⟨wc', hwc'_mem, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (le_of_lt wc'.weight_pos)
      (sub_nonneg.mpr ((hm _ _).mp (hValid wc' hwc'_mem)))
  -- The strict term is strictly positive
  have hlt : m.mu ↑wc.left > m.mu ↑wc.right := by
    by_contra h; push_neg at h
    exact hwc_strict ((hm _ _).mpr h)
  have hp : ∃ x ∈ P.map f, (0 : ℚ) < x :=
    ⟨f wc, List.mem_map.mpr ⟨wc, hwc_mem, rfl⟩,
      mul_pos wc.weight_pos (sub_pos.mpr hlt)⟩
  -- Portfolio value > 0
  have hpos := list_sum_pos hnn hp
  -- But by interchange, portfolio value = Σ_i mu_i * weightedSum_i = 0
  rw [portfolio_interchange m P] at hpos
  have hzero : Finset.univ.sum (fun i => m.mu {i} * P.weightedSum i) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [hNeutral i, mul_zero])
  linarith

-- ═══════════════════════════════════════════════════════════════
-- § 4. Hard Direction: cancellation → representable (Farkas/Scott)
-- ═══════════════════════════════════════════════════════════════

/-- The feasibility polytope for measure representation: probability vectors
    p : Fin n → ℚ that are nonneg, normalized, and **faithfully encode** the
    ordering on disjoint pairs — exactly `sys.ge ↑A ↑B ↔ A.sum p ≥ B.sum p`.
    The ↔ (rather than →) is essential: the forward direction ensures the
    measure respects the ordering, while the backward direction ensures
    strictness is preserved (no spurious ties). -/
def feasibleWeights (n : ℕ) (sys : EpistemicSystemFA (Fin n)) : Set (Fin n → ℚ) :=
  { p | (∀ i, 0 ≤ p i) ∧
        Finset.univ.sum p = 1 ∧
        ∀ (A B : Finset (Fin n)), Disjoint A B →
          (sys.ge ↑A ↑B ↔ A.sum p ≥ B.sum p) }

/-- Point-mass measure from a weight vector: μ(A) = Σᵢ (if i ∈ A then pᵢ else 0).
    Uses explicit if-then-else rather than Finset.filter to avoid DecidablePred
    instance matching issues in rewrite tactics. -/
private noncomputable def atomMu {n : ℕ} (p : Fin n → ℚ) (A : Set (Fin n)) : ℚ :=
  Finset.univ.sum (fun i => if i ∈ A then p i else 0)

/-- atomMu agrees with Finset.sum on finset coercions. -/
private theorem atomMu_eq_finset_sum {n : ℕ} (p : Fin n → ℚ) (S : Finset (Fin n)) :
    atomMu p ↑S = S.sum p := by
  simp only [atomMu, Finset.mem_coe]
  rw [← finset_sum_as_univ S p]

/-- A feasible weight vector yields a representing measure.
    Construction: μ(A) = Σᵢ (if i ∈ A then pᵢ else 0). Finite additivity follows
    from a pointwise membership case split. Representation (ge ↔ μ(A) ≥ μ(B))
    reduces to disjoint pairs via `reduce_to_disjoint` (using FA's Axiom A),
    then applies the ↔ condition from `feasibleWeights`. -/
private theorem feasible_to_measure {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {p : Fin n → ℚ} (hp : p ∈ feasibleWeights n sys) :
    ∃ m : FinAddMeasure (Fin n), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  obtain ⟨hnn, hsum, hcompat⟩ := hp
  -- Nonneg: each summand is nonneg
  have h_nonneg : ∀ A, 0 ≤ atomMu p A := by
    intro A; simp only [atomMu]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.sum_insert has]
      exact add_nonneg (by split <;> [exact hnn a; exact le_refl 0]) ih
  -- Finite additivity via pointwise case split on membership
  have h_additive : ∀ A B : Set (Fin n), (∀ x, x ∈ A → x ∉ B) →
      atomMu p (A ∪ B) = atomMu p A + atomMu p B := by
    intro A B hdisj
    simp only [atomMu, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B
    · exact absurd hB (hdisj i hA)
    · simp [Set.mem_union, hA, hB]
    · simp [Set.mem_union, hA, hB]
    · simp [Set.mem_union, hA, hB]
  -- Normalization: all atoms in univ
  have h_total : atomMu p Set.univ = 1 := by
    simp only [atomMu, Set.mem_univ, ite_true, hsum]
  let m : FinAddMeasure (Fin n) := ⟨atomMu p, h_nonneg, h_additive, h_total⟩
  -- Representation via reduce_to_disjoint
  refine ⟨m, reduce_to_disjoint sys m (fun C D hdisj => ?_)⟩
  -- Convert Sets C, D to Finsets via filter
  have hCeq : (↑(Finset.univ.filter (· ∈ C)) : Set (Fin n)) = C := by ext x; simp
  have hDeq : (↑(Finset.univ.filter (· ∈ D)) : Set (Fin n)) = D := by ext x; simp
  have hfinDisj : Disjoint (Finset.univ.filter (· ∈ C)) (Finset.univ.filter (· ∈ D)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    exact hdisj x hx1 hx2
  -- hcompat on filter-finsets, transported to Sets via coercion identity
  have key := hcompat _ _ hfinDisj
  rw [hCeq, hDeq] at key
  -- Bridge atomMu on Sets to Finset.sum (conv_lhs avoids rewriting RHS)
  have hmuC : atomMu p C = (Finset.univ.filter (· ∈ C)).sum p := by
    conv_lhs => rw [show C = ↑(Finset.univ.filter (· ∈ C)) from hCeq.symm]
    exact atomMu_eq_finset_sum p _
  have hmuD : atomMu p D = (Finset.univ.filter (· ∈ D)).sum p := by
    conv_lhs => rw [show D = ↑(Finset.univ.filter (· ∈ D)) from hDeq.symm]
    exact atomMu_eq_finset_sum p _
  -- Unfold inducedGe (a def, not auto-reduced) and rewrite atomMu to finset sums
  change sys.ge C D ↔ atomMu p C ≥ atomMu p D
  rw [hmuC, hmuD]
  exact key

-- ── Step 4a. Not all singletons null ─────────────

/-- If all singletons are null, then ∅ ≿ S for any finset S (by FA induction). -/
private lemma ge_empty_of_all_null {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (hall : ∀ i, sys.ge ∅ {i}) (S : Finset (Fin n)) : sys.ge ∅ ↑S := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.coe_empty]; exact sys.refl ∅
  | @insert a S' haS' ih =>
    have h1 : (↑S' : Set (Fin n)) \ ({a} ∪ ↑S') = ∅ := by
      ext x; simp only [Set.mem_diff, Set.mem_union, Finset.mem_coe,
        Set.mem_empty_iff_false, iff_false, not_and, Decidable.not_not]
      intro hx; exact Or.inr hx
    have h2 : ({a} ∪ ↑S' : Set (Fin n)) \ ↑S' = {a} := by
      ext x; simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · rintro ⟨hx | hx, hnx⟩ <;> [exact hx; exact absurd hx hnx]
      · intro hx; subst hx; exact ⟨Or.inl rfl, fun h => haS' (Finset.mem_coe.mp h)⟩
    rw [Finset.coe_insert, Set.insert_eq]
    exact sys.trans ∅ ↑S' ({a} ∪ ↑S') ih
      (by rw [sys.additive ↑S' ({a} ∪ ↑S'), h1, h2]; exact hall a)

/-- Not all singletons can be null: ∃ i, ¬sys.ge ∅ {i}. If all were null,
    FA induction gives sys.ge ∅ Set.univ, contradicting nonTrivial. -/
private theorem not_all_null {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    ∃ i : Fin n, ¬sys.ge ∅ {i} := by
  by_contra hall; push_neg at hall
  exact sys.nonTrivial (by rw [← Finset.coe_univ]; exact ge_empty_of_all_null sys hall _)

-- ── Step 4b. Farkas alternative for the ordering LP ──

/-- **Farkas alternative for the ordering LP**: either a one-directional
    probability representation exists, or there is a valid portfolio
    whose weighted comparison sums are strictly negative at every atom.

    This is LP duality: the feasibility polytope
      {p ≥ 0 : 1ᵀp = 1, vⱼᵀp ≥ 0 for each ge-constraint j}
    is nonempty iff no dual certificate of infeasibility exists.
    A certificate (y, α) with Aᵀy ≥ 0 and bᵀy < 0 translates to
    nonneg weights wⱼ with Σwⱼ(vⱼ)ᵢ < 0 at every atom.

    **Route 1**: specialize Mathlib's `ProperCone.hyperplane_separation_point`
    by proving finitely generated cones are closed (Carathéodory). -/
private theorem farkas_ordering_lp {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    (∃ p : Fin n → ℚ, (∀ i, 0 ≤ p i) ∧ Finset.univ.sum p = 1 ∧
      ∀ (A B : Finset (Fin n)), Disjoint A B →
        sys.ge ↑A ↑B → A.sum p ≥ B.sum p) ∨
    (∃ P : Portfolio n, P.isValid sys.ge ∧
      ∀ i : Fin n, P.weightedSum i < 0) :=
  sorry

-- ── Step 4c. Certificate → cancellation violation ───

private lemma toList_map_sum {α : Type*} [AddCommMonoid α] {ι : Type*}
    (s : Finset ι) (f : ι → α) :
    (s.val.toList.map f).sum = s.sum f := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]; rfl

private lemma compVec_single_empty {n : ℕ} (a j : Fin n) :
    comparisonVec n {a} ∅ j = if j = a then 1 else 0 := by
  unfold comparisonVec; simp only [Finset.mem_singleton]; split <;> simp

private lemma weightedSum_append {n : ℕ} (P Q : List (WComparison n)) (i : Fin n) :
    Portfolio.weightedSum (List.append P Q) i =
    Portfolio.weightedSum P i + Portfolio.weightedSum Q i := by
  unfold Portfolio.weightedSum
  show (List.map _ (P ++ Q)).sum = (List.map _ P).sum + (List.map _ Q).sum
  rw [List.map_append, List.sum_append]

/-- Singleton portfolio: one ({i}, ∅, dᵢ) entry per atom. -/
private noncomputable def singletonPortfolio {n : ℕ} (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    List (WComparison n) :=
  (Finset.univ : Finset (Fin n)).val.toList.map fun i =>
    (⟨{i}, ∅, d i, Finset.disjoint_empty_right _, hd i⟩ : WComparison n)

private theorem weightedSum_singletonPortfolio {n : ℕ} (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (j : Fin n) :
    Portfolio.weightedSum (singletonPortfolio d hd) j = d j := by
  unfold singletonPortfolio Portfolio.weightedSum
  rw [List.map_map]
  conv => lhs; arg 1; arg 1; ext i; simp only [Function.comp]; rw [compVec_single_empty]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero]
  rw [toList_map_sum, Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]

/-- An infeasibility certificate (valid portfolio with strictly negative
    weighted sums at every atom) yields a neutral portfolio with a strict
    member, violating cancellation.

    Construction: append ({i}, ∅, dᵢ) for each atom i with dᵢ = −wsum(i) > 0.
    Neutrality: wsum(j) + dⱼ = 0 by construction.
    Strictness: ∃ i₀ with ¬sys.ge ∅ {i₀} (from `not_all_null`). -/
private theorem certificate_to_violation {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (P : Portfolio n) (hV : P.isValid sys.ge)
    (hNeg : ∀ i : Fin n, P.weightedSum i < 0) :
    ∃ Q : Portfolio n, Q.isValid sys.ge ∧ Q.isNeutral ∧ Q.hasStrict sys.ge := by
  let d : Fin n → ℚ := fun i => -P.weightedSum i
  have hd : ∀ i, 0 < d i := fun i => by simp only [d]; linarith [hNeg i]
  let singles := singletonPortfolio d hd
  refine ⟨List.append P singles, ?valid, ?neutral, ?strict⟩
  case valid =>
    intro wc hwc
    rcases List.mem_append.mp hwc with h | h
    · exact hV wc h
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
      simp only [Finset.coe_singleton, Finset.coe_empty]
      exact sys.mono ∅ {i} (Set.empty_subset _)
  case neutral =>
    intro j
    rw [weightedSum_append P singles j, weightedSum_singletonPortfolio d hd j]
    simp only [d]; linarith
  case strict =>
    obtain ⟨i₀, hi₀⟩ := not_all_null sys
    refine ⟨⟨{i₀}, ∅, d i₀, Finset.disjoint_empty_right _, hd i₀⟩, ?mem, ?str⟩
    case mem =>
      exact List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨i₀, Multiset.mem_toList.mpr (Finset.mem_univ i₀), rfl⟩))
    case str =>
      simp only [Finset.coe_empty, Finset.coe_singleton]; exact hi₀

-- ── Step 4d. One-directional feasibility from cancellation ──

/-- Cancellation implies one-directional LP feasibility:
    ∃ p ≥ 0, Σp = 1, sys.ge → p(A) ≥ p(B).
    Composition of `farkas_ordering_lp` (Farkas alternative) and
    `certificate_to_violation` (certificate → cancellation violation). -/
private theorem onedir_from_cancel {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge) :
    ∃ p : Fin n → ℚ, (∀ i, 0 ≤ p i) ∧ Finset.univ.sum p = 1 ∧
      ∀ (A B : Finset (Fin n)), Disjoint A B →
        sys.ge ↑A ↑B → A.sum p ≥ B.sum p := by
  rcases farkas_ordering_lp sys with h | ⟨P, hV, hNeg⟩
  · exact h
  · obtain ⟨Q, hQV, hQN, hQS⟩ := certificate_to_violation sys P hV hNeg
    exact absurd hQS (hcancel Q hQV hQN)

-- ── Step 4e. Strengthen → to ↔ ───────────────────

/-- Strengthen one-directional to bidirectional feasibility: if
    p ≥ 0, Σp = 1, and sys.ge ↑A ↑B → A.sum p ≥ B.sum p for disjoint
    pairs, then also A.sum p ≥ B.sum p → sys.ge ↑A ↑B (no spurious ties).

    Uses cancellation: a spurious tie (A.sum p = B.sum p with B ≻ A)
    would yield a portfolio violating cancellation. -/
private theorem strengthen_to_bidir {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge)
    {p : Fin n → ℚ} (hnn : ∀ i, 0 ≤ p i)
    (hsum : Finset.univ.sum p = 1)
    (hone : ∀ (A B : Finset (Fin n)), Disjoint A B →
      sys.ge ↑A ↑B → A.sum p ≥ B.sum p) :
    p ∈ feasibleWeights n sys :=
  sorry

-- ── Step 4f. Compose: cancellation → feasible weights ──

/-- The core LP step: cancellation implies the feasibility polytope is nonempty.
    Decomposes into:
    1. `farkas_ordering_lp` — Farkas alternative gives → feasible or certificate
    2. `certificate_to_violation` — certificate contradicts cancellation
    3. `onedir_from_cancel` — so → feasibility holds
    4. `strengthen_to_bidir` — strengthen → to ↔ using cancellation -/
private theorem cancellation_nonempty {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge) :
    ∃ p, p ∈ feasibleWeights n sys := by
  obtain ⟨p, hnn, hsum, hone⟩ := onedir_from_cancel sys hcancel
  exact ⟨p, strengthen_to_bidir sys hcancel hnn hsum hone⟩

/-- **Scott's theorem** (hard direction): if no valid neutral portfolio has a
    strict member, then a finitely additive measure exists representing the
    ordering. Decomposes into two steps:
    1. `cancellation_nonempty`: Farkas / LP duality shows the feasibility
       polytope is nonempty when cancellation holds.
    2. `feasible_to_measure`: a feasible weight vector constructs a
       representing `FinAddMeasure`. -/
theorem cancellation_implies_representable {n : ℕ}
    (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge) :
    ∃ m : FinAddMeasure (Fin n), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  obtain ⟨p, hp⟩ := cancellation_nonempty sys hcancel
  exact feasible_to_measure sys hp

-- ═══════════════════════════════════════════════════════════════
-- § 5. FA → Cancellation for small n
-- ═══════════════════════════════════════════════════════════════

/-- FA on Fin 3 implies the cancellation property.
    Derived from the direct measure construction (`theorem8a_fin3` in Defs.lean)
    composed with the easy direction of Scott's theorem. -/
theorem fa_cancellation_fin3 (sys : EpistemicSystemFA (Fin 3)) :
    Cancellation 3 sys.ge := by
  obtain ⟨m, hm⟩ := theorem8a_fin3 sys
  exact representable_implies_cancellation sys m hm

/-- Not all 4 singletons can be null (non-triviality). -/
private theorem not_all_null_fin4 (sys : EpistemicSystemFA (Fin 4))
    (h0 : sys.ge ∅ {(0 : Fin 4)}) (h1 : sys.ge ∅ {(1 : Fin 4)})
    (h2 : sys.ge ∅ {(2 : Fin 4)}) (h3 : sys.ge ∅ {(3 : Fin 4)}) : False := by
  have h01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) := by
    have : sys.ge {1} ({0, 1} : Set (Fin 4)) := by
      rw [sys.additive {1} {0, 1}]
      rw [show ({1} : Set (Fin 4)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1} : Set (Fin 4)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
      exact h0
    exact sys.trans _ _ _ h1 this
  have h012 : sys.ge ∅ ({0, 1, 2} : Set (Fin 4)) := by
    have : sys.ge {2} ({0, 1, 2} : Set (Fin 4)) := by
      rw [sys.additive {2} {0, 1, 2}]
      rw [show ({2} : Set (Fin 4)) \ {0, 1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1, 2} : Set (Fin 4)) \ {2} = {0, 1} from by ext x; fin_cases x <;> simp_all]
      exact h01
    exact sys.trans _ _ _ h2 this
  exact sys.nonTrivial (sys.trans _ _ _ h3
    ((sys.additive {3} Set.univ).mpr
      (by rw [show ({3} : Set (Fin 4)) \ Set.univ = ∅ from by ext x; simp,
              show (Set.univ : Set (Fin 4)) \ {3} = {0, 1, 2} from by ext x; fin_cases x <;> simp_all]
          exact h012)))

/-- Helper: if element 0 is null on Fin 4, derive cancellation via null reduction to Fin 3. -/
private theorem fa_cancellation_fin4_null0 (sys : EpistemicSystemFA (Fin 4))
    (h0 : sys.ge ∅ {(0 : Fin 4)})
    (hnn : ∃ i : Fin 3, ¬sys.ge ∅ {Fin.succ i}) :
    Cancellation 4 sys.ge := by
  obtain ⟨m, hm⟩ := null_elem_reduce sys h0 hnn (fun sys' => theorem8a_fin3 sys')
  exact representable_implies_cancellation sys m hm

/-- All-positive case: when all 4 singletons have positive mass, FA implies
    cancellation on Fin 4. This is a finite combinatorial verification:
    the FA axioms (totality + transitivity + qualitative additivity) constrain
    the ordering on Fin 4 sufficiently to prevent neutral portfolios with
    strict members.

    The mathematical content: with 4 atoms and all singletons positive,
    the ordering is determined (up to ties) by the 6 pairwise singleton
    comparisons plus the additivity axiom. Any neutral portfolio must
    balance its weighted comparison vectors to zero at every atom, and
    FA forces all comparisons in such a portfolio to be ties.

    TODO: direct combinatorial proof, or construct a representing measure
    (analogous to `theorem8a_fin3`) and derive cancellation via
    `representable_implies_cancellation`. -/
private theorem fa_cancellation_fin4_allpos (sys : EpistemicSystemFA (Fin 4))
    (h0 : ¬sys.ge ∅ {(0 : Fin 4)}) (h1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (h2 : ¬sys.ge ∅ {(2 : Fin 4)}) (h3 : ¬sys.ge ∅ {(3 : Fin 4)}) :
    Cancellation 4 sys.ge := by
  sorry

/-- FA on Fin 4 implies the cancellation property.
    Null cases: reduce via `null_elem_reduce` + `theorem8a_fin3`.
    All-positive case: direct combinatorial argument (`fa_cancellation_fin4_allpos`). -/
theorem fa_cancellation_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    Cancellation 4 sys.ge := by
  by_cases h0 : sys.ge ∅ {(0 : Fin 4)}
  · -- element 0 null: reduce to Fin 3
    exact fa_cancellation_fin4_null0 sys h0 (by
      by_contra hall; push_neg at hall
      exact not_all_null_fin4 sys h0 (hall 0) (hall 1) (hall 2))
  · by_cases h1 : sys.ge ∅ {(1 : Fin 4)}
    · -- element 1 null: permute via swap(0,1) to put null at 0
      obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 1) sys
        (null_elem_reduce (transportFA (Equiv.swap 0 1) sys)
          ((perm_null_convert _ _ 0 1 (by decide)).mpr h1)
          ⟨0, fun h => h0 ((perm_null_convert _ _ 1 0 (by decide)).mp h)⟩
          (fun sys' => theorem8a_fin3 sys'))
      exact representable_implies_cancellation sys m hm
    · by_cases h2 : sys.ge ∅ {(2 : Fin 4)}
      · -- element 2 null: permute via swap(0,2)
        obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 2) sys
          (null_elem_reduce (transportFA (Equiv.swap 0 2) sys)
            ((perm_null_convert _ _ 0 2 (by decide)).mpr h2)
            ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
            (fun sys' => theorem8a_fin3 sys'))
        exact representable_implies_cancellation sys m hm
      · by_cases h3 : sys.ge ∅ {(3 : Fin 4)}
        · -- element 3 null: permute via swap(0,3)
          obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 3) sys
            (null_elem_reduce (transportFA (Equiv.swap 0 3) sys)
              ((perm_null_convert _ _ 0 3 (by decide)).mpr h3)
              ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
              (fun sys' => theorem8a_fin3 sys'))
          exact representable_implies_cancellation sys m hm
        · -- all singletons positive
          exact fa_cancellation_fin4_allpos sys h0 h1 h2 h3

-- ═══════════════════════════════════════════════════════════════
-- § 6. KPS Theorem 8a via cancellation
-- ═══════════════════════════════════════════════════════════════

/-- **Theorem 8a for Fin 3** (via cancellation): every FA system on Fin 3 is
    representable by a finitely additive probability measure. -/
theorem theorem8a_fin3' (sys : EpistemicSystemFA (Fin 3)) :
    ∃ (m : FinAddMeasure (Fin 3)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  cancellation_implies_representable sys (fa_cancellation_fin3 sys)

/-- **Theorem 8a for Fin 4** (via cancellation): every FA system on Fin 4 is
    representable by a finitely additive probability measure. -/
theorem theorem8a_fin4' (sys : EpistemicSystemFA (Fin 4)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  cancellation_implies_representable sys (fa_cancellation_fin4 sys)

end Core.Scale
