import Linglib.Core.Scales.EpistemicScale.Fin3
import Linglib.Core.Polyhedral
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Field

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
* `fa_cancellation_fin4` — FA axioms imply cancellation on Fin 4 (in `Cancellation88.lean`)
* `theorem8a_fin3'` — KPS Theorem 8a for n = 3 (via cancellation)
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

-- ── Step 4b. Farkas alternative (→ version) ─────

private lemma finRange_map_sum {α : Type*} [AddCommMonoid α] {k : ℕ} (f : Fin k → α) :
    ((List.finRange k).map f).sum = ∑ i : Fin k, f i := by
  induction k with
  | zero => simp [List.finRange]
  | succ k ih =>
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
    rw [ih (f ∘ Fin.succ), Fin.sum_univ_succ]; simp [Function.comp]

/-- Split a sum over `Fin ((n + 2) + k)` into nonneg + normUp + normLo + ordering. -/
private lemma sum_split_n2k {n k : ℕ} (f : Fin ((n + 2) + k) → ℚ) :
    ∑ i : Fin ((n + 2) + k), f i =
    (∑ i : Fin n, f ⟨i.val, by omega⟩) +
    f ⟨n, by omega⟩ + f ⟨n + 1, by omega⟩ +
    (∑ m : Fin k, f ⟨n + 2 + m.val, by omega⟩) := by
  simp only [Fin.sum_univ_add, Fin.sum_univ_two, Fin.natAdd, Fin.castAdd, Fin.castLE,
    Fin.val_zero, Fin.val_one, Nat.add_zero, add_assoc]

/-- The comparison-vector dot product equals the finset-sum difference. -/
private lemma compVec_as_sum_diff {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → ℚ)
    (hdisj : Disjoint A B) :
    ∑ j : Fin n, ((comparisonVec n A B j : ℤ) : ℚ) * x j = A.sum x - B.sum x := by
  rw [finset_sum_as_univ A x, finset_sum_as_univ B x, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [comparisonVec]
  by_cases hA : j ∈ A <;> by_cases hB : j ∈ B
  · exact absurd hB (Finset.disjoint_left.mp hdisj hA)
  · simp [hA, hB]
  · simp [hA, hB]
  · simp [hA, hB]

/-- Construct a portfolio from Fin-indexed data: pairs with positive weights. -/
private noncomputable def portfolioOfWeights {n : ℕ}
    (pairs : List (Finset (Fin n) × Finset (Fin n)))
    (ws : Fin pairs.length → ℚ)
    (h_disj : ∀ m : Fin pairs.length, Disjoint (pairs.get m).1 (pairs.get m).2)
    (h_pos : ∀ m : Fin pairs.length, 0 < ws m) :
    Portfolio n :=
  (List.finRange pairs.length).map fun m =>
    ⟨(pairs.get m).1, (pairs.get m).2, ws m, h_disj m, h_pos m⟩

/-- The weighted sum of `portfolioOfWeights` equals the Fin-indexed sum. -/
private theorem weightedSum_portfolioOfWeights {n : ℕ}
    (pairs : List (Finset (Fin n) × Finset (Fin n)))
    (ws : Fin pairs.length → ℚ)
    (h_disj : ∀ m, Disjoint (pairs.get m).1 (pairs.get m).2)
    (h_pos : ∀ m, 0 < ws m) (j : Fin n) :
    Portfolio.weightedSum (portfolioOfWeights pairs ws h_disj h_pos) j =
    ∑ m : Fin pairs.length,
      ws m * ((comparisonVec n (pairs.get m).1 (pairs.get m).2 j : ℤ) : ℚ) := by
  simp only [portfolioOfWeights, Portfolio.weightedSum, List.map_map, Function.comp]
  exact finRange_map_sum _

/-- Validity of `portfolioOfWeights`: each entry's pair has `ge`. -/
private theorem isValid_portfolioOfWeights {n : ℕ}
    (pairs : List (Finset (Fin n) × Finset (Fin n)))
    (ws : Fin pairs.length → ℚ)
    (h_disj : ∀ m, Disjoint (pairs.get m).1 (pairs.get m).2)
    (h_pos : ∀ m, 0 < ws m)
    (ge : Set (Fin n) → Set (Fin n) → Prop)
    (h_ge : ∀ m : Fin pairs.length, ge ↑(pairs.get m).1 ↑(pairs.get m).2) :
    (portfolioOfWeights pairs ws h_disj h_pos).isValid ge := by
  intro wc hwc
  simp only [portfolioOfWeights] at hwc
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hwc
  exact h_ge m

/-- **Farkas alternative for the ordering LP**: either a one-directional
    probability representation exists, or there is a valid portfolio
    whose weighted comparison sums are strictly negative at every atom.

    Applies `Polyhedral.farkas` to the system encoding the ordering LP
    {p ≥ 0, 1ᵀp = 1, compVec(A,B)·p ≥ 0 for each ge-pair}, then maps
    both Farkas alternatives back to the goal.

    Note: this gives the **one-directional** (→) condition only.
    Strengthening to ↔ requires `cancel_strengthens_to_bidir`. -/
private theorem farkas_ordering_lp {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    (∃ p : Fin n → ℚ, (∀ i, 0 ≤ p i) ∧ Finset.univ.sum p = 1 ∧
      ∀ (A B : Finset (Fin n)), Disjoint A B →
        sys.ge ↑A ↑B → A.sum p ≥ B.sum p) ∨
    (∃ P : Portfolio n, P.isValid sys.ge ∧
      ∀ i : Fin n, P.weightedSum i < 0) := by
  -- Enumerate all disjoint ge-pairs
  let gePairs : List (Finset (Fin n) × Finset (Fin n)) :=
    ((Finset.univ ×ˢ Finset.univ : Finset _).filter
      (fun ab => Disjoint ab.1 ab.2 ∧ sys.ge ↑ab.1 ↑ab.2)).toList
  let k := gePairs.length
  -- Constraint function: n nonnegativity + 1 normUp + 1 normLo + k ordering
  let ineqFn : Fin ((n + 2) + k) → Polyhedral.Ineq n := fun i =>
    if h : i.val < n then
      ⟨fun j => if j = ⟨i.val, h⟩ then -1 else 0, 0⟩
    else if _ : i.val = n then
      ⟨fun _ => 1, 1⟩
    else if _ : i.val = n + 1 then
      ⟨fun _ => -1, -1⟩
    else
      have hm : i.val - (n + 2) < k := by omega
      let pair := gePairs.get ⟨i.val - (n + 2), hm⟩
      ⟨fun j => -(((comparisonVec n pair.1 pair.2 j : ℤ) : ℚ)), 0⟩
  let S : Polyhedral.System n := List.ofFn ineqFn
  have hget : ∀ i : Fin ((n + 2) + k), ineqFn i ∈ S :=
    fun i => List.mem_ofFn.mpr ⟨i, rfl⟩
  have hgePairsMem : ∀ (A B : Finset (Fin n)), Disjoint A B → sys.ge ↑A ↑B →
      (A, B) ∈ gePairs := by
    intro A B hd hge
    simp only [gePairs, Finset.mem_toList, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ⟨hd, hge⟩
  have hgePairsDisj : ∀ m : Fin k, Disjoint (gePairs.get m).1 (gePairs.get m).2 := by
    intro ⟨m, hm⟩
    have := List.get_mem gePairs ⟨m, hm⟩
    simp only [gePairs, Finset.mem_toList, Finset.mem_filter] at this
    exact this.2.1
  have hgePairsGe : ∀ m : Fin k, sys.ge ↑(gePairs.get m).1 ↑(gePairs.get m).2 := by
    intro ⟨m, hm⟩
    have := List.get_mem gePairs ⟨m, hm⟩
    simp only [gePairs, Finset.mem_toList, Finset.mem_filter] at this
    exact this.2.2
  -- Apply Farkas
  rcases Polyhedral.farkas S with ⟨x, hx⟩ | hcert
  · -- ═══ Feasible case: extract probability vector ═══
    left
    have hsat : ∀ i : Fin ((n + 2) + k), (ineqFn i).sat x := fun i => hx _ (hget i)
    refine ⟨x, ?_, ?_, ?_⟩
    · -- Nonnegativity: from constraint -xᵢ ≤ 0
      intro i
      have h := hsat ⟨i.val, by omega⟩
      simp only [ineqFn, dif_pos i.isLt, Polyhedral.Ineq.sat, Polyhedral.dot] at h
      simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true] at h
      linarith
    · -- Normalization: from 1ᵀx ≤ 1 and -1ᵀx ≤ -1
      have h_up := hsat ⟨n, by omega⟩
      have h_lo := hsat ⟨n + 1, by omega⟩
      have hup_eq : ineqFn ⟨n, by omega⟩ = ⟨fun (_ : Fin n) => (1 : ℚ), 1⟩ := by
        simp [ineqFn]
      have hlo_eq : ineqFn ⟨n + 1, by omega⟩ = ⟨fun (_ : Fin n) => (-1 : ℚ), -1⟩ := by
        simp [ineqFn]
      rw [Polyhedral.Ineq.sat, Polyhedral.dot, hup_eq] at h_up
      rw [Polyhedral.Ineq.sat, Polyhedral.dot, hlo_eq] at h_lo
      simp only [one_mul] at h_up
      simp only [neg_one_mul, Finset.sum_neg_distrib] at h_lo
      linarith
    · -- Ordering: from -(compVec · x) ≤ 0
      intro A B hdisj hge
      obtain ⟨⟨m, hm⟩, hget_m⟩ := List.mem_iff_get.mp (hgePairsMem A B hdisj hge)
      have h := hsat ⟨n + 2 + m, by omega⟩
      have hord_eq : ineqFn ⟨n + 2 + m, by omega⟩ =
          ⟨fun j => -(((comparisonVec n (gePairs.get ⟨m, hm⟩).1
            (gePairs.get ⟨m, hm⟩).2 j : ℤ) : ℚ)), 0⟩ := by
        simp [ineqFn, show ¬(n + 2 + m < n) from by omega,
          show ¬(n + 2 + m = n) from by omega,
          show ¬(n + 2 + m = n + 1) from by omega]
      rw [Polyhedral.Ineq.sat, Polyhedral.dot, hord_eq] at h
      simp only [hget_m, neg_mul, Finset.sum_neg_distrib] at h
      linarith [compVec_as_sum_diff A B x hdisj]
  · -- ═══ Certificate case: build portfolio with negative weighted sums ═══
    right
    obtain ⟨cert⟩ := hcert
    have hlen : S.length = (n + 2) + k := List.length_ofFn
    have hS_get : ∀ i : Fin S.length,
        S.get i = ineqFn (i.cast hlen) := fun i => List.get_ofFn ineqFn i
    -- Cast cert weights to natural indices
    let ws : Fin ((n + 2) + k) → ℚ := fun i => cert.ws (i.cast hlen.symm)
    have ws_nn : ∀ i, 0 ≤ ws i := fun i => cert.nonneg _
    -- Transport: reindex sums from Fin S.length to Fin ((n+2)+k)
    have hreindex : ∀ f : Fin S.length → ℚ,
        ∑ i : Fin S.length, f i =
        ∑ i : Fin ((n + 2) + k), f (i.cast hlen.symm) :=
      fun f => Fintype.sum_equiv (finCongr hlen) _ _ (fun i => by simp [finCongr])
    have hcoeffsZero : ∀ j : Fin n,
        ∑ i : Fin ((n + 2) + k), ws i * (ineqFn i).lhs j = 0 := by
      intro j
      have h := cert.coeffsZero j
      rw [hreindex] at h; simp_rw [hS_get] at h; exact h
    have hboundNeg :
        ∑ i : Fin ((n + 2) + k), ws i * (ineqFn i).rhs < 0 := by
      have h := cert.boundNeg
      rw [hreindex] at h; simp_rw [hS_get] at h; exact h
    -- Decompose boundNeg: ws(n) - ws(n+1) < 0
    have hbound_decomp : ws ⟨n, by omega⟩ - ws ⟨n + 1, by omega⟩ < 0 := by
      have h := hboundNeg
      rw [sum_split_n2k] at h
      have h_nn_zero : ∑ i : Fin n, ws ⟨i.val, by omega⟩ * (ineqFn ⟨i.val, by omega⟩).rhs = 0 :=
        Finset.sum_eq_zero fun i _ => by simp [ineqFn, dif_pos i.isLt]
      have h_ord_zero : ∑ m : Fin k, ws ⟨n + 2 + m.val, by omega⟩ *
          (ineqFn ⟨n + 2 + m.val, by omega⟩).rhs = 0 :=
        Finset.sum_eq_zero fun m _ => by
          have : ineqFn ⟨n + 2 + m.val, by omega⟩ =
              ⟨fun j => -(((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
                (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ)), 0⟩ := by
            simp [ineqFn, show ¬(n + 2 + m.val < n) from by omega,
              show ¬(n + 2 + m.val = n) from by omega,
              show ¬(n + 2 + m.val = n + 1) from by omega]
          rw [this]; exact mul_zero _
      have h_up : (ineqFn ⟨n, by omega⟩).rhs = 1 := by simp [ineqFn]
      have h_lo : (ineqFn ⟨n + 1, by omega⟩).rhs = -1 := by
        simp [ineqFn, show ¬(n + 1 < n) from by omega]
      simp only [h_nn_zero, h_ord_zero, h_up, h_lo, zero_add, add_zero] at h; linarith
    -- Helper: evaluate ineqFn at nonneg/norm/ordering indices
    have hineq_nn : ∀ (i : Fin n) (j : Fin n),
        (ineqFn ⟨i.val, by omega⟩).lhs j = if j = i then -1 else 0 := by
      intro i _; simp only [ineqFn, dif_pos i.isLt]
    have hineq_up : ∀ j : Fin n, (ineqFn ⟨n, by omega⟩).lhs j = 1 := by
      intro _; simp [ineqFn]
    have hineq_lo : ∀ j : Fin n, (ineqFn ⟨n + 1, by omega⟩).lhs j = -1 := by
      intro _; simp [ineqFn, show ¬(n + 1 < n) from by omega]
    have hineq_ord : ∀ (m : Fin k) (j : Fin n),
        (ineqFn ⟨n + 2 + m.val, by omega⟩).lhs j =
        -(((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
            (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ)) := by
      intro m _
      simp [ineqFn, show ¬(n + 2 + m.val < n) from by omega,
        show ¬(n + 2 + m.val = n) from by omega,
        show ¬(n + 2 + m.val = n + 1) from by omega]
    -- Decompose coeffsZero: ordering sums = -ws_nn(j) + (ws_up - ws_lo)
    have hord_sum : ∀ j : Fin n,
        ∑ m : Fin k, ws ⟨n + 2 + m.val, by omega⟩ *
          (-(((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
               (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ))) =
        ws ⟨j.val, by omega⟩ - (ws ⟨n, by omega⟩ - ws ⟨n + 1, by omega⟩) := by
      intro j; have h := hcoeffsZero j
      rw [sum_split_n2k] at h
      have h_nn : ∑ i : Fin n, ws ⟨i.val, by omega⟩ * (ineqFn ⟨i.val, by omega⟩).lhs j =
          -ws ⟨j.val, by omega⟩ := by
        rw [Finset.sum_eq_single j]
        · rw [hineq_nn j j]; simp
        · intro i _ hij; rw [hineq_nn i j, if_neg (Ne.symm hij)]; ring
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [h_nn, hineq_up, hineq_lo] at h
      simp_rw [hineq_ord] at h
      linarith
    -- Ordering weighted sums are < 0
    have hord_neg : ∀ j : Fin n,
        ∑ m : Fin k, ws ⟨n + 2 + m.val, by omega⟩ *
          ((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
            (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ) < 0 := by
      intro j
      have h := hord_sum j
      have : ∑ m : Fin k, ws ⟨n + 2 + m.val, by omega⟩ *
          ((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
            (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ) =
        -(∑ m : Fin k, ws ⟨n + 2 + m.val, by omega⟩ *
          (-(((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
            (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ)))) := by
        simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
      rw [this, h]
      linarith [ws_nn ⟨j.val, by omega⟩, hbound_decomp]
    -- Build portfolio with perturbed weights (ws_ord + ε) to ensure all > 0
    let ws_ord : Fin k → ℚ := fun m => ws ⟨n + 2 + m.val, by omega⟩
    by_cases hn : n = 0
    · subst hn
      refine ⟨[], ?_, fun j => Fin.elim0 j⟩
      intro wc h; cases h
    · -- n ≥ 1: use perturbed weights
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      let neg_sums : Fin n → ℚ := fun j =>
        ∑ m : Fin k, ws_ord m *
          ((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
            (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ)
      have hns_neg : ∀ j, neg_sums j < 0 := hord_neg
      let cv_bound : ℚ := ↑k + 1
      have hcv_pos : 0 < cv_bound := by positivity
      let min_gap : ℚ := if _ : 0 < k then
        Finset.univ.inf' ⟨⟨0, hn'⟩, Finset.mem_univ _⟩ (fun j => -neg_sums j)
      else 1
      have hmin_pos : 0 < min_gap := by
        simp only [min_gap]; split
        · rw [Finset.lt_inf'_iff]; exact fun j _ => neg_pos.mpr (hns_neg j)
        · exact one_pos
      let ε : ℚ := min_gap / (2 * cv_bound)
      have hε_pos : 0 < ε := div_pos hmin_pos (by positivity)
      let ws_pert : Fin k → ℚ := fun m => ws_ord m + ε
      have h_pert_pos : ∀ m, 0 < ws_pert m :=
        fun m => add_pos_of_nonneg_of_pos (ws_nn ⟨n + 2 + m.val, by omega⟩) hε_pos
      let P := portfolioOfWeights gePairs ws_pert hgePairsDisj h_pert_pos
      refine ⟨P, isValid_portfolioOfWeights _ _ _ _ _ hgePairsGe, fun j => ?_⟩
      rw [weightedSum_portfolioOfWeights]
      -- Perturbed sum = original sum + ε * Σ cv
      have h_split :
          ∑ m : Fin k, ws_pert m * ((comparisonVec n (gePairs.get m).1
            (gePairs.get m).2 j : ℤ) : ℚ) =
          neg_sums j + ε * ∑ m : Fin k,
            ((comparisonVec n (gePairs.get m).1
              (gePairs.get m).2 j : ℤ) : ℚ) := by
        simp only [ws_pert, add_mul, Finset.sum_add_distrib, Finset.mul_sum]; ring
      rw [h_split]
      -- Bound each compVec entry by 1
      have hcv_le1 : ∀ m : Fin k, ((comparisonVec n (gePairs.get m).1
          (gePairs.get m).2 j : ℤ) : ℚ) ≤ 1 := by
        intro m
        suffices h : (comparisonVec n (gePairs.get m).1 (gePairs.get m).2 j : ℤ) ≤ 1 by
          exact_mod_cast h
        simp only [comparisonVec]
        by_cases hA : j ∈ (gePairs.get m).1 <;> by_cases hB : j ∈ (gePairs.get m).2
        · exact absurd hB (Finset.disjoint_left.mp (hgePairsDisj m) hA)
        all_goals simp_all
      -- Sum of compVec entries ≤ k
      have hcvs_le : (∑ m : Fin k, ((comparisonVec n (gePairs.get m).1
          (gePairs.get m).2 j : ℤ) : ℚ)) ≤ ↑k :=
        le_trans (Finset.sum_le_sum fun m _ => hcv_le1 m)
          (by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul])
      -- ε * cv_bound = min_gap / 2
      have hε_eq : ε * cv_bound = min_gap / 2 := by
        simp only [ε]
        rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt hcv_pos)]
      -- min_gap ≤ -neg_sums j
      have hmin_le : min_gap ≤ -neg_sums j := by
        simp only [min_gap]; split
        · exact Finset.inf'_le _ (Finset.mem_univ j)
        · exfalso
          have hk0 : k = 0 := by omega
          have : neg_sums j = 0 := by
            show ∑ m : Fin k, _ = 0
            have : (Finset.univ : Finset (Fin k)) = ∅ := by
              ext ⟨m, hm⟩; simp; omega
            simp [this]
          linarith [hns_neg j]
      nlinarith [mul_le_mul_of_nonneg_left hcvs_le (le_of_lt hε_pos)]

-- ── Step 4b'. Cancellation strengthens → to ↔ ───

/-- Split a sum over `Fin ((n + k) + K)` into nonneg + ordering + strict parts. -/
private lemma sum_three_parts {n k K : ℕ} (f : Fin ((n + k) + K) → ℚ) :
    ∑ i, f i = (∑ i : Fin n, f ⟨i.val, by omega⟩) +
    (∑ m : Fin k, f ⟨n + m.val, by omega⟩) +
    (∑ s : Fin K, f ⟨(n + k) + s.val, by omega⟩) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add (fun i : Fin (n + k) => f (Fin.castAdd K i))]
  congr 1

/-- Weighted sum of a filterMap portfolio equals the Finset sum
    (zero-weight terms contribute 0 and are skipped by filterMap). -/
private lemma filterMap_weightedSum {n k' : ℕ}
    (pairs : Fin k' → Finset (Fin n) × Finset (Fin n))
    (w : Fin k' → ℚ) (hw : ∀ i, 0 ≤ w i)
    (hdisj : ∀ i, Disjoint (pairs i).1 (pairs i).2)
    (j : Fin n) :
    Portfolio.weightedSum
      ((List.finRange k').filterMap (fun i =>
        if h : 0 < w i then
          some ⟨(pairs i).1, (pairs i).2, w i, hdisj i, h⟩
        else none)) j =
    ∑ i : Fin k', w i *
      ((comparisonVec n (pairs i).1 (pairs i).2 j : ℤ) : ℚ) := by
  simp only [Portfolio.weightedSum]
  conv_rhs => rw [← finRange_map_sum]
  suffices ∀ l : List (Fin k'),
      ((l.filterMap (fun i =>
        if h : 0 < w i then
          some ⟨(pairs i).1, (pairs i).2, w i, hdisj i, h⟩
        else none)).map (fun wc : WComparison n =>
        wc.weight * ((comparisonVec n wc.left wc.right j : ℤ) : ℚ))).sum =
      (l.map (fun i =>
        w i * ((comparisonVec n (pairs i).1 (pairs i).2 j : ℤ) : ℚ))).sum
      from this _
  intro l; induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hpos : 0 < w hd
    · -- Include entry: filterMap keeps it
      simp only [List.filterMap_cons, dif_pos hpos, List.map_cons, List.sum_cons, ih]
    · -- Skip entry: filterMap drops it, contribution is 0
      simp only [List.filterMap_cons, dif_neg hpos]
      rw [ih]
      have : w hd = 0 := le_antisymm (not_lt.mp hpos) (hw hd)
      simp [this]

/-- Strict pairs: disjoint (A, B) where sys.ge ↑A ↑B strictly (¬sys.ge ↑B ↑A). -/
private noncomputable def strictPairsOf {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    List (Finset (Fin n) × Finset (Fin n)) :=
  ((Finset.univ ×ˢ Finset.univ : Finset _).filter
    (fun ab => Disjoint ab.1 ab.2 ∧ sys.ge ↑ab.1 ↑ab.2 ∧ ¬sys.ge ↑ab.2 ↑ab.1)).toList

private theorem strictPairs_mem {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (A B : Finset (Fin n)) (hd : Disjoint A B) (hge : sys.ge ↑A ↑B) (hng : ¬sys.ge ↑B ↑A) :
    (A, B) ∈ strictPairsOf sys := by
  simp only [strictPairsOf, Finset.mem_toList, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and]
  exact ⟨hd, hge, hng⟩

private theorem strictPairs_disj {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (strictPairsOf sys).length) :
    Disjoint ((strictPairsOf sys).get m).1 ((strictPairsOf sys).get m).2 := by
  have := List.get_mem (strictPairsOf sys) m
  simp only [strictPairsOf, Finset.mem_toList, Finset.mem_filter] at this
  exact this.2.1

private theorem strictPairs_ge {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (strictPairsOf sys).length) :
    sys.ge ↑((strictPairsOf sys).get m).1 ↑((strictPairsOf sys).get m).2 := by
  have := List.get_mem (strictPairsOf sys) m
  simp only [strictPairsOf, Finset.mem_toList, Finset.mem_filter] at this
  exact this.2.2.1

private theorem strictPairs_strict {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (strictPairsOf sys).length) :
    ¬sys.ge ↑((strictPairsOf sys).get m).2 ↑((strictPairsOf sys).get m).1 := by
  have := List.get_mem (strictPairsOf sys) m
  simp only [strictPairsOf, Finset.mem_toList, Finset.mem_filter] at this
  exact this.2.2.2

set_option maxHeartbeats 1600000 in
private theorem cancel_strengthens_to_bidir {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge)
    (hexists : ∃ p : Fin n → ℚ, (∀ i, 0 ≤ p i) ∧ Finset.univ.sum p = 1 ∧
      ∀ (A B : Finset (Fin n)), Disjoint A B →
        sys.ge ↑A ↑B → A.sum p ≥ B.sum p) :
    ∃ p, p ∈ feasibleWeights n sys := by
  obtain ⟨p₀, hnn₀, hsum₀, hge₀⟩ := hexists
  -- Enumerate all ge pairs
  let gePairs : List (Finset (Fin n) × Finset (Fin n)) :=
    ((Finset.univ ×ˢ Finset.univ : Finset _).filter
      (fun ab => Disjoint ab.1 ab.2 ∧ sys.ge ↑ab.1 ↑ab.2)).toList
  let k := gePairs.length
  let sp := strictPairsOf sys
  let K := sp.length
  have hgePairsMem : ∀ (A B : Finset (Fin n)), Disjoint A B → sys.ge ↑A ↑B →
      (A, B) ∈ gePairs := by
    intro A B hd hge
    simp only [gePairs, Finset.mem_toList, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ⟨hd, hge⟩
  have hgePairsDisj : ∀ m : Fin k, Disjoint (gePairs.get m).1 (gePairs.get m).2 := by
    intro ⟨m, hm⟩
    have := List.get_mem gePairs ⟨m, hm⟩
    simp only [gePairs, Finset.mem_toList, Finset.mem_filter] at this
    exact this.2.1
  have hgePairsGe : ∀ m : Fin k, sys.ge ↑(gePairs.get m).1 ↑(gePairs.get m).2 := by
    intro ⟨m, hm⟩
    have := List.get_mem gePairs ⟨m, hm⟩
    simp only [gePairs, Finset.mem_toList, Finset.mem_filter] at this
    exact this.2.2
  -- Case split: are there strict pairs?
  by_cases hK : K = 0
  · -- No strict pairs: p₀ is already ↔ feasible
    refine ⟨p₀, hnn₀, hsum₀, fun A B hdisj => ⟨hge₀ A B hdisj, fun hge => ?_⟩⟩
    -- Need: sys.ge ↑A ↑B. Suppose not → strict pair exists, contradicting K = 0
    by_contra hng
    have hBA : sys.ge ↑B ↑A := (sys.total ↑A ↑B).resolve_left hng
    have hmem := strictPairs_mem sys B A hdisj.symm hBA hng
    have hempty : (strictPairsOf sys).length = 0 := hK
    have : (strictPairsOf sys) = [] := by
      rcases strictPairsOf sys with _ | ⟨_, _⟩ <;> simp_all
    simp [this] at hmem
  · -- Strict pairs exist: build augmented LP and apply Farkas
    have hK_pos : 0 < K := Nat.pos_of_ne_zero hK
    -- Build constraint function: n nonneg + k ordering + K strict
    let ineqFn : Fin ((n + k) + K) → Polyhedral.Ineq n := fun i =>
      if h : i.val < n then
        ⟨fun j => if j = ⟨i.val, h⟩ then -1 else 0, 0⟩
      else if _ : i.val < n + k then
        ⟨fun j => -(((comparisonVec n (gePairs.get ⟨i.val - n, by omega⟩).1
            (gePairs.get ⟨i.val - n, by omega⟩).2 j : ℤ) : ℚ)), 0⟩
      else
        ⟨fun j => -(((comparisonVec n (sp.get ⟨i.val - (n + k), by omega⟩).1
            (sp.get ⟨i.val - (n + k), by omega⟩).2 j : ℤ) : ℚ)), -1⟩
    let S : Polyhedral.System n := List.ofFn ineqFn
    have hget : ∀ i : Fin ((n + k) + K), ineqFn i ∈ S :=
      fun i => List.mem_ofFn.mpr ⟨i, rfl⟩
    -- Apply Farkas
    rcases Polyhedral.farkas S with ⟨x, hx⟩ | hcert
    · -- ═══ Feasible case: extract and normalize ═══
      have hsat : ∀ i : Fin ((n + k) + K), (ineqFn i).sat x := fun i => hx _ (hget i)
      -- Extract nonnegativity
      have hx_nn : ∀ i : Fin n, 0 ≤ x i := by
        intro i
        have h := hsat ⟨i.val, by omega⟩
        simp only [ineqFn, dif_pos i.isLt, Polyhedral.Ineq.sat, Polyhedral.dot] at h
        simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true] at h
        linarith
      -- Extract ordering constraints
      have hx_ord : ∀ (A B : Finset (Fin n)), Disjoint A B →
          sys.ge ↑A ↑B → A.sum x ≥ B.sum x := by
        intro A B hdisj hge
        obtain ⟨⟨m, hm⟩, hget_m⟩ := List.mem_iff_get.mp (hgePairsMem A B hdisj hge)
        have h := hsat ⟨n + m, by omega⟩
        simp only [ineqFn, show ¬(n + m < n) from by omega, dite_false,
          show (n + m < n + k) from by omega, dite_true,
          Polyhedral.Ineq.sat, Polyhedral.dot] at h
        simp only [show n + m - n = m from by omega] at h
        simp only [neg_mul, Finset.sum_neg_distrib] at h
        have hcv := compVec_as_sum_diff A B x hdisj
        rw [hget_m] at h; linarith
      -- Extract strict constraints
      have hx_strict : ∀ s : Fin K, (sp.get s).1.sum x ≥ (sp.get s).2.sum x + 1 := by
        intro ⟨s, hs⟩
        have h := hsat ⟨n + k + s, by omega⟩
        simp only [ineqFn, show ¬(n + k + s < n) from by omega, dite_false,
          show ¬(n + k + s < n + k) from by omega,
          Polyhedral.Ineq.sat, Polyhedral.dot] at h
        simp only [show n + k + s - (n + k) = s from by omega] at h
        simp only [neg_mul, Finset.sum_neg_distrib] at h
        linarith [compVec_as_sum_diff (sp.get ⟨s, hs⟩).1 (sp.get ⟨s, hs⟩).2 x
          (strictPairs_disj sys ⟨s, hs⟩)]
      -- Normalize: Σx > 0 (from strict constraint on pair 0)
      have hsum_pos : 0 < Finset.univ.sum x := by
        have hs0 := hx_strict ⟨0, hK_pos⟩
        have hA := Finset.sum_nonneg (fun i (_ : i ∈ (sp.get ⟨0, hK_pos⟩).1) => hx_nn i)
        have hB := Finset.sum_nonneg (fun i (_ : i ∈ (sp.get ⟨0, hK_pos⟩).2) => hx_nn i)
        calc Finset.univ.sum x
            ≥ (sp.get ⟨0, hK_pos⟩).1.sum x := Finset.sum_le_univ_sum_of_nonneg hx_nn
          _ ≥ (sp.get ⟨0, hK_pos⟩).2.sum x + 1 := hs0
          _ ≥ 0 + 1 := by linarith
          _ > 0 := by linarith
      -- Define normalized vector
      let σ := Finset.univ.sum x
      have hσ_pos : 0 < σ := hsum_pos
      have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
      refine ⟨fun i => x i / σ, fun i => div_nonneg (hx_nn i) (le_of_lt hσ_pos), ?_, ?_⟩
      · -- Σ(x/σ) = 1
        show Finset.univ.sum (fun i => x i / σ) = 1
        rw [← Finset.sum_div]; exact div_self hσ_ne
      · -- ↔ for disjoint pairs
        intro A B hdisj
        constructor
        · -- → direction
          intro hge
          show A.sum (fun i => x i / σ) ≥ B.sum (fun i => x i / σ)
          have h := hx_ord A B hdisj hge
          rw [show A.sum (fun i => x i / σ) = A.sum x / σ from by rw [Finset.sum_div],
              show B.sum (fun i => x i / σ) = B.sum x / σ from by rw [Finset.sum_div]]
          exact div_le_div_of_nonneg_right h (le_of_lt hσ_pos)
        · -- ← direction (contrapositive)
          intro hge
          by_contra hng
          have hBA : sys.ge ↑B ↑A := (sys.total ↑A ↑B).resolve_left hng
          have hmem := strictPairs_mem sys B A hdisj.symm hBA hng
          obtain ⟨⟨s, hs⟩, hgets⟩ := List.mem_iff_get.mp hmem
          have hgap := hx_strict ⟨s, hs⟩
          rw [hgets] at hgap
          -- B.sum x > A.sum x, so A.sum (x/σ) < B.sum (x/σ)
          have hlt : A.sum (fun i => x i / σ) < B.sum (fun i => x i / σ) := by
            rw [show A.sum (fun i => x i / σ) = A.sum x / σ from by rw [Finset.sum_div],
                show B.sum (fun i => x i / σ) = B.sum x / σ from by rw [Finset.sum_div]]
            exact div_lt_div_of_pos_right (by linarith) hσ_pos
          linarith
    · -- ═══ Infeasible case: certificate → cancellation violation ═══
      exfalso
      obtain ⟨cert⟩ := hcert
      have hlen : S.length = (n + k) + K := List.length_ofFn
      -- Cast cert weights to natural indices
      let ws : Fin ((n + k) + K) → ℚ := fun i => cert.ws (i.cast hlen.symm)
      have ws_nn : ∀ i, 0 ≤ ws i := fun i => cert.nonneg _
      -- Transport: reindex sums
      have hreindex : ∀ f : Fin S.length → ℚ,
          ∑ i : Fin S.length, f i =
          ∑ i : Fin ((n + k) + K), f (i.cast hlen.symm) :=
        fun f => Fintype.sum_equiv (finCongr hlen) _ _ (fun i => by simp [finCongr])
      have hS_get : ∀ i : Fin S.length,
          S.get i = ineqFn (i.cast hlen) := fun i => List.get_ofFn ineqFn i
      -- Coefficients zero
      have hcoeffsZero : ∀ j : Fin n,
          ∑ i : Fin ((n + k) + K), ws i * (ineqFn i).lhs j = 0 := by
        intro j
        have h := cert.coeffsZero j
        rw [hreindex] at h; simp_rw [hS_get] at h; exact h
      -- Bound negative
      have hboundNeg :
          ∑ i : Fin ((n + k) + K), ws i * (ineqFn i).rhs < 0 := by
        have h := cert.boundNeg
        rw [hreindex] at h; simp_rw [hS_get] at h; exact h
      -- ── Decompose boundNeg: strict weights sum > 0 ──
      have hstrictWtSum : 0 < ∑ s : Fin K, ws ⟨(n + k) + s.val, by omega⟩ := by
        rw [sum_three_parts] at hboundNeg
        have h1 : ∑ i : Fin n, ws ⟨i.val, by omega⟩ * (ineqFn ⟨i.val, by omega⟩).rhs = 0 :=
          Finset.sum_eq_zero fun i _ => by
            have : (ineqFn ⟨i.val, by omega⟩).rhs = 0 := by
              simp only [ineqFn, dif_pos i.isLt]
            simp [this]
        have h2 : ∑ m : Fin k, ws ⟨n + m.val, by omega⟩ *
            (ineqFn ⟨n + m.val, by omega⟩).rhs = 0 :=
          Finset.sum_eq_zero fun m _ => by
            have : (ineqFn ⟨n + m.val, by omega⟩).rhs = 0 := by
              simp only [ineqFn, show ¬(n + m.val < n) from by omega,
                show n + m.val < n + k from by omega, dite_false, dite_true]
            simp [this]
        have h3 : ∑ s : Fin K, ws ⟨(n + k) + s.val, by omega⟩ *
            (ineqFn ⟨(n + k) + s.val, by omega⟩).rhs =
            -(∑ s : Fin K, ws ⟨(n + k) + s.val, by omega⟩) := by
          have hrhs : ∀ s : Fin K, (ineqFn ⟨(n + k) + s.val, by omega⟩).rhs = (-1 : ℚ) := by
            intro s; simp only [ineqFn, show ¬((n + k) + s.val < n) from by omega,
              show ¬((n + k) + s.val < n + k) from by omega, dite_false]
          simp_rw [hrhs, mul_neg_one, Finset.sum_neg_distrib]
        linarith
      -- ── Find s₀ with positive strict weight ──
      obtain ⟨s₀, _, hs₀⟩ : ∃ s ∈ (Finset.univ : Finset (Fin K)),
          0 < ws ⟨(n + k) + s.val, by omega⟩ := by
        by_contra hall; push_neg at hall
        have : ∑ s : Fin K, ws ⟨(n + k) + s.val, by omega⟩ = 0 :=
          Finset.sum_eq_zero fun s hs => le_antisymm (hall s hs)
            (ws_nn ⟨(n + k) + s.val, by omega⟩)
        linarith
      -- ── Coefficient decomposition via sum_three_parts ──
      have hDecomp : ∀ j : Fin n,
          ws ⟨j.val, by omega⟩ +
          (∑ m : Fin k, ws ⟨n + m.val, by omega⟩ *
            ((comparisonVec n (gePairs.get m).1 (gePairs.get m).2 j : ℤ) : ℚ)) +
          (∑ s : Fin K, ws ⟨(n + k) + s.val, by omega⟩ *
            ((comparisonVec n (sp.get s).1 (sp.get s).2 j : ℤ) : ℚ)) = 0 := by
        intro j; have h := hcoeffsZero j
        rw [sum_three_parts] at h
        -- Nonneg: only the j-th row contributes -ws(j)
        have h_nn : ∑ i : Fin n, ws ⟨i.val, by omega⟩ * (ineqFn ⟨i.val, by omega⟩).lhs j =
            -ws ⟨j.val, by omega⟩ := by
          rw [Finset.sum_eq_single j]
          · simp only [ineqFn, dif_pos j.isLt]; simp
          · intro i _ hij
            simp only [ineqFn, dif_pos i.isLt]
            simp [show j ≠ i from Ne.symm hij]
          · intro h; exact absurd (Finset.mem_univ j) h
        -- Ordering: simplify lhs
        have h_ord : ∀ m : Fin k, ws ⟨n + m.val, by omega⟩ *
            (ineqFn ⟨n + m.val, by omega⟩).lhs j =
            -(ws ⟨n + m.val, by omega⟩ *
              ((comparisonVec n (gePairs.get m).1 (gePairs.get m).2 j : ℤ) : ℚ)) := by
          intro m
          have : (ineqFn ⟨n + m.val, by omega⟩).lhs j =
              -(((comparisonVec n (gePairs.get ⟨m.val, m.isLt⟩).1
                (gePairs.get ⟨m.val, m.isLt⟩).2 j : ℤ) : ℚ)) := by
            simp only [ineqFn, show ¬(n + m.val < n) from by omega,
              show n + m.val < n + k from by omega, dite_false, dite_true]
            have : (⟨n + m.val - n, by omega⟩ : Fin k) = m := by
              ext; show n + m.val - n = m.val; omega
            rw [this]
          rw [this]; ring
        -- Strict: simplify lhs
        have h_str : ∀ s : Fin K, ws ⟨(n + k) + s.val, by omega⟩ *
            (ineqFn ⟨(n + k) + s.val, by omega⟩).lhs j =
            -(ws ⟨(n + k) + s.val, by omega⟩ *
              ((comparisonVec n (sp.get s).1 (sp.get s).2 j : ℤ) : ℚ)) := by
          intro s
          have : (ineqFn ⟨(n + k) + s.val, by omega⟩).lhs j =
              -(((comparisonVec n (sp.get ⟨s.val, s.isLt⟩).1
                (sp.get ⟨s.val, s.isLt⟩).2 j : ℤ) : ℚ)) := by
            simp only [ineqFn, show ¬((n + k) + s.val < n) from by omega,
              show ¬((n + k) + s.val < n + k) from by omega, dite_false]
            have : (⟨(n + k) + s.val - (n + k), by omega⟩ : Fin K) = s := by
              ext; show (n + k) + s.val - (n + k) = s.val; omega
            rw [this]
          rw [this]; ring
        simp_rw [h_nn, h_ord, Finset.sum_neg_distrib, h_str, Finset.sum_neg_distrib] at h
        linarith
      -- ── Build portfolio violating cancellation ──
      let Q_ord : List (WComparison n) :=
        (List.finRange k).filterMap fun m =>
          if h : 0 < ws ⟨n + m.val, by omega⟩ then
            some ⟨(gePairs.get m).1, (gePairs.get m).2,
              ws ⟨n + m.val, by omega⟩, hgePairsDisj m, h⟩
          else none
      let Q_strict : List (WComparison n) :=
        (List.finRange K).filterMap fun s =>
          if h : 0 < ws ⟨(n + k) + s.val, by omega⟩ then
            some ⟨(sp.get s).1, (sp.get s).2,
              ws ⟨(n + k) + s.val, by omega⟩, strictPairs_disj sys s, h⟩
          else none
      let Q_sing : List (WComparison n) :=
        (List.finRange n).filterMap fun j =>
          if h : 0 < ws ⟨j.val, by omega⟩ then
            some ⟨{j}, ∅, ws ⟨j.val, by omega⟩, Finset.disjoint_empty_right _, h⟩
          else none
      let Q : Portfolio n := Q_ord ++ Q_strict ++ Q_sing
      have hQ_strict : Q.hasStrict sys.ge :=
        ⟨⟨(sp.get s₀).1, (sp.get s₀).2, ws ⟨(n + k) + s₀.val, by omega⟩,
          strictPairs_disj sys s₀, hs₀⟩,
          List.mem_append_left _ (List.mem_append_right _
            (List.mem_filterMap.mpr ⟨s₀, List.mem_finRange s₀, dif_pos hs₀⟩)),
          strictPairs_strict sys s₀⟩
      have hQ_valid : Q.isValid sys.ge := by
        intro wc hwc
        rcases List.mem_append.mp hwc with h | h
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨m, _, hm⟩ := List.mem_filterMap.mp h
            split_ifs at hm with hpos
            cases hm; exact hgePairsGe m
          · obtain ⟨s, _, hs⟩ := List.mem_filterMap.mp h
            split_ifs at hs with hpos
            cases hs; exact strictPairs_ge sys s
        · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
          split_ifs at hj with hpos
          cases hj
          simp only [Finset.coe_singleton, Finset.coe_empty]
          exact sys.mono ∅ {j} (Set.empty_subset _)
      have hQ_neutral : Q.isNeutral := by
        intro j
        show Portfolio.weightedSum (Q_ord ++ Q_strict ++ Q_sing) j = 0
        simp only [Portfolio.weightedSum, List.map_append, List.sum_append]
        rw [show (Q_ord.map _).sum = _ from filterMap_weightedSum
              (fun m => ((gePairs.get m).1, (gePairs.get m).2))
              (fun m => ws ⟨n + m.val, by omega⟩)
              (fun m => ws_nn ⟨n + m.val, by omega⟩) hgePairsDisj j,
            show (Q_strict.map _).sum = _ from filterMap_weightedSum
              (fun s => ((sp.get s).1, (sp.get s).2))
              (fun s => ws ⟨(n + k) + s.val, by omega⟩)
              (fun s => ws_nn ⟨(n + k) + s.val, by omega⟩)
              (strictPairs_disj sys) j,
            show (Q_sing.map _).sum = _ from filterMap_weightedSum
              (fun i => ({i}, (∅ : Finset (Fin n))))
              (fun i => ws ⟨i.val, by omega⟩)
              (fun i => ws_nn ⟨i.val, by omega⟩)
              (fun _ => Finset.disjoint_empty_right _) j]
        have hsing : ∑ i : Fin n, ws ⟨i.val, by omega⟩ *
            ((comparisonVec n {i} ∅ j : ℤ) : ℚ) = ws ⟨j.val, by omega⟩ := by
          rw [Finset.sum_eq_single j]
          · simp [comparisonVec, Finset.mem_singleton]
          · intro i _ hij
            simp [comparisonVec, Finset.mem_singleton, Ne.symm hij]
          · intro h; exact absurd (Finset.mem_univ j) h
        rw [hsing]; linarith [hDecomp j]
      exact absurd hQ_strict (hcancel Q hQ_valid hQ_neutral)

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

-- ── Step 4d. Compose: cancellation → feasible weights ──

/-- The core LP step: cancellation implies the feasibility polytope is nonempty.
    Three-step proof:
    1. `farkas_ordering_lp` — either a → solution exists, or a certificate does
    2. Certificate case: `certificate_to_violation` converts it to a neutral
       portfolio with strict member, contradicting cancellation
    3. → solution case: `cancel_strengthens_to_bidir` upgrades → to ↔ -/
private theorem cancellation_nonempty {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge) :
    ∃ p, p ∈ feasibleWeights n sys := by
  rcases farkas_ordering_lp sys with h | ⟨P, hV, hNeg⟩
  · exact cancel_strengthens_to_bidir sys hcancel h
  · obtain ⟨Q, hQV, hQN, hQS⟩ := certificate_to_violation sys P hV hNeg
    exact absurd hQS (hcancel Q hQV hQN)

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
theorem not_all_null_fin4 (sys : EpistemicSystemFA (Fin 4))
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
theorem fa_cancellation_fin4_null0 (sys : EpistemicSystemFA (Fin 4))
    (h0 : sys.ge ∅ {(0 : Fin 4)})
    (hnn : ∃ i : Fin 3, ¬sys.ge ∅ {Fin.succ i}) :
    Cancellation 4 sys.ge := by
  obtain ⟨m, hm⟩ := null_elem_reduce sys h0 hnn (fun sys' => theorem8a_fin3 sys')
  exact representable_implies_cancellation sys m hm

/-- Cancellation follows from a "forward + strict" witness: positive weights p
    summing to 1 such that every valid comparison has p-value ≥ 0 and every
    strict comparison has p-value > 0.
    This avoids constructing a full representing measure. -/
theorem cancellation_from_weights {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (p : Fin n → ℚ) (hp : ∀ i, 0 < p i) (hsum : Finset.univ.sum p = 1)
    (hfwd : ∀ (A B : Finset (Fin n)), Disjoint A B → sys.ge ↑A ↑B →
      A.sum p ≥ B.sum p)
    (hstrict : ∀ (A B : Finset (Fin n)), Disjoint A B → sys.ge ↑A ↑B →
      ¬sys.ge ↑B ↑A → A.sum p > B.sum p) :
    Cancellation n sys.ge := by
  -- Construct temporary measure from p
  let m : FinAddMeasure (Fin n) := {
    mu := fun S => Finset.univ.sum (fun i => if i ∈ S then p i else 0)
    nonneg := fun S => Finset.sum_nonneg (fun i _ => by split <;> [exact le_of_lt (hp i); exact le_refl _])
    additive := fun A B hdisj => by
      simp only [Set.mem_union]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      by_cases hA : i ∈ A <;> by_cases hB : i ∈ B
      · exact absurd hB (hdisj i hA)
      · simp [hA, hB]
      · simp [hA, hB]
      · simp [hA, hB]
    total := by
      conv_rhs => rw [← hsum]
      apply Finset.sum_congr rfl; intro i _; simp
  }
  have hmu_single : ∀ i : Fin n, m.mu {i} = p i := by
    intro i; dsimp only [m]
    simp only [Set.mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hmu_finset : ∀ S : Finset (Fin n), m.mu ↑S = S.sum p := by
    intro S; rw [mu_finset_sum m S]
    apply Finset.sum_congr rfl; intro i _; exact hmu_single i
  intro P hValid hNeutral ⟨wc, hwc_mem, hwc_strict⟩
  let f : WComparison n → ℚ := fun wc => wc.weight * (m.mu ↑wc.left - m.mu ↑wc.right)
  have hnn : ∀ x ∈ P.map f, (0 : ℚ) ≤ x := by
    intro x hx
    obtain ⟨wc', hwc'_mem, rfl⟩ := List.mem_map.mp hx
    apply mul_nonneg (le_of_lt wc'.weight_pos)
    rw [sub_nonneg, hmu_finset, hmu_finset]
    exact hfwd wc'.left wc'.right wc'.disjoint (hValid wc' hwc'_mem)
  have hlt : m.mu ↑wc.left > m.mu ↑wc.right := by
    rw [hmu_finset, hmu_finset]
    exact hstrict wc.left wc.right wc.disjoint (hValid wc hwc_mem) hwc_strict
  have hp_pos : ∃ x ∈ P.map f, (0 : ℚ) < x :=
    ⟨f wc, List.mem_map.mpr ⟨wc, hwc_mem, rfl⟩, mul_pos wc.weight_pos (sub_pos.mpr hlt)⟩
  have hpos := list_sum_pos hnn hp_pos
  rw [portfolio_interchange m P] at hpos
  have hzero : Finset.univ.sum (fun i => m.mu {i} * P.weightedSum i) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [hNeutral i, mul_zero])
  linarith

/-- Wrapper around `cancellation_from_weights` that replaces the two universally-quantified
    obligations (hfwd, hstrict) with a single contrapositive condition:
    for every disjoint pair (A, B) where A.sum p < B.sum p, we have ¬sys.ge ↑A ↑B.
    Equal-sum pairs need bidirectionality (heq).
    The proof of cancellation_from_weights does the hfwd/hstrict dispatch once;
    each chamber only provides the ~5-10 ¬ge facts for "wrong-direction" pairs. -/
theorem cancellation_from_weights_fin4 (sys : EpistemicSystemFA (Fin 4))
    (p : Fin 4 → ℚ) (hp : ∀ i, 0 < p i) (hsum : Finset.univ.sum p = 1)
    (hnge : ∀ (A B : Finset (Fin 4)), Disjoint A B →
      A.sum p < B.sum p → ¬sys.ge ↑A ↑B)
    (heq : ∀ (A B : Finset (Fin 4)), Disjoint A B →
      A.sum p = B.sum p → sys.ge ↑A ↑B → sys.ge ↑B ↑A) :
    Cancellation 4 sys.ge := by
  apply cancellation_from_weights sys p hp hsum
  · -- hfwd: sys.ge ↑A ↑B → A.sum p ≥ B.sum p
    intro A B hDisj hGe
    by_contra hlt; push_neg at hlt
    exact absurd hGe (hnge A B hDisj hlt)
  · -- hstrict: sys.ge ↑A ↑B → ¬sys.ge ↑B ↑A → A.sum p > B.sum p
    intro A B hDisj hGe hStrict
    by_contra h; push_neg at h
    rcases eq_or_lt_of_le h with h | h
    · exact absurd (heq A B hDisj h hGe) hStrict
    · exact absurd hGe (hnge A B hDisj h)

/-- When weights are **generic** (no two nonempty disjoint subsets have equal sum),
    cancellation reduces to a single forward obligation: sys.ge ↑A ↑B → A.sum p ≥ B.sum p.
    The strict direction and equal-sum bidirectionality are both free:
    - strict: contrapositive of hfwd (if A.sum p < B.sum p then ¬sys.ge ↑A ↑B)
    - heq: vacuously true (genericity rules out equal-sum disjoint pairs) -/
theorem cancellation_from_generic_weights {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (p : Fin n → ℚ) (hp : ∀ i, 0 < p i) (hsum : Finset.univ.sum p = 1)
    (hfwd : ∀ (A B : Finset (Fin n)), Disjoint A B → sys.ge ↑A ↑B →
      A.sum p ≥ B.sum p)
    (hgeneric : ∀ (A B : Finset (Fin n)), Disjoint A B →
      A.sum p = B.sum p → A = ∅ ∧ B = ∅) :
    Cancellation n sys.ge := by
  apply cancellation_from_weights sys p hp hsum hfwd
  intro A B hDisj hGe hStrict
  by_contra h; push_neg at h
  rcases eq_or_lt_of_le h with heq | hlt
  · obtain ⟨rfl, rfl⟩ := hgeneric A B hDisj heq
    exact hStrict (sys.refl _)
  · exact absurd hGe (fun hge => absurd (hfwd A B hDisj hge) (not_le.mpr hlt))

/-- Classify all Finset (Fin 4) into one of 16 explicit values. -/
lemma finset_fin4_eq (S : Finset (Fin 4)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {3} ∨
    S = {0,1} ∨ S = {0,2} ∨ S = {0,3} ∨ S = {1,2} ∨ S = {1,3} ∨ S = {2,3} ∨
    S = {0,1,2} ∨ S = {0,1,3} ∨ S = {0,2,3} ∨ S = {1,2,3} ∨
    S = Finset.univ := by
  suffices h : ∀ S : Finset (Fin 4), S ∈ ({∅, {0}, {1}, {2}, {3},
    {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3},
    {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, Finset.univ} : Finset (Finset (Fin 4))) by
    have := h S; simp [Finset.mem_insert] at this; exact this
  decide

/-- ¬ge({1,3}, {0,2}) from singleton hypotheses via additive decomposition.
    Route A (¬ge({1},{0})): ge({1,3},{0,2}) → additive ge({0,2},{0,3}) via ge({2},{3})
      → trans → ge({1,3},{0,3}) → additive → ge({1},{0}) → contradiction.
    Route B (¬ge({3},{2})): ge({1,3},{0,2}) → additive ge({0,2},{1,2}) via ge({0},{1})
      → trans → ge({1,3},{1,2}) → additive → ge({3},{2}) → contradiction. -/
theorem nge_13_02 (sys : EpistemicSystemFA (Fin 4))
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h23 : sys.ge {(2 : Fin 4)} {3})
    (h : ¬sys.ge {(1 : Fin 4)} {0} ∨ ¬sys.ge {(3 : Fin 4)} {2}) :
    ¬sys.ge ({1, 3} : Set (Fin 4)) {0, 2} := by
  intro hge
  rcases h with h10 | h32
  · -- Route A: through {0,3}. ge({0,2},{0,3}) ↔ ge({2},{3}).
    have h1 : sys.ge ({0, 2} : Set (Fin 4)) {0, 3} := by
      rw [sys.additive ({0, 2} : Set (Fin 4)) {0, 3}]
      rw [show ({0, 2} : Set (Fin 4)) \ {0, 3} = {(2 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
          show ({0, 3} : Set (Fin 4)) \ {0, 2} = {(3 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]]
      exact h23
    -- ge({1,3},{0,3}) ↔ ge({1},{0})
    have h2 := sys.trans _ _ _ hge h1
    rw [sys.additive ({1, 3} : Set (Fin 4)) {0, 3}] at h2
    rw [show ({1, 3} : Set (Fin 4)) \ {0, 3} = {(1 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
        show ({0, 3} : Set (Fin 4)) \ {1, 3} = {(0 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]] at h2
    exact h10 h2
  · -- Route B: through {1,2}. ge({0,2},{1,2}) ↔ ge({0},{1}).
    have h1 : sys.ge ({0, 2} : Set (Fin 4)) {1, 2} := by
      rw [sys.additive ({0, 2} : Set (Fin 4)) {1, 2}]
      rw [show ({0, 2} : Set (Fin 4)) \ {1, 2} = {(0 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
          show ({1, 2} : Set (Fin 4)) \ {0, 2} = {(1 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]]
      exact h01
    -- ge({1,3},{1,2}) ↔ ge({3},{2})
    have h2 := sys.trans _ _ _ hge h1
    rw [sys.additive ({1, 3} : Set (Fin 4)) {1, 2}] at h2
    rw [show ({1, 3} : Set (Fin 4)) \ {1, 2} = {(3 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
        show ({1, 2} : Set (Fin 4)) \ {1, 3} = {(2 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]] at h2
    exact h32 h2

/-- ¬ge({2,3}, {0,1}) from singleton hypotheses via additive decomposition.
    Route A (¬ge({2},{0})): ge({2,3},{0,1}) → additive ge({0,1},{0,3}) via ge({1},{3})
      → trans → ge({2,3},{0,3}) → additive → ge({2},{0}) → contradiction.
    Route B (¬ge({3},{1})): ge({2,3},{0,1}) → additive ge({0,1},{1,2}) via ge({0},{2})
      → trans → ge({2,3},{1,2}) → additive → ge({3},{1}) → contradiction. -/
theorem nge_23_01 (sys : EpistemicSystemFA (Fin 4))
    (h12 : sys.ge {(1 : Fin 4)} {2}) (h23 : sys.ge {(2 : Fin 4)} {3})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (h : ¬sys.ge {(2 : Fin 4)} {0} ∨ ¬sys.ge {(3 : Fin 4)} {1}) :
    ¬sys.ge ({2, 3} : Set (Fin 4)) {0, 1} := by
  intro hge
  rcases h with h20 | h31
  · -- Route A: through {0,3}. ge({0,1},{0,3}) ↔ ge({1},{3}).
    have h13 := sys.trans _ _ _ h12 h23
    have h1 : sys.ge ({0, 1} : Set (Fin 4)) {0, 3} := by
      rw [sys.additive ({0, 1} : Set (Fin 4)) {0, 3}]
      rw [show ({0, 1} : Set (Fin 4)) \ {0, 3} = {(1 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
          show ({0, 3} : Set (Fin 4)) \ {0, 1} = {(3 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]]
      exact h13
    -- ge({2,3},{0,3}) ↔ ge({2},{0})
    have h2 := sys.trans _ _ _ hge h1
    rw [sys.additive ({2, 3} : Set (Fin 4)) {0, 3}] at h2
    rw [show ({2, 3} : Set (Fin 4)) \ {0, 3} = {(2 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
        show ({0, 3} : Set (Fin 4)) \ {2, 3} = {(0 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]] at h2
    exact h20 h2
  · -- Route B: through {1,2}. ge({0,1},{1,2}) ↔ ge({0},{2}).
    have h02 := sys.trans _ _ _ h01 h12
    have h1 : sys.ge ({0, 1} : Set (Fin 4)) {1, 2} := by
      rw [sys.additive ({0, 1} : Set (Fin 4)) {1, 2}]
      rw [show ({0, 1} : Set (Fin 4)) \ {1, 2} = {(0 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
          show ({1, 2} : Set (Fin 4)) \ {0, 1} = {(2 : Fin 4)} from
            by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]]
      exact h02
    -- ge({2,3},{1,2}) ↔ ge({3},{1})
    have h2 := sys.trans _ _ _ hge h1
    rw [sys.additive ({2, 3} : Set (Fin 4)) {1, 2}] at h2
    rw [show ({2, 3} : Set (Fin 4)) \ {1, 2} = {(3 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff],
        show ({1, 2} : Set (Fin 4)) \ {2, 3} = {(1 : Fin 4)} from
          by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]] at h2
    exact h31 h2

/-- Cancellation transfers through permutations (via representability). -/
theorem perm_cancellation {n : ℕ} (σ : Fin n ≃ Fin n)
    (sys : EpistemicSystemFA (Fin n))
    (hc : Cancellation n (transportFA σ sys).ge) :
    Cancellation n sys.ge := by
  obtain ⟨m, hm⟩ := perm_repr σ sys (cancellation_implies_representable _ hc)
  exact representable_implies_cancellation sys m hm

-- ═══════════════════════════════════════════════════════════════
-- § 6. KPS Theorem 8a via cancellation
-- ═══════════════════════════════════════════════════════════════

/-- **Theorem 8a for Fin 3** (via cancellation): every FA system on Fin 3 is
    representable by a finitely additive probability measure. -/
theorem theorem8a_fin3' (sys : EpistemicSystemFA (Fin 3)) :
    ∃ (m : FinAddMeasure (Fin 3)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  cancellation_implies_representable sys (fa_cancellation_fin3 sys)

end Core.Scale
