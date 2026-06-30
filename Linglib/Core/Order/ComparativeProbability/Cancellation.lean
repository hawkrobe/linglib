import Linglib.Core.Order.FourierMotzkin
import Linglib.Core.Order.ComparativeProbability.Representability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Scott cancellation for comparative probability

[kraft-pratt-seidenberg-1959]

Scott's cancellation framework for representability of comparative probability orderings
by finitely additive measures. A comparative probability ordering ≿ is representable
by a finitely additive measure iff it satisfies the **cancellation property**: no valid
neutral portfolio has a strict member.

The hard direction (cancellation → representable) is an instance of LP duality / Farkas'
lemma (`Polyhedral.farkas`, in `Core/Order/FourierMotzkin.lean`): the feasibility polytope
{p ≥ 0 : Σpᵢ = 1, ordering constraints} is nonempty iff no dual certificate of
infeasibility exists, and such a certificate corresponds exactly to a neutral portfolio
with a strict member.

## Main declarations

* `representable_implies_cancellation` — easy direction: measure existence → cancellation
* `cancellation_implies_representable` — hard direction: cancellation → measure existence
  (via `feasibleWeights`, `cancellation_nonempty`, `feasible_to_measure`)
* `fa_cancellation_fin3` — FA axioms imply cancellation on Fin 3 (in `CancellationFin4.lean`)
* `fa_cancellation_fin4` — FA axioms imply cancellation on Fin 4 (in `CancellationFin4.lean`)
-/

-- ═══════════════════════════════════════════════════════════════
-- Cancellation conditions for comparative probability
-- ═══════════════════════════════════════════════════════════════

namespace ComparativeProbability

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
    · linarith [List.sum_nonneg htl_nn]
    · linarith [hnn hd (.head _), ih htl_nn hxtl]

/-- The portfolio value (weighted sum of measure differences) equals the
    dot product of singleton measures with the weighted comparison sums.
    Proved by list induction on the portfolio; the key step connects
    comparison vectors to measure differences via `FinAddMeasure.muFinsetSum`. -/
private lemma finset_sum_as_univ {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℚ) :
    S.sum f = Finset.univ.sum (fun i => if i ∈ S then f i else 0) := by
  rw [← Finset.sum_filter]; congr 1; ext x; simp

private lemma single_comp_sum {n : ℕ} (m : FinAddMeasure ℚ (Fin n))
    (L R : Finset (Fin n)) (hd : Disjoint L R) :
    m.mu ↑L - m.mu ↑R =
    Finset.univ.sum (fun i : Fin n =>
      m.mu {i} * ((comparisonVec n L R i : ℤ) : ℚ)) := by
  rw [m.muFinsetSum L, m.muFinsetSum R, finset_sum_as_univ L, finset_sum_as_univ R,
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [comparisonVec]
  by_cases hL : i ∈ L <;> by_cases hR : i ∈ R <;> simp_all [Finset.disjoint_left.mp hd]

private lemma portfolio_interchange {n : ℕ} (m : FinAddMeasure ℚ (Fin n))
    (P : Portfolio n) :
    (P.map (fun wc => wc.weight * (m.mu ↑wc.left - m.mu ↑wc.right))).sum =
    Finset.univ.sum (fun i => m.mu {i} * Portfolio.weightedSum P i) := by
  induction P with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact (Finset.sum_eq_zero fun i _ => by simp [Portfolio.weightedSum]).symm
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
    rw [single_comp_sum m wc.left wc.right wc.disjoint, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

/-- **Easy direction**: If μ represents the ordering, no neutral portfolio has a
    strict member. Each comparison contributes wⱼ·(μ(Aⱼ)−μ(Bⱼ)) ≥ 0 to the
    portfolio value; if any is strict, the value is positive. But by the
    interchange lemma, the value also equals Σᵢ μ({i})·weightedSum(i) = 0
    by neutrality. -/
theorem representable_implies_cancellation {n : ℕ}
    {ge : Set (Fin n) → Set (Fin n) → Prop}
    (m : FinAddMeasure ℚ (Fin n))
    (hm : ∀ A B, ge A B ↔ m.inducedGe A B) :
    Cancellation n ge := by
  intro P hValid hNeutral ⟨wc, hwc_mem, hwc_strict⟩
  -- Define the portfolio valuation function
  let f : WComparison n → ℚ := fun wc => wc.weight * (m.mu ↑wc.left - m.mu ↑wc.right)
  -- Each term is nonneg
  have hnn : ∀ x ∈ P.map f, (0 : ℚ) ≤ x := by
    intro x hx
    obtain ⟨wc', hwc'_mem, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg wc'.weight_pos.le
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
    Representable sys := by
  obtain ⟨hnn, hsum, hcompat⟩ := hp
  -- Nonneg: each summand is nonneg
  have h_nonneg : ∀ A, 0 ≤ atomMu p A := fun A =>
    Finset.sum_nonneg fun i _ => by split <;> [exact hnn i; rfl]
  -- Finite additivity via pointwise case split on membership
  have h_additive : ∀ A B : Set (Fin n), Disjoint A B →
      atomMu p (A ∪ B) = atomMu p A + atomMu p B := by
    intro A B hAB
    simp only [atomMu, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
      simp_all [Set.mem_union, Set.disjoint_left.mp hAB]
  -- Normalization: all atoms in univ
  have h_total : atomMu p Set.univ = 1 := by
    simp only [atomMu, Set.mem_univ, ite_true, hsum]
  let m : FinAddMeasure ℚ (Fin n) := ⟨atomMu p, h_nonneg, h_additive, h_total⟩
  -- Representation via reduce_to_disjoint
  refine ⟨m, reduce_to_disjoint sys m (fun C D hdisj => ?_)⟩
  -- Convert Sets C, D to Finsets via filter
  have hCeq : (↑(Finset.univ.filter (· ∈ C)) : Set (Fin n)) = C := by ext x; simp
  have hDeq : (↑(Finset.univ.filter (· ∈ D)) : Set (Fin n)) = D := by ext x; simp
  have hfinDisj : Disjoint (Finset.univ.filter (· ∈ C)) (Finset.univ.filter (· ∈ D)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    exact Set.disjoint_left.mp hdisj hx1 hx2
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
  rw [hmuC, hmuD]; exact key

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
      · rintro rfl; exact ⟨Or.inl rfl, fun h => haS' (Finset.mem_coe.mp h)⟩
    rw [Finset.coe_insert, Set.insert_eq]
    exact sys.trans ∅ ↑S' ({a} ∪ ↑S') ih
      (by rw [sys.additive ↑S' ({a} ∪ ↑S'), h1, h2]; exact hall a)

/-- Not all singletons can be null: ∃ i, ¬sys.ge ∅ {i}. If all were null,
    FA induction gives sys.ge ∅ Set.univ, contradicting nonTrivial. -/
theorem not_all_null {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
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

/-- The comparison-vector dot product equals the finset-sum difference. -/
private lemma compVec_as_sum_diff {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → ℚ)
    (hdisj : Disjoint A B) :
    ∑ j : Fin n, ((comparisonVec n A B j : ℤ) : ℚ) * x j = A.sum x - B.sum x := by
  rw [finset_sum_as_univ A x, finset_sum_as_univ B x, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [comparisonVec]
  by_cases hA : j ∈ A <;> by_cases hB : j ∈ B <;>
    simp_all [Finset.disjoint_left.mp hdisj]

/-- All disjoint `ge`-pairs: disjoint (A, B) where `sys.ge ↑A ↑B`. -/
private noncomputable def gePairsOf {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    List (Finset (Fin n) × Finset (Fin n)) :=
  ((Finset.univ ×ˢ Finset.univ : Finset _).filter
    (fun ab => Disjoint ab.1 ab.2 ∧ sys.ge ↑ab.1 ↑ab.2)).toList

private theorem gePairs_mem {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (A B : Finset (Fin n)) (hd : Disjoint A B) (hge : sys.ge ↑A ↑B) :
    (A, B) ∈ gePairsOf sys := by
  simp only [gePairsOf, Finset.mem_toList, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and]; exact ⟨hd, hge⟩

private theorem gePairs_disj {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (gePairsOf sys).length) :
    Disjoint ((gePairsOf sys).get m).1 ((gePairsOf sys).get m).2 := by
  have := List.get_mem (gePairsOf sys) m
  simp only [gePairsOf, Finset.mem_toList, Finset.mem_filter] at this; exact this.2.1

private theorem gePairs_ge {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (gePairsOf sys).length) :
    sys.ge ↑((gePairsOf sys).get m).1 ↑((gePairsOf sys).get m).2 := by
  have := List.get_mem (gePairsOf sys) m
  simp only [gePairsOf, Finset.mem_toList, Finset.mem_filter] at this; exact this.2.2

-- ── Step 4b. The ordering LP: one Farkas application ─────

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
    Finset.mem_univ, true_and]; exact ⟨hd, hge, hng⟩

private theorem strictPairs_disj {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (strictPairsOf sys).length) :
    Disjoint ((strictPairsOf sys).get m).1 ((strictPairsOf sys).get m).2 := by
  have := List.get_mem (strictPairsOf sys) m
  simp only [strictPairsOf, Finset.mem_toList, Finset.mem_filter] at this; exact this.2.1

private theorem strictPairs_ge {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (strictPairsOf sys).length) :
    sys.ge ↑((strictPairsOf sys).get m).1 ↑((strictPairsOf sys).get m).2 := by
  have := List.get_mem (strictPairsOf sys) m
  simp only [strictPairsOf, Finset.mem_toList, Finset.mem_filter] at this; exact this.2.2.1

private theorem strictPairs_strict {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (m : Fin (strictPairsOf sys).length) :
    ¬sys.ge ↑((strictPairsOf sys).get m).2 ↑((strictPairsOf sys).get m).1 := by
  have := List.get_mem (strictPairsOf sys) m
  simp only [strictPairsOf, Finset.mem_toList, Finset.mem_filter] at this; exact this.2.2.2

/-- `(univ, ∅)` is always a strict pair, so the strict list is nonempty. -/
private theorem strictPairs_length_pos {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    0 < (strictPairsOf sys).length :=
  List.length_pos_of_mem (strictPairs_mem sys Finset.univ ∅ (Finset.disjoint_empty_right _)
    (by rw [Finset.coe_univ, Finset.coe_empty]; exact sys.mono _ _ (Set.empty_subset _))
    (by rw [Finset.coe_univ, Finset.coe_empty]; exact sys.nonTrivial))

/-- The core LP step: cancellation implies the feasibility polytope is nonempty.
    One Farkas application to the LP {p ≥ 0; compVec·p ≥ 0 per ge-pair;
    compVec·p ≥ 1 per strict pair}: a feasible point normalizes to a member of
    `feasibleWeights`; an infeasibility certificate assembles a valid neutral
    portfolio with a strict member, contradicting cancellation. -/
private theorem cancellation_nonempty {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge) :
    ∃ p, p ∈ feasibleWeights n sys := by
  let gePairs : List (Finset (Fin n) × Finset (Fin n)) := gePairsOf sys
  let k := gePairs.length
  let sp := strictPairsOf sys
  let K := sp.length
  have hgePairsMem : ∀ (A B : Finset (Fin n)), Disjoint A B → sys.ge ↑A ↑B →
      (A, B) ∈ gePairs := gePairs_mem sys
  have hgePairsDisj : ∀ m : Fin k, Disjoint (gePairs.get m).1 (gePairs.get m).2 :=
    gePairs_disj sys
  have hgePairsGe : ∀ m : Fin k, sys.ge ↑(gePairs.get m).1 ↑(gePairs.get m).2 :=
    gePairs_ge sys
  have hK_pos : 0 < K := strictPairs_length_pos sys
  -- constraint function: n nonneg + k ordering + K strict
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
      simp only [ineqFn, dif_pos i.isLt, Polyhedral.Ineq.sat, Polyhedral.dot, ite_mul,
        neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
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
      have hpair : 0 < (sp.get ⟨0, hK_pos⟩).1.sum x := by
        linarith [hx_strict ⟨0, hK_pos⟩,
          Finset.sum_nonneg (fun i (_ : i ∈ (sp.get ⟨0, hK_pos⟩).2) => hx_nn i)]
      linarith [Finset.sum_le_univ_sum_of_nonneg hx_nn (s := (sp.get ⟨0, hK_pos⟩).1)]
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
      refine ⟨fun hge => ?_, fun hge => ?_⟩
      · -- → direction
        show A.sum (fun i => x i / σ) ≥ B.sum (fun i => x i / σ)
        rw [← Finset.sum_div, ← Finset.sum_div]
        exact div_le_div_of_nonneg_right (hx_ord A B hdisj hge) (le_of_lt hσ_pos)
      · -- ← direction (contrapositive)
        by_contra hng
        have hBA : sys.ge ↑B ↑A := (sys.total ↑A ↑B).resolve_left hng
        have hmem := strictPairs_mem sys B A hdisj.symm hBA hng
        obtain ⟨⟨s, hs⟩, hgets⟩ := List.mem_iff_get.mp hmem
        have hgap := hx_strict ⟨s, hs⟩
        rw [hgets] at hgap
        -- B.sum x > A.sum x, so A.sum (x/σ) < B.sum (x/σ)
        have hlt : A.sum (fun i => x i / σ) < B.sum (fun i => x i / σ) := by
          rw [← Finset.sum_div, ← Finset.sum_div]
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

-- ── Step 4d. Compose: cancellation → feasible weights ──

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
    Representable sys := by
  obtain ⟨p, hp⟩ := cancellation_nonempty sys hcancel
  exact feasible_to_measure sys hp

/-- **Scott's theorem**: an FA system is representable by a finitely additive
    measure iff it satisfies the cancellation property. -/
theorem representable_iff_cancellation {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    Representable sys ↔ Cancellation n sys.ge :=
  ⟨fun ⟨m, hm⟩ => representable_implies_cancellation m hm,
   cancellation_implies_representable sys⟩

/-- A null atom plus a representability oracle one cardinality down yields
    cancellation: swap the null atom to position 0 and apply `null_elem_reduce`. -/
theorem cancellation_of_null_atom {n : ℕ} (sys : EpistemicSystemFA (Fin (n + 2)))
    {j : Fin (n + 2)} (hj : sys.ge ∅ {j})
    (sub : ∀ sys' : EpistemicSystemFA (Fin (n + 1)), Representable sys') :
    Cancellation (n + 2) sys.ge := by
  set σ := Equiv.swap (0 : Fin (n + 2)) j with hσ
  have h0 : (transportFA σ sys).ge ∅ {0} := by
    rw [perm_null_iff, show σ.symm 0 = j by simp [hσ]]; exact hj
  have hnn : ∃ i : Fin (n + 1), ¬(transportFA σ sys).ge ∅ {Fin.succ i} := by
    obtain ⟨k, hk⟩ := not_all_null (transportFA σ sys)
    obtain ⟨i, rfl⟩ : ∃ i, Fin.succ i = k :=
      Fin.exists_succ_eq.mpr fun h => hk (h ▸ h0)
    exact ⟨i, hk⟩
  obtain ⟨m, hm⟩ := perm_repr σ sys (null_elem_reduce _ h0 hnn sub)
  exact representable_implies_cancellation m hm

end ComparativeProbability
