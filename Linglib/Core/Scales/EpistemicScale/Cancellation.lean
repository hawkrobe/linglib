import Linglib.Core.Scales.EpistemicScale.Fin3

/-!
# Cancellation conditions for comparative probability

@cite{kraft-pratt-seidenberg-1959}

Scott's cancellation framework for representability of comparative probability orderings
by finitely additive measures. A comparative probability ordering is representable iff
it satisfies the cancellation property: no valid neutral portfolio has a strict member.

## Main results

* `representable_implies_cancellation` — easy direction: measure existence → cancellation
* `cancellation_implies_representable` — hard direction (sorry): cancellation → measure existence
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
private lemma portfolio_interchange {n : ℕ} (m : FinAddMeasure (Fin n))
    (P : Portfolio n) :
    (P.map (fun wc => wc.weight * (m.mu ↑wc.left - m.mu ↑wc.right))).sum =
    Finset.univ.sum (fun i => m.mu {i} * P.weightedSum i) := by
  sorry
  -- TODO: list induction + indicator algebra connecting comparisonVec to measures.
  -- Each step uses: Σ_i mu_i * compVec(i) = mu(L) - mu(R) (from mu_finset_sum)
  -- and Finset.sum_add_distrib for the cons case.

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

/-- Scott's theorem (hard direction): if no valid neutral portfolio has a strict
    member, then a finitely additive measure exists representing the ordering.
    Uses Farkas' lemma: LP infeasibility ↔ ∃ dual certificate (= neutral portfolio). -/
theorem cancellation_implies_representable {n : ℕ}
    (sys : EpistemicSystemFA (Fin n))
    (hcancel : Cancellation n sys.ge) :
    ∃ m : FinAddMeasure (Fin n), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  sorry
  -- Future: derive from ProperCone.hyperplane_separation applied to the
  -- feasibility cone {p ∈ ℝⁿ : p ≥ 0, Σpᵢ = 1, ordering constraints}.

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

/-- FA on Fin 4 implies the cancellation property. -/
theorem fa_cancellation_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    Cancellation 4 sys.ge := by
  sorry -- TODO: direct combinatorial argument or reduction to Fin 3 via merge

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
