import Linglib.Core.Probability.Finite
import Linglib.Core.Probability.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Marginals, conditionals, and products of joint PMFs

Structural operations on `PMF (α × β)`: the projections `fst`/`snd`
(row/column marginals), the conditional `cond`, and the independent
`product` (a mathlib gap, `[UPSTREAM]` candidate). These are
measure-free bookkeeping on finite joints; information-theoretic
consumers live in `Entropy.lean`, Bayesian ones in `JointPosterior.lean`.

## Main definitions

* `PMF.fst`, `PMF.snd` — marginals of a joint PMF via `PMF.map`.
* `PMF.cond` — conditional distribution given a second-coordinate value.
* `PMF.product` — independent product distribution.

## Main results

* `fst_apply` / `snd_apply` — marginals as row/column sums.
* `snd_mul_cond`, `toMeasure_cond` — chain rule and the bridge to
  `ProbabilityTheory.cond`.
* `product_apply`, `toMeasure_product` — pointwise and measure-level
  characterization of the product.
-/

set_option autoImplicit false

namespace PMF

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

open scoped ENNReal

-- ============================================================================
-- §3: Marginals (via PMF.map)
-- ============================================================================

/-- Marginal along the first projection. -/
noncomputable def fst (joint : PMF (α × β)) : PMF α := joint.map Prod.fst

/-- Marginal along the second projection. -/
noncomputable def snd (joint : PMF (α × β)) : PMF β := joint.map Prod.snd

-- ============================================================================
-- §3.5: Marginal-from-joint structural lemmas
-- ============================================================================

/-- `joint.fst a = ∑ b, joint (a, b)` for finite-Fintype joint PMFs.
    The first marginal is the row-sum of the joint. -/
theorem fst_apply [DecidableEq α] (joint : PMF (α × β)) (a : α) :
    joint.fst a = ∑ b : β, joint (a, b) := by
  show joint.map Prod.fst a = _
  rw [PMF.map_apply]
  rw [tsum_eq_sum (s := (Finset.univ : Finset (α × β)))
        (fun p (h : p ∉ Finset.univ) => absurd (Finset.mem_univ p) h)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    exact fun h => hb h.symm
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- `joint.snd b = ∑ a, joint (a, b)` for finite-Fintype joint PMFs.
    The second marginal is the column-sum of the joint. -/
theorem snd_apply [DecidableEq β] (joint : PMF (α × β)) (b : β) :
    joint.snd b = ∑ a : α, joint (a, b) := by
  show joint.map Prod.snd b = _
  rw [PMF.map_apply]
  rw [tsum_eq_sum (s := (Finset.univ : Finset (α × β)))
        (fun p (h : p ∉ Finset.univ) => absurd (Finset.mem_univ p) h)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_eq_single b]
  · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    exact fun h => ha h.symm
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- `toRealFn` of the first marginal equals the row-sum of `toRealFn` of the joint. -/
theorem fst_toRealFn_eq_sum [DecidableEq α] (joint : PMF (α × β)) (a : α) :
    joint.fst.toRealFn a = ∑ b : β, joint.toRealFn (a, b) := by
  unfold toRealFn
  rw [fst_apply]
  rw [ENNReal.toReal_sum (fun b _ => joint.apply_ne_top (a, b))]

/-- `toRealFn` of the second marginal equals the column-sum of `toRealFn` of the joint. -/
theorem snd_toRealFn_eq_sum [DecidableEq β] (joint : PMF (α × β)) (b : β) :
    joint.snd.toRealFn b = ∑ a : α, joint.toRealFn (a, b) := by
  unfold toRealFn
  rw [snd_apply]
  rw [ENNReal.toReal_sum (fun a _ => joint.apply_ne_top (a, b))]

/-- The joint is atomwise dominated by its first marginal. -/
theorem apply_le_fst [DecidableEq α] (joint : PMF (α × β)) (x : α × β) :
    joint x ≤ joint.fst x.1 := by
  rw [fst_apply]
  exact Finset.single_le_sum (f := fun b => joint (x.1, b))
    (fun _ _ => zero_le) (Finset.mem_univ x.2)

/-- The joint is atomwise dominated by its second marginal. -/
theorem apply_le_snd [DecidableEq β] (joint : PMF (α × β)) (x : α × β) :
    joint x ≤ joint.snd x.2 := by
  rw [snd_apply]
  exact Finset.single_le_sum (f := fun a => joint (a, x.2))
    (fun _ _ => zero_le) (Finset.mem_univ x.1)

/-- A point of positive joint mass has positive first-marginal mass. -/
theorem fst_apply_ne_zero [DecidableEq α] {joint : PMF (α × β)} {x : α × β}
    (h : joint x ≠ 0) : joint.fst x.1 ≠ 0 :=
  fun hz => h (le_zero_iff.mp (hz ▸ apply_le_fst joint x))

/-- A point of positive joint mass has positive second-marginal mass. -/
theorem snd_apply_ne_zero [DecidableEq β] {joint : PMF (α × β)} {x : α × β}
    (h : joint x ≠ 0) : joint.snd x.2 ≠ 0 :=
  fun hz => h (le_zero_iff.mp (hz ▸ apply_le_snd joint x))

omit [Fintype α] [Fintype β] in
/-- The fiber mass over a second-coordinate value is the second marginal. -/
theorem tsum_indicator_fiber_snd [DecidableEq β] (G : PMF (α × β)) (b : β) :
    ∑' x, ({x : α × β | x.2 = b}.indicator G) x = G.snd b := by
  rw [snd, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x.2 = b
  · rw [Set.indicator_of_mem (show x ∈ {x : α × β | x.2 = b} from hx),
      if_pos hx.symm]
  · rw [Set.indicator_of_notMem (show x ∉ {x : α × β | x.2 = b} from hx),
      if_neg fun hb => hx hb.symm]

omit [Fintype α] [Fintype β] in
/-- A positive second marginal is witnessed on its fiber. -/
theorem snd_apply_ne_zero_iff [DecidableEq β] (G : PMF (α × β)) (b : β) :
    G.snd b ≠ 0 ↔ ∃ x ∈ {x : α × β | x.2 = b}, x ∈ G.support := by
  rw [← tsum_indicator_fiber_snd G b, ne_eq, ENNReal.tsum_eq_zero, not_forall]
  simp

omit [Fintype α] [Fintype β] in
/-- The conditional distribution of the first coordinate of a joint given the
    second: the discrete disintegration of a joint PMF (the PMF mirror of
    `MeasureTheory.Measure.condKernel`), via `PMF.filter` on the fiber. Junk
    (an arbitrary point mass) at `b` of marginal mass zero; lemmas hypothesize
    `G.snd b ≠ 0`. -/
noncomputable def cond [DecidableEq β] (G : PMF (α × β)) (b : β) : PMF α :=
  if h : G.snd b ≠ 0 then
    (G.filter {x | x.2 = b} ((snd_apply_ne_zero_iff G b).mp h)).map Prod.fst
  else .pure G.support_nonempty.some.1

omit [Fintype α] [Fintype β] in
/-- The conditional is the joint renormalized by the marginal. -/
theorem cond_apply [DecidableEq β] (G : PMF (α × β)) {b : β} (h : G.snd b ≠ 0)
    (a : α) : G.cond b a = G (a, b) / G.snd b := by
  classical
  rw [cond, dif_pos h, PMF.map_apply,
    tsum_eq_single (a, b) fun x hx => ?_]
  · rw [if_pos rfl, PMF.filter_apply, Set.indicator_apply,
      if_pos (show (a, b) ∈ {x : α × β | x.2 = b} from rfl),
      tsum_indicator_fiber_snd, div_eq_mul_inv]
  · by_cases hx1 : a = x.1
    · rw [if_pos hx1, PMF.filter_apply, Set.indicator_apply,
        if_neg (show x ∉ {x : α × β | x.2 = b} from
          fun hx2 => hx (Prod.ext hx1.symm hx2)), zero_mul]
    · exact if_neg hx1

omit [Fintype α] [Fintype β] in
/-- **Disintegration identity**: marginal times conditional is the joint. -/
theorem snd_mul_cond [DecidableEq β] (G : PMF (α × β)) {b : β}
    (h : G.snd b ≠ 0) (a : α) : G.snd b * G.cond b a = G (a, b) := by
  rw [cond_apply G h a,
    ENNReal.mul_div_cancel' (fun h0 => absurd h0 h)
      fun ht => absurd ht (PMF.apply_ne_top _ _)]

omit [Fintype α] [Fintype β] in
/-- The measure of the conditional is the conditioned measure's first
    marginal, connecting `PMF.cond` to `ProbabilityTheory.cond`. -/
theorem toMeasure_cond [DecidableEq β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (G : PMF (α × β)) {b : β} (h : G.snd b ≠ 0) :
    (G.cond b).toMeasure
      = (ProbabilityTheory.cond G.toMeasure (Prod.snd ⁻¹' {b})).map Prod.fst := by
  rw [cond, dif_pos h]
  refine MeasureTheory.Measure.ext fun s hs => ?_
  rw [PMF.toMeasure_map_apply Prod.fst _ s measurable_fst hs,
    PMF.toMeasure_filter _ (show MeasurableSet {x : α × β | x.2 = b} from
      measurable_snd (measurableSet_singleton b)) _,
    MeasureTheory.Measure.map_apply measurable_fst hs]
  rfl

omit [Fintype α] [Fintype β] in
/-- The measure of the first marginal is the first marginal of the measure. -/
theorem toMeasure_fst [MeasurableSpace α] [MeasurableSpace β]
    (joint : PMF (α × β)) : joint.toMeasure.fst = joint.fst.toMeasure := by
  refine MeasureTheory.Measure.ext fun s hs => ?_
  rw [MeasureTheory.Measure.fst_apply hs, fst,
    PMF.toMeasure_map_apply Prod.fst joint s measurable_fst hs]

omit [Fintype α] [Fintype β] in
/-- The measure of the second marginal is the second marginal of the measure. -/
theorem toMeasure_snd [MeasurableSpace α] [MeasurableSpace β]
    (joint : PMF (α × β)) : joint.toMeasure.snd = joint.snd.toMeasure := by
  refine MeasureTheory.Measure.ext fun s hs => ?_
  rw [MeasureTheory.Measure.snd_apply hs, snd,
    PMF.toMeasure_map_apply Prod.snd joint s measurable_snd hs]

/-- Law of the unconscious statistician for the first marginal: the joint
    expectation of a function of the first coordinate is its expectation
    under the marginal. -/
theorem sum_toReal_mul_fst [DecidableEq α] (joint : PMF (α × β)) (f : α → ℝ) :
    ∑ x : α × β, (joint x).toReal * f x.1
      = ∑ a, (joint.fst a).toReal * f a := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [← Finset.sum_mul]
  exact congrArg (· * f a) (fst_toRealFn_eq_sum joint a).symm

/-- Law of the unconscious statistician for the second marginal. -/
theorem sum_toReal_mul_snd [DecidableEq β] (joint : PMF (α × β)) (f : β → ℝ) :
    ∑ x : α × β, (joint x).toReal * f x.2
      = ∑ b, (joint.snd b).toReal * f b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  dsimp only
  rw [← Finset.sum_mul]
  exact congrArg (· * f b) (snd_toRealFn_eq_sum joint b).symm

-- ============================================================================
-- §3.6: Independent product distribution
-- ============================================================================

/-! ### Product PMF

`PMF.product P Q` is the independent joint distribution: `(P.product Q) (a, b) =
P a · Q b`. Foundation for defining `mutualInformation` as `KL(joint ‖ product)`.

**Mathlib gap.** `PMF.product` is missing from mathlib. Defined here via the
standard monadic `bind`/`map` construction. -/

/-- The independent product distribution of two PMFs. -/
noncomputable def product (P : PMF α) (Q : PMF β) : PMF (α × β) :=
  P.bind (fun a => Q.map (Prod.mk a))

omit [Fintype α] [Fintype β] in
@[simp] theorem product_apply (P : PMF α) (Q : PMF β) (a : α) (b : β) :
    P.product Q (a, b) = P a * Q b := by
  classical
  simp only [product, PMF.bind_apply, PMF.map_apply]
  rw [tsum_eq_single a fun a' ha' => mul_eq_zero_of_right _
      ((tsum_congr fun b' =>
        if_neg fun h => ha' (Prod.mk.inj h).1.symm).trans tsum_zero)]
  exact congrArg (P a * ·) ((tsum_eq_single b fun b' hb' =>
    if_neg fun h => hb' (Prod.mk.inj h).2.symm).trans (if_pos rfl))

omit [Fintype α] [Fintype β] in
@[simp] theorem product_toRealFn (P : PMF α) (Q : PMF β) (a : α) (b : β) :
    (P.product Q).toRealFn (a, b) = P.toRealFn a * Q.toRealFn b := by
  unfold toRealFn
  rw [product_apply]
  exact ENNReal.toReal_mul

omit [Fintype α] [Fintype β] in
/-- The measure of the product PMF is the product of the measures. -/
theorem toMeasure_product [MeasurableSpace α] [MeasurableSpace β]
    (P : PMF α) (Q : PMF β) :
    (P.product Q).toMeasure = P.toMeasure.prod Q.toMeasure := by
  refine (MeasureTheory.Measure.prod_eq fun s t hs ht => ?_).symm
  rw [PMF.toMeasure_apply _ (hs.prod ht), PMF.toMeasure_apply _ hs,
    PMF.toMeasure_apply _ ht]
  have hpt : ∀ x : α × β, (s ×ˢ t).indicator (⇑(P.product Q)) x
      = s.indicator ⇑P x.1 * t.indicator ⇑Q x.2 := by
    intro ⟨a, b⟩
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;>
      simp [Set.mem_prod, ha, hb]
  simp_rw [hpt, ENNReal.tsum_prod', ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]


end PMF
