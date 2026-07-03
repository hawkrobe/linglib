import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv

/-!
# PMF constructors and ℝ-coercion utilities beyond mathlib's basic surface

Two layers:

**ℝ-coercion utilities** — `toRealFn`, `sum_toRealFn_eq_one`, and
nonneg/≤1 lemmas. The standard way to access a `PMF α`'s masses as
`ℝ`-valued (via `ENNReal.toReal`) without losing the `0 ≤ · ≤ 1` /
sum-to-1 invariants.

**ℝ-valued constructor** — `PMF.ofRealWeightFn`, the canonical entry
point for "I have non-negative `ℝ` weights and want a PMF":

| Constructor | Input | Specialises |
|---|---|---|
| `PMF.ofRealWeightFn` | `(α → ℝ)` non-negative + element-witness positivity (Fintype) | lifts via `ENNReal.ofReal` and routes through mathlib's `PMF.normalize` |

The constructor takes a **specific** positive witness `(a : α) (h : 0 < f a)`
rather than the existential form `(∃ a, 0 < f a)`. This avoids
`Classical.choose` in the body and matches the shape of mathlib's own
`PMF.normalize` hypotheses (`tsum f ≠ 0`, which is `tsum_ne_zero_iff`-
equivalent to a single witness via `ENNReal.summable.tsum_ne_zero_iff`).
For consumers holding `0 < ∑ a, f a` instead, derive a witness via
`Finset.sum_pos`.

`[UPSTREAM]` candidate: `ofRealWeightFn` fits cleanly into
`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean` as the
standard "non-negative real weights" entry point, paralleling `ofFintype`
(already-normalised ℝ≥0∞) and `normalize` (general ℝ≥0∞).

**Note on `PMF.normalize` for Fintype `ℝ≥0∞`-valued weights**: there is
no wrapper — call `PMF.normalize f hf0 hf` directly. The hypothesis
boilerplate at Fintype call sites is:
```
PMF.normalize f
  (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨a, h_pos⟩)
  (ENNReal.tsum_ne_top_of_fintype h_finite)
```
A `normalizeOfFintype` wrapper around this pattern was tried and removed
(0.231.X) — it bundled marginal value at the cost of an extra layer.
-/

open scoped ENNReal

namespace ENNReal

/-- On a finite type, an ENNReal `tsum` is finite iff every term is.
Convenience composition of `tsum_fintype` + `ENNReal.sum_ne_top` — the
combined form is the natural hypothesis shape for `PMF.normalize` /
`PMF.posterior` consumers. -/
theorem tsum_ne_top_of_fintype {α : Type*} [Fintype α] {f : α → ℝ≥0∞}
    (h : ∀ a, f a ≠ ∞) : ∑' a, f a ≠ ∞ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun a _ => h a

end ENNReal

namespace PMF

variable {α : Type*}

-- ============================================================================
-- §1: ENNReal → ℝ coercion of the mass function
-- ============================================================================

/-- Coerce a `PMF α`'s mass function from `ℝ≥0∞` to `ℝ`. -/
noncomputable def toRealFn (p : PMF α) : α → ℝ := fun a => (p a).toReal

theorem toRealFn_nonneg (p : PMF α) (a : α) : 0 ≤ p.toRealFn a :=
  ENNReal.toReal_nonneg

theorem toRealFn_le_one (p : PMF α) (a : α) : p.toRealFn a ≤ 1 := by
  have h := p.coe_le_one a
  unfold toRealFn
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

/-- For a `[Fintype α]` PMF, the `toReal`-coerced masses sum to 1. -/
theorem sum_toRealFn_eq_one [Fintype α] (p : PMF α) :
    ∑ a, p.toRealFn a = 1 := by
  have h_sum_ennreal : ∑ a : α, p a = 1 :=
    (PMF.tsum_coe p ▸ tsum_eq_sum (fun a (h : a ∉ Finset.univ) =>
      absurd (Finset.mem_univ a) h)).symm
  unfold toRealFn
  rw [show (∑ a, (p a).toReal) = ((∑ a : α, p a) : ℝ≥0∞).toReal from
      (ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)).symm]
  rw [h_sum_ennreal, ENNReal.toReal_one]

-- ============================================================================
-- §2: ℝ-valued normalisation for Fintype carriers
-- ============================================================================

/-- Construct a `PMF α` over a `Fintype` from a non-negative `ℝ`-valued
weight function with one positivity witness. Lifts to `ℝ≥0∞` via
`ENNReal.ofReal` and routes through mathlib's `PMF.normalize`.

The `_h_nonneg` hypothesis is unused in the body (`ENNReal.ofReal` clamps
negatives to 0 silently), but is kept on the signature because the
spec lemmas `support_ofRealWeightFn` and `ofRealWeightFn_toRealFn_eq`
require non-negativity to characterise the result faithfully. -/
noncomputable def ofRealWeightFn [Fintype α]
    (f : α → ℝ) (_h_nonneg : ∀ a, 0 ≤ f a)
    (a : α) (h_pos : 0 < f a) : PMF α :=
  PMF.normalize (fun x => ENNReal.ofReal (f x))
    (ENNReal.summable.tsum_ne_zero_iff.mpr
      ⟨a, by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h_pos⟩)
    (ENNReal.tsum_ne_top_of_fintype (fun _ => ENNReal.ofReal_ne_top))

/-- Closed-form value of `ofRealWeightFn`: each mass is the `ENNReal.ofReal`
of the weight, divided by the sum of `ofReal`-lifted weights. -/
@[simp] theorem ofRealWeightFn_apply [Fintype α]
    (f : α → ℝ) (h_nonneg : ∀ a, 0 ≤ f a)
    (a : α) (h_pos : 0 < f a) (b : α) :
    ofRealWeightFn f h_nonneg a h_pos b =
        ENNReal.ofReal (f b) * (∑ x, ENNReal.ofReal (f x))⁻¹ := by
  rw [ofRealWeightFn, PMF.normalize_apply]
  congr 2
  exact tsum_eq_sum (fun x (h : x ∉ Finset.univ) => absurd (Finset.mem_univ x) h)

/-- Support of `ofRealWeightFn` is the set of strictly-positive weights —
non-negative weights of `0` get cast to `ENNReal.ofReal 0 = 0` and drop out. -/
theorem support_ofRealWeightFn [Fintype α]
    (f : α → ℝ) (h_nonneg : ∀ a, 0 ≤ f a)
    (a : α) (h_pos : 0 < f a) :
    (ofRealWeightFn f h_nonneg a h_pos).support = {x | 0 < f x} := by
  rw [ofRealWeightFn, PMF.support_normalize]
  ext x
  rw [Function.mem_support, Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]

/-- Round-trip: when `f` is already normalised (sums to 1 in ℝ),
`ofRealWeightFn`'s normalisation divides by 1, recovering `f` exactly
through `toRealFn`. -/
theorem ofRealWeightFn_toRealFn_eq [Fintype α]
    (f : α → ℝ) (h_nonneg : ∀ a, 0 ≤ f a)
    (a : α) (h_pos : 0 < f a) (h_sum_one : ∑ a, f a = 1) :
    (ofRealWeightFn f h_nonneg a h_pos).toRealFn = f := by
  funext b
  show ((ofRealWeightFn f h_nonneg a h_pos) b).toReal = f b
  rw [ofRealWeightFn_apply]
  have h_sum_ennreal : (∑ x, ENNReal.ofReal (f x)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => h_nonneg x), h_sum_one,
        ENNReal.ofReal_one]
  rw [h_sum_ennreal, inv_one, mul_one, ENNReal.toReal_ofReal (h_nonneg b)]

end PMF

namespace PMF

/-! ### Iterated conditioning -/

variable {α : Type*}

/-- **Iterated conditioning collapses**: filtering on `s`, then on a subevent
    `s' ⊆ s`, is filtering on `s'` directly. Incremental Bayesian update by
    restriction agrees with direct conditioning ([levy-2008]'s eqs. (5)–(8)).
    `[UPSTREAM]` candidate for `Mathlib/Probability/ProbabilityMassFunction`. -/
theorem filter_filter (p : PMF α) {s s' : Set α} (hss : s' ⊆ s)
    (h : ∃ a ∈ s, a ∈ p.support) (h'' : ∃ a ∈ s', a ∈ p.support)
    (h' : ∃ a ∈ s', a ∈ (p.filter s h).support) :
    (p.filter s h).filter s' h' = p.filter s' h'' := by
  have hM0 : (∑' a, s.indicator p a) ≠ 0 := by simpa using h
  have hMtop : (∑' a, s.indicator p a) ≠ ⊤ := p.tsum_coe_indicator_ne_top s
  have hind : ∀ a, s'.indicator (⇑(p.filter s h)) a
      = s'.indicator p a * (∑' b, s.indicator p b)⁻¹ := by
    intro a
    by_cases ha : a ∈ s'
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, filter_apply,
        Set.indicator_of_mem (hss ha)]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, zero_mul]
  ext a
  rw [filter_apply, filter_apply]
  simp only [hind]
  rw [ENNReal.tsum_mul_right,
    ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hM0))
      (Or.inl (p.tsum_coe_indicator_ne_top s')), inv_inv,
    mul_comm ((∑' a, s'.indicator (⇑p) a)⁻¹) (∑' a, s.indicator (⇑p) a),
    ← mul_assoc, mul_assoc (s'.indicator (⇑p) a),
    ENNReal.inv_mul_cancel hM0 hMtop, mul_one]

/-- Conditional mass of a subevent under filtering: for `s' ⊆ s`, the filtered
    distribution gives `s'` the mass `p(s') / p(s)`. -/
theorem tsum_indicator_filter_of_subset (p : PMF α) {s s' : Set α} (hss : s' ⊆ s)
    (h : ∃ a ∈ s, a ∈ p.support) :
    ∑' a, s'.indicator (⇑(p.filter s h)) a
      = (∑' a, s'.indicator (⇑p) a) / (∑' a, s.indicator (⇑p) a) := by
  have hind : ∀ a, s'.indicator (⇑(p.filter s h)) a
      = s'.indicator (⇑p) a * (∑' b, s.indicator (⇑p) b)⁻¹ := by
    intro a
    by_cases ha : a ∈ s'
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, filter_apply,
        Set.indicator_of_mem (hss ha)]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, zero_mul]
  simp only [hind]
  rw [ENNReal.tsum_mul_right, div_eq_mul_inv]

open scoped ProbabilityTheory in
/-- `PMF.filter` is `Measure.cond`: conditioning a PMF on an event agrees with
    the measure-theoretic conditional measure. `[UPSTREAM]` candidate — it
    connects mathlib's two conditioning notions. -/
theorem toMeasure_filter [MeasurableSpace α] (p : PMF α) {s : Set α}
    (hs : MeasurableSet s) (h : ∃ a ∈ s, a ∈ p.support) :
    (p.filter s h).toMeasure = p.toMeasure[|s] := by
  refine MeasureTheory.Measure.ext fun t ht => ?_
  rw [ProbabilityTheory.cond_apply hs, PMF.toMeasure_apply,
    PMF.toMeasure_apply, PMF.toMeasure_apply]
  have hpt : ∀ a, t.indicator (⇑(p.filter s h)) a
      = (s ∩ t).indicator (⇑p) a * (∑' b, s.indicator (⇑p) b)⁻¹ := by
    intro a
    by_cases hat : a ∈ t
    · rw [Set.indicator_of_mem hat, filter_apply]
      by_cases has : a ∈ s
      · rw [Set.indicator_of_mem has, Set.indicator_of_mem (Set.mem_inter has hat)]
      · rw [Set.indicator_of_notMem has,
          Set.indicator_of_notMem (fun hc => has hc.1)]
    · rw [Set.indicator_of_notMem hat,
        Set.indicator_of_notMem (fun hc => hat hc.2), zero_mul]
  · simp only [hpt]
    rw [ENNReal.tsum_mul_right, mul_comm]
  · exact hs.inter ht
  · exact hs
  · exact ht

end PMF
