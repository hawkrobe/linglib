import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv

open scoped NNReal

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

/-- Mass of the uniform distribution, in ℝ. -/
@[simp] theorem uniformOfFintype_toRealFn [Fintype α] [Nonempty α] (a : α) :
    (uniformOfFintype α).toRealFn a = (Fintype.card α : ℝ)⁻¹ := by
  simp [toRealFn, uniformOfFintype_apply]

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

/-! ### Convex mixture -/

/-- Convex combination of two PMFs at rate `r`: draw a Bernoulli-`r` coin,
then sample `q` on heads and `p` on tails. Normalization is free from
`bind` — no `Fintype`, no sum proof. -/
noncomputable def mix (r : ℝ≥0) (hr : r ≤ 1) (p q : PMF α) : PMF α :=
  (bernoulli r hr).bind fun b => bif b then q else p

@[simp] theorem mix_apply (r : ℝ≥0) (hr : r ≤ 1) (p q : PMF α) (a : α) :
    mix r hr p q a = (1 - r) * p a + r * q a := by
  rw [mix, bind_apply, tsum_bool]
  simp [bernoulli_apply, mul_comm]

/-- The mixture in ℝ: `(1 − r)·p + r·q` pointwise. -/
theorem toRealFn_mix (r : ℝ≥0) (hr : r ≤ 1) (p q : PMF α) (a : α) :
    (mix r hr p q).toRealFn a = (1 - r) * p.toRealFn a + r * q.toRealFn a := by
  have h1 : (1 - (r : ℝ≥0∞)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  simp only [toRealFn, mix_apply]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top h1 (p.apply_ne_top a))
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (q.apply_ne_top a)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sub_of_le (by exact_mod_cast hr) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.coe_toReal]

/-- Normalize non-negative `ℝ` weights with positive total into a PMF.
The `_h_nonneg` hypothesis is unused in the body (`ENNReal.ofReal` clamps
negatives silently) but is kept so the spec lemmas characterise the
result faithfully. -/
noncomputable def ofRealWeightFn [Fintype α] (f : α → ℝ)
    (_h_nonneg : ∀ a, 0 ≤ f a) (h_pos : 0 < ∑ a, f a) : PMF α :=
  PMF.normalize (fun x => ENNReal.ofReal (f x))
    (by
      have hex : ∃ a, 0 < f a := by
        by_contra h
        push Not at h
        exact absurd h_pos (not_lt.mpr (Finset.sum_nonpos fun a _ => h a))
      obtain ⟨a, ha⟩ := hex
      exact ENNReal.summable.tsum_ne_zero_iff.mpr
        ⟨a, by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact ha⟩)
    (ENNReal.tsum_ne_top_of_fintype (fun _ => ENNReal.ofReal_ne_top))

/-- Closed-form value of `ofRealWeightFn` in `ℝ≥0∞`. -/
@[simp] theorem ofRealWeightFn_apply [Fintype α]
    (f : α → ℝ) (h_nonneg : ∀ a, 0 ≤ f a) (h_pos : 0 < ∑ a, f a) (b : α) :
    ofRealWeightFn f h_nonneg h_pos b =
        ENNReal.ofReal (f b) * (∑ x, ENNReal.ofReal (f x))⁻¹ := by
  rw [ofRealWeightFn, PMF.normalize_apply]
  congr 2
  exact tsum_eq_sum (fun x (h : x ∉ Finset.univ) => absurd (Finset.mem_univ x) h)

/-- Closed form in ℝ: each mass is its weight divided by the total. -/
theorem ofRealWeightFn_toRealFn_apply [Fintype α]
    (f : α → ℝ) (h_nonneg : ∀ a, 0 ≤ f a) (h_pos : 0 < ∑ a, f a) (b : α) :
    (ofRealWeightFn f h_nonneg h_pos).toRealFn b = f b / ∑ x, f x := by
  simp only [toRealFn, ofRealWeightFn_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h_nonneg b),
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => h_nonneg x), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal h_pos.le, div_eq_mul_inv]

/-- Support of `ofRealWeightFn`: the strictly-positive weights. -/
theorem support_ofRealWeightFn [Fintype α]
    (f : α → ℝ) (h_nonneg : ∀ a, 0 ≤ f a) (h_pos : 0 < ∑ a, f a) :
    (ofRealWeightFn f h_nonneg h_pos).support = {x | 0 < f x} := by
  rw [ofRealWeightFn, PMF.support_normalize]
  ext x
  rw [Function.mem_support, Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]

/-- Already-normalised weights are recovered exactly. -/
theorem ofRealWeightFn_toRealFn_eq [Fintype α]
    (f : α → ℝ) (h_nonneg : ∀ a, 0 ≤ f a) (h_pos : 0 < ∑ a, f a)
    (h_sum_one : ∑ a, f a = 1) :
    (ofRealWeightFn f h_nonneg h_pos).toRealFn = f :=
  funext fun b => by rw [ofRealWeightFn_toRealFn_apply, h_sum_one, div_one]

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

/-- A set meeting the support has nonzero measure. -/
theorem toMeasure_ne_zero [MeasurableSpace α] (p : PMF α) {s : Set α}
    (hs : MeasurableSet s) (h : ∃ a ∈ s, a ∈ p.support) : p.toMeasure s ≠ 0 :=
  (p.toMeasure_apply_eq_zero_iff hs).not.mpr <|
    Set.not_disjoint_iff.mpr <| h.elim fun a ha => ⟨a, ha.2, ha.1⟩

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
