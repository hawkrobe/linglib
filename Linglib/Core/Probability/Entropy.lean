import Linglib.Core.Probability.Finite
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.Constructions
import Linglib.Core.InformationTheory.KullbackLeibler.Cond
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Shannon entropy on `PMF`

Entropy / mutual information / conditional entropy / KL divergence / JSD as
methods on mathlib's `PMF α` (gated by `[Fintype α]`).

This file makes `PMF` the canonical distribution type for Shannon-entropy
operations across linglib. After the unification refactor (CHANGELOG entry
forthcoming), consumers go from:

    Core.InformationTheory.entropy Finset.univ p     -- old shape (private after Phase 6)
    p.entropy                                          -- new shape (PMF α)

The `Core.InformationTheory` module is reduced to non-Shannon-entropy
primitives (ΔP, structural lemmas about negMulLog/klFun/Hellinger). The
PMF-canonical shape is what RSA pragmatic operators (`L0OfMeaning` /
`S1Belief` / `L1`) already use as their normalized output type, and is the
natural target type for `ParadigmSystem` and the Rathi `LearnerModel`
(both refactored in the same migration).

## Public API

| Operator | Signature |
|---|---|
| `PMF.entropy` | `(p : PMF α) → ℝ`  — `H(p) = -∑ p log p` |
| `PMF.mutualInformation` | `(joint : PMF (α × β)) → ℝ`  — `I(X;Y)` from joint |
| `PMF.conditionalEntropy` | `(joint : PMF (α × β)) → ℝ`  — `H(β \| α)` from joint |
| `PMF.klDiv` | `(p q : PMF α) [MeasurableSpace α] → ℝ≥0∞`  — KL(p ‖ q), grounded in mathlib's `InformationTheory.klDiv` via `PMF.toMeasure` |
| `PMF.jsd` | `(p q : PMF α) → ℝ`  — Jensen-Shannon divergence |
| `PMF.toRealFn` | `(p : PMF α) → α → ℝ`  — `ℝ≥0∞ → ℝ` coercion |

## Implementation

Each operator is defined as `noncomputable def` (uses `Real.log` via
`Real.negMulLog`, plus `ENNReal.toReal`). Marginals are derived via
`PMF.map Prod.fst/snd` so the joint-distribution shape is canonical.

The proofs delegate to `Core.InformationTheory` lemmas via the coercion
`PMF.toRealFn : PMF α → α → ℝ`. The bridge is purely definitional
(`rfl`-provable). Phase 6 of the unification refactor keeps the
`Core.InformationTheory.entropy`-family operators as `private` helpers
for these delegations rather than as a public API.

## Cover-Thomas anchoring

Foundational properties match the Cover-Thomas (2006) information-theory
text. `entropy_nonneg` (CT 2.6.4) is proved here; `mutualInformation_nonneg`
(CT 2.6.5) and `conditionalEntropy_le_entropy` (CT 2.6.4) require
marginal-from-joint structural lemmas (`PMF.map_apply` on `Prod.fst/snd`)
and live in Phase 4 of the refactor (cross-paper bridges) along with the
substrate-level theorems that consume them.

All proofs in this file are structural. No `sorry`, no `decide`.
-/

set_option autoImplicit false

namespace PMF

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

open scoped ENNReal

-- ============================================================================
-- §1: Entropy
-- (ENNReal-to-Real coercion + PMF constructors live in `Constructions.lean`)
-- ============================================================================

/-- Shannon entropy of `p` (in nats): `H(p) = -∑ p log p = ∑ negMulLog p`.

    Defined directly on `PMF α` (not via delegation to
    `Core.InformationTheory.entropy`); the equivalence is the bridge
    theorem `entropy_eq_sum_negMulLog_toReal`. This independence lets the
    PMF entropy substrate stand on its own (mathlib pattern: each operator
    at its natural type, no cross-namespace delegation). -/
noncomputable def entropy (p : PMF α) : ℝ :=
  ∑ a, Real.negMulLog (p a).toReal

/-- Entropy is non-negative (Cover-Thomas 2.6.4). Direct proof via
    `Real.negMulLog_nonneg` applied pointwise: each summand is `≥ 0` since
    `(p a).toReal ∈ [0, 1]`. -/
theorem entropy_nonneg (p : PMF α) : 0 ≤ p.entropy := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (p.toRealFn_nonneg a) (p.toRealFn_le_one a)

/-- **Anti-drift bridge to mathlib's `Real.binEntropy`** (deferred): on a
    Bernoulli PMF with mass `p` and `1 - p`, our `PMF.entropy` should
    agree with mathlib's specialized `binEntropy p`. The bridge SHAPE is
    anti-drift — if mathlib changes `binEntropy` semantics the equivalence
    becomes provably false.

    TODO: stated in a follow-up. Requires `PMF.bernoulli` (mathlib has it
    over `ℝ≥0`; needs ℝ-coercion + arithmetic identities `negMulLog x =
    x · log x⁻¹` for the Bernoulli case). ~20 LOC. -/
example : True := trivial  -- placeholder; see TODO above

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

@[simp] theorem product_apply (P : PMF α) (Q : PMF β) (a : α) (b : β) :
    P.product Q (a, b) = P a * Q b := by
  classical
  simp only [product, PMF.bind_apply, PMF.map_apply]
  rw [tsum_eq_sum (fun a' (h : a' ∉ Finset.univ) => absurd (Finset.mem_univ a') h)]
  rw [Finset.sum_eq_single a]
  · rw [tsum_eq_sum (fun b' (h : b' ∉ Finset.univ) => absurd (Finset.mem_univ b') h)]
    rw [Finset.sum_eq_single b]
    · rw [if_pos rfl]
    · intro b' _ hb'
      exact if_neg (fun h => hb' (Prod.mk.inj h).2.symm)
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro a' _ ha'
    convert mul_zero _
    rw [tsum_eq_sum (fun b' (h : b' ∉ Finset.univ) => absurd (Finset.mem_univ b') h)]
    apply Finset.sum_eq_zero
    intro b' _
    exact if_neg (fun h => ha' (Prod.mk.inj h).1.symm)
  · intro h; exact absurd (Finset.mem_univ a) h

@[simp] theorem product_toRealFn (P : PMF α) (Q : PMF β) (a : α) (b : β) :
    (P.product Q).toRealFn (a, b) = P.toRealFn a * Q.toRealFn b := by
  unfold toRealFn
  rw [product_apply]
  exact ENNReal.toReal_mul

-- §4 (mutualInformation) and §5 (conditionalEntropy) moved to after §6 KL —
-- they depend on `PMF.klDiv` which is defined in §6.

-- ============================================================================
-- §6: KL divergence — grounded in mathlib's `InformationTheory.klDiv`
-- ============================================================================

/-! ### KL divergence on PMFs: rfl-bridge to mathlib

`PMF.klDiv` is defined as the mathlib measure-theoretic
`InformationTheory.klDiv` applied to `PMF.toMeasure`. The bridge is
`rfl`-provable — drift is structurally impossible. If mathlib refactors
`klDiv`, our def follows automatically.

The return type `ℝ≥0∞` matches mathlib's. Non-negativity is by **type**,
not by theorem — no `klDiv_nonneg` lemma needed. All ~12 mathlib `klDiv`
theorems (`klDiv_self`, `klDiv_zero_left`, `klDiv_eq_zero_iff`,
`klDiv_eq_top_iff`, `klDiv_ne_top`, ...) become available on `PMF.klDiv`
via the `rfl`-bridge with no further proof obligation.

**There is no `PMF.klDivergence` (`ℝ`-returning) backwards-compatibility
form.** Per linglib's no-backcompat-shims discipline (MEMORY:
`feedback_no_backcompat`), the previous discrete-sum `klDivergence` was
deleted to force consumers onto the single canonical API. Consumers that
need an `ℝ` value use `(p.klDiv q).toReal`. The discrete-sum form (when
needed for proof manipulation) is the theorem `klDiv_eq_sum_klFun`. -/

/-- **KL divergence on PMFs**, grounded in mathlib's
    `InformationTheory.klDiv`. Returns `ℝ≥0∞` (non-negative by type;
    `∞` for non-abs-continuous case). Inherits all mathlib `klDiv`
    theorems via the `rfl`-bridge. Requires `[MeasurableSpace α]`; for
    `[Fintype α]`, equip with the discrete `⊤` measurable space. -/
noncomputable def klDiv {α : Type*} [MeasurableSpace α] (p q : PMF α) : ℝ≥0∞ :=
  _root_.InformationTheory.klDiv p.toMeasure q.toMeasure

/-- The rfl-bridge: `PMF.klDiv` IS mathlib's `klDiv` on the `toMeasure`
    coercions. Drift is structurally impossible. -/
@[simp] theorem klDiv_eq_toMeasure_klDiv {α : Type*} [MeasurableSpace α]
    (p q : PMF α) :
    p.klDiv q = _root_.InformationTheory.klDiv p.toMeasure q.toMeasure := rfl

/-! ### Mathlib-inherited theorems

The following theorems are direct corollaries of mathlib's `klDiv` API on
the `toMeasure`-coerced PMFs. They're stated here as 1-line wrappers for
ergonomic consumer access (`p.klDiv_self` reads better than
`_root_.InformationTheory.klDiv_self p.toMeasure`). -/

/-- Mathlib `klDiv_self`: KL divergence of a PMF against itself is 0. -/
theorem klDiv_self {α : Type*} [MeasurableSpace α] (p : PMF α) :
    p.klDiv p = 0 :=
  _root_.InformationTheory.klDiv_self _

/-- KL divergence is `∞` exactly when `p` is not absolutely continuous wrt `q`
    or `llr` is not integrable. Inherited from mathlib's `klDiv_eq_top_iff`. -/
theorem klDiv_eq_top_iff {α : Type*} [MeasurableSpace α] (p q : PMF α) :
    p.klDiv q = ∞ ↔
    MeasureTheory.Measure.AbsolutelyContinuous p.toMeasure q.toMeasure →
    ¬ MeasureTheory.Integrable
        (MeasureTheory.llr p.toMeasure q.toMeasure) p.toMeasure :=
  _root_.InformationTheory.klDiv_eq_top_iff

/-- KL divergence is finite iff `p ≪ q` and `llr` is integrable.
    Inherited from mathlib's `klDiv_ne_top_iff`. -/
theorem klDiv_ne_top_iff {α : Type*} [MeasurableSpace α] (p q : PMF α) :
    p.klDiv q ≠ ∞ ↔
    MeasureTheory.Measure.AbsolutelyContinuous p.toMeasure q.toMeasure ∧
    MeasureTheory.Integrable
      (MeasureTheory.llr p.toMeasure q.toMeasure) p.toMeasure :=
  _root_.InformationTheory.klDiv_ne_top_iff

/-- Sufficient condition for `p.klDiv q ≠ ∞`. Inherited from mathlib's
    `klDiv_ne_top`. -/
theorem klDiv_ne_top {α : Type*} [MeasurableSpace α] {p q : PMF α}
    (hpq : MeasureTheory.Measure.AbsolutelyContinuous p.toMeasure q.toMeasure)
    (hint : MeasureTheory.Integrable
      (MeasureTheory.llr p.toMeasure q.toMeasure) p.toMeasure) :
    p.klDiv q ≠ ∞ :=
  _root_.InformationTheory.klDiv_ne_top hpq hint

/-- **Discrete-sum reduction theorem** (`klDiv_eq_sum_klFun`):
    for `[Fintype α]` PMFs, the mathlib-grounded `klDiv` reduces to a
    discrete sum (when `p ≪ q`; the value is `∞` otherwise).

        p.klDiv q = ∑ a, q a * ENNReal.ofReal (klFun ((p a / q a).toReal))

    Proof structure: bridge `p.toMeasure = q.toMeasure.withDensity (p/q)`
    via `Measure.ext` + `lintegral_fintype` + per-atom ENNReal cancellation
    `(p a / q a) * q a = p a` (which holds under singleton-AC); from there
    `Measure.rnDeriv_withDensity` gives the rnDeriv ae-equality, and
    `klDiv_eq_lintegral_klFun_of_ac` plus `lintegral_fintype` close the
    sum reduction. -/
theorem klDiv_eq_sum_klFun {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α)
    (hpq : MeasureTheory.Measure.AbsolutelyContinuous p.toMeasure q.toMeasure) :
    p.klDiv q =
      ∑ a, q a * ENNReal.ofReal (_root_.InformationTheory.klFun
        (((p a) / (q a)).toReal)) := by
  -- All functions on `[Fintype α] [MeasurableSingletonClass α]` are measurable.
  have hf_meas : Measurable (fun x : α => p x / q x) := measurable_of_finite _
  -- Lift set-AC to atom-AC: `q a = 0 → p a = 0`. Used in ENNReal cancellation.
  have h_ac_atom : ∀ x : α, q x = 0 → p x = 0 := by
    intro x hqx
    have hQ : q.toMeasure {x} = 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]; exact hqx
    have hP : p.toMeasure {x} = 0 := hpq hQ
    rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)] at hP
  -- Pointwise ENNReal cancellation: `(p x / q x) * q x = p x`.
  have h_div_mul : ∀ x : α, (p x) / (q x) * (q x) = p x := fun x =>
    ENNReal.div_mul_cancel' (h_ac_atom x) (fun h => absurd h (PMF.apply_ne_top q x))
  -- Lift the pointwise identity to a measure-level one:
  -- `p.toMeasure = q.toMeasure.withDensity (p/q)`.
  have h_with_density :
      p.toMeasure = q.toMeasure.withDensity (fun x => p x / q x) := by
    refine MeasureTheory.Measure.ext (fun s hs => ?_)
    rw [MeasureTheory.withDensity_apply _ hs,
        ← MeasureTheory.lintegral_indicator hs,
        MeasureTheory.lintegral_fintype,
        PMF.toMeasure_apply_fintype _ s]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
    by_cases hy : y ∈ s
    · simp only [Set.indicator_of_mem hy]
      exact (h_div_mul y).symm
    · simp only [Set.indicator_of_notMem hy, zero_mul]
  -- The density is the rnDeriv (q.toMeasure-almost-everywhere).
  have h_rnDeriv :
      p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun x => p x / q x := by
    conv_lhs => rw [h_with_density]
    exact MeasureTheory.Measure.rnDeriv_withDensity _ hf_meas
  -- ae-equality of klFun composed with rnDeriv vs (p/q).
  have h_integrand : (fun x => ENNReal.ofReal
      (_root_.InformationTheory.klFun (p.toMeasure.rnDeriv q.toMeasure x).toReal))
      =ᵐ[q.toMeasure] (fun x => ENNReal.ofReal
      (_root_.InformationTheory.klFun ((p x / q x).toReal))) := by
    filter_upwards [h_rnDeriv] with x hx
    rw [hx]
  -- Combine: klDiv → mathlib lintegral form → ae-rewrite → lintegral_fintype → atomwise.
  rw [PMF.klDiv_eq_toMeasure_klDiv,
      _root_.InformationTheory.klDiv_eq_lintegral_klFun_of_ac hpq,
      MeasureTheory.lintegral_congr_ae h_integrand,
      MeasureTheory.lintegral_fintype]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y), mul_comm]

open scoped ProbabilityTheory in
/-- The Kullback-Leibler divergence of `p` conditioned on an event `s` from
`p` itself is the negative log-mass of the event ([levy-2008]'s eq. (4) at
its most general). -/
theorem klDiv_filter_self {α : Type*} [MeasurableSpace α] (p : PMF α) {s : Set α}
    (hs : MeasurableSet s) (h : ∃ a ∈ s, a ∈ p.support) :
    (p.filter s h).klDiv p = ENNReal.ofReal (-Real.log (p.toMeasure s).toReal) := by
  rw [klDiv_eq_toMeasure_klDiv, PMF.toMeasure_filter p hs h]
  exact InformationTheory.klDiv_cond_self p.toMeasure hs (p.toMeasure_ne_zero hs h)

-- ============================================================================
-- §7: Jensen-Shannon divergence — KL-symmetrized form (mathlib-style)
-- ============================================================================

/-! ### Midpoint distribution + KL-based JSD

Mathlib-style definition: `JSD(p, q) := (KL(p ‖ m) + KL(q ‖ m))/2` where
`m = (p + q)/2`. The classical `H(m) − (H(p) + H(q))/2` formula becomes
a derived theorem (`jsd_eq_entropy_form`).

**Reuse payoff**: `jsd_nonneg` reduces to `ENNReal.toReal_nonneg` / 2.
`jsd_symm` reduces to symmetry of the sum + symmetry of `midPMF`. -/

/-- The 1/2-mixture distribution: `(midPMF p q) a = (p a + q a) / 2`. -/
noncomputable def midPMF (p q : PMF α) : PMF α :=
  PMF.ofFintype (fun a => (p a + q a) / 2) <| by
    show (∑ a : α, (p a + q a) / 2) = 1
    have h_sum_p : (∑ a : α, p a) = 1 :=
      (tsum_eq_sum (fun a (h : a ∉ Finset.univ) =>
        absurd (Finset.mem_univ a) h)).symm.trans (PMF.tsum_coe p)
    have h_sum_q : (∑ a : α, q a) = 1 :=
      (tsum_eq_sum (fun a (h : a ∉ Finset.univ) =>
        absurd (Finset.mem_univ a) h)).symm.trans (PMF.tsum_coe q)
    -- ENNReal doesn't have DivisionSemiring (no field structure due to ⊤),
    -- so use div_eq_mul_inv + Finset.sum_mul.
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, h_sum_p, h_sum_q,
        show ((1 : ℝ≥0∞) + 1) = 2 from by norm_num, ← div_eq_mul_inv]
    exact ENNReal.div_self (by norm_num) (by norm_num)

@[simp] theorem midPMF_apply (p q : PMF α) (a : α) :
    (midPMF p q) a = (p a + q a) / 2 := by
  unfold midPMF
  rw [PMF.ofFintype_apply]

theorem midPMF_symm (p q : PMF α) : midPMF p q = midPMF q p := by
  ext a
  rw [midPMF_apply, midPMF_apply, add_comm]

theorem midPMF_toRealFn (p q : PMF α) (a : α) :
    (midPMF p q).toRealFn a = (p.toRealFn a + q.toRealFn a) / 2 := by
  unfold toRealFn
  rw [midPMF_apply, ENNReal.toReal_div, ENNReal.toReal_add (PMF.apply_ne_top p a)
        (PMF.apply_ne_top q a)]
  rfl

/-- Jensen-Shannon divergence `JSD(p, q) := (KL(p ‖ m) + KL(q ‖ m))/2`
    where `m := midPMF p q`, grounded in `PMF.klDiv`. -/
noncomputable def jsd [MeasurableSpace α] (p q : PMF α) : ℝ :=
  ((p.klDiv (midPMF p q)).toReal + (q.klDiv (midPMF p q)).toReal) / 2

/-- **JSD is non-negative** — free from `ENNReal.toReal_nonneg`. -/
theorem jsd_nonneg [MeasurableSpace α] (p q : PMF α) : 0 ≤ jsd p q := by
  unfold jsd
  positivity

/-- **JSD is symmetric** — `JSD(p, q) = JSD(q, p)`, free from `midPMF_symm`. -/
theorem jsd_symm [MeasurableSpace α] (p q : PMF α) : jsd p q = jsd q p := by
  unfold jsd
  rw [midPMF_symm]
  ring

-- ============================================================================
-- §7.5: Hellinger family (Bhattacharyya, squared-Hellinger, Hellinger distance)
-- ============================================================================

/-! ### Hellinger family on PMF

[herbstritt-franke-2019] use Hellinger distance as an alternative to
KL divergence in RSA speaker utilities, because Hellinger remains finite
when literal interpretations assign zero probability to states the speaker
considers possible (whereas KL diverges).

Defined directly on PMFs (no `Core.InformationTheory` delegation). Mathlib
gap — these specializations to `PMF` are upstreamable. -/

/-- Bhattacharyya coefficient `BC(P, Q) = ∑ √(P · Q)`. -/
noncomputable def bhattacharyyaCoeff (P Q : PMF α) : ℝ :=
  ∑ a : α, Real.sqrt (P.toRealFn a * Q.toRealFn a)

/-- Squared Hellinger distance `H²(P, Q) = 1 - BC(P, Q)`. -/
noncomputable def hellingerDistSq (P Q : PMF α) : ℝ :=
  1 - bhattacharyyaCoeff P Q

/-- Hellinger distance `HD(P, Q) = √H²(P, Q)`. Proper metric on PMFs;
    bounded in `[0, 1]` for probability distributions. -/
noncomputable def hellingerDist (P Q : PMF α) : ℝ :=
  Real.sqrt (hellingerDistSq P Q)

theorem hellingerDistSq_nonneg (P Q : PMF α)
    (h : bhattacharyyaCoeff P Q ≤ 1) :
    0 ≤ hellingerDistSq P Q := by
  unfold hellingerDistSq; linarith

/-! ### Bretagnolle–Huber substrate (private helpers)

Pure real-arithmetic helpers for the BH inequality `2 · H²(P, Q) ≤ KL(P ‖ Q)`.
Inlined here (not in `Core.InformationTheory`) so that Entropy is
self-contained against Core deletion. -/

/-- Pointwise: `(√x − 1)² ≤ klFun(x)` for `x ≥ 0`. Identity:
    `klFun(x) − (√x − 1)² = 2√x · klFun(√x)`, both factors non-negative. -/
private theorem sqrt_sub_one_sq_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x - 1) ^ 2 ≤ _root_.InformationTheory.klFun x := by
  set s := Real.sqrt x with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg x
  have hs_sq : s * s = x := Real.mul_self_sqrt hx
  have hkl_s : 0 ≤ _root_.InformationTheory.klFun s :=
    _root_.InformationTheory.klFun_nonneg hs_nn
  have hlog : Real.log x = 2 * Real.log s := by
    rw [hs_def, Real.log_sqrt hx]; ring
  have hidentity : _root_.InformationTheory.klFun x =
      (s - 1) ^ 2 + 2 * s * _root_.InformationTheory.klFun s := by
    unfold _root_.InformationTheory.klFun
    rw [hlog, ← hs_sq]
    ring
  have h2skl_nn : 0 ≤ 2 * s * _root_.InformationTheory.klFun s :=
    mul_nonneg (mul_nonneg (by norm_num) hs_nn) hkl_s
  linarith

/-- Per-index BH bridge: `q · (√(p/q) − 1)² = (√p − √q)²` for `p ≥ 0`, `q > 0`. -/
private theorem mul_sqrt_div_sub_one_sq (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    q * (Real.sqrt (p / q) - 1) ^ 2 = (Real.sqrt p - Real.sqrt q) ^ 2 := by
  have hsQ_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsQ_ne : Real.sqrt q ≠ 0 := ne_of_gt hsQ_pos
  have hsQ_sq : Real.sqrt q ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
  rw [Real.sqrt_div hp q]
  have hstep : Real.sqrt p / Real.sqrt q - 1 =
      (Real.sqrt p - Real.sqrt q) / Real.sqrt q := by
    field_simp
  rw [hstep, div_pow, hsQ_sq]
  have hq_ne : q ≠ 0 := ne_of_gt hq
  field_simp

/-- **Discrete log-ratio sum form of `klDiv`**:
    `(P.klDiv Q).toReal = ∑ a, P a · log (P a / Q a)` under strict-positive Q.

    This is the consumer-facing discrete sum that downstream files want
    (Cover-Thomas Eq. 2.23). Self-contained — uses only mathlib's `klFun`
    plus `klDiv_eq_sum_klFun`. Independent of `Core.InformationTheory.klFinite`. -/
theorem toReal_klDiv_eq_sum_log_div [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : PMF α) (hQ_pos : ∀ a, 0 < Q.toRealFn a) :
    (P.klDiv Q).toReal =
      ∑ a, P.toRealFn a * Real.log (P.toRealFn a / Q.toRealFn a) := by
  have hQ_ne_top : ∀ a, Q a ≠ ∞ := PMF.apply_ne_top Q
  have hQ_ne_zero : ∀ a, Q a ≠ 0 := fun a hQa => by
    have h := hQ_pos a
    rw [show Q.toRealFn a = (Q a).toReal from rfl, hQa, ENNReal.toReal_zero] at h
    exact lt_irrefl 0 h
  -- AC from strict-positive Q (every singleton has positive Q-mass, so the
  -- only Q-null measurable set is empty).
  have hAC : MeasureTheory.Measure.AbsolutelyContinuous P.toMeasure Q.toMeasure := by
    refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs hQs => ?_
    rw [PMF.toMeasure_apply_fintype _ s] at hQs
    rw [PMF.toMeasure_apply_fintype _ s]
    have h_each_zero : ∀ y ∈ (Finset.univ : Finset α), s.indicator (⇑Q) y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => zero_le)).mp hQs
    have h_x_notin : ∀ x, x ∉ s := fun x hx_in => by
      have h := h_each_zero x (Finset.mem_univ x)
      rw [Set.indicator_of_mem hx_in] at h
      exact hQ_ne_zero x h
    refine Finset.sum_eq_zero (fun x _ => Set.indicator_of_notMem (h_x_notin x) _)
  -- Apply discrete reduction.
  rw [klDiv_eq_sum_klFun P Q hAC]
  -- Pull `.toReal` inside the sum (each summand is finite).
  rw [ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (hQ_ne_top a) ENNReal.ofReal_ne_top)]
  -- Per-summand: ENNReal arithmetic → real arithmetic.
  have h_summand : ∀ a, (Q a * ENNReal.ofReal
      (_root_.InformationTheory.klFun ((P a / Q a).toReal))).toReal
      = Q.toRealFn a * _root_.InformationTheory.klFun
          (P.toRealFn a / Q.toRealFn a) := by
    intro a
    rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal
          (_root_.InformationTheory.klFun_nonneg ENNReal.toReal_nonneg),
        ENNReal.toReal_div]
    rfl
  simp_rw [h_summand]
  -- Bridge ∑ q · klFun(p/q) = ∑ p · log(p/q) via the identity
  -- `q · klFun(p/q) - p · log(p/q) = q - p` (when q > 0), summed against
  -- ∑P = ∑Q = 1.
  have h_per : ∀ a,
      Q.toRealFn a * _root_.InformationTheory.klFun
          (P.toRealFn a / Q.toRealFn a)
        - P.toRealFn a * Real.log (P.toRealFn a / Q.toRealFn a)
        = Q.toRealFn a - P.toRealFn a := by
    intro a
    have hq_ne : Q.toRealFn a ≠ 0 := ne_of_gt (hQ_pos a)
    unfold _root_.InformationTheory.klFun
    field_simp
    ring
  have h_sum_diff :
      (∑ a, Q.toRealFn a * _root_.InformationTheory.klFun
          (P.toRealFn a / Q.toRealFn a))
        - (∑ a, P.toRealFn a * Real.log (P.toRealFn a / Q.toRealFn a))
      = 0 := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [h_per]
    rw [Finset.sum_sub_distrib, Q.sum_toRealFn_eq_one,
        P.sum_toRealFn_eq_one, sub_self]
  linarith

-- ============================================================================
-- §7.6: Mutual information — KL of joint vs product (mathlib-style)
-- ============================================================================

/-! ### MI as KL of joint vs product

Mathlib-style definition: `I(X;Y) := KL(joint ‖ marginal_X × marginal_Y).toReal`.
The classical `H(X) + H(Y) − H(X,Y)` formula becomes a derived theorem
(Cover-Thomas Thm 2.6.5, `mutualInformation_eq_entropy_sum`).

**Reuse payoff**: `mutualInformation_nonneg` reduces to `ENNReal.toReal_nonneg`.
Future `klDiv` chain rules from mathlib transfer to MI for free. -/

/-- Mutual information `I(X;Y) := KL(joint ‖ marginal_X × marginal_Y).toReal`,
    grounded in `PMF.klDiv` (rfl-bridged to mathlib's `InformationTheory.klDiv`). -/
noncomputable def mutualInformation [MeasurableSpace α] [MeasurableSpace β]
    (joint : PMF (α × β)) : ℝ :=
  (joint.klDiv (joint.fst.product joint.snd)).toReal

omit [Fintype α] [Fintype β] in
/-- **Mutual information is non-negative** (Cover-Thomas 2.6.5):
    free from `ENNReal.toReal_nonneg` since `klDiv` returns `ℝ≥0∞`. -/
theorem mutualInformation_nonneg [MeasurableSpace α] [MeasurableSpace β]
    (joint : PMF (α × β)) : 0 ≤ joint.mutualInformation :=
  ENNReal.toReal_nonneg

/-- **Cover-Thomas Thm 2.6.5 bridge**: `I(X;Y) = H(X) + H(Y) − H(X,Y)`.
    Connects the KL-based definition (this file) to the classical
    H-difference form. -/
theorem mutualInformation_eq_entropy_sum [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DecidableEq α] [DecidableEq β]
    (joint : PMF (α × β))
    (h_margX_pos : ∀ a, 0 < joint.fst.toRealFn a)
    (h_margY_pos : ∀ b, 0 < joint.snd.toRealFn b) :
    joint.mutualInformation
      = joint.fst.entropy + joint.snd.entropy - joint.entropy := by
  -- Strict-positive product follows from strict-positive marginals.
  have h_prod_pos : ∀ p : α × β,
      0 < (joint.fst.product joint.snd).toRealFn p := by
    rintro ⟨a, b⟩
    rw [product_toRealFn]
    exact mul_pos (h_margX_pos a) (h_margY_pos b)
  -- Step 1: expand KL as discrete log-ratio sum.
  unfold mutualInformation
  rw [toReal_klDiv_eq_sum_log_div joint
        (joint.fst.product joint.snd) h_prod_pos]
  -- Step 2: substitute product_toRealFn for cleaner working form.
  have h_subst : (∑ p : α × β, joint.toRealFn p *
            Real.log (joint.toRealFn p /
              (joint.fst.product joint.snd).toRealFn p))
      = ∑ ab : α × β, joint.toRealFn ab *
            Real.log (joint.toRealFn ab /
              (joint.fst.toRealFn ab.1 * joint.snd.toRealFn ab.2)) := by
    refine Finset.sum_congr rfl (fun ⟨a, b⟩ _ => ?_)
    rw [product_toRealFn]
  rw [h_subst, Fintype.sum_prod_type]
  -- Step 3: per-(a,b) algebra: split log of product, distribute joint.
  have h_per : ∀ a b,
      joint.toRealFn (a, b) *
        Real.log (joint.toRealFn (a, b) /
          (joint.fst.toRealFn a * joint.snd.toRealFn b))
        = joint.toRealFn (a, b) * Real.log (joint.toRealFn (a, b))
          - joint.toRealFn (a, b) * Real.log (joint.fst.toRealFn a)
          - joint.toRealFn (a, b) * Real.log (joint.snd.toRealFn b) := by
    intro a b
    by_cases hJ : joint.toRealFn (a, b) = 0
    · simp [hJ]
    · have hMX_ne : joint.fst.toRealFn a ≠ 0 := ne_of_gt (h_margX_pos a)
      have hMY_ne : joint.snd.toRealFn b ≠ 0 := ne_of_gt (h_margY_pos b)
      have hMXY_ne : joint.fst.toRealFn a * joint.snd.toRealFn b ≠ 0 :=
        mul_ne_zero hMX_ne hMY_ne
      rw [Real.log_div hJ hMXY_ne, Real.log_mul hMX_ne hMY_ne]
      ring
  simp_rw [h_per, Finset.sum_sub_distrib]
  -- Step 4: each split sum is -H(·) by negMulLog identity + marginal.
  have h_term1 :
      (∑ a, ∑ b, joint.toRealFn (a, b) * Real.log (joint.toRealFn (a, b)))
        = -joint.entropy := by
    rw [← Fintype.sum_prod_type
          (fun p : α × β => joint.toRealFn p * Real.log (joint.toRealFn p))]
    unfold entropy toRealFn
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Real.negMulLog]; ring
  have h_term2 :
      (∑ a, ∑ b, joint.toRealFn (a, b) * Real.log (joint.fst.toRealFn a))
        = -joint.fst.entropy := by
    have h_inner : ∀ a, (∑ b, joint.toRealFn (a, b) *
            Real.log (joint.fst.toRealFn a))
        = joint.fst.toRealFn a * Real.log (joint.fst.toRealFn a) := by
      intro a
      rw [← Finset.sum_mul, ← fst_toRealFn_eq_sum joint a]
    simp_rw [h_inner]
    unfold entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    show joint.fst.toRealFn a * Real.log (joint.fst.toRealFn a) =
         -Real.negMulLog _
    simp only [Real.negMulLog, toRealFn]; ring
  have h_term3 :
      (∑ a, ∑ b, joint.toRealFn (a, b) * Real.log (joint.snd.toRealFn b))
        = -joint.snd.entropy := by
    rw [Finset.sum_comm]
    have h_inner : ∀ b, (∑ a, joint.toRealFn (a, b) *
            Real.log (joint.snd.toRealFn b))
        = joint.snd.toRealFn b * Real.log (joint.snd.toRealFn b) := by
      intro b
      rw [← Finset.sum_mul, ← snd_toRealFn_eq_sum joint b]
    simp_rw [h_inner]
    unfold entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    show joint.snd.toRealFn b * Real.log (joint.snd.toRealFn b) =
         -Real.negMulLog _
    simp only [Real.negMulLog, toRealFn]; ring
  rw [h_term1, h_term2, h_term3]
  ring

-- ============================================================================
-- §7.7: Conditional entropy
-- ============================================================================

/-- Conditional entropy `H(β | α) = H(α, β) - H(α)`. -/
noncomputable def conditionalEntropy (joint : PMF (α × β)) : ℝ :=
  joint.entropy - joint.fst.entropy

/-- **Conditioning reduces entropy** (Cover-Thomas 2.6.4): `H(β | α) ≤ H(β)`.
    Direct corollary of `mutualInformation_nonneg` (free from
    `ENNReal.toReal_nonneg`) plus the H-difference bridge
    `mutualInformation_eq_entropy_sum`. -/
theorem conditionalEntropy_le_entropy
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DecidableEq α] [DecidableEq β]
    (joint : PMF (α × β))
    (h_margX_pos : ∀ a, 0 < joint.fst.toRealFn a)
    (h_margY_pos : ∀ b, 0 < joint.snd.toRealFn b) :
    joint.conditionalEntropy ≤ joint.snd.entropy := by
  have hmi_nonneg : 0 ≤ joint.mutualInformation := joint.mutualInformation_nonneg
  rw [mutualInformation_eq_entropy_sum joint h_margX_pos h_margY_pos] at hmi_nonneg
  unfold conditionalEntropy
  linarith

/-- **Bretagnolle–Huber inequality** on PMFs: `2 · H²(P, Q) ≤ KL(P ‖ Q)`.

    Stated against the mathlib-grounded `PMF.klDiv` (returns `ℝ≥0∞`); the
    `2 * hellingerDistSq` factor is wrapped via `ENNReal.ofReal` for type
    compatibility.

    Proof: combines `klDiv_eq_sum_klFun` (discrete reduction) with the
    sqrt-klFun pointwise inequality and the Hellinger bridge
    `(√p − √q)² = q · (√(p/q) − 1)²`. Self-contained — no `Core` deps. -/
theorem two_hellingerDistSq_le_klDiv [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (P Q : PMF α)
    (hQ_pos : ∀ a, 0 < Q.toRealFn a) :
    ENNReal.ofReal (2 * hellingerDistSq P Q) ≤ P.klDiv Q := by
  -- ENNReal-side facts about Q from the strict-positivity hypothesis.
  have hQ_ne_top : ∀ a, Q a ≠ ∞ := PMF.apply_ne_top Q
  have hQ_ne_zero : ∀ a, Q a ≠ 0 := fun a hQa => by
    have h := hQ_pos a
    rw [show Q.toRealFn a = (Q a).toReal from rfl, hQa, ENNReal.toReal_zero] at h
    exact lt_irrefl 0 h
  -- Strict-positive Q ⇒ AC.
  have hAC : MeasureTheory.Measure.AbsolutelyContinuous P.toMeasure Q.toMeasure := by
    refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs hQs => ?_
    rw [PMF.toMeasure_apply_fintype _ s] at hQs
    rw [PMF.toMeasure_apply_fintype _ s]
    have h_each_zero : ∀ y ∈ (Finset.univ : Finset α), s.indicator (⇑Q) y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => zero_le)).mp hQs
    have h_x_notin : ∀ x, x ∉ s := fun x hx_in => by
      have h := h_each_zero x (Finset.mem_univ x)
      rw [Set.indicator_of_mem hx_in] at h
      exact hQ_ne_zero x h
    refine Finset.sum_eq_zero (fun x _ => Set.indicator_of_notMem (h_x_notin x) _)
  rw [klDiv_eq_sum_klFun P Q hAC]
  -- Per-atom bridge: ENNReal mul → ofReal of ℝ mul.
  have hP_nn : ∀ a, 0 ≤ P.toRealFn a := P.toRealFn_nonneg
  have hQ_real_nn : ∀ a, 0 ≤ Q.toRealFn a := Q.toRealFn_nonneg
  have h_klFun_nn : ∀ a, 0 ≤ _root_.InformationTheory.klFun
      (P.toRealFn a / Q.toRealFn a) := fun a =>
    _root_.InformationTheory.klFun_nonneg
      (div_nonneg (hP_nn a) (hQ_real_nn a))
  have h_summand : ∀ a, Q a * ENNReal.ofReal
      (_root_.InformationTheory.klFun ((P a / Q a).toReal))
      = ENNReal.ofReal (Q.toRealFn a *
          _root_.InformationTheory.klFun (P.toRealFn a / Q.toRealFn a)) := by
    intro a
    rw [show ((P a) / (Q a)).toReal = P.toRealFn a / Q.toRealFn a from
          ENNReal.toReal_div _ _,
        show Q a = ENNReal.ofReal (Q.toRealFn a) from
          (ENNReal.ofReal_toReal (hQ_ne_top a)).symm,
        ← ENNReal.ofReal_mul (hQ_real_nn a)]
  simp_rw [h_summand]
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun a _ =>
        mul_nonneg (hQ_real_nn a) (h_klFun_nn a))]
  -- Inlined Hellinger BH proof on ℝ-side: `2 * H²(P, Q) ≤ ∑ Q · klFun(P/Q)`.
  apply ENNReal.ofReal_le_ofReal
  -- Bridge `2 · H² = ∑ (√P − √Q)²` (uses ∑P = ∑Q = 1).
  have hsq_diff : ∀ a, (Real.sqrt (P.toRealFn a) - Real.sqrt (Q.toRealFn a)) ^ 2 =
      P.toRealFn a + Q.toRealFn a - 2 * Real.sqrt (P.toRealFn a * Q.toRealFn a) := by
    intro a
    have hsP : Real.sqrt (P.toRealFn a) ^ 2 = P.toRealFn a := Real.sq_sqrt (hP_nn a)
    have hsQ : Real.sqrt (Q.toRealFn a) ^ 2 = Q.toRealFn a := Real.sq_sqrt (hQ_real_nn a)
    have hsPQ : Real.sqrt (P.toRealFn a) * Real.sqrt (Q.toRealFn a) =
        Real.sqrt (P.toRealFn a * Q.toRealFn a) :=
      (Real.sqrt_mul (hP_nn a) (Q.toRealFn a)).symm
    nlinarith [hsP, hsQ, hsPQ]
  have hbridge : 2 * hellingerDistSq P Q =
      ∑ a, (Real.sqrt (P.toRealFn a) - Real.sqrt (Q.toRealFn a)) ^ 2 := by
    unfold hellingerDistSq bhattacharyyaCoeff
    have hexpand : ∑ a, (Real.sqrt (P.toRealFn a) - Real.sqrt (Q.toRealFn a)) ^ 2 =
        (∑ a, P.toRealFn a) + (∑ a, Q.toRealFn a)
          - 2 * (∑ a, Real.sqrt (P.toRealFn a * Q.toRealFn a)) := by
      simp_rw [hsq_diff]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hexpand, P.sum_toRealFn_eq_one, Q.sum_toRealFn_eq_one]
    ring
  rw [hbridge]
  -- Pointwise: `(√P − √Q)² ≤ Q · klFun(P/Q)` via the two helper lemmas.
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_sqrt_div_sub_one_sq (P.toRealFn a) (Q.toRealFn a) (hP_nn a) (hQ_pos a)]
  exact mul_le_mul_of_nonneg_left
    (sqrt_sub_one_sq_le_klFun (div_nonneg (hP_nn a) (hQ_real_nn a)))
    (hQ_real_nn a)

end PMF
