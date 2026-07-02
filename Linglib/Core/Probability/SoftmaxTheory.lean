import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.MeanInequalities
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Linglib.Core.Probability.LogitChoice

/-!
# Softmax: variational, information-theoretic, and limiting characterizations

The deep theory of `softmax` (defined in `Core.Probability.LogitChoice`): why it
takes the exponential form, what it optimizes, how it concentrates, and its link
to exponential tilting.

## Main results

* `cauchy_mul_exp`, `luce_fechnerian_exp` — the Fechnerian bridge: the exponential
  form is forced by a Cauchy functional equation (ratio scale → interval scale).
* `gibbs_variational` — softmax uniquely maximizes `H(p) + α·⟨p, s⟩` on the simplex.
* `softmax_maximizes_entropyReg`, `softmax_unique_maximizer`,
  `softmax_minimizes_freeEnergy`, `max_entropy_duality`, `entropy_le_log_card` —
  the maximum-entropy / minimum-free-energy characterization.
* `softmax_argmax_limit`, `softmax_nonmax_limit` — concentration on the argmax as
  rationality → ∞.
* `bayesian_maximizes` — the Bayesian posterior maximizes expected log-likelihood.
* `partitionFn_eq_mgf`, `logSumExp_eq_cgf`, `tilted_count_eq_withDensity_softmax` —
  softmax as the counting-measure case of mathlib's exponential tilting.

`[UPSTREAM]`: pure-math characterizations of softmax; no linguistics. Quality-and-role
marker — sits above `LogitChoice`, below the rational-agent framing.
-/

namespace Core

open Real Finset

/-! ### Why softmax? The Fechnerian characterization

The exponential parameterization `score = exp(α · utility)` is not a design
choice — it is the **unique** transformation connecting Luce's ratio scale to
a utility (interval) scale ([adams-messick-1958]).

**Ratio vs interval scales.** Luce's Axiom 1 (IIA) yields a **ratio scale**
`v`: only ratios `v(a)/v(b)` are meaningful. Fechner's
psychophysics requires an **interval scale** `u`: only differences
`u(a) - u(b)` are meaningful. The question: how are `v` and `u` related?

**Derivation.** From `P(a,b) = v(a)/(v(a)+v(b))`, the odds ratio is
`v(a)/v(b) = g(u(a) - u(b))` for some function `g`. Transitivity of ratios
(`v(a)/v(c) = [v(a)/v(b)] · [v(b)/v(c)]`) forces Cauchy's multiplicative
functional equation: `g(s + t) = g(s) · g(t)`. The unique monotone increasing
solution is `g(s) = exp(k · s)` (`cauchy_mul_exp`), giving:

- `v(a) = C · exp(k · u(a))` — the ratio scale IS the exponential of utility
- `P(a,b) = 1/(1 + exp(-k · (u(a) - u(b))))` — the logistic function
- For n alternatives: `P(a|S) = exp(k · u(a)) / Σ exp(k · u(b))` — softmax

The parameter `k > 0` is the rationality parameter `α` in RSA.

-/

private theorem cauchy_g0_eq_one (g : ℝ → ℝ)
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) : g 0 = 1 := by
  have h0 : g 0 = g 0 * g 0 := by
    have := hg_mul 0 0; simp at this; exact this
  have : g 0 * (g 0 - 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · exfalso
    have h1 : g (-1) < g 0 := hg_mono (by linarith : (-1 : ℝ) < 0)
    have h2 : g 0 < g 1 := hg_mono (by linarith : (0 : ℝ) < 1)
    have h3 : g (-1) * g 1 = g 0 := by
      have := hg_mul (-1) 1; simp at this; exact this.symm
    rw [h] at h1 h2 h3
    linarith [mul_neg_of_neg_of_pos h1 h2]
  · linarith

private theorem cauchy_g_pos (g : ℝ → ℝ)
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) (x : ℝ) : 0 < g x := by
  have hg0 := cauchy_g0_eq_one g hg_mul hg_mono
  have hsq : g x = g (x / 2) * g (x / 2) := by
    have := hg_mul (x / 2) (x / 2); rw [add_halves] at this; exact this
  by_contra h; push Not at h
  have hgx_zero : g x = 0 := le_antisymm h (by rw [hsq]; exact mul_self_nonneg _)
  have hx2_zero : g (x / 2) = 0 := by rwa [hsq, mul_self_eq_zero] at hgx_zero
  have hg0' : g 0 = g x * g (-x) := by
    have := hg_mul x (-x); simp at this; exact this
  rw [hgx_zero, zero_mul] at hg0'; linarith

private theorem cauchy_additive_zero (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) : h 0 = 0 := by
  have := hadd 0 0; simp at this; linarith

private theorem cauchy_additive_neg (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (x : ℝ) : h (-x) = -h x := by
  have : h (x + (-x)) = h x + h (-x) := hadd x (-x)
  simp [cauchy_additive_zero h hadd] at this; linarith

private theorem cauchy_additive_nat (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (n : ℕ) : h n = n * h 1 := by
  induction n with
  | zero => simp [cauchy_additive_zero h hadd]
  | succ k ih => rw [Nat.cast_succ, hadd, ih]; ring

private theorem cauchy_additive_int (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (n : ℤ) : h n = n * h 1 := by
  cases n with
  | ofNat k => simp [cauchy_additive_nat h hadd k]
  | negSucc k =>
    simp only [Int.cast_negSucc]
    rw [cauchy_additive_neg h hadd, cauchy_additive_nat h hadd (k + 1)]
    push_cast; ring

private theorem cauchy_additive_rat (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (q : ℚ) : h q = q * h 1 := by
  have hden_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hden_ne : (q.den : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hmul_nat : ∀ (n : ℕ) (x : ℝ), h (n * x) = n * h x := by
    intro n x; induction n with
    | zero => simp [cauchy_additive_zero h hadd]
    | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih]; ring
  have step1 : (q.den : ℝ) * h q = h (q.num : ℤ) := by
    rw [← hmul_nat q.den q]; congr 1; rw [Rat.cast_def]; field_simp
  rw [cauchy_additive_int h hadd] at step1
  have : h q = (q.num : ℝ) * h 1 / q.den := by field_simp at step1 ⊢; linarith
  rw [this, Rat.cast_def]; field_simp

private theorem cauchy_monotone_additive_linear (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (hmono : StrictMono h) :
    ∀ x, h x = x * h 1 := by
  have h0 : h 0 = 0 := cauchy_additive_zero h hadd
  have h1_pos : 0 < h 1 := by linarith [hmono (show (0 : ℝ) < 1 by norm_num), h0]
  intro x
  by_contra hne
  rcases ne_iff_lt_or_gt.mp hne with hlt | hgt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show h x / h 1 < x by
      rw [div_lt_iff₀ h1_pos]; linarith)
    have : h x < h q := by
      rw [cauchy_additive_rat h hadd q]
      have := (div_lt_iff₀ h1_pos).mp hq1; linarith
    linarith [hmono hq2]
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < h x / h 1 by
      rw [lt_div_iff₀ h1_pos]; linarith)
    have : h q < h x := by
      rw [cauchy_additive_rat h hadd q]
      have := (lt_div_iff₀ h1_pos).mp hq2; linarith
    linarith [hmono hq1]

/-- **Cauchy's multiplicative functional equation** (classical): if `g : ℝ → ℝ`
    satisfies `g(s + t) = g(s) · g(t)` and is strictly monotone increasing, then
    `g(s) = exp(k · s)` for some `k > 0`. -/
theorem cauchy_mul_exp (g : ℝ → ℝ)
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) :
    ∃ k : ℝ, 0 < k ∧ g 0 = 1 ∧ ∀ s, g s = Real.exp (k * s) := by
  have hg0 := cauchy_g0_eq_one g hg_mul hg_mono
  have hg_pos := cauchy_g_pos g hg_mul hg_mono
  set h := fun x => log (g x) with hh_def
  have hadd : ∀ s t, h (s + t) = h s + h t := fun s t => by
    simp only [h]; rw [hg_mul s t, log_mul (ne_of_gt (hg_pos s)) (ne_of_gt (hg_pos t))]
  have hmono : StrictMono h := fun a b hab => by
    simp only [h]; exact log_lt_log (hg_pos a) (hg_mono hab)
  have hlinear := cauchy_monotone_additive_linear h hadd hmono
  have hk_pos : 0 < h 1 := by
    have := hmono (show (0 : ℝ) < 1 by norm_num)
    simp only [h] at this; rw [hg0, log_one] at this; exact this
  refine ⟨h 1, hk_pos, hg0, fun s => ?_⟩
  have := hlinear s
  simp only [h] at this
  rw [← exp_log (hg_pos s), this, mul_comm]

/-- **Fechnerian uniqueness** ([adams-messick-1958]): if a ratio scale `v`
    and interval scale `u` represent the same ordering via
    `v(x)/v(y) = g(u(x) - u(y))` for a strictly monotone multiplicative `g`, then
    `v` is the exponential of `u`. -/
theorem luce_fechnerian_exp {X : Type*} (v u : X → ℝ) (g : ℝ → ℝ)
    (hv_pos : ∀ x, 0 < v x)
    (h_ratio : ∀ x y, v x / v y = g (u x - u y))
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) :
    ∃ k : ℝ, 0 < k ∧ ∀ x₀ x, v x = v x₀ * Real.exp (k * (u x - u x₀)) := by
  obtain ⟨k, hk, _, hg_exp⟩ := cauchy_mul_exp g hg_mul hg_mono
  exact ⟨k, hk, fun x₀ x => by
    have h := h_ratio x x₀
    rw [hg_exp (u x - u x₀)] at h
    rwa [div_eq_iff (ne_of_gt (hv_pos x₀)), mul_comm] at h⟩

/-! ### Gibbs variational principle

The softmax distribution uniquely maximizes entropy plus expected score on the
probability simplex — the mathematical foundation for RSA convergence
([zaslavsky-hu-levy-2020]).

The KL machinery used here — `klFinite`, `kl_eq_sum_klFun`, `kl_nonneg` — is
inlined as private `ι → ℝ` helpers, since mathlib provides only the `PMF` form
(`PMF.klDiv` / `PMF.toReal_klDiv_eq_sum_log_div`).
-/

/-- Private `ι → ℝ` discrete KL divergence for the Gibbs proofs in this section. -/
private noncomputable def klFinite {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)

/-- Per-element identity: `q · klFun(p/q) = if p=0 then 0 else p log(p/q) + (q − p)`. -/
private theorem kl_term_eq_klFun {p_i q_i : ℝ} (hq : 0 < q_i) (_hp : 0 ≤ p_i) :
    (if p_i = 0 then (0 : ℝ) else p_i * Real.log (p_i / q_i)) =
    q_i * _root_.InformationTheory.klFun (p_i / q_i) + (p_i - q_i) := by
  by_cases hp0 : p_i = 0
  · simp only [hp0, ↓reduceIte, zero_div, _root_.InformationTheory.klFun_zero, mul_one,
               zero_sub, add_neg_cancel]
  · simp only [hp0, ↓reduceIte]
    unfold _root_.InformationTheory.klFun
    have hq_ne : q_i ≠ 0 := ne_of_gt hq
    field_simp
    ring

/-- `klFinite = ∑ q · klFun(p/q)` when sums match. -/
private theorem kl_eq_sum_klFun {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    klFinite p q = ∑ i, q i * _root_.InformationTheory.klFun (p i / q i) := by
  unfold klFinite
  have hterm : ∀ i, (if p i = 0 then (0 : ℝ) else p i * Real.log (p i / q i)) =
      q i * _root_.InformationTheory.klFun (p i / q i) + (p i - q i) :=
    λ i => kl_term_eq_klFun (hq i) (hp i)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hcancel : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  linarith

/-- KL non-negativity (Gibbs' inequality). -/
private theorem kl_nonneg {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    0 ≤ klFinite p q := by
  rw [kl_eq_sum_klFun p q hq hp hsum]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (le_of_lt (hq i))
    (_root_.InformationTheory.klFun_nonneg (div_nonneg (hp i) (le_of_lt (hq i))))

/-- KL non-negativity, distribution form. -/
private theorem kl_nonneg' {ι : Type*} [Fintype ι] [Nonempty ι] {p q : ι → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ klFinite p q :=
  kl_nonneg p q hq_pos hp_nonneg (by rw [hp_sum, hq_sum])

/-- Private `ι → ℝ` Shannon entropy for the Gibbs proofs in this section. -/
private noncomputable def entropy {α : Type*} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ a ∈ s, Real.negMulLog (p a)

section GibbsVariational

variable {ι : Type*} [Fintype ι]

/-- The per-meaning speaker objective: f(s) = Σᵤ [negMulLog(sᵤ) + α · sᵤ · vᵤ].

This is the function that the speaker maximizes for each meaning m,
where vᵤ = log L(m|u) is the listener utility of utterance u. -/
noncomputable def speakerObj (v : ι → ℝ) (α : ℝ) (s : ι → ℝ) : ℝ :=
  ∑ u, (Real.negMulLog (s u) + α * s u * v u)

/-- The softmax achieves f(s*) = log Z, where Z is the partition function. -/
theorem speakerObj_at_softmax [Nonempty ι] (v : ι → ℝ) (α : ℝ) :
    speakerObj v α (softmax (α • v)) = logSumExp (α • v) := by
  unfold speakerObj logSumExp
  have hlog_softmax : ∀ u, log (softmax (α • v) u) =
      α * v u - log (partitionFn (α • v)) := by
    intro u
    simp only [softmax, partitionFn, Pi.smul_apply, smul_eq_mul]
    rw [log_div (ne_of_gt (exp_pos _)) (ne_of_gt (Finset.sum_pos
      (fun j _ => exp_pos _) Finset.univ_nonempty)), log_exp]
  have hterm : ∀ u, Real.negMulLog (softmax (α • v) u) + α * softmax (α • v) u * v u =
      softmax (α • v) u * log (partitionFn (α • v)) := by
    intro u; unfold Real.negMulLog; rw [hlog_softmax]; ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, softmax_sum_eq_one, one_mul]
  simp only [partitionFn, Pi.smul_apply, smul_eq_mul]

/-- Key identity: speakerObj(s) + KL(s ‖ s*) = logSumExp (= speakerObj(s*)). -/
private theorem speakerObj_plus_kl [Nonempty ι] (v : ι → ℝ) (α : ℝ)
    (s : ι → ℝ) (_hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    speakerObj v α s + klFinite s (softmax (α • v)) = logSumExp (α • v) := by
  unfold speakerObj klFinite logSumExp
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ u, (Real.negMulLog (s u) + α * s u * v u) +
      (if s u = 0 then (0 : ℝ) else s u * log (s u / softmax (α • v) u)) =
      s u * log (∑ j : ι, exp (α * v j)) := by
    intro u
    by_cases hs0 : s u = 0
    · simp [hs0, Real.negMulLog]
    · simp only [hs0, ↓reduceIte]
      have hs_pos : 0 < softmax (α • v) u := softmax_pos (α • v) u
      rw [log_div hs0 (ne_of_gt hs_pos)]
      have hlog_sm : log (softmax (α • v) u) = α * v u - log (∑ j : ι, exp (α * v j)) := by
        simp only [softmax, Pi.smul_apply, smul_eq_mul]
        rw [log_div (ne_of_gt (exp_pos _)) (ne_of_gt (Finset.sum_pos
          (fun j _ => exp_pos _) Finset.univ_nonempty)), log_exp]
      rw [hlog_sm]; unfold Real.negMulLog; ring
  simp_rw [hterm, ← Finset.sum_mul, hs_sum, one_mul]

/-- **Gibbs Variational Principle**: softmax maximizes entropy + expected score.

For any distribution p on ι and scores s : ι → ℝ:
  H(p) + α·⟨p, s⟩ ≤ H(q) + α·⟨q, s⟩
where q = softmax(s, α) and H(p) = Σ negMulLog(pᵢ). -/
theorem gibbs_variational [Nonempty ι] (s : ι → ℝ) (α : ℝ) (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) + α * ∑ i, p i * s i ≤
    (∑ i, Real.negMulLog (softmax (α • s) i)) + α * ∑ i, softmax (α • s) i * s i := by
  set q := softmax (α • s)
  have hq_pos : ∀ i, 0 < q i := fun i => softmax_pos (α • s) i
  have hq_sum : ∑ i, q i = 1 := softmax_sum_eq_one (α • s)
  have hkl := kl_nonneg' hp_nonneg hq_pos hp_sum hq_sum
  have h_logq : ∀ i, Real.log (q i) = α * s i - logSumExp (α • s) := fun i => log_softmax (α • s) i
  have h_combine : ∀ i,
      Real.negMulLog (p i) +
        (if p i = 0 then (0 : ℝ) else p i * Real.log (p i / q i)) =
      -(p i * Real.log (q i)) := by
    intro i
    by_cases hpi : p i = 0
    · simp [hpi, Real.negMulLog]
    · simp only [hpi, ↓reduceIte, Real.negMulLog]
      have hpi_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
      rw [Real.log_div (ne_of_gt hpi_pos) (ne_of_gt (hq_pos i))]
      ring
  have h1 : (∑ i, Real.negMulLog (p i)) + klFinite p q =
      -(∑ i, p i * Real.log (q i)) := by
    unfold klFinite
    rw [← Finset.sum_add_distrib]
    simp_rw [h_combine, Finset.sum_neg_distrib]
  have h2 : -(∑ i, p i * Real.log (q i)) = -(α * ∑ i, p i * s i) + logSumExp (α • s) := by
    have : ∑ i, p i * Real.log (q i) = α * ∑ i, p i * s i - logSumExp (α • s) := by
      simp_rw [h_logq]
      rw [show ∑ i : ι, p i * (α * s i - logSumExp (α • s)) =
          ∑ i, (α * (p i * s i) - logSumExp (α • s) * p i) from
        Finset.sum_congr rfl fun i _ => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp_sum, mul_one]
    linarith
  have h3 : (∑ i, Real.negMulLog (q i)) + α * ∑ i, q i * s i = logSumExp (α • s) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show ∑ i : ι, (Real.negMulLog (q i) + α * (q i * s i)) = ∑ i, logSumExp (α • s) * q i from
      Finset.sum_congr rfl fun i _ => by simp only [Real.negMulLog, h_logq i]; ring]
    rw [← Finset.mul_sum, hq_sum, mul_one]
  linarith

end GibbsVariational

/-! ### Softmax concentration at high rationality

As the rationality parameter α → ∞, softmax concentrates all probability mass
on the action with highest utility — i.e., softmax converges to argmax. This
connects:

- **MaxEnt phonology ↔ OT**: a MaxEnt grammar with weights `w` becomes
  categorical (OT-like) as temperature → 0 (equivalently α → ∞).
- **RSA ↔ neo-Gricean pragmatics**: a soft-rational RSA speaker becomes a
  hard-rational Gricean reasoner in the α → ∞ limit.
-/

section SoftmaxLimit

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Nonempty ι] [DecidableEq ι] in
/-- Each softmax component is bounded by `exp(α(sⱼ - s_{i_max}))`, obtained
    by dropping all but the `i_max` term from the partition function. -/
private theorem softmax_le_exp_diff (s : ι → ℝ) (α : ℝ) (j i_max : ι) :
    softmax (α • s) j ≤ exp (α * (s j - s i_max)) := by
  simp only [softmax, Pi.smul_apply, smul_eq_mul]
  rw [show α * (s j - s i_max) = α * s j - α * s i_max from by ring, exp_sub]
  exact div_le_div_of_nonneg_left (exp_pos _).le (exp_pos _)
    (single_le_sum (f := fun k => exp (α * s k)) (fun k _ => (exp_pos _).le) (mem_univ i_max))

omit [Nonempty ι] [DecidableEq ι] in
/-- When `x < 0`, `exp(α · x) < ε` for all sufficiently large `α`. -/
private theorem exp_mul_neg_lt (x : ℝ) (hx : x < 0) (ε : ℝ) (hε : 0 < ε)
    (α : ℝ) (hα : α > log ε / x) : exp (α * x) < ε := by
  calc exp (α * x) < exp (log ε) := by
        apply exp_lt_exp.mpr
        have := mul_lt_mul_of_neg_right hα hx
        rwa [div_mul_cancel₀ (log ε) (ne_of_lt hx)] at this
    _ = ε := exp_log hε

open Filter Topology in
/-- **Softmax → argmax limit**: as α → ∞, softmax concentrates on the unique
    maximizer. For any `i_max` with `s i_max` strictly greater than all other
    scores, `softmax(s, α)_{i_max} → 1`.

    This is the formal connection between MaxEnt (soft optimization) and OT
    (hard optimization): OT is the α → ∞ limit of MaxEnt. -/
theorem softmax_argmax_limit (s : ι → ℝ) (i_max : ι)
    (h_max : ∀ j, j ≠ i_max → s j < s i_max) :
    Tendsto (fun α : ℝ => softmax (α • s) i_max) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set n := Fintype.card ι
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  set εn := ε / n
  have hεn : 0 < εn := div_pos hε hn_pos
  let threshFn : ι → ℝ := fun j =>
    if j = i_max then (0 : ℝ) else log εn / (s j - s i_max)
  refine ⟨univ.sup' ⟨i_max, mem_univ _⟩ threshFn + 1, fun α hα => ?_⟩
  have hbound : ∀ j ≠ i_max, softmax (α • s) j < εn := by
    intro j hj
    apply lt_of_le_of_lt (softmax_le_exp_diff s α j i_max)
    apply exp_mul_neg_lt _ (sub_neg.mpr (h_max j hj)) εn hεn
    have h1 : threshFn j ≤ univ.sup' ⟨i_max, mem_univ _⟩ threshFn :=
      le_sup' _ (mem_univ j)
    simp only [threshFn, hj, ↓reduceIte] at h1
    linarith
  have htail : 1 - softmax (α • s) i_max = ∑ j ∈ univ.erase i_max, softmax (α • s) j := by
    rw [← softmax_sum_eq_one (α • s), ← add_sum_erase _ _ (mem_univ i_max)]; ring
  have htail_nonneg : 0 ≤ 1 - softmax (α • s) i_max := by
    rw [htail]; exact sum_nonneg fun j _ => le_of_lt (softmax_pos (α • s) j)
  have htail_strict : 1 - softmax (α • s) i_max < ε := by
    rw [htail]
    rcases (univ.erase i_max : Finset ι).eq_empty_or_nonempty with hempty | ⟨j, hj⟩
    · simp [hempty]; exact hε
    · calc ∑ k ∈ univ.erase i_max, softmax (α • s) k
          < ∑ _ ∈ univ.erase i_max, εn :=
            sum_lt_sum (fun k hk => le_of_lt (hbound k (mem_erase.mp hk).1))
              ⟨j, hj, hbound j (mem_erase.mp hj).1⟩
        _ ≤ ∑ (_ : ι), εn :=
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => hεn.le)
        _ = ↑n * εn := by rw [sum_const, card_univ, nsmul_eq_mul]
        _ = ε := mul_div_cancel₀ _ (ne_of_gt hn_pos)
  rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith

omit [Nonempty ι] [DecidableEq ι] in
open Filter Topology in
/-- Complement of the limit: non-maximal actions get probability → 0. -/
theorem softmax_nonmax_limit (s : ι → ℝ) (i_max : ι)
    (h_max : ∀ j, j ≠ i_max → s j < s i_max) (j : ι) (hj : j ≠ i_max) :
    Tendsto (fun α : ℝ => softmax (α • s) j) atTop (𝓝 0) := by
  have : Nonempty ι := ⟨j⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨log ε / (s j - s i_max) + 1, fun α hα => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (softmax_pos _ _)]
  exact lt_of_le_of_lt (softmax_le_exp_diff s α j i_max)
    (exp_mul_neg_lt _ (sub_neg.mpr (h_max j hj)) ε hε α (by linarith))

end SoftmaxLimit

section Entropy

/-! ### Shannon entropy and maximum entropy

This section uses the private `ι → ℝ` Shannon entropy (`entropy`, above), since
softmax is a real-arithmetic construction; consumers wanting the `PMF`-typed form
can convert via `Core.Probability.Entropy`. -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]


/-- Maximum entropy is achieved by the uniform distribution. -/
theorem entropy_le_log_card (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    entropy Finset.univ p ≤ log (Fintype.card ι) := by
  set n := (Fintype.card ι : ℝ) with hn_def
  have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  set q : ι → ℝ := λ _ => 1 / n with hq_def
  have hq_pos : ∀ i, 0 < q i := fun _ => by simp [hq_def]; positivity
  have hq_sum : ∑ i, q i = 1 := by
    simp only [hq_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn_def]
    field_simp
  have hkl := kl_nonneg' hp_nonneg hq_pos hp_sum hq_sum
  -- KL(p ‖ q) = log n - H(p): rearrange to H(p) ≤ log n
  suffices h : klFinite p q = -entropy Finset.univ p + log n by linarith
  simp only [klFinite, entropy, Real.negMulLog]
  -- Each term: if p=0 then 0 else p*log(p/q) = -(-(p)*log(p)) + p*log n
  have hterm : ∀ i, (if p i = 0 then (0 : ℝ) else p i * log (p i / q i)) =
      -(-(p i) * log (p i)) + p i * log n := by
    intro i
    by_cases hp0 : p i = 0
    · simp [hp0]
    · simp only [hp0, ↓reduceIte]
      have hq_ne : q i ≠ 0 := ne_of_gt (hq_pos i)
      rw [log_div hp0 hq_ne]
      have hlogq : log (q i) = -log n := by
        simp only [hq_def, log_div one_ne_zero hn_ne, log_one, zero_sub]
      rw [hlogq]; ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp_sum, one_mul,
      Finset.sum_neg_distrib]


/-- Entropy of softmax: H(softmax(s, α)) = log Z - α · 𝔼[s]. -/
theorem entropy_softmax (s : ι → ℝ) (α : ℝ) :
    entropy Finset.univ (softmax (α • s)) =
    log (partitionFn (α • s)) - α * ∑ i : ι, softmax (α • s) i * s i := by
  simp only [entropy, softmax, partitionFn, Real.negMulLog, Pi.smul_apply, smul_eq_mul]
  have hne : (∑ j : ι, exp (α * s j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty)
  have hlog : ∀ i, log (exp (α * s i) / ∑ j : ι, exp (α * s j)) =
                   α * s i - log (∑ j : ι, exp (α * s j)) := by
    intro i; rw [log_div (ne_of_gt (exp_pos _)) hne, log_exp]
  simp_rw [hlog]
  have hsum1 : ∑ i : ι, exp (α * s i) / ∑ j : ι, exp (α * s j) = 1 := by
    rw [← Finset.sum_div, div_self hne]
  -- Move negation outside: ∑ -(x · y) = -∑ x · y
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]
  calc -∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) *
        (α * s i - log (∑ j : ι, exp (α * s j)))
      = -∑ i : ι, ((exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) -
                   (exp (α * s i) / ∑ j : ι, exp (α * s j)) * log (∑ j : ι, exp (α * s j))) := by
        congr 1; apply Finset.sum_congr rfl; intros; ring
    _ = -(∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) -
          ∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * log (∑ j : ι, exp (α * s j))) := by
        rw [Finset.sum_sub_distrib]
    _ = -(∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) -
          (∑ i : ι, exp (α * s i) / ∑ j : ι, exp (α * s j)) * log (∑ j : ι, exp (α * s j))) := by
        rw [← Finset.sum_mul]
    _ = -(∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) - 1 * log (∑ j : ι, exp (α * s j))) := by
        rw [hsum1]
    _ = log (∑ j : ι, exp (α * s j)) - ∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) := by ring
    _ = log (∑ j : ι, exp (α * s j)) - ∑ i : ι, α * ((exp (α * s i) / ∑ j : ι, exp (α * s j)) * s i) := by
        congr 1; apply Finset.sum_congr rfl; intros; ring
    _ = log (∑ j : ι, exp (α * s j)) - α * ∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * s i := by
        rw [← Finset.mul_sum]

/-- Entropy-regularized objective: G_α(p, s) = ⟨s, p⟩ + (1/α) H(p). -/
noncomputable def entropyRegObjective (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i : ι, p i * s i + (1 / α) * entropy Finset.univ p

/-- The maximum value of the entropy-regularized objective. -/
theorem entropyRegObjective_softmax (s : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    entropyRegObjective s α (softmax (α • s)) = (1 / α) * log (partitionFn (α • s)) := by
  simp only [entropyRegObjective, entropy_softmax]
  have hne : α ≠ 0 := ne_of_gt hα
  field_simp
  ring

/-- Softmax maximizes the entropy-regularized objective. -/
theorem softmax_maximizes_entropyReg (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    entropyRegObjective s α p ≤ entropyRegObjective s α (softmax (α • s)) := by
  -- entropyRegObjective unfolds to ∑ pᵢsᵢ + (1/α) · entropy Finset.univ p
  -- and entropy Finset.univ p = ∑ negMulLog (p i), exactly what gibbs_variational uses
  simp only [entropyRegObjective, entropy]
  have hgibbs := gibbs_variational s α p hp_nonneg hp_sum
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have h := div_le_div_of_nonneg_right hgibbs (le_of_lt hα)
  simp only [add_div, mul_div_cancel_left₀ _ hα_ne] at h
  simp only [div_eq_inv_mul] at h
  rw [show (α⁻¹ : ℝ) = 1 / α from by ring] at h
  linarith

omit [Nonempty ι] in
/-- KL divergence zero implies distributions are equal (when q > 0 and sums match). -/
private theorem kl_eq_zero_imp_eq (p q : ι → ℝ) (hq_pos : ∀ i, 0 < q i)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = ∑ i, q i)
    (hkl : klFinite p q = 0) :
    p = q := by
  rw [kl_eq_sum_klFun p q hq_pos hp_nonneg hsum] at hkl
  funext i
  have hpi_div_qi_nonneg : 0 ≤ p i / q i := div_nonneg (hp_nonneg i) (le_of_lt (hq_pos i))
  have hqi_pos : 0 < q i := hq_pos i
  have hqi_nonneg : 0 ≤ q i := le_of_lt hqi_pos
  -- Each term q_i * klFun(p_i/q_i) ≥ 0 and their sum = 0
  have hterm_nonneg : ∀ j, 0 ≤ q j * InformationTheory.klFun (p j / q j) := by
    intro j; exact mul_nonneg (le_of_lt (hq_pos j))
      (InformationTheory.klFun_nonneg (div_nonneg (hp_nonneg j) (le_of_lt (hq_pos j))))
  have hterm_zero : q i * InformationTheory.klFun (p i / q i) = 0 := by
    have hsz := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm_nonneg j) |>.mp hkl
    exact hsz i (Finset.mem_univ i)
  -- q_i > 0 so klFun(p_i/q_i) = 0, hence p_i/q_i = 1
  rcases mul_eq_zero.mp hterm_zero with hq0 | hkl0
  · exact absurd hq0 (ne_of_gt hqi_pos)
  · rw [InformationTheory.klFun_eq_zero_iff hpi_div_qi_nonneg] at hkl0
    exact div_eq_one_iff_eq (ne_of_gt hqi_pos) |>.mp hkl0

/-- Softmax is the unique maximizer of the entropy-regularized objective. -/
theorem softmax_unique_maximizer (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1)
    (h_max : entropyRegObjective s α p = entropyRegObjective s α (softmax (α • s))) :
    p = softmax (α • s) := by
  set q := softmax (α • s) with hq_def
  have hq_pos : ∀ i, 0 < q i := fun i => softmax_pos (α • s) i
  have hq_sum : ∑ i, q i = 1 := softmax_sum_eq_one (α • s)
  -- From speakerObj_plus_kl: speakerObj(p) + KL(p ‖ q) = logSumExp = speakerObj(q) + 0
  have h_p := speakerObj_plus_kl s α p hp_nonneg hp_sum
  have h_q := speakerObj_plus_kl s α q (fun i => le_of_lt (hq_pos i)) hq_sum
  -- KL(q ‖ q) = 0
  have hkl_self : klFinite q q = 0 := by
    simp only [klFinite]
    apply Finset.sum_eq_zero
    intro i _
    have hne : q i ≠ 0 := ne_of_gt (hq_pos i)
    simp [hne]
  rw [hkl_self, add_zero] at h_q
  -- So KL(p ‖ q) = logSumExp - speakerObj(p) = speakerObj(q) - speakerObj(p)
  have hkl_val : klFinite p q = speakerObj s α q - speakerObj s α p := by linarith
  -- entropyRegObjective equality means speakerObj equality (up to rescaling)
  -- entropyRegObjective = Σ p*s + (1/α) * H(p)
  -- speakerObj = Σ negMulLog(p) + α * Σ p*s  (i.e. H(p) + α⟨p,s⟩ but per-element)
  -- We showed: entropyRegObj(p) = (1/α) * speakerObj(p)
  have hobj_eq : speakerObj s α p = speakerObj s α q := by
    -- entropyRegObjective = Σ p*s + (1/α)*H(p) = (1/α)(H(p) + α Σ p*s) = (1/α)*speakerObj
    have hα_ne' : α ≠ 0 := ne_of_gt hα
    have hconv : ∀ r : ι → ℝ, (∀ i, 0 ≤ r i) →
        entropyRegObjective s α r = (1 / α) * speakerObj s α r := by
      intro r hr_nn
      simp only [entropyRegObjective, speakerObj]
      simp only [entropy]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
      ring
    have h1 := hconv p hp_nonneg
    have h2 := hconv q (fun i => le_of_lt (hq_pos i))
    have hα_ne : (1 : ℝ) / α ≠ 0 := by positivity
    rw [h1, h2] at h_max
    exact mul_left_cancel₀ hα_ne h_max
  -- Therefore KL(p ‖ q) = 0
  have hkl_zero : klFinite p q = 0 := by linarith
  exact kl_eq_zero_imp_eq p q hq_pos hp_nonneg (by rw [hp_sum, hq_sum]) hkl_zero

/-- Free energy (from statistical mechanics). -/
noncomputable def freeEnergy (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  -∑ i : ι, p i * s i - (1 / α) * entropy Finset.univ p

/-- Softmax is the Boltzmann distribution: minimizes free energy. -/
theorem softmax_minimizes_freeEnergy (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    freeEnergy s α (softmax (α • s)) ≤ freeEnergy s α p := by
  simp only [freeEnergy]
  have h := softmax_maximizes_entropyReg s α hα p hp_nonneg hp_sum
  simp only [entropyRegObjective] at h
  linarith

/-- The log-partition function is convex in α. -/
theorem logSumExp_convex (s : ι → ℝ) :
    ConvexOn ℝ Set.univ (fun α : ℝ => logSumExp (α • s)) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    unfold logSumExp
    simp only [Pi.smul_apply, smul_eq_mul]
    -- Edge cases: a = 0 or b = 0
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp [show b = 1 from by linarith]
    rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp [show a = 1 from by linarith]
    -- Main case: 0 < a, 0 < b, a + b = 1
    -- Key step: exp((ax+by)·sᵢ) = exp(x·sᵢ)^a · exp(y·sᵢ)^b
    have hexp_split : ∀ i, exp ((a * x + b * y) * s i) =
        (exp (x * s i)) ^ a * (exp (y * s i)) ^ b := by
      intro i
      rw [← exp_mul, ← exp_mul]
      rw [show (a * x + b * y) * s i = x * s i * a + y * s i * b from by ring]
      rw [exp_add]
    -- Apply Hölder with p = 1/a, q = 1/b
    have hpq : a⁻¹.HolderConjugate b⁻¹ := HolderConjugate.inv_inv ha_pos hb_pos hab
    have holder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ (α := ι)) hpq
      (f := fun i => (exp (x * s i)) ^ a)
      (g := fun i => (exp (y * s i)) ^ b)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) a)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) b)
    -- Simplify Hölder LHS: ∑ exp(x·sᵢ)^a · exp(y·sᵢ)^b = ∑ exp((ax+by)·sᵢ)
    conv at holder => lhs; arg 2; ext i; rw [← hexp_split]
    -- Simplify Hölder RHS powers: (exp(x·sᵢ)^a)^(1/a) = exp(x·sᵢ), etc.
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have hsimp_f : ∀ i, ((exp (x * s i)) ^ a) ^ a⁻¹ = exp (x * s i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ ha_ne, rpow_one]
    have hsimp_g : ∀ i, ((exp (y * s i)) ^ b) ^ b⁻¹ = exp (y * s i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ hb_ne, rpow_one]
    simp_rw [hsimp_f, hsimp_g] at holder
    -- The RHS of holder uses (1 / a⁻¹) and (1 / b⁻¹); simplify to a and b
    simp only [one_div, inv_inv] at holder
    -- Take log of both sides (both are positive)
    have hZ_x : (0 : ℝ) < ∑ i : ι, exp (x * s i) :=
      Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
    have hZ_y : (0 : ℝ) < ∑ i : ι, exp (y * s i) :=
      Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
    have hZ_mid : 0 < ∑ j : ι, exp ((a * x + b * y) * s j) :=
      Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty
    have hlog_le := log_le_log hZ_mid holder
    rw [log_mul (ne_of_gt (rpow_pos_of_pos hZ_x a)) (ne_of_gt (rpow_pos_of_pos hZ_y b)),
        log_rpow hZ_x, log_rpow hZ_y] at hlog_le
    linarith

/-- Derivative of log-partition gives expected value:
    `d/dα log(Σ exp(α sᵢ)) = Σ softmax(s,α)ᵢ · sᵢ`. -/
theorem deriv_logSumExp (s : ι → ℝ) (α : ℝ) :
    deriv (fun α => logSumExp (α • s)) α = ∑ i : ι, softmax (α • s) i * s i := by
  simp only [logSumExp, softmax, Pi.smul_apply, smul_eq_mul]
  have hZ_ne : (∑ j : ι, exp (α * s j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty)
  -- Derivative of each exp(α * s j) w.r.t. α
  have hexp : ∀ j : ι, HasDerivAt (fun a => exp (a * s j))
      (exp (α * s j) * s j) α := by
    intro j
    have h1 : HasDerivAt (fun a => a * s j) (1 * s j) α :=
      (hasDerivAt_id α).mul_const (s j)
    have h2 := (Real.hasDerivAt_exp (α * s j)).comp α h1
    simp only [one_mul] at h2
    exact h2
  -- Derivative of the sum
  have hsum : HasDerivAt (fun a => ∑ j : ι, exp (a * s j))
      (∑ j : ι, exp (α * s j) * s j) α :=
    HasDerivAt.fun_sum fun j _ => hexp j
  -- Derivative of log(sum) via chain rule, then extract
  rw [(hsum.log hZ_ne).deriv, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ### Per-element offsets

These instantiate the plain `logSumExp`/`softmax` at the shifted argument
`α • s + r`, i.e. `logSumExp (α • s + r) = log Σ exp(α·sᵢ + rᵢ)`. This form
appears when differentiating the log-partition with respect to a single weight
`wⱼ` in a multi-constraint grammar, where `sᵢ` is constraint `j`'s contribution
to candidate `i` and `rᵢ` the contribution of all other constraints (constant in
`wⱼ`). -/

/-- Derivative of offset log-partition gives weighted expected value:
    `d/dα log(Σ exp(α·sᵢ + rᵢ)) = Σ softmax(α•s + r)ᵢ · sᵢ`. -/
theorem hasDerivAt_logSumExpOffset (s r : ι → ℝ) (α : ℝ) :
    HasDerivAt (fun w => logSumExp (w • s + r))
      (∑ i : ι, softmax (α • s + r) i * s i) α := by
  simp only [logSumExp, softmax, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hZ_ne : (∑ j : ι, exp (α * s j + r j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty)
  have hexp : ∀ j : ι, HasDerivAt (fun a => exp (a * s j + r j))
      (exp (α * s j + r j) * s j) α := by
    intro j
    have h1 : HasDerivAt (fun a => a * s j + r j) (s j) α := by
      have := ((hasDerivAt_id α).mul_const (s j)).add_const (r j)
      simpa using this
    exact (Real.hasDerivAt_exp (α * s j + r j)).comp α h1
  have hsum : HasDerivAt (fun a => ∑ j : ι, exp (a * s j + r j))
      (∑ j : ι, exp (α * s j + r j) * s j) α :=
    HasDerivAt.fun_sum fun j _ => hexp j
  convert hsum.log hZ_ne using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The offset log-partition function is convex in α. -/
theorem logSumExpOffset_convex (s r : ι → ℝ) :
    ConvexOn ℝ Set.univ (fun α : ℝ => logSumExp (α • s + r)) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    unfold logSumExp
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp [show b = 1 from by linarith]
    rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp [show a = 1 from by linarith]
    have hexp_split : ∀ i, exp ((a * x + b * y) * s i + r i) =
        (exp (x * s i + r i)) ^ a * (exp (y * s i + r i)) ^ b := by
      intro i
      rw [← exp_mul, ← exp_mul, ← exp_add]
      congr 1
      linear_combination -(r i) * hab
    have hpq : a⁻¹.HolderConjugate b⁻¹ := HolderConjugate.inv_inv ha_pos hb_pos hab
    have holder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ (α := ι)) hpq
      (f := fun i => (exp (x * s i + r i)) ^ a)
      (g := fun i => (exp (y * s i + r i)) ^ b)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) a)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) b)
    conv at holder => lhs; arg 2; ext i; rw [← hexp_split]
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have hsimp_f : ∀ i, ((exp (x * s i + r i)) ^ a) ^ a⁻¹ = exp (x * s i + r i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ ha_ne, rpow_one]
    have hsimp_g : ∀ i, ((exp (y * s i + r i)) ^ b) ^ b⁻¹ = exp (y * s i + r i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ hb_ne, rpow_one]
    simp_rw [hsimp_f, hsimp_g] at holder
    simp only [one_div, inv_inv] at holder
    have hZ_x : (0 : ℝ) < ∑ i : ι, exp (x * s i + r i) :=
      Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty
    have hZ_y : (0 : ℝ) < ∑ i : ι, exp (y * s i + r i) :=
      Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty
    have hZ_mid : 0 < ∑ j : ι, exp ((a * x + b * y) * s j + r j) :=
      Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty
    have hlog_le := log_le_log hZ_mid holder
    rw [log_mul (ne_of_gt (rpow_pos_of_pos hZ_x a)) (ne_of_gt (rpow_pos_of_pos hZ_y b)),
        log_rpow hZ_x, log_rpow hZ_y] at hlog_le
    linarith

/-- The log conditional likelihood `α ↦ (α · sᵧ + rᵧ) − logSumExp(α•s + r)`
    is concave (affine minus convex). -/
theorem logConditional_concaveOn (s r : ι → ℝ) (y : ι) :
    ConcaveOn ℝ Set.univ
      (fun α => (α * s y + r y) - logSumExp (α • s + r)) := by
  apply ConcaveOn.sub
  · constructor
    · exact convex_univ
    · intro x _ z _ a b ha hb hab
      simp only [smul_eq_mul]
      nlinarith [show a * r y + b * r y = r y from by linear_combination (r y) * hab]
  · exact logSumExpOffset_convex s r

/-- The derivative of log conditional likelihood `α ↦ (α·sᵧ + rᵧ) − logSumExp(α•s + r)`
    is the observed feature value minus the expected value:
    `d/dα = sᵧ − Σᵢ softmax(α•s + r)ᵢ · sᵢ`. -/
theorem hasDerivAt_logConditional (s r : ι → ℝ) (y : ι) (α : ℝ) :
    HasDerivAt (fun w => (w * s y + r y) - logSumExp (w • s + r))
      (s y - ∑ i : ι, softmax (α • s + r) i * s i) α := by
  have h_affine : HasDerivAt (fun a => a * s y + r y) (s y) α := by
    have := ((hasDerivAt_id α).mul_const (s y)).add_const (r y)
    simpa using this
  exact h_affine.sub (hasDerivAt_logSumExpOffset s r α)

/-- Strong duality: max entropy = min free energy. -/
theorem max_entropy_duality (s : ι → ℝ) (c : ℝ)
    (α : ℝ) (_hα : 0 < α) (h_constraint : ∑ i : ι, softmax (α • s) i * s i = c) :
    entropy Finset.univ (softmax (α • s)) =
    log (partitionFn (α • s)) - α * c := by
  rw [entropy_softmax, h_constraint]

end Entropy

/-! ### Bayesian optimality -/

section BayesianOptimality

variable {ι : Type*} [Fintype ι]

/-- **Bayesian optimality**: the normalized posterior maximizes weighted
log-likelihood on the probability simplex. For weights `wᵢ ≥ 0` with
`C = Σ wᵢ > 0` and any distribution `L` on the simplex, the normalized posterior
`p*ᵢ = wᵢ / C` satisfies `Σᵢ wᵢ · log Lᵢ ≤ Σᵢ wᵢ · log p*ᵢ`. -/
theorem bayesian_maximizes (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hC_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, w i * log (L i) ≤ ∑ i, w i * log (w i / ∑ j, w j) := by
  set C := ∑ i, w i with hC_def
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hp_nonneg : ∀ i, 0 ≤ w i / C := λ i => div_nonneg (hw_nonneg i) (le_of_lt hC_pos)
  have hp_sum : ∑ i, w i / C = 1 := by rw [← Finset.sum_div, div_self hC_ne]
  have hkl : 0 ≤ klFinite (λ i => w i / C) L :=
    kl_nonneg _ L hL_pos hp_nonneg (by rw [hp_sum, hL_sum])
  suffices h : (∑ i, w i * log (w i / C)) - (∑ i, w i * log (L i)) =
      C * klFinite (fun i => w i / C) L by
    linarith [mul_nonneg (le_of_lt hC_pos) hkl]
  unfold klFinite
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hwi : w i = 0
  · simp [hwi]
  · have hwC_ne : w i / C ≠ 0 := div_ne_zero hwi hC_ne
    simp only [hwC_ne, ↓reduceIte]
    have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
    rw [show C * (w i / C * log (w i / C / L i)) = w i * log (w i / C / L i) from by
      rw [← mul_assoc]; congr 1; field_simp]
    rw [log_div (ne_of_gt (div_pos hwi_pos hC_pos)) (ne_of_gt (hL_pos i))]
    ring

end BayesianOptimality
/-! ### Connection to exponential tilting and the cumulant generating function

Softmax is the finite/counting-measure case of mathlib's exponential-family
machinery: the partition function is the moment generating function, log-sum-exp
is the cumulant generating function, and softmax is the density of the
exponentially-tilted (Esscher / Boltzmann–Gibbs) counting measure. -/

section Tilting

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The partition function `∑ exp(α·sᵢ)` is the moment generating function of the
scores under the counting measure. -/
theorem partitionFn_eq_mgf (s : ι → ℝ) (α : ℝ) :
    partitionFn (α • s) = mgf s Measure.count α := by
  simp only [partitionFn, mgf, integral_count, Pi.smul_apply, smul_eq_mul]

/-- Log-sum-exp is the cumulant generating function of the scores under the
counting measure. -/
theorem logSumExp_eq_cgf (s : ι → ℝ) (α : ℝ) :
    logSumExp (α • s) = cgf s Measure.count α := by
  simp only [logSumExp, cgf, mgf, integral_count, Pi.smul_apply, smul_eq_mul]

/-- Softmax is the density of the exponentially-tilted counting measure: tilting
the counting measure by the scores `α·s` yields the measure whose density is
`softmax (α•s)`. -/
theorem tilted_count_eq_withDensity_softmax (s : ι → ℝ) (α : ℝ) :
    Measure.count.tilted (fun i => α * s i) =
      Measure.count.withDensity (fun i => ENNReal.ofReal (softmax (α • s) i)) := by
  simp only [Measure.tilted]
  congr 1
  funext i
  simp only [softmax, integral_count, Pi.smul_apply, smul_eq_mul]

end Tilting

end Core
