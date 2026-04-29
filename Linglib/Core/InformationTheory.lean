import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Information-Theoretic Primitives
@cite{ackerman-malouf-2013} @cite{cheng-holyoak-1995} @cite{cover-thomas-2006}
@cite{dunn-2025} @cite{ellis-2006}

Domain-agnostic information-theoretic functions, used by both pragmatic models
(RSA) and morphological complexity metrics.

The entropy / mutual-information / conditional-entropy / Jensen-Shannon
families are real-valued and route through mathlib's `Real.negMulLog`
(`x ↦ -x · log x`), the canonical Shannon-entropy summand. Entropy is
expressed in **nats** (natural log) — the mathlib convention. To convert
to bits, multiply by `1 / Real.log 2` (or use `Real.logb 2` directly).

## Mathlib-canonical form

Following mathlib's `Finset.sum` discipline, all entropy-family functions
take a `Finset α` (the support) plus a probability function `α → ℝ`. This
matches mathlib's pattern (cf. `Finset.sum`, `MeasureTheory.integral`):
ONE canonical type-indexed form, not parallel implementations.

For the function-indexed version over a `Fintype` use
`entropy Finset.univ p`. For ad-hoc list-of-pairs distributions
common in study files, `Finset.image Prod.fst dist.toFinset` extracts the
support and `fun a => (dist.find? (·.1 = a)).map Prod.snd |>.getD 0`
extracts the function (or just refactor the upstream definition to
return `(Finset α, α → ℝ)` directly).

## Main definitions

- `entropy s p`: Shannon entropy `H(p) = ∑ a ∈ s, negMulLog (p a)`
- `conditionalEntropy s sj joint marginalX`: H(Y|X) = H(X,Y) - H(X)
- `mutualInformation`: I(X;Y) = H(X) + H(Y) - H(X,Y)
- `jsdOf s p q`: Jensen-Shannon divergence
- `deltaP`: ΔP directional association measure (ℚ-valued, no log)
- `deltaPCounts`: ΔP from a 2×2 contingency table (ℚ-valued, no log)
- `klFinite p q`: discrete KL divergence `Σᵢ pᵢ · log(pᵢ/qᵢ)` (with `0·log(0/q)=0` guard)
- `bhattacharyyaCoeff`, `hellingerDistSq`, `hellingerDist`: Hellinger family
-/

namespace Core.InformationTheory

open Real

/-! ## Shannon entropy — Finset-and-function form

Mathlib-canonical shape: `(Finset α, α → ℝ) → ℝ` via `∑ a ∈ s, negMulLog (p a)`.
The mathlib convention `0 · log 0 = 0` is built into `Real.negMulLog`. -/

/-- Shannon entropy of a probability function over a finite support (in nats):

    `H(p) = -Σ_{a ∈ s} p(a) log p(a) = Σ_{a ∈ s} negMulLog(p(a))`.

    Mathlib-canonical form: take the support as a `Finset` and the probability
    as a function. For `[Fintype α]`, use `Finset.univ` for the support. -/
noncomputable def entropy {α : Type*} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ a ∈ s, Real.negMulLog (p a)

/-- Entropy is non-negative for probability distributions on the support. -/
theorem entropy_nonneg {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp_nonneg : ∀ a ∈ s, 0 ≤ p a) (hp_sum : ∑ a ∈ s, p a = 1) :
    0 ≤ entropy s p :=
  Finset.sum_nonneg fun a ha =>
    Real.negMulLog_nonneg (hp_nonneg a ha)
      (le_trans (Finset.single_le_sum (f := p)
        (fun b hb => hp_nonneg b hb) ha) hp_sum.le)

/-- Entropy of the uniform distribution `p ≡ 1/|s|` over a non-empty `s`. -/
theorem entropy_uniform {α : Type*} (s : Finset α) (h : s.Nonempty) :
    entropy s (fun _ => 1 / s.card) = log s.card := by
  simp only [entropy, Real.negMulLog]
  have hcard_pos : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr h)
  have hne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  rw [Finset.sum_const, nsmul_eq_mul,
      log_div one_ne_zero hne, log_one, zero_sub]
  field_simp

/-! ## Mutual information, conditional entropy, JSD

All take the supports as `Finset` and the joint/marginal distributions as
functions, mirroring `entropy`'s shape. -/

/-- Mutual information `I(X;Y) = H(X) + H(Y) - H(X,Y)` (in nats).

    Take the support of joint as `sJoint : Finset (α × β)`, supports of
    marginals as `sX : Finset α` and `sY : Finset β`, and the corresponding
    probability functions. Alternative form: `I(X;Y) = H(X) - H(X|Y)`. -/
noncomputable def mutualInformation {α β : Type*}
    (sJoint : Finset (α × β)) (joint : α × β → ℝ)
    (sX : Finset α) (marginalX : α → ℝ)
    (sY : Finset β) (marginalY : β → ℝ) : ℝ :=
  entropy sX marginalX + entropy sY marginalY -
    entropy sJoint joint

/-- Conditional entropy `H(Y|X) = H(X,Y) - H(X)` (in nats).

    Used by MemorySurprisal for `S_M = H(W_t | M_t)` and by LCEC for
    `H(Cᵢ|Cⱼ)`. -/
noncomputable def conditionalEntropy {α β : Type*}
    (sJoint : Finset (α × β)) (joint : α × β → ℝ)
    (sX : Finset α) (marginalX : α → ℝ) : ℝ :=
  entropy sJoint joint - entropy sX marginalX

/-- Jensen-Shannon divergence over a finite support:

    `JSD(p, q) = H(m) - (H(p) + H(q)) / 2` where `m(a) = (p(a) + q(a)) / 2`.

    Symmetric, bounded, and a metric (after sqrt). In nats. Used for
    grammar distance, register comparison, and anywhere KL divergence's
    asymmetry is undesirable. -/
noncomputable def jsdOf {α : Type*} (s : Finset α) (p q : α → ℝ) : ℝ :=
  entropy s (fun a => (p a + q a) / 2) -
    (entropy s p + entropy s q) / 2

/-! ## ΔP (directional association, no log) -/

/-- ΔP: directional association measure (@cite{ellis-2006}, Table 1;
via @cite{cheng-holyoak-1995} Probabilistic Contrast Model).

ΔP(x → y) = P(y | x) - P(y | ¬x)

Measures how much knowing x changes the probability of y.
@cite{ellis-2006} uses ΔP to explain L2 morpheme acquisition: grammatical
functors with low ΔP (many cue-outcome competitors) are acquired late.
@cite{dunn-2025} uses ΔP to identify constructions from corpus data.

Properties:
- Bounded: ΔP ∈ [-1, 1] for valid probability inputs
- ΔP = 0 when x and y are independent (see `deltaP_eq_zero_of_independent`)
- Directional: ΔP(x→y) ≠ ΔP(y→x) in general

Takes joint probability P(x,y), marginal P(x), and marginal P(y).
Returns the directional association from x to y. -/
def deltaP (pXY pX pY : ℚ) : ℚ :=
  let pYgivenX := if pX ≤ 0 then 0 else pXY / pX
  let pYgivenNotX := if pX ≥ 1 then 0 else (pY - pXY) / (1 - pX)
  pYgivenX - pYgivenNotX

/-- ΔP from a 2×2 contingency table (@cite{ellis-2006}, Table 1).

Given observed counts:

|     |  y  | ¬y  |
|-----|-----|-----|
|  x  |  a  |  b  |
| ¬x  |  c  |  d  |

ΔP(x → y) = a/(a+b) - c/(c+d)

This is the standard form for contingency learning: `a` is the frequency of
cue-outcome co-occurrence, `b` is cue without outcome, `c` is outcome
without cue, `d` is neither. Also used in corpus-based CxG (@cite{dunn-2025})
for slot-filler association strength. -/
def deltaPCounts (a b c d : ℕ) : ℚ :=
  let ab : ℚ := ↑a + ↑b
  let cd : ℚ := ↑c + ↑d
  (if ab = 0 then 0 else ↑a / ab) - (if cd = 0 then 0 else ↑c / cd)

/-- ΔP vanishes under independence: if P(x,y) = P(x)·P(y), then ΔP = 0.

This is the key property: ΔP measures departure from independence.
When slot and filler are statistically independent (knowing the slot
tells you nothing about the filler), ΔP is zero. -/
theorem deltaP_eq_zero_of_independent (pX pY : ℚ)
    (hpX_pos : 0 < pX) (hpX_lt : pX < 1) :
    deltaP (pX * pY) pX pY = 0 := by
  have hne : pX ≠ 0 := (ne_of_lt hpX_pos).symm
  have hne1 : (1 : ℚ) - pX ≠ 0 := sub_ne_zero.mpr (ne_of_lt hpX_lt).symm
  dsimp only [deltaP]
  rw [if_neg (not_le.mpr hpX_pos), if_neg (not_le.mpr hpX_lt)]
  rw [mul_div_cancel_left₀ pY hne]
  rw [show pY - pX * pY = pY * (1 - pX) from by
    rw [mul_sub, mul_one, mul_comm pY pX]]
  rw [mul_div_cancel_right₀ pY hne1, sub_self]

/-! ## Kullback–Leibler divergence (finite, ℝ-valued)

Discrete-finite specialization of mathlib's `InformationTheory.klDiv`,
routed through mathlib's `klFun (x) = x · log x + 1 − x`. -/

section KLDivergence

variable {ι : Type*} [Fintype ι]

/-- Finite KL divergence: `KL(p ‖ q) = Σᵢ pᵢ · log(pᵢ / qᵢ)`.
    Convention: `0 · log(0/q) = 0` (via the `if`-guard). -/
noncomputable def klFinite (p q : ι → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)

/-- When `q > 0`, each KL term can be written via `klFun`:
    `p · log(p/q) = q · klFun(p/q) + (p − q)`. -/
private theorem kl_term_eq_klFun {p_i q_i : ℝ} (hq : 0 < q_i) (_hp : 0 ≤ p_i) :
    (if p_i = 0 then (0 : ℝ) else p_i * log (p_i / q_i)) =
    q_i * _root_.InformationTheory.klFun (p_i / q_i) + (p_i - q_i) := by
  by_cases hp0 : p_i = 0
  · simp only [hp0, ↓reduceIte, zero_div, _root_.InformationTheory.klFun_zero, mul_one, zero_sub,
               add_neg_cancel]
  · simp only [hp0, ↓reduceIte]
    unfold _root_.InformationTheory.klFun
    have hq_ne : q_i ≠ 0 := ne_of_gt hq
    field_simp
    ring

/-- Finite KL divergence equals `Σᵢ qᵢ · klFun(pᵢ/qᵢ)` when `Σpᵢ = Σqᵢ`. -/
theorem kl_eq_sum_klFun (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    klFinite p q = ∑ i, q i * _root_.InformationTheory.klFun (p i / q i) := by
  unfold klFinite
  have hterm : ∀ i, (if p i = 0 then (0 : ℝ) else p i * log (p i / q i)) =
      q i * _root_.InformationTheory.klFun (p i / q i) + (p i - q i) :=
    λ i => kl_term_eq_klFun (hq i) (hp i)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hcancel : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  linarith

/-- **Gibbs' inequality (finite form)**: `KL(p ‖ q) ≥ 0`.

    For distributions `p, q` with `qᵢ > 0`, `pᵢ ≥ 0`, and `Σpᵢ = Σqᵢ`:
    `Σᵢ pᵢ · log(pᵢ/qᵢ) ≥ 0`. Proof via mathlib's `klFun_nonneg`. -/
theorem kl_nonneg (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    0 ≤ klFinite p q := by
  rw [kl_eq_sum_klFun p q hq hp hsum]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (le_of_lt (hq i))
  exact _root_.InformationTheory.klFun_nonneg (div_nonneg (hp i) (le_of_lt (hq i)))

/-- Alternative KL non-negativity with distribution hypotheses. -/
theorem kl_nonneg' [Nonempty ι] {p q : ι → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ klFinite p q :=
  kl_nonneg p q hq_pos hp_nonneg (by rw [hp_sum, hq_sum])

/-- Cross-entropy decomposition:
    `KL(p ‖ q) = (Σ pᵢ log pᵢ) − (Σ pᵢ log qᵢ)`

    The hypothesis is **absolute continuity** `p ≪ q`: wherever `p` puts
    mass, `q` does too. Strictly weaker than `∀ i, 0 < q i`. -/
theorem klFinite_eq_negEntropy_sub_crossEntropy (p q : ι → ℝ)
    (hAC : ∀ i, p i ≠ 0 → q i ≠ 0) :
    klFinite p q = (∑ i, p i * log (p i)) - (∑ i, p i * log (q i)) := by
  unfold klFinite
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hP : p i = 0
  · simp [hP]
  · rw [if_neg hP, log_div hP (hAC i hP), mul_sub]

/-- KL with a Dirac point mass reduces to negative log-probability (= surprisal):
    `KL(δₛ ‖ Q) = −log Q(s)`.

    Foundation of standard RSA speaker utility `U(u; s) = log L₀(s | u)`
    (@cite{frank-goodman-2012}, @cite{goodman-stuhlmuller-2013}). -/
theorem klFinite_pi_single_eq_neg_log [DecidableEq ι]
    (s : ι) (q : ι → ℝ) (hQ : q s ≠ 0) :
    klFinite (Pi.single s 1) q = -log (q s) := by
  unfold klFinite
  rw [Finset.sum_eq_single s]
  · have h1 : Pi.single (M := fun _ => ℝ) s 1 s = 1 := Pi.single_eq_same s 1
    rw [if_neg (by rw [h1]; exact one_ne_zero), h1, one_mul, one_div, log_inv]
  · intro j _ hj
    have h0 : Pi.single (M := fun _ => ℝ) s 1 j = 0 := Pi.single_eq_of_ne hj 1
    rw [h0, if_pos rfl]
  · intro h; exact (h (Finset.mem_univ s)).elim

/-- Expected log-likelihood under uncertain beliefs equals negative KL plus
    speaker entropy: `E_p[log q] = −KL(p ‖ q) + Σ p log p`.

    Since `Σ p log p` is independent of `q`, softmax over utterances cancels
    it, yielding the equivalence between Frank-Goodman surprisal `log L₀(s|u)`
    and Goodman-Stuhlmüller belief-weighted utility. -/
theorem expected_log_eq_neg_klFinite_plus_negEntropy (p q : ι → ℝ)
    (hAC : ∀ i, p i ≠ 0 → q i ≠ 0) :
    (∑ i, p i * log (q i)) = -klFinite p q + (∑ i, p i * log (p i)) := by
  rw [klFinite_eq_negEntropy_sub_crossEntropy p q hAC]; ring

end KLDivergence

/-! ## Hellinger family (Bhattacharyya, squared-Hellinger, Hellinger distance)
@cite{herbstritt-franke-2019}

Finite-distribution Hellinger family used as an alternative speaker utility
in RSA pragmatics: @cite{herbstritt-franke-2019} argue (footnote 8) that
Hellinger distance is necessary for probability expressions because KL
assigns infinite disutility to messages whose literal interpretation
assigns zero probability to states the speaker considers possible.
The §-Hellinger-vs-KL inequality `2 · H²(P, Q) ≤ KL(P ‖ Q)`
(Bretagnolle–Huber, sorried) makes the Hellinger speaker's permissiveness
over the KL speaker a proved corollary rather than a docstring claim. -/

section Hellinger

variable {ι : Type*} [Fintype ι]

/-- Bhattacharyya coefficient: `BC(P, Q) = Σᵢ √(Pᵢ · Qᵢ)`.

    For probability distributions `BC = 1 ↔ P = Q` and `BC = 0 ↔` disjoint
    support. -/
noncomputable def bhattacharyyaCoeff (P Q : ι → ℝ) : ℝ :=
  ∑ i : ι, √(P i * Q i)

/-- Squared Hellinger distance: `H²(P, Q) = 1 − BC(P, Q)`.

    Ranges from 0 (identical distributions) to 1 (disjoint support).
    Equivalent to the standard form `(1/2) Σᵢ (√Pᵢ − √Qᵢ)²` for
    distributions summing to 1. -/
noncomputable def hellingerDistSq (P Q : ι → ℝ) : ℝ :=
  1 - bhattacharyyaCoeff P Q

/-- Hellinger distance: `HD(P, Q) = √H²(P, Q)`.

    Satisfies `0 ≤ HD ≤ 1` for probability distributions. Unlike KL,
    Hellinger distance is always finite and is a proper metric (symmetric,
    triangle inequality).

    The @cite{herbstritt-franke-2019} speaker utility (their eq. 16) is
    `EU(m, o, a) = −HD(P_belief, P_LL)`. -/
noncomputable def hellingerDist (P Q : ι → ℝ) : ℝ :=
  √(hellingerDistSq P Q)

/-- Squared Hellinger distance is non-negative when `BC ≤ 1`.

    For normalised distributions `Σ Pᵢ = Σ Qᵢ = 1`, Cauchy-Schwarz gives
    `BC(P, Q) ≤ 1`, hence `H² ≥ 0`. -/
theorem hellingerDistSq_nonneg_of_bc_le_one (P Q : ι → ℝ)
    (h : bhattacharyyaCoeff P Q ≤ 1) :
    0 ≤ hellingerDistSq P Q := by
  unfold hellingerDistSq; linarith

/-- **Bretagnolle–Huber inequality**: `2 · H²(P, Q) ≤ KL(P ‖ Q)`.

    The standard sharp comparison between Hellinger and KL on probability
    distributions. Combined with `H² ≥ 0`, yields `H²(P, Q) ≤ KL(P ‖ Q)`,
    making the Hellinger speaker's choice set a **superset** of the KL
    speaker's: any utterance the KL speaker can consider, the Hellinger
    speaker can too — but not conversely.

    **Proof sketch (TODO):** Pointwise `klFun(x) ≥ 2(√x − 1)²` (factor-of-2
    convexity bound). Multiply by `qᵢ` and sum: `Σ qᵢ klFun(pᵢ/qᵢ) ≥
    2 Σ (√pᵢ − √qᵢ)²`. The LHS equals `KL(p ‖ q)` via `kl_eq_sum_klFun`;
    the RHS equals `2 · 2 · H²(p, q) = 4 H²` for normalised `p, q`, but only
    `2 H²` is needed. Standard reference: Bretagnolle–Huber (1979). -/
theorem two_hellingerDistSq_le_klFinite [Nonempty ι] (P Q : ι → ℝ)
    (_hP_nonneg : ∀ i, 0 ≤ P i) (_hQ_pos : ∀ i, 0 < Q i)
    (_hP_sum : ∑ i, P i = 1) (_hQ_sum : ∑ i, Q i = 1) :
    2 * hellingerDistSq P Q ≤ klFinite P Q := by
  sorry

end Hellinger

end Core.InformationTheory
