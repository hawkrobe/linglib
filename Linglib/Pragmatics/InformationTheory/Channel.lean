import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Communication Channels
[cover-thomas-2006] [shannon-1948] [zaslavsky-etal-2019]

A `CommChannel C W` is a finite-alphabet stochastic conditional
distribution `p(w | c)` — the basic Shannon channel restricted to finite
input/output types. Used as substrate by:

- `ChannelCapacity.lean` — capacity, CAP, mutual-information bounds
- `Pragmatics.AsymmetricCommunication` — speaker-listener
  asymmetric setups (variation, iterated learning)
- `ZaslavskyEtAl2019` — color naming
- `Diachronic.Lexicalization` — listener model conditioned on `L`
- RSA literal speaker S₀ (the channel) and L₀ (the posterior)

The derived quantities (`marginalWord`, `posterior`, `commPrecision`,
`mutualInfo`) live here because they are channel-and-prior functions of
purely Shannon character. Capacity-specific theorems live in the sibling
`ChannelCapacity.lean`.

## Main definitions

- `CommChannel`: row-stochastic matrix `p(w | c)`
- `marginalWord`: `p(w) = Σ_c p(c) · p(w|c)`
- `posterior`: `p(c|w)` via Bayes' rule
- `commPrecision`: expected surprisal `S(c) = -Σ_w p(w|c) · log p(c|w)`
- `mutualInfo`: `I(W;C) = Σ_{c,w} p(c) · p(w|c) · log(p(c|w)/p(c))`
-/

set_option autoImplicit false

namespace Pragmatics.InformationTheory

open Finset BigOperators Real

variable {C W : Type} [Fintype C] [Fintype W]

/-- A finite-alphabet communication channel: a row-stochastic conditional
    `encode c w = p(w | c)`. The Shannon-channel primitive shared by
    information-theoretic and pragmatic communication models.

    Originally `NamingChannel` in [zaslavsky-etal-2019]; lifted here
    because the same primitive serves color-naming, lexicalization,
    asymmetric-lexicon models, and RSA literal-speaker semantics. -/
structure CommChannel (C W : Type) [Fintype C] [Fintype W] where
  /-- p(w|c): probability of word `w` given meaning `c`. -/
  encode : C → W → ℝ
  encode_nonneg : ∀ c w, 0 ≤ encode c w
  encode_sum_one : ∀ c, ∑ w : W, encode c w = 1

/-- Marginal word probability `p(w) = Σ_c p(c) · p(w|c)`. -/
noncomputable def marginalWord (nc : CommChannel C W) (prior : C → ℝ)
    (w : W) : ℝ :=
  ∑ c : C, prior c * nc.encode c w

/-- Posterior `p(c|w)` via Bayes' rule. The listener's belief about the
    meaning after hearing word `w` (≡ RSA literal listener L₀). -/
noncomputable def posterior (nc : CommChannel C W) (prior : C → ℝ)
    (w : W) (c : C) : ℝ :=
  nc.encode c w * prior c / marginalWord nc prior w

/-- Communicative precision (expected surprisal) of meaning `c`:
    `S(c) = -Σ_w p(w|c) · log p(c|w)`. Lower means the channel
    communicates `c` more precisely. Defined in [zaslavsky-etal-2019]. -/
noncomputable def commPrecision (nc : CommChannel C W) (prior : C → ℝ)
    (c : C) : ℝ :=
  -∑ w : W, nc.encode c w * log (posterior nc prior w c)

/-- Mutual information `I(W;C) = Σ_{c,w} p(c) · p(w|c) · log(p(c|w)/p(c))`. -/
noncomputable def mutualInfo (nc : CommChannel C W) (prior : C → ℝ) : ℝ :=
  ∑ c : C, ∑ w : W,
    prior c * nc.encode c w * log (posterior nc prior w c / prior c)

/-! ## Basic structural lemmas -/

/-- Each encode probability is at most 1 (from row-stochastic constraint). -/
lemma CommChannel.encode_le_one (nc : CommChannel C W) (c : C) (w : W) :
    nc.encode c w ≤ 1 := by
  have := single_le_sum (fun w' _ => nc.encode_nonneg c w') (mem_univ w)
  linarith [nc.encode_sum_one c]

/-- Marginal word probability is non-negative under a non-negative prior. -/
lemma marginalWord_nonneg (nc : CommChannel C W) (prior : C → ℝ)
    (hp : ∀ c, 0 ≤ prior c) (w : W) :
    0 ≤ marginalWord nc prior w :=
  sum_nonneg fun c _ => mul_nonneg (hp c) (nc.encode_nonneg c w)

/-- The marginal word distribution sums to 1 under a normalized prior. -/
lemma marginalWord_sum_one (nc : CommChannel C W) (prior : C → ℝ)
    (hsum : ∑ c : C, prior c = 1) :
    ∑ w : W, marginalWord nc prior w = 1 := by
  unfold marginalWord; rw [sum_comm]
  simp_rw [← mul_sum, nc.encode_sum_one, mul_one]; exact hsum

/-- When `prior c > 0` and `encode c w > 0`, the marginal `p(w) > 0`. -/
lemma marginalWord_pos_of (nc : CommChannel C W) (prior : C → ℝ)
    (hp : ∀ c, 0 ≤ prior c) {c : C} {w : W}
    (hpc : 0 < prior c) (hew : 0 < nc.encode c w) :
    0 < marginalWord nc prior w :=
  lt_of_lt_of_le (mul_pos hpc hew)
    (single_le_sum (fun c' _ => mul_nonneg (hp c') (nc.encode_nonneg c' w)) (mem_univ c))

end Pragmatics.InformationTheory
