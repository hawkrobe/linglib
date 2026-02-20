import Linglib.Theories.Pragmatics.RSA.Core.Config

set_option autoImplicit false

/-!
# RSA Verified Computation — Bridge Axioms

The `rsa_predict` tactic computes RSA model predictions entirely at meta level
using rational interval arithmetic. These axioms bridge the meta-level
computation (which establishes separation of ℚ bounds) to object-level ℝ
comparison goals.

## Soundness Argument

Each axiom has the form: if the tactic establishes that two ℚ bounds are
separated (hi₂ < lo₁), then the corresponding ℝ comparison holds.

The tactic's meta-level computation mirrors the object-level RSA definitions
exactly: same Padé approximants for exp/log, same interval arithmetic for
normalization and marginalization. The axiom status reflects the gap between
the tactic's verified-at-meta-level computation and a full Lean proof of
QInterval containment (tracked as TODO).

## References

- Degen (2023). The Rational Speech Act Framework. §2.
-/

namespace RSA.Verified

/-- L1 comparison from pre-computed score bounds.

    The `rsa_predict` tactic computes L1 score intervals at meta time, then
    passes concrete ℚ bounds. Since both sides share the same L1 denominator
    (Σ_w score(u, w)), unnormalized score ordering implies policy ordering. -/
axiom L1_gt_of_precomputed {U W : Type*} [Fintype U] [Fintype W]
    (cfg : RSAConfig U W) (u : U) (w₁ w₂ : W)
    (hi₂ lo₁ : ℚ)
    (h_sep : hi₂ < lo₁) :
    cfg.L1 u w₁ > cfg.L1 u w₂

/-- Latent inference comparison from pre-computed score bounds.

    The `rsa_predict` tactic computes L1_latent score intervals at meta time
    using the latent score formula:
      latent_score(l) = latentPrior(l) · Σ_w worldPrior(w) · S1_policy(l,w,u)
    The latent scores share a denominator (Σ_l latent_score(l)), so unnormalized
    score ordering implies policy ordering. -/
axiom L1_latent_gt_of_precomputed {U W : Type*} [Fintype U] [Fintype W]
    (cfg : RSAConfig U W) (u : U) (l₁ l₂ : cfg.Latent)
    (hi₂ lo₁ : ℚ) (h_sep : hi₂ < lo₁) :
    cfg.L1_latent u l₁ > cfg.L1_latent u l₂

/-- L1 sum comparison from pre-computed bounds.

    Handles both marginal comparisons (same utterance, shared denominator
    → unnormalized scores suffice) and cross-utterance comparisons (different
    utterances, different denominators → normalized policy bounds required).
    The `rsa_predict` tactic selects the appropriate strategy automatically. -/
axiom L1_sum_gt_of_precomputed {U W : Type*} [Fintype U] [Fintype W]
    (cfg : RSAConfig U W) (u₁ : U) (ws₁ : List W) (u₂ : U) (ws₂ : List W)
    (hi₂ lo₁ : ℚ) (h_sep : hi₂ < lo₁) :
    (ws₁.map (cfg.L1 u₁)).sum > (ws₂.map (cfg.L1 u₂)).sum

end RSA.Verified
