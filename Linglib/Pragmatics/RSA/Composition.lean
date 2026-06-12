import Linglib.Pragmatics.RSA.Basic

/-!
# Stage-to-stage prior composition of RSA configurations

`RSAConfig.composeWithPrior prev u_prev next` is `next` with its world prior
replaced by `prev`'s pragmatic-listener posterior `prev.L1 u_prev` — the
listener-side half of sequential RSA, where one stage's L1 becomes the next
stage's prior ([nouwen-2024]'s evaluative-then-adjective model). In
Lassiter–Goodman-style stages the same posterior also enters the literal
listener's normalization; that half lives in `next.meaning`, which this
operation leaves untouched.

Stage-to-stage listener chaining is *not* equivalent to within-utterance
speaker chaining (`trajectoryProb` over `Ctx = List U`): per-step S1
normalizers are world-dependent, so the two encodings generically diverge
([cohn-gordon-goodman-potts-2019]). They agree at the literal-listener
layer, where iterated Bayesian update equals the product-of-experts
posterior.

## Main declarations

- `RSA.RSAConfig.composeWithPrior`: override `next.worldPrior` with
  `prev.L1 u_prev`.
-/

namespace RSA

namespace RSAConfig

variable {U₁ U₂ U₃ W : Type*} [Fintype U₁] [Fintype U₂] [Fintype U₃] [Fintype W]

/-- Compose two `RSAConfig`s by Bayesian update: `next` with its world prior
    replaced by `prev.L1 u_prev`. The previous stage's listener posterior —
    given the observed utterance `u_prev` from `prev`'s vocabulary — becomes
    the prior over worlds for the next stage. -/
noncomputable def composeWithPrior (prev : RSAConfig U₁ W) (u_prev : U₁)
    (next : RSAConfig U₂ W) : RSAConfig U₂ W :=
  { next with
    worldPrior := prev.L1 u_prev
    worldPrior_nonneg := prev.L1agent.policy_nonneg u_prev }

@[simp] theorem composeWithPrior_worldPrior (prev : RSAConfig U₁ W)
    (u_prev : U₁) (next : RSAConfig U₂ W) :
    (composeWithPrior prev u_prev next).worldPrior = prev.L1 u_prev := rfl

@[simp] theorem composeWithPrior_meaning (prev : RSAConfig U₁ W) (u_prev : U₁)
    (next : RSAConfig U₂ W) :
    (composeWithPrior prev u_prev next).meaning = next.meaning := rfl

@[simp] theorem composeWithPrior_s1Score (prev : RSAConfig U₁ W) (u_prev : U₁)
    (next : RSAConfig U₂ W) :
    (composeWithPrior prev u_prev next).s1Score = next.s1Score := rfl

@[simp] theorem composeWithPrior_α (prev : RSAConfig U₁ W) (u_prev : U₁)
    (next : RSAConfig U₂ W) :
    (composeWithPrior prev u_prev next).α = next.α := rfl

@[simp] theorem composeWithPrior_latentPrior (prev : RSAConfig U₁ W)
    (u_prev : U₁) (next : RSAConfig U₂ W) :
    (composeWithPrior prev u_prev next).latentPrior = next.latentPrior := rfl

@[simp] theorem composeWithPrior_transition (prev : RSAConfig U₁ W)
    (u_prev : U₁) (next : RSAConfig U₂ W) :
    (composeWithPrior prev u_prev next).transition = next.transition := rfl

@[simp] theorem composeWithPrior_initial (prev : RSAConfig U₁ W) (u_prev : U₁)
    (next : RSAConfig U₂ W) :
    (composeWithPrior prev u_prev next).initial = next.initial := rfl

/-- Prior override is destructive: composing into an already-composed config
    discards the inner override. -/
@[simp] theorem composeWithPrior_composeWithPrior
    (c₁ : RSAConfig U₁ W) (u₁ : U₁) (c₂ : RSAConfig U₂ W) (u₂ : U₂)
    (c₃ : RSAConfig U₃ W) :
    composeWithPrior c₂ u₂ (composeWithPrior c₁ u₁ c₃) =
      composeWithPrior c₂ u₂ c₃ := rfl

end RSAConfig

end RSA
