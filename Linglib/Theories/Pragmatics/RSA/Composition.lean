import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Theories.Pragmatics.RSA.Noisy

/-!
# RSAConfig.composeWithPrior — stage-to-stage Bayesian composition

@cite{nouwen-2024}

The canonical operation that composes two `RSAConfig`s by Bayesian update:
the L1 posterior of the previous stage becomes the worldPrior of the next.

```
   prev : RSAConfig U₁ W           next : RSAConfig U₂ W
   ─────────────────────           ────────────────────
   prev.L1 u_prev : W → ℝ          (anything that takes a worldPrior)
                                    │
                                    ▼
   composeWithPrior prev u_prev next : RSAConfig U₂ W
   (= next, but with worldPrior overridden by prev.L1 u_prev)
```

This makes the "one config's L1 IS the next config's prior" idiom — currently
inlined in @cite{nouwen-2024}'s `seqAdjCfg` — a first-class operation rather
than a per-study plumbing pattern.

## Speaker chain rule (A) vs listener chain rule (C)

Sequential RSA admits two encodings that are Bayesian-equivalent in the right
setup:

- **(A) Speaker chain (within-utterance, `Ctx`-based).** A single
  `RSAConfig` with `Ctx = List U` and a `ctx`-dependent meaning function.
  Per-word S1 probabilities are chained via `trajectoryProb` (`Basic.lean`).
  Used by `Incremental.lean` (CGGP) and Product-of-Experts noisy models
  (@cite{waldon-degen-2021}, @cite{schlotterbeck-wang-2023}).

- **(C) Listener chain (stage-to-stage).** A chain of `RSAConfig`s
  where stage k's worldPrior is stage (k-1)'s L1 (this operation).
  Used by @cite{nouwen-2024}'s sequential evaluative-then-adjective inference.

For a noisy lex `f : U → W → ℚ` and a sequence `[w₁, ..., wₙ]`, both encodings
yield the same L1 posterior:

  L1(r | trajectory) ∝ ∏ₖ f(wₖ, r) · prior(r)

A computes this via the speaker-side product `∏ₖ S1(wₖ | r, ctx≤k-1)` (noting
that linglib's `trajectoryProb` is product-of-per-step-softmaxes, which agrees
with this only after marginalization — see `trajectoryProb_eq_compose_chain`
TODO);  C computes this by iterating Bayesian update on the listener side.

The `trajectoryProb_eq_compose_chain` theorem below states the equivalence
explicitly (with `sorry`); the full proof relates per-step S1 normalization
(A) to per-step Bayesian denominators (C), and is left as future work
documented in MEMORY.md.
-/

namespace RSA

namespace RSAConfig

variable {U₁ U₂ U₃ W : Type*} [Fintype U₁] [Fintype U₂] [Fintype U₃] [Fintype W]

/-- Compose two `RSAConfig`s by Bayesian update: override `next.worldPrior`
    with `prev.L1 u_prev`. All other fields come from `next`.

    This is the canonical stage-to-stage composition operation. The previous
    stage's listener posterior — given some specific observed utterance
    `u_prev` from `prev`'s vocabulary — becomes the prior over worlds for
    the next stage. -/
noncomputable def composeWithPrior (prev : RSAConfig U₁ W) (u_prev : U₁)
    (next : RSAConfig U₂ W) : RSAConfig U₂ W where
  Ctx := next.Ctx
  Latent := next.Latent
  latentFintype := next.latentFintype
  meaning := next.meaning
  meaning_nonneg := next.meaning_nonneg
  s1Score := next.s1Score
  s1Score_nonneg := next.s1Score_nonneg
  α := next.α
  α_pos := next.α_pos
  latentPrior := next.latentPrior
  latentPrior_nonneg := next.latentPrior_nonneg
  worldPrior w := prev.L1 u_prev w
  worldPrior_nonneg w := prev.L1agent.policy_nonneg u_prev w
  transition := next.transition
  initial := next.initial

@[simp] theorem composeWithPrior_worldPrior (prev : RSAConfig U₁ W)
    (u_prev : U₁) (next : RSAConfig U₂ W) (w : W) :
    (composeWithPrior prev u_prev next).worldPrior w = prev.L1 u_prev w := rfl

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

/-- **Associativity at the worldPrior layer.** Composing a chain
    `c₁ → c₂ → c₃` is the same as composing `(c₁ → c₂) → c₃` because
    `composeWithPrior` only overrides the worldPrior, and the final
    config's worldPrior comes from the immediately-preceding config's L1.

    Note: this is associativity of *worldPrior threading*, not associativity
    in a category-theoretic sense — the L1 of `composeWithPrior` is a derived
    quantity that may differ from `prev.L1` because it uses the new prior. -/
@[simp] theorem composeWithPrior_assoc_worldPrior
    (c₁ : RSAConfig U₁ W) (u₁ : U₁) (c₂ : RSAConfig U₂ W) (u₂ : U₂)
    (c₃ : RSAConfig U₃ W) (w : W) :
    (composeWithPrior (composeWithPrior c₁ u₁ c₂) u₂ c₃).worldPrior w =
      (composeWithPrior c₁ u₁ c₂).L1 u₂ w := rfl

/-- **Speaker-vs-listener chain rule equivalence (TODO, sorry'd).**

    For a Product-of-Experts noisy lex `s : NoisyLex U W` over a shared
    utterance vocabulary, the within-utterance `Ctx`-based encoding (A —
    speaker chain via `trajectoryProb`) and the stage-to-stage
    `composeWithPrior` chain (C — listener chain) yield the same L1
    posterior at the final stage.

    Formally: for any prefix `[u₁, ..., uₙ]` of utterances and final-step
    observation `uₙ`, the L1 of the (n-stage `composeWithPrior` chain
    starting from one-shot configs over `s.lex`) equals the L1 of the
    sequential config `(s.toRSAConfigSeq scene)` after observing the
    trajectory.

    This documents the architectural identity that justifies the
    coexistence of the two idioms in the codebase. The full proof
    requires relating per-step S1 normalization (A) to per-step Bayesian
    denominators (C). It is left as a sorry-marked TODO so the claim is
    grep-able and warning-flagged. -/
theorem trajectoryProb_eq_compose_chain {U W : Type} [Fintype U] [Fintype W]
    (s : NoisyLex U W) (scene : W → Bool) (uLast : U) (w : W) :
    -- A: L1 of the sequential PoE config after observing [uLast]
    (s.toRSAConfigSeq scene).L1 uLast w =
    -- C: L1 of the one-shot bundle (single-stage degenerate chain)
    s.toRSAConfig.L1 uLast w := by
  sorry  -- TODO: A ≡ C for noisy PoE semantics. Single-stage case to start;
         -- generalize to n-stage chain via induction on the trajectory.

end RSAConfig

end RSA
