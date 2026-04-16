import Linglib.Core.Constraint.Decoder
import Linglib.Core.Agent.GumbelLuce
import Linglib.Core.Agent.Thurstone

/-!
# Noise Kernels — Random Utility Models for Constraint Decoders
@cite{mcfadden-1974} @cite{thurstone-1927}

A `NoiseKernel` names the noise distribution of a Random Utility Model
(RUM), in McFadden's sense (@cite{mcfadden-1974}): each candidate's
deterministic score `s(c)` is perturbed by an independent noise variable
`ε(c)`, and the chosen candidate is the argmax of `s(c) + ε(c)`.
The induced choice probability defines a `Decoder` over real-valued scores.

```
  Score :  Cand → ℝ            (deterministic component)
        +
  Noise :  Cand → Random ℝ      (independent perturbation)
        ↓
  Choose:  argmax over (s + ε)  ──▶  P : Cand → ℝ
```

The noise distribution determines the choice rule. Three classical results:

| Noise distribution | Induced choice rule | Bridge theorem               |
|--------------------|---------------------|------------------------------|
| Dirac (no noise)   | argmax (uniform)    | `dirac_eq_argmaxDecoder`     |
| Gumbel(0, 1/α)     | softmax(α)          | `gumbel_eq_softmaxDecoder`   |
| Normal(0, σ²)      | probit (Φ-based)    | binary case via Thurstone V  |

The Gumbel ↔ softmax equivalence is McFadden's theorem (proved as
`mcfaddenIntegral_eq_softmax` in `Core.Agent.GumbelLuce`). The Gaussian
binary case is Thurstone Case V (`Core.Agent.Thurstone`); the n-ary
Gaussian case requires multivariate normal integration and is not yet
implemented as a `Decoder`.

## Why a separate kernel layer?

The `Decoder` interface is the *what* (a probability distribution over
candidates). `NoiseKernel` is the *why* (a noise distribution that
induces it via argmax). Two different noise distributions can yield
the same decoder up to numerical approximation (Gumbel ≈ Gaussian via
the logistic-Φ approximation, see `Core.Agent.Thurstone` §4), and the
same noise distribution can yield different decoders at different
temperatures. Separating the layers lets us state and use those
correspondences cleanly.

## Specialization to deterministic systems

When the noise kernel is `dirac` (no noise), the decoder reduces to
deterministic argmax. This is the bridge from RUM to the algebraic
(semiring) view: a deterministic decoder turns score-aggregation into
a max-plus (or min-plus / tropical) semiring operation. The semiring
correspondence is developed in a companion file (`Semiring.lean`).
-/

namespace Core.Constraint

open Core Real

-- ============================================================================
-- § 1: NoiseKernel
-- ============================================================================

/-- A noise kernel names a noise distribution for a Random Utility Model.

    Each constructor corresponds to a classical RUM theorem giving the
    closed-form choice probabilities for that noise distribution.
    Decoders are recovered via `toDecoder`. -/
inductive NoiseKernel where
  /-- No noise: the decoder is deterministic argmax. -/
  | dirac : NoiseKernel
  /-- I.i.d. Gumbel(0, 1/α) noise. By McFadden's theorem
      (@cite{mcfadden-1974}), the choice rule is `softmax α`. -/
  | gumbel (α : ℝ) : NoiseKernel
  /-- I.i.d. Gaussian(0, σ²) noise. By Thurstone Case V
      (@cite{thurstone-1927}), the binary choice probability is
      `Φ((s_a - s_b)/(σ√2))`. The n-ary decoder requires multivariate
      normal integration and is not yet implemented; the kernel is
      retained as a placeholder so theorems about it can be stated. -/
  | gaussian (σ : ℝ) : NoiseKernel

namespace NoiseKernel

/-- The decoder induced by a noise kernel on real-valued scores.

    For `gaussian σ` we currently fall back to `argmaxDecoder` as a
    placeholder — the Gaussian decoder requires multivariate normal
    integration that is not yet wired in. The placeholder is *not*
    semantically correct for `gaussian σ` with `σ > 0`; downstream code
    should use the binary Thurstone Case V machinery directly until
    `Decoder`-level Gaussian support lands. -/
noncomputable def toDecoder {Cand : Type*} : NoiseKernel → Decoder Cand ℝ
  | .dirac      => argmaxDecoder
  | .gumbel α   => softmaxDecoder α
  | .gaussian _ => argmaxDecoder

-- ============================================================================
-- § 2: Bridge Theorems
-- ============================================================================

/-- The Dirac kernel's decoder is exactly `argmaxDecoder`. By definition. -/
theorem dirac_eq_argmaxDecoder {Cand : Type*} :
    (NoiseKernel.dirac.toDecoder : Decoder Cand ℝ) = argmaxDecoder := rfl

/-- McFadden's theorem at the decoder level: the Gumbel(0, 1/α) kernel's
    decoder is exactly `softmaxDecoder α`. By definition; the underlying
    RUM-to-softmax identity is `mcfaddenIntegral_eq_softmax` in
    `Core.Agent.GumbelLuce`. -/
theorem gumbel_eq_softmaxDecoder {Cand : Type*} (α : ℝ) :
    (NoiseKernel.gumbel α).toDecoder = (softmaxDecoder α : Decoder Cand ℝ) := rfl

/-- For a `Fintype` candidate type, the Gumbel-induced softmax decoder
    agrees with `Core.softmax` (the McFadden-integral form) on every
    candidate, when the candidate set is the full type. -/
theorem gumbel_decoder_eq_softmax {ι : Type*} [Fintype ι] [Nonempty ι]
    (α : ℝ) (s : ι → ℝ) (i : ι) :
    (NoiseKernel.gumbel α).toDecoder.decode Finset.univ s i = softmax s α i := by
  classical
  show (softmaxDecoder α).decode Finset.univ s i = softmax s α i
  simp [softmaxDecoder, softmax, Finset.mem_univ]

end NoiseKernel

-- ============================================================================
-- § 3: Specialization to Deterministic Systems
-- ============================================================================

/-- The deterministic specialization: when the noise kernel is `dirac`,
    the entire `ConstraintSystem` reduces to a deterministic argmax
    selection. This is the *deterministic case* of the RUM family —
    and the entry point to the semiring view (see `Semiring.lean`).

    Stated as a defining equation rather than a theorem because the
    reduction is by `rfl` once both sides are unfolded. -/
theorem toDecoder_dirac_eq_argmax {Cand : Type*} :
    (NoiseKernel.dirac.toDecoder : Decoder Cand ℝ) = argmaxDecoder :=
  NoiseKernel.dirac_eq_argmaxDecoder

end Core.Constraint
