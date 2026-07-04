import Linglib.Pragmatics.RSA.Sequential
import Linglib.Pragmatics.RSA.Channel

/-!
# NoisyLex — Noisy lexical semantics bundle

[degen-etal-2020] [waldon-degen-2021] [schlotterbeck-wang-2023]

A `NoisyLex U W` packages the per-(token, world) lex function shared by
RSA models with continuous / Product-of-Experts semantics. From the
bundle we derive:

- `prefixMeaning` — PoE composition over a list of tokens
  (delegates to `RSA.prefixMeaning`)
Studies build their sequential chains from `lex` and `prefixMeaning`
(No-Brevity β = 1 for [schlotterbeck-wang-2023]; rpow + cost-atom for
[waldon-degen-2021]).

This is the *structure-shaped* alternative to the typeclass roadmap
that previously lived in `Channel.lean`. There is no canonical noisy
semantics per (U, W) pair — every paper picks its own reliability
parameters — so each study constructs an explicit `NoisyLex` value and
calls a builder, mirroring how mathlib's `PMF` / `Kernel` are bundled
structures rather than typeclass-driven.

## Scope

The builders here all use **PoE prefix-product** L0 semantics — the
meaning at a prefix is the product of per-word lex values. Studies
that use **extension-averaging** L0 instead (e.g. [waldon-degen-2021]'s
`continuousMeaning` averages PoE over scene-filtered completions) need
their own bespoke chains; the bundle's `lex` and `prefixMeaning`
are still useful as building blocks (see `WaldonDegen2021.uttContinuousQ_eq_prefixMeaning`).

A complementary bundle for *extension-counting* (Boolean truth, not
graded) semantics ([cohn-gordon-goodman-potts-2019]) lives in
`Incremental.lean` as `IncrementalSemantics`.
-/

namespace RSA

variable {U W : Type}

/-- Bundle of noisy lexical semantics: a per-(token, world) ℚ-valued
    score that is non-negative everywhere. The `lex` field is the
    "Product of Experts" per-word factor underlying
    [degen-etal-2020], [waldon-degen-2021], and
    [schlotterbeck-wang-2023].

    Currently ℚ-valued for computable studies. PMF / ℝ generalization
    is future work tracked in MEMORY.md (`RSA → mathlib-PMF migration`). -/
structure NoisyLex (U W : Type) where
  /-- Per-(token, world) noisy meaning value. -/
  lex : U → W → ℚ
  /-- Noisy meaning is non-negative. -/
  lex_nonneg : ∀ u w, 0 ≤ lex u w

namespace NoisyLex

variable {U W : Type}

/-- The PoE prefix meaning derived from the lex function — multiplicative
    composition over a list of tokens. Delegates to `RSA.prefixMeaning`. -/
def prefixMeaning (s : NoisyLex U W) (pfx : List U) (w : W) : ℚ :=
  RSA.prefixMeaning s.lex pfx w

theorem prefixMeaning_nonneg (s : NoisyLex U W) (pfx : List U) (w : W) :
    0 ≤ s.prefixMeaning pfx w :=
  RSA.prefixMeaning_nonneg s.lex_nonneg pfx w

theorem prefixMeaning_perm (s : NoisyLex U W) {pfx pfx' : List U}
    (h : pfx.Perm pfx') (w : W) :
    s.prefixMeaning pfx w = s.prefixMeaning pfx' w :=
  RSA.prefixMeaning_perm h w

/-- Standard noisy-lex construction: pick a "true" reliability `r⁺` and
    a noise floor `r⁻` (typically `1 - r⁺`), and let `lex u w = r⁺` when
    `applies u w` and `r⁻` otherwise. This is the [degen-etal-2020]
    Bernoulli-channel form: `lex = noiseChannel r⁺ r⁻ (applies? 1 0)`. -/
def ofChannel (applies : U → W → Bool) (rPlus rMinus : ℚ)
    (h0 : 0 ≤ rMinus) (h1 : rMinus ≤ rPlus) : NoisyLex U W where
  lex u w := if applies u w then rPlus else rMinus
  lex_nonneg u w := by
    by_cases h : applies u w
    · simp [h]; linarith
    · simp [h, h0]

/-- The `ofChannel` lex agrees with `RSA.Noise.noiseChannel`. -/
theorem ofChannel_lex_eq_noiseChannel (applies : U → W → Bool)
    (rPlus rMinus : ℚ) (h0 : 0 ≤ rMinus) (h1 : rMinus ≤ rPlus) (u : U) (w : W) :
    (ofChannel applies rPlus rMinus h0 h1).lex u w =
      RSA.Noise.noiseChannel rPlus rMinus (if applies u w then 1 else 0) := by
  simp only [ofChannel, RSA.Noise.noiseChannel]
  by_cases h : applies u w <;> simp [h]

end NoisyLex

end RSA
