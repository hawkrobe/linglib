import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Theories.Pragmatics.RSA.Channel
import Linglib.Theories.Pragmatics.RSA.Sequential

/-!
# NoisyLex — Noisy lexical semantics bundle

@cite{degen-etal-2020} @cite{waldon-degen-2021} @cite{schlotterbeck-wang-2023}

A `NoisyLex U W` packages the per-(token, world) lex function shared by
RSA models with continuous / Product-of-Experts semantics. From the
bundle we derive:

- `prefixMeaning` — PoE composition over a list of tokens
  (delegates to `RSA.prefixMeaning`)
- `toRSAConfig` — one-shot RSAConfig: meaning is `lex` directly
- `toRSAConfigSeq scene` — sequential RSAConfig with α=1, no cost
  (S&W's β=1 default)
- `toRSAConfigSeqWithUtility scene α α_pos cost` — sequential with
  rpow + exp(-α·cost) speaker (W&D-flavored speaker, PoE-prefix L0)

This is the *structure-shaped* alternative to the typeclass roadmap
that previously lived in `Channel.lean`. There is no canonical noisy
semantics per (U, W) pair — every paper picks its own reliability
parameters — so each study constructs an explicit `NoisyLex` value and
calls a builder, mirroring how mathlib's `PMF` / `Kernel` are bundled
structures rather than typeclass-driven.

## Scope

The builders here all use **PoE prefix-product** L0 semantics — the
meaning at a prefix is the product of per-word lex values. Studies
that use **extension-averaging** L0 instead (e.g. @cite{waldon-degen-2021}'s
`continuousMeaning` averages PoE over scene-filtered completions) need
their own bespoke `RSAConfig.mk`; the bundle's `lex` and `prefixMeaning`
are still useful as building blocks (see `WaldonDegen2021.uttContinuousQ_eq_prefixMeaning`).

A complementary bundle for *extension-counting* (Boolean truth, not
graded) semantics (@cite{cohn-gordon-goodman-potts-2019}) lives in
`Incremental.lean` as `IncrementalSemantics`.
-/

namespace RSA

variable {U W : Type}

/-- Bundle of noisy lexical semantics: a per-(token, world) ℚ-valued
    score that is non-negative everywhere. The `lex` field is the
    "Product of Experts" per-word factor underlying
    @cite{degen-etal-2020}, @cite{waldon-degen-2021}, and
    @cite{schlotterbeck-wang-2023}.

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
    `applies u w` and `r⁻` otherwise. This is the @cite{degen-etal-2020}
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

variable [Fintype U] [Fintype W]

/-- One-shot RSAConfig from a NoisyLex bundle. Meaning is just the lex
    function; `Ctx = Unit`, α = 1, no cost, uniform priors. -/
noncomputable def toRSAConfig (s : NoisyLex U W) : RSAConfig U W where
  meaning _ _ u w := (s.lex u w : ℝ)
  meaning_nonneg _ _ u w := by exact_mod_cast s.lex_nonneg u w
  s1Score l0 _ _ w u := l0 u w
  s1Score_nonneg _ _ _ _ _ hl _ := hl _ _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

@[simp] theorem toRSAConfig_meaning (s : NoisyLex U W) (ctx : Unit) (l : Unit)
    (u : U) (w : W) :
    s.toRSAConfig.meaning ctx l u w = (s.lex u w : ℝ) := rfl

@[simp] theorem toRSAConfig_α (s : NoisyLex U W) : s.toRSAConfig.α = 1 := rfl

/-- Sequential RSAConfig from a NoisyLex bundle, optionally scene-restricted.
    Meaning is the PoE product over `ctx ++ [u]`; off-scene worlds get 0.
    Default scene is the full domain. α = 1, no cost (the
    @cite{schlotterbeck-wang-2023} "S1^inc with β = 1" configuration). -/
noncomputable def toRSAConfigSeq (s : NoisyLex U W)
    (scene : W → Bool := fun _ => true) : RSAConfig U W where
  Ctx := List U
  meaning ctx _ u w :=
    if scene w then (s.prefixMeaning (ctx ++ [u]) w : ℝ) else 0
  meaning_nonneg _ _ _ w := by
    split
    · exact_mod_cast s.prefixMeaning_nonneg _ w
    · exact le_refl _
  s1Score l0 _ _ w u := l0 u w
  s1Score_nonneg _ _ _ _ _ hl _ := hl _ _
  α := 1
  α_pos := one_pos
  transition ctx w := ctx ++ [w]
  initial := []
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

@[simp] theorem toRSAConfigSeq_meaning (s : NoisyLex U W) (scene : W → Bool)
    (ctx : List U) (l : Unit) (u : U) (w : W) :
    (s.toRSAConfigSeq scene).meaning ctx l u w =
      if scene w then (s.prefixMeaning (ctx ++ [u]) w : ℝ) else 0 := rfl

@[simp] theorem toRSAConfigSeq_α (s : NoisyLex U W) (scene : W → Bool) :
    (s.toRSAConfigSeq scene).α = 1 := rfl

@[simp] theorem toRSAConfigSeq_transition (s : NoisyLex U W) (scene : W → Bool)
    (ctx : List U) (u : U) :
    (s.toRSAConfigSeq scene).transition ctx u = ctx ++ [u] := rfl

@[simp] theorem toRSAConfigSeq_initial (s : NoisyLex U W) (scene : W → Bool) :
    (s.toRSAConfigSeq scene).initial = ([] : List U) := rfl

/-- **Headline order-independence at the bundle level.** The `meaning`
    of a sequential noisy-RSA config depends on `(ctx, u)` only through
    the multiset `ctx ++ [u]`. Inherits from `RSA.prefixMeaning_perm`. -/
theorem toRSAConfigSeq_meaning_perm (s : NoisyLex U W) (scene : W → Bool)
    {ctx₁ ctx₂ : List U} {u₁ u₂ : U}
    (h : (ctx₁ ++ [u₁]).Perm (ctx₂ ++ [u₂])) (w : W) (l : Unit) :
    (s.toRSAConfigSeq scene).meaning ctx₁ l u₁ w =
      (s.toRSAConfigSeq scene).meaning ctx₂ l u₂ w := by
  simp only [toRSAConfigSeq_meaning]
  by_cases hsc : scene w = true <;> simp [hsc, NoisyLex.prefixMeaning,
    RSA.prefixMeaning_perm h w]

/-- Sequential RSAConfig with `rpow + exp(-α·cost)` speaker (the W&D-style
    soft-rational speaker), but PoE-prefix L0 meaning. For studies that
    want α ≠ 1 or non-zero per-word cost while still using PoE semantics. -/
noncomputable def toRSAConfigSeqWithUtility (s : NoisyLex U W)
    (scene : W → Bool := fun _ => true)
    (α : ℝ) (α_pos : 0 < α)
    (cost : U → ℝ := fun _ => 0) : RSAConfig U W where
  Ctx := List U
  meaning ctx _ u w :=
    if scene w then (s.prefixMeaning (ctx ++ [u]) w : ℝ) else 0
  meaning_nonneg _ _ _ w := by
    split
    · exact_mod_cast s.prefixMeaning_nonneg _ w
    · exact le_refl _
  s1Score l0 a _ w u := Real.rpow (l0 u w) a * Real.exp (-a * cost u)
  s1Score_nonneg _ _ _ w u hl₀ _ :=
    mul_nonneg (Real.rpow_nonneg (hl₀ u w) _) (Real.exp_pos _).le
  α := α
  α_pos := α_pos
  transition ctx w := ctx ++ [w]
  initial := []
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

@[simp] theorem toRSAConfigSeqWithUtility_meaning (s : NoisyLex U W)
    (scene : W → Bool) (α : ℝ) (α_pos : 0 < α) (cost : U → ℝ)
    (ctx : List U) (l : Unit) (u : U) (w : W) :
    (s.toRSAConfigSeqWithUtility scene α α_pos cost).meaning ctx l u w =
      if scene w then (s.prefixMeaning (ctx ++ [u]) w : ℝ) else 0 := rfl

@[simp] theorem toRSAConfigSeqWithUtility_α (s : NoisyLex U W)
    (scene : W → Bool) (α : ℝ) (α_pos : 0 < α) (cost : U → ℝ) :
    (s.toRSAConfigSeqWithUtility scene α α_pos cost).α = α := rfl

end NoisyLex

end RSA
