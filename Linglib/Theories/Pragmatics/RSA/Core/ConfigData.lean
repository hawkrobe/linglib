import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# RSAConfigData — Computable RSA Configuration

A computable (ℚ-valued) parallel to `RSAConfig` (ℝ-valued). Models define
`RSAConfigData` and derive `RSAConfig` via `.toRSAConfig`.

## Design

`RSAConfig` uses a freeform `s1Score` lambda, which is flexible but
noncomputable. `RSAConfigData` replaces this with `S1ScoreSpec`, an
enumeration of the scoring patterns actually used across all implementations.

Each `S1ScoreSpec` variant has:
1. A computable ℚ implementation (for `native_decide` verification)
2. A noncomputable ℝ expansion (for `toRSAConfig`)
3. A soundness bridge (the ℝ expansion matches the original `s1Score`)

## S1ScoreSpec Variants

| Variant | Formula | Papers |
|---------|---------|--------|
| `beliefBased` | `L0(w\|u)^α` | Frank & Goodman 2012, Beller & Gerstenberg 2025 |
| `qudBelief` | `(Σ_{w'∼w} L0(w'\|u))^α` | Kao et al. 2014 Metaphor/Irony |
| `qudAction` | `if proj=0 then 0 else exp(α·(log proj - cost u))` | Kao et al. 2014 Hyperbole |
| `beliefAction` | `if L0=0 then 0 else exp(α·(log L0 - cost u))` | Qing & Franke 2015 σ_b |
| `actionBased` | `exp(α·(L0(w\|u) - cost u))` | Qing & Franke 2015 σ_a |
| `beliefWeighted` | `if qualOk then exp(α·Σ_s b(l,s)·log L0(u,s)) else 0` | Goodman & Stuhlmüller 2013 |
-/

namespace RSA

open BigOperators Real Finset

-- ============================================================================
-- S1ScoreSpec
-- ============================================================================

/-- S1 scoring specification. Each variant captures a standard RSA scoring
    pattern. The type parameters are:
    - `U` : utterance type
    - `W` : world type
    - `L` : latent variable type -/
inductive S1ScoreSpec (U W L : Type*) where
  /-- score = L0(w|u)^α.
      Standard belief-based informativity.
      Used by Frank & Goodman 2012, Beller & Gerstenberg 2025. -/
  | beliefBased
  /-- score = (Σ_{w': project w' l = project w l} L0(w'|u))^α.
      QUD-projected belief-based informativity (no cost).
      Used by Kao et al. 2014 Metaphor, Kao et al. 2015 Irony. -/
  | qudBelief (project : W → L → ℕ)
  /-- score = if projected = 0 then 0 else exp(α · (log projected - cost u))
      where projected = Σ_{w': project w' l = project w l} L0(w'|u).
      QUD-projected with utterance cost.
      Used by Kao et al. 2014 Hyperbole. -/
  | qudAction (cost : U → ℚ) (project : W → L → ℕ)
  /-- score = if L0(w|u) = 0 then 0 else exp(α · (log L0(w|u) - cost u)).
      Belief-oriented with utterance cost (gated).
      Used by Qing & Franke 2015 σ_b. -/
  | beliefAction (cost : U → ℚ)
  /-- score = exp(α · (L0(w|u) - cost u)).
      Action-oriented: raw L0 probability, no log.
      Used by Qing & Franke 2015 σ_a. -/
  | actionBased (cost : U → ℚ)
  /-- score = if quality(l, u) then exp(α · Σ_w belief(l, w) · log L0(u, w)) else 0.
      Belief-weighted expected log-informativity, gated by quality.
      Used by Goodman & Stuhlmüller 2013. -/
  | beliefWeighted (belief : L → W → ℚ) (quality : L → U → Bool)

-- ============================================================================
-- RSAConfigData
-- ============================================================================

/-- Computable RSA configuration with ℚ-valued data fields.

    Mirrors `RSAConfig` but all fields are computable, enabling
    `native_decide` verification. The `toRSAConfig` lift casts ℚ → ℝ
    and expands `scoreSpec` into the appropriate `s1Score` lambda. -/
structure RSAConfigData (U W : Type*) [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W] where
  /-- Latent variable type (default Unit). -/
  Latent : Type := Unit
  /-- Fintype instance for Latent. -/
  [latentFintype : Fintype Latent]
  /-- DecidableEq instance for Latent. -/
  [latentDecEq : DecidableEq Latent]
  /-- Literal semantics φ(l, u, w) ≥ 0, ℚ-valued. -/
  meaning : Latent → U → W → ℚ
  /-- Meaning values are non-negative. -/
  meaning_nonneg : ∀ l u w, 0 ≤ meaning l u w
  /-- S1 scoring pattern. -/
  scoreSpec : S1ScoreSpec U W Latent
  /-- Rationality parameter (natural number, ≥ 1). -/
  α : ℕ
  /-- Rationality is positive. -/
  α_pos : 0 < α := by omega
  /-- Prior over worlds (unnormalized, ℚ-valued). -/
  worldPrior : W → ℚ := fun _ => 1
  /-- World prior is non-negative. -/
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intro _; positivity
  /-- Prior over latent variables (unnormalized, ℚ-valued). -/
  latentPrior : W → Latent → ℚ := fun _ _ => 1
  /-- Latent prior is non-negative. -/
  latentPrior_nonneg : ∀ w l, 0 ≤ latentPrior w l := by intro _ _; positivity

attribute [instance] RSAConfigData.latentFintype RSAConfigData.latentDecEq

-- ============================================================================
-- S1ScoreSpec → s1Score (ℝ expansion)
-- ============================================================================

variable {U W L : Type*} [Fintype U] [Fintype W] [Fintype L] [DecidableEq W]

/-- QUD projection: sum L0 over the equivalence class of w under latent l.
    {w' | project w' l = project w l} -/
noncomputable def qudProjectR [DecidableEq L]
    (project : W → L → ℕ) (l : L) (l0 : U → W → ℝ) (u : U) (w : W) : ℝ :=
  (Finset.univ.filter (fun w' => project w' l = project w l)).sum (l0 u)

/-- Expand S1ScoreSpec to the ℝ-valued s1Score function expected by RSAConfig.
    Each variant produces the corresponding formula using ℝ operations. -/
noncomputable def S1ScoreSpec.toS1Score [DecidableEq L]
    (spec : S1ScoreSpec U W L) :
    (U → W → ℝ) → ℝ → L → W → U → ℝ :=
  match spec with
  | .beliefBased => fun l0 α _l w u =>
    rpow (l0 u w) α
  | .qudBelief project => fun l0 α l w u =>
    rpow (qudProjectR project l l0 u w) α
  | .qudAction cost project => fun l0 α l w u =>
    let projected := qudProjectR project l l0 u w
    if projected = 0 then 0
    else exp (α * (log projected - ↑(cost u)))
  | .beliefAction cost => fun l0 α _l w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - ↑(cost u)))
  | .actionBased cost => fun l0 α _l w u =>
    exp (α * (l0 u w - ↑(cost u)))
  | .beliefWeighted belief quality => fun l0 α l _w u =>
    if quality l u then
      exp (α * ∑ s : W, ↑(belief l s) * log (l0 u s))
    else 0

set_option linter.unusedSectionVars false in
/-- Non-negativity of s1Score for each ScoreSpec variant. -/
theorem S1ScoreSpec.toS1Score_nonneg [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (l0 : U → W → ℝ) (α : ℝ) (l : L) (w : W) (u : U)
    (hl0 : ∀ u' w', 0 ≤ l0 u' w') (_hα : 0 < α) :
    0 ≤ spec.toS1Score l0 α l w u := by
  match spec with
  | .beliefBased =>
    exact rpow_nonneg (hl0 u w) α
  | .qudBelief project =>
    exact rpow_nonneg (Finset.sum_nonneg fun w' _ => hl0 u w') α
  | .qudAction _ project =>
    simp only [toS1Score]
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  | .beliefAction _ =>
    simp only [toS1Score]
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  | .actionBased _ =>
    exact le_of_lt (exp_pos _)
  | .beliefWeighted _ _ =>
    simp only [toS1Score]
    split
    · exact le_of_lt (exp_pos _)
    · exact le_refl 0

-- ============================================================================
-- toRSAConfig
-- ============================================================================

/-- Lift RSAConfigData to RSAConfig by casting ℚ → ℝ and expanding scoreSpec. -/
noncomputable def RSAConfigData.toRSAConfig [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) : RSAConfig U W where
  Latent := d.Latent
  meaning l u w := ↑(d.meaning l u w)
  meaning_nonneg l u w := by exact_mod_cast d.meaning_nonneg l u w
  s1Score := d.scoreSpec.toS1Score
  s1Score_nonneg l0 α l w u hl0 hα := d.scoreSpec.toS1Score_nonneg l0 α l w u hl0 hα
  α := ↑d.α
  α_pos := by exact_mod_cast d.α_pos
  worldPrior w := ↑(d.worldPrior w)
  worldPrior_nonneg w := by exact_mod_cast d.worldPrior_nonneg w
  latentPrior w l := ↑(d.latentPrior w l)
  latentPrior_nonneg w l := by exact_mod_cast d.latentPrior_nonneg w l

end RSA
