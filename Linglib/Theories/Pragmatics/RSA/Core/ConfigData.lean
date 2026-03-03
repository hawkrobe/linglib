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
| `beliefBased` | `L0(w\|u)^α` | @cite{frank-goodman-2012}, @cite{beller-gerstenberg-2025} |
| `qudBelief` | `(Σ_{w'∼w} L0(w'\|u))^α` | @cite{kao-etal-2014-hyperbole} Metaphor/Irony |
| `qudAction` | `if proj=0 then 0 else exp(α·(log proj - cost u))` | @cite{kao-etal-2014-hyperbole} Hyperbole |
| `beliefAction` | `if L0=0 then 0 else exp(α·(log L0 - cost u))` | @cite{qing-franke-2015} σ_b |
| `actionBased` | `exp(α·(L0(w\|u) - cost u))` | @cite{qing-franke-2015} σ_a |
| `weightedBeliefAction` | `if L0=0 then 0 else exp(α·(γ·log L0 + bonus u))` | @cite{hawkins-etal-2025} |
| `beliefWeighted` | `if qualOk then exp(α·Σ_s b(l,s)·log L0(u,s)) else 0` | @cite{goodman-stuhlmuller-2013} |
-/

namespace RSA

open BigOperators Real Finset

-- ============================================================================
-- S1UtilityTerm
-- ============================================================================

/-- Utility term component for `combinedUtility` scoring.
    Each term contributes an additive component to the S1 utility:
    `score = exp(α · Σ_i term_i)`. -/
inductive S1UtilityTerm (U W L : Type*) where
  /-- weight(l) · log L0(u, w) — log-informativity at the true world. -/
  | logInformativity (weight : L → ℚ)
  /-- weight(l) · Σ_w' L0(u,w') · value(w') — expected value under L0. -/
  | expectedValue (weight : L → ℚ) (value : W → ℚ)
  /-- fn(l, u) — per-(latent, utterance) constant (cost, bonus, etc.). -/
  | constant (fn : L → U → ℚ)

/-- Does this term use log(L0), requiring L0 > 0? -/
def S1UtilityTerm.isLogTerm {U W L : Type*} : S1UtilityTerm U W L → Bool
  | .logInformativity _ => true
  | _ => false

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
      Used by @cite{frank-goodman-2012}, @cite{beller-gerstenberg-2025}. -/
  | beliefBased
  /-- score = (Σ_{w': project w' l = project w l} L0(w'|u))^α.
      QUD-projected belief-based informativity (no cost).
      Used by @cite{kao-etal-2014-hyperbole} Metaphor, @cite{kao-goodman-2015} Irony. -/
  | qudBelief (project : W → L → ℕ)
  /-- score = if projected = 0 then 0 else exp(α · (log projected - cost u))
      where projected = Σ_{w': project w' l = project w l} L0(w'|u).
      QUD-projected with utterance cost.
      Used by @cite{kao-etal-2014-hyperbole} Hyperbole. -/
  | qudAction (cost : U → ℚ) (project : W → L → ℕ)
  /-- score = if L0(w|u) = 0 then 0 else exp(α · (log L0(w|u) - cost u)).
      Belief-oriented with utterance cost (gated).
      Used by @cite{qing-franke-2015} σ_b. -/
  | beliefAction (cost : U → ℚ)
  /-- score = exp(α · (L0(w|u) - cost u)).
      Action-oriented: raw L0 probability, no log.
      Used by @cite{qing-franke-2015} σ_a. -/
  | actionBased (cost : U → ℚ)
  /-- score = if L0(w|u) = 0 then 0 else exp(α · (infWeight · log L0(w|u) + bonus u)).
      Weighted belief-action: informativity weight γ on log L0, plus a per-utterance
      bonus that can encode action relevance, cost, or any u-dependent term.
      Subsumes `beliefAction`: `beliefAction(cost) = weightedBeliefAction 1 (fun u => -cost u)`.
      Used by @cite{hawkins-etal-2025} (PRIOR-PQ). -/
  | weightedBeliefAction (infWeight : ℚ) (bonus : U → ℚ)
  /-- score = if quality(l, u) then exp(α · Σ_w belief(l, w) · log L0(u, w)) else 0.
      Belief-weighted expected log-informativity, gated by quality.
      Used by @cite{goodman-stuhlmuller-2013}. -/
  | beliefWeighted (belief : L → W → ℚ) (quality : L → U → Bool)
  /-- score = if (logActive(l) ∧ L0=0) then 0 else exp(α · Σ_i term_i(l, u, w, L0)).
      Arbitrary sum of utility terms. Subsumes `weightedBeliefAction`.
      Used by @cite{yoon-etal-2020} (politeness).

      The `logActive` gate controls when L0=0 forces score=0. When the
      informativity weight is 0 (pure social speaker), setting `logActive l = false`
      allows utterances incompatible with the true state to receive positive scores.
      Default: always gate (safe for models where all latent values have non-zero
      informativity weight). -/
  | combinedUtility (terms : List (S1UtilityTerm U W L)) (logActive : L → Bool := fun _ => true)

-- ============================================================================
-- S2ScoreSpec
-- ============================================================================

/-- Utility term component for `S2ScoreSpec.utilityMaximizing` scoring.
    Each term contributes an additive component to the S2 utility,
    computed w.r.t. L1 marginals (not L0). -/
inductive S2UtilityTerm (U W L : Type*) where
  /-- ω · ln P_L1(w|u) — log-informativity at the true world, w.r.t. L1. -/
  | logStateMarginal (weight : ℚ)
  /-- ω · Σ_w' P_L1(w'|u) · V(w') — expected value under L1 state marginals. -/
  | expectedValue (weight : ℚ) (value : W → ℚ)
  /-- ω · ln P_L1(l̂|u) — log probability of target latent under L1. -/
  | logLatentMarginal (weight : ℚ) (target : L)
  /-- f(u) — per-utterance constant (cost, etc.). -/
  | constant (fn : U → ℚ)

/-- S2 scoring specification. Determines how the S2 speaker scores utterances.
    - `endorsement`: S2(u|w) ∝ L1(w|u) — same as L1 endorsement (no extra utility).
    - `utilityMaximizing`: S2(u|w) ∝ exp(α · Σ terms) — full utility model. -/
inductive S2ScoreSpec (U W L : Type*) where
  /-- S2 score = L1(w|u). Simple endorsement (no presentational utility). -/
  | endorsement
  /-- S2 score = exp(α · Σ_i term_i). Utility-maximizing with L1-derived terms. -/
  | utilityMaximizing (α : ℚ) (terms : List (S2UtilityTerm U W L))

-- ============================================================================
-- RSAConfigData
-- ============================================================================

/-- Computable RSA configuration with ℚ-valued data fields.

    Mirrors `RSAConfig` but all fields are computable, enabling
    `native_decide` verification. The `toRSAConfig` lift casts ℚ → ℝ
    and expands `s1Spec` into the appropriate `s1Score` lambda. -/
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
  s1Spec : S1ScoreSpec U W Latent
  /-- Rationality parameter (positive rational). -/
  α : ℚ
  /-- Rationality is positive. -/
  α_pos : 0 < α := by norm_num
  /-- Optional S2 scoring specification. When `some`, enables S2 speaker layer. -/
  s2Spec : Option (S2ScoreSpec U W Latent) := none
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

/-- Evaluate a utility term in ℝ, given L0 policy and current (l, u, w). -/
noncomputable def S1UtilityTerm.evalR
    (term : S1UtilityTerm U W L) (l0 : U → W → ℝ) (l : L) (u : U) (w : W) : ℝ :=
  match term with
  | .logInformativity weight => ↑(weight l) * log (l0 u w)
  | .expectedValue weight value => ↑(weight l) * ∑ w' : W, l0 u w' * ↑(value w')
  | .constant fn => ↑(fn l u)

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
  | .weightedBeliefAction infWeight bonus => fun l0 α _l w u =>
    if l0 u w = 0 then 0
    else exp (α * (↑infWeight * log (l0 u w) + ↑(bonus u)))
  | .beliefWeighted belief quality => fun l0 α l _w u =>
    if quality l u then
      exp (α * ∑ s : W, ↑(belief l s) * log (l0 u s))
    else 0
  | .combinedUtility terms logActive => fun l0 α l w u =>
    if l0 u w = 0 then
      if logActive l then 0 else exp (α * terms.foldl (fun acc t => acc + t.evalR l0 l u w) 0)
    else exp (α * terms.foldl (fun acc t => acc + t.evalR l0 l u w) 0)

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
  | .weightedBeliefAction _ _ =>
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
  | .combinedUtility _ _ =>
    simp only [toS1Score]
    split
    · split
      · exact le_refl 0
      · exact le_of_lt (exp_pos _)
    · exact le_of_lt (exp_pos _)

-- ============================================================================
-- toRSAConfig
-- ============================================================================

/-- Lift RSAConfigData to RSAConfig by casting ℚ → ℝ and expanding s1Spec. -/
noncomputable def RSAConfigData.toRSAConfig [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) : RSAConfig U W where
  Latent := d.Latent
  meaning l u w := ↑(d.meaning l u w)
  meaning_nonneg l u w := by exact_mod_cast d.meaning_nonneg l u w
  s1Score := d.s1Spec.toS1Score
  s1Score_nonneg l0 α l w u hl0 hα := d.s1Spec.toS1Score_nonneg l0 α l w u hl0 hα
  α := ↑d.α
  α_pos := Rat.cast_pos.mpr d.α_pos
  worldPrior w := ↑(d.worldPrior w)
  worldPrior_nonneg w := by exact_mod_cast d.worldPrior_nonneg w
  latentPrior w l := ↑(d.latentPrior w l)
  latentPrior_nonneg w l := by exact_mod_cast d.latentPrior_nonneg w l

/-- Decompose `d.toRSAConfig = cfg` into per-field hypotheses.

    Used by the `rsa_predict` tactic's Tier 2 bridge: after building an
    `RSAConfigData` with matching ℚ data, this theorem reduces the config
    equality to field-by-field proofs that the tactic constructs individually.

    Requires `d.Latent` and `cfg.Latent` to be definitionally equal (always
    true in practice since both are the same concrete type).

    Fields use `HEq` where their types depend on `Latent` (meaning, s1Score,
    latentPrior). Proof fields (meaning_nonneg, s1Score_nonneg, α_pos,
    worldPrior_nonneg, latentPrior_nonneg) are handled by proof irrelevance.
    The `Fintype Latent` instance is handled by `Subsingleton.elim`. -/
theorem RSAConfigData.toRSAConfig_eq [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (cfg : RSAConfig U W)
    (h_lat : d.Latent = cfg.Latent)
    (h_meaning : @HEq (d.Latent → U → W → ℝ) d.toRSAConfig.meaning
                       (cfg.Latent → U → W → ℝ) cfg.meaning)
    (h_s1 : @HEq ((U → W → ℝ) → ℝ → d.Latent → W → U → ℝ) d.toRSAConfig.s1Score
                  ((U → W → ℝ) → ℝ → cfg.Latent → W → U → ℝ) cfg.s1Score)
    (h_α : d.toRSAConfig.α = cfg.α)
    (h_wp : d.toRSAConfig.worldPrior = cfg.worldPrior)
    (h_lp : @HEq (W → d.Latent → ℝ) d.toRSAConfig.latentPrior
                  (W → cfg.Latent → ℝ) cfg.latentPrior)
    : d.toRSAConfig = cfg := by
  cases cfg with
  | mk L m mnn s snn a ap lp lpnn wp wpnn =>
    subst h_lat
    replace h_meaning := eq_of_heq h_meaning
    replace h_s1 := eq_of_heq h_s1
    replace h_lp := eq_of_heq h_lp
    subst h_meaning h_s1 h_α h_lp h_wp
    simp only [toRSAConfig]
    congr 1
    all_goals first | rfl | exact Subsingleton.elim _ _

end RSA
