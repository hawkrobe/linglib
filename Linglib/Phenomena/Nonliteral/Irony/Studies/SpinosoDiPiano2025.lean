import Linglib.Phenomena.Nonliteral.Irony.KaoEtAl2015
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Spinoso-Di Piano et al. (2025) — (RSA)² @cite{spinoso-di-piano-etal-2025}

"(RSA)²: Irony as a Latent Rhetorical Strategy in a Rational Speech Act Model."
Proceedings of SCiL 2025.

## The Model

Replaces RSA's literal meaning indicator with a **rhetorical function**
`f_r(c, m, u)` parameterized by strategy `r ∈ {literal, ironic}`. The strategy
is a latent variable marginalized at L1, yielding the paper's title: (RSA)².

- **L0**: L0(w|r,u) ∝ f_r(u, w)
  - literal: f_literal(u, w) = ⟦u = w⟧
  - ironic:  f_ironic(u, w) = ⟦opposite(u) = w⟧
- **S1**: S1(u|r,w) ∝ L0(w|r,u)^α (belief-based, rpow)
- **L1**: L1(w|u) ∝ P(w) · Σ_r P(r) · S1(u|r,w)

Parameters: α = 1, uniform strategy prior.

## Key Insight: Zero New RSA Infrastructure

The (RSA)² architecture maps directly onto `RSAConfig` with `Latent := Strategy`.
The rhetorical function IS the meaning function; strategy marginalization IS
L1's latent marginalization. No new types or operators needed.

## Comparison to Kao et al. (2015)

Both models derive irony from context-dependent pragmatic inference over the
same weather domain. The key difference:

| Dimension | Kao et al. 2015 | Spinoso-Di Piano et al. 2025 |
|-----------|-----------------|-------------------------------|
| Latent | QUD (state/valence/arousal) | Strategy (literal/ironic) |
| World | Weather × Valence × Arousal (20 states) | Weather only (5 states) |
| Mechanism | Arousal QUD enables valence flip | Antonym mapping enables flip |
| Claim | Affect (arousal) is necessary | Affect is unnecessary |

The simplification IS the result: irony emerges from strategy inference alone,
without modeling affect dimensions, matching the same qualitative predictions.

## Qualitative Findings

| # | Finding | Config | Description |
|---|---------|--------|-------------|
| 1 | ironic_reading | terribleCfg | "amazing" → terrible weather |
| 2 | literal_reading | pleasantCfg | "amazing" → amazing weather |
| 3 | infer_ironic | terribleCfg | "amazing" → ironic strategy |
| 4 | infer_literal | pleasantCfg | "amazing" → literal strategy |
| 5 | terrible_ironic | pleasantCfg | "terrible" → amazing weather |
| 6 | terrible_literal | terribleCfg | "terrible" → terrible weather |

Theorems 1+2 and 5+6 demonstrate context-dependence (same utterance, opposite
interpretation). Theorems 3+4 are unique to (RSA)² — the strategy posterior is
directly observable, unlike the QUD posterior in Kao et al. (2015).

## Implementation Note

The paper's domain has U = W = Weather (utterances are weather descriptions,
worlds are weather states). RSAConfig requires distinct U and W types for
`rsa_predict` reification, so we use a thin `Utterance` wrapper around
`Weather` for the utterance type.
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Irony.Studies.SpinosoDiPiano2025

open Phenomena.Nonliteral.Irony.KaoEtAl2015 (Weather pleasantWeather terribleWeather)
open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Utterance type: weather descriptions used as speech acts. Structurally
    identical to `Weather` but a distinct type for `RSAConfig`. -/
inductive Utterance where
  | terrible | bad | ok | good | amazing
  deriving DecidableEq, BEq, Repr

instance : Fintype Utterance where
  elems := {.terrible, .bad, .ok, .good, .amazing}
  complete := fun x => by cases x <;> simp

/-- The two rhetorical strategies from (RSA)². The literal strategy maps
    utterances to their face-value meaning; the ironic strategy maps them
    to their evaluative antonym. -/
inductive Strategy where
  | literal
  | ironic
  deriving DecidableEq, BEq, Repr

instance : Fintype Strategy where
  elems := {.literal, .ironic}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Evaluative Antonym (Weather Scale)
-- ============================================================================

/-- Evaluative antonym on the weather scale: flip the endpoints, fix the
    midpoint. This is the core mechanism of ironic meaning — "amazing"
    ironically conveys "terrible" and vice versa. -/
def opposite : Weather → Weather
  | .terrible => .amazing
  | .bad      => .good
  | .ok       => .ok
  | .good     => .bad
  | .amazing  => .terrible

/-- Double irony cancels: opposite is an involution. -/
theorem opposite_involutive : ∀ w : Weather, opposite (opposite w) = w := by
  intro w; cases w <;> rfl

-- ============================================================================
-- §3. Rhetorical Meaning Function
-- ============================================================================

/-- Bool-valued rhetorical meaning: does utterance u convey world w under
    strategy r?
    - literal: u matches w (face-value)
    - ironic: u matches the antonym of w (evaluative flip)

    Cross-type comparison expanded by cases since U ≠ W. -/
def rhetoricalMeaning (r : Strategy) (u : Utterance) (w : Weather) : Bool :=
  match r, u, w with
  | .literal, .terrible, .terrible => true
  | .literal, .bad,      .bad      => true
  | .literal, .ok,       .ok       => true
  | .literal, .good,     .good     => true
  | .literal, .amazing,  .amazing  => true
  | .ironic,  .terrible, .amazing  => true
  | .ironic,  .bad,      .good     => true
  | .ironic,  .ok,       .ok       => true
  | .ironic,  .good,     .bad      => true
  | .ironic,  .amazing,  .terrible => true
  | _, _, _ => false

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

/-- (RSA)² model, parametric in weather context prior.

    `Latent := Strategy` — the rhetorical strategy is the latent variable.
    S1 score is rpow(L0, α) — standard belief-based RSA.
    α = 1 (paper's default), uniform strategy prior. -/
@[reducible] noncomputable def cfg
    (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s) :
    RSA.RSAConfig Utterance Weather where
  Latent := Strategy
  meaning r u w := if rhetoricalMeaning r u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α _r w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior := wp
  worldPrior_nonneg := hw

-- ============================================================================
-- §5. Context-Specific Configurations
-- ============================================================================

/-- Pleasant weather context — "amazing" is literal, "terrible" is ironic. -/
noncomputable abbrev pleasantCfg :=
  cfg pleasantWeather (fun s => by cases s <;> simp [pleasantWeather])

/-- Terrible weather context — "terrible" is literal, "amazing" is ironic. -/
noncomputable abbrev terribleCfg :=
  cfg terribleWeather (fun s => by cases s <;> simp [terribleWeather])

-- ============================================================================
-- §6. Bridge Theorems
-- ============================================================================

section Theorems

open RSA.RSAConfig

-- --------------------------------------------------------------------------
-- Context-dependent world inference
-- --------------------------------------------------------------------------

set_option rsa_predict.skipReflection true in
/-- Ironic reading: in terrible weather, L1 hearing "amazing" infers the
    weather is terrible (not amazing). The listener recognizes the speaker
    is being ironic — saying the opposite of what they mean. -/
theorem ironic_reading :
    terribleCfg.L1_marginal .amazing (fun w => w == .terrible) >
    terribleCfg.L1_marginal .amazing (fun w => w == .amazing) := by
  rsa_predict

set_option rsa_predict.skipReflection true in
/-- Literal reading: in pleasant weather, L1 hearing "amazing" infers the
    weather is amazing (matching the literal content). Same utterance,
    opposite interpretation — context determines strategy. -/
theorem literal_reading :
    pleasantCfg.L1_marginal .amazing (fun w => w == .amazing) >
    pleasantCfg.L1_marginal .amazing (fun w => w == .terrible) := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Strategy inference (unique to (RSA)²)
-- --------------------------------------------------------------------------

set_option rsa_predict.skipReflection true in
/-- In terrible weather, L1 infers the speaker is using the ironic strategy
    when saying "amazing". This is directly observable in (RSA)² — unlike
    Kao et al. (2015) where the QUD posterior is the analogous quantity. -/
theorem infer_ironic :
    terribleCfg.L1_latent .amazing .ironic >
    terribleCfg.L1_latent .amazing .literal := by
  rsa_predict

set_option rsa_predict.skipReflection true in
/-- In pleasant weather, L1 infers the literal strategy for "amazing". -/
theorem infer_literal :
    pleasantCfg.L1_latent .amazing .literal >
    pleasantCfg.L1_latent .amazing .ironic := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Symmetric predictions with "terrible"
-- --------------------------------------------------------------------------

set_option rsa_predict.skipReflection true in
/-- In pleasant weather, L1 hearing "terrible" infers the weather is
    actually amazing — the ironic flip. Parallels Kao et al. (2015)'s
    `ironic_valence_flip`. -/
theorem terrible_ironic :
    pleasantCfg.L1_marginal .terrible (fun w => w == .amazing) >
    pleasantCfg.L1_marginal .terrible (fun w => w == .terrible) := by
  rsa_predict

set_option rsa_predict.skipReflection true in
/-- In terrible weather, L1 hearing "terrible" infers the weather is
    terrible — literal interpretation. -/
theorem terrible_literal :
    terribleCfg.L1_marginal .terrible (fun w => w == .terrible) >
    terribleCfg.L1_marginal .terrible (fun w => w == .amazing) := by
  rsa_predict

end Theorems

end Phenomena.Nonliteral.Irony.Studies.SpinosoDiPiano2025
