import Linglib.Phenomena.Nonliteral.Irony.KaoEtAl2015
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Spinoso-Di Piano et al. (2025) — (RSA)² @cite{spinoso-di-piano-etal-2025}

"(RSA)²: Irony as a Latent Rhetorical Strategy in a Rational Speech Act Model."
Proceedings of the 63rd Annual Meeting of the Association for Computational
Linguistics (ACL 2025), pp. 20898–20938.

## The Model

Replaces RSA's literal meaning indicator with a **rhetorical function**
`f_r(c, m, u)` parameterized by strategy `r ∈ {literal, ironic}`. The strategy
is a latent variable marginalized at L1, yielding the paper's title: (RSA)².

- **L0**: L0(m|c,u,r) ∝ f_r(c, m, u) · P(m|c)        (Eq 4)
  - literal: f_literal(c, m, u) = ⟦m = meaning(u)⟧
  - ironic:  f_ironic(c, m, u) = ⟦m = opposite(meaning(u))⟧
- **S1**: S1(u|m,c,r) ∝ L0(m|c,u,r)^α · P(u|c)        (Eq 5)
- **L1**: L1(m|c,u,r) ∝ S1(u|m,c,r) · P(m|c)           (Eq 6)
- **Marginalization**: L1(m|c,u) = Σ_r L1(m|c,u,r) · P(r|c,u)  (Eq 7)

Parameters: α = 1 (paper's default), uniform P(u|c), uniform P(r).

## What We Formalize

We formalize the **conceptual hand-specified model** from Section 3.2 of the
paper, where f_r is a deterministic indicator (0/1). The paper's experimental
results use a neural network to approximate f_r from human data; that
quantitative fit is outside our scope.

For indicator meanings with one matching world per (u,r) pair, P(m|c) drops out
of L0 normalization, so our RSAConfig (which puts worldPrior only in L1)
produces equivalent predictions. Similarly, uniform P(u|c) drops out of S1.
The joint marginalization in RSAConfig is algebraically equivalent to the
paper's per-strategy normalization then mixing (Eq 7).

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

## Verified Predictions

| # | Theorem | Config | Description |
|---|---------|--------|-------------|
| 1 | ironic_reading | terribleCfg | "amazing" → terrible weather (Fig 3) |
| 2 | literal_reading | pleasantCfg | "amazing" → amazing weather |
| 3 | infer_ironic | terribleCfg | "amazing" → ironic strategy |
| 4 | infer_literal | pleasantCfg | "amazing" → literal strategy |
| 5 | terrible_ironic | pleasantCfg | "terrible" → amazing weather |
| 6 | terrible_literal | terribleCfg | "terrible" → terrible weather |
| 7 | ok_strategy_neutral | terribleCfg | "ok" → strategies equiprobable |
| 8 | bad_ironic | pleasantCfg | "bad" → good weather (interior scale) |
| 9 | good_ironic | terribleCfg | "good" → bad weather (interior scale) |
| 10 | ok_strategy_neutral_pleasant | pleasantCfg | "ok" → strategies equiprobable |

Theorems 1+2 and 5+6 demonstrate context-dependence (same utterance, opposite
interpretation). Theorems 3+4 are unique to (RSA)² — the strategy posterior is
directly observable, unlike the QUD posterior in Kao et al. (2015). Theorems
7+10 test a boundary case: since opposite(ok) = ok, the ironic and literal
strategies produce identical L0 distributions for "ok" in BOTH contexts, making
L1's strategy inference uninformative. Theorems 8+9 test interior scale
positions (bad/good rather than endpoints terrible/amazing).

## Structural Properties

`rhetoricalMeaning_swap` captures the core mechanism algebraically: ironic
meaning at world w equals literal meaning at the antonym world opposite(w).
This follows from `opposite` being an involution and grounds the ironic strategy
as "literal interpretation in the opposite world."

`irony_iff_prior_favors_antonym` is the deepest result: the (RSA)² model's
entire behavior reduces to comparing the world prior at two points. Irony
emerges iff worldPrior(opposite(u.toWeather)) > worldPrior(u.toWeather). This
is a much stronger claim than individual prediction theorems — it explains WHY
the cross-model agreement with Kao et al. (2015) holds: both models agree
whenever the weather prior is sufficiently asymmetric, because (RSA)²'s
prediction IS just a prior comparison.

## Implementation Note

The paper uses U = W = Weather (utterances are weather descriptions, worlds are
weather states). RSAConfig requires distinct types, so we use a thin `Utterance`
wrapper with an explicit `toWeather` conversion.
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Irony.Studies.SpinosoDiPiano2025

open Phenomena.Nonliteral.Irony.KaoEtAl2015 (Weather pleasantWeather terribleWeather)
open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Utterance type: weather descriptions used as speech acts. Structurally
    mirrors `Weather` but a distinct type for `RSAConfig`. -/
inductive Utterance where
  | terrible | bad | ok | good | amazing
  deriving DecidableEq, BEq, Repr

instance : Fintype Utterance where
  elems := {.terrible, .bad, .ok, .good, .amazing}
  complete := fun x => by cases x <;> simp

/-- Map each utterance to its corresponding weather state. -/
def Utterance.toWeather : Utterance → Weather
  | .terrible => .terrible
  | .bad      => .bad
  | .ok       => .ok
  | .good     => .good
  | .amazing  => .amazing

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

/-- The paper's rhetorical function f_r(c, m, u) (Eq 4), specialized to the
    hand-specified indicator case:
    - literal: true iff the utterance's weather meaning matches the world
    - ironic: true iff the antonym of the utterance's meaning matches the world

    Derives from `opposite` rather than enumerating cases. -/
def rhetoricalMeaning (r : Strategy) (u : Utterance) (w : Weather) : Bool :=
  match r with
  | .literal => u.toWeather == w
  | .ironic  => opposite u.toWeather == w

/-- Strategy swap: ironic meaning at w equals literal meaning at opposite(w).
    The ironic strategy is structurally equivalent to literal interpretation
    "in the opposite world." Follows from `opposite` being an involution. -/
theorem rhetoricalMeaning_swap (u : Utterance) (w : Weather) :
    rhetoricalMeaning .ironic u w = rhetoricalMeaning .literal u (opposite w) := by
  cases u <;> cases w <;> rfl

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

/-- (RSA)² model, parametric in weather context prior P(m|c).

    `Latent := Strategy` — the rhetorical strategy is the latent variable.
    S1 score is L0^α (belief-based, α = 1), uniform strategy and utterance
    priors. World prior enters at L1 (equivalent to paper's Eq 4–7 for
    indicator meanings). -/
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

/-- Pleasant weather context (priors from Kao & Goodman 2015). -/
noncomputable abbrev pleasantCfg :=
  cfg pleasantWeather (fun s => by cases s <;> simp [pleasantWeather])

/-- Terrible weather context (priors from Kao & Goodman 2015). -/
noncomputable abbrev terribleCfg :=
  cfg terribleWeather (fun s => by cases s <;> simp [terribleWeather])

-- ============================================================================
-- §6. Verified Predictions
-- ============================================================================

section Theorems

open RSA.RSAConfig

-- --------------------------------------------------------------------------
-- Context-dependent world inference (Figure 3)
-- --------------------------------------------------------------------------

/-- Ironic reading: in terrible weather, L1 hearing "amazing" infers the
    weather is terrible (not amazing). The listener recognizes the speaker
    is being ironic — saying the opposite of what they mean. Matches the
    paper's Figure 3 (right panel). -/
theorem ironic_reading :
    terribleCfg.L1_marginal .amazing (fun w => w == .terrible) >
    terribleCfg.L1_marginal .amazing (fun w => w == .amazing) := by
  rsa_predict

/-- Literal reading: in pleasant weather, L1 hearing "amazing" infers the
    weather is amazing (face-value content). Same utterance, opposite
    interpretation — context (the world prior) determines which strategy
    dominates. -/
theorem literal_reading :
    pleasantCfg.L1_marginal .amazing (fun w => w == .amazing) >
    pleasantCfg.L1_marginal .amazing (fun w => w == .terrible) := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Strategy inference (unique to (RSA)²)
-- --------------------------------------------------------------------------

/-- In terrible weather, L1 infers the speaker is using the ironic strategy
    when saying "amazing". This is directly observable in (RSA)² — unlike
    Kao et al. (2015) where the QUD posterior is the analogous quantity. -/
theorem infer_ironic :
    terribleCfg.L1_latent .amazing .ironic >
    terribleCfg.L1_latent .amazing .literal := by
  rsa_predict

/-- In pleasant weather, L1 infers the literal strategy for "amazing". -/
theorem infer_literal :
    pleasantCfg.L1_latent .amazing .literal >
    pleasantCfg.L1_latent .amazing .ironic := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Symmetric predictions with "terrible"
-- --------------------------------------------------------------------------

/-- In pleasant weather, L1 hearing "terrible" infers the weather is
    actually amazing — the ironic flip. Analogous to Kao et al. (2015)'s
    `ironic_valence_flip`, but over weather states rather than valence. -/
theorem terrible_ironic :
    pleasantCfg.L1_marginal .terrible (fun w => w == .amazing) >
    pleasantCfg.L1_marginal .terrible (fun w => w == .terrible) := by
  rsa_predict

/-- In terrible weather, L1 hearing "terrible" infers the weather is
    terrible — literal interpretation. -/
theorem terrible_literal :
    terribleCfg.L1_marginal .terrible (fun w => w == .terrible) >
    terribleCfg.L1_marginal .terrible (fun w => w == .amazing) := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Interior scale predictions (bad/good, not just endpoints)
-- --------------------------------------------------------------------------

/-- Interior irony: in pleasant weather, L1 hearing "bad" infers the weather
    is good (not bad). Tests the antonym mapping on non-endpoint scale
    positions: opposite(bad) = good, so the ironic reading maps to good. -/
theorem bad_ironic :
    pleasantCfg.L1_marginal .bad (fun w => w == .good) >
    pleasantCfg.L1_marginal .bad (fun w => w == .bad) := by
  rsa_predict

/-- Interior irony: in terrible weather, L1 hearing "good" infers the weather
    is bad (not good). Symmetric to `bad_ironic`: opposite(good) = bad. -/
theorem good_ironic :
    terribleCfg.L1_marginal .good (fun w => w == .bad) >
    terribleCfg.L1_marginal .good (fun w => w == .good) := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Boundary case: "ok" is its own antonym
-- --------------------------------------------------------------------------

/-- Since opposite(ok) = ok, the ironic and literal strategies produce
    identical L0 distributions for "ok". The strategy posterior is therefore
    uninformative — L1 assigns equal probability to both strategies. -/
theorem ok_strategy_neutral :
    terribleCfg.L1_latent .ok .literal =
    terribleCfg.L1_latent .ok .ironic := by
  rsa_predict

/-- The ok boundary case holds in pleasant weather too — the strategy
    neutrality is context-independent (it's a structural consequence of
    opposite(ok) = ok, not of the weather prior). -/
theorem ok_strategy_neutral_pleasant :
    pleasantCfg.L1_latent .ok .literal =
    pleasantCfg.L1_latent .ok .ironic := by
  rsa_predict

end Theorems

-- ============================================================================
-- §7. Structural Properties
-- ============================================================================

section Structural

open RSA.RSAConfig

/-- L1's unnormalized score is zero at weather states matching neither the
    literal nor the ironic reading. The (RSA)² model only considers two
    candidate interpretations per utterance: u.toWeather (literal) and
    opposite(u.toWeather) (ironic). All other weather states are ruled out.

    Proof: meaning(r, u, w) = 0 for both strategies when w matches
    neither reading, so L0(w|u,r) = 0, hence rpow(0, 1) = 0, hence
    S1(u|w,r) = 0, hence the L1 score (which sums over strategies) is 0. -/
theorem L1_score_zero_of_no_match (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) (w : Weather)
    (h_lit : u.toWeather ≠ w) (h_iron : opposite u.toWeather ≠ w) :
    (cfg wp hw).L1agent.score u w = 0 := by
  have hm : ∀ l : Strategy, (cfg wp hw).meaning l u w = 0 := by
    intro l
    show (if rhetoricalMeaning l u w then (1 : ℝ) else 0) = 0
    have : rhetoricalMeaning l u w = false := by
      cases l <;> cases u <;> cases w <;>
        simp_all [rhetoricalMeaning, Utterance.toWeather, opposite] <;> decide
    simp [this]
  have hL0 : ∀ l : Strategy, ((cfg wp hw).L0agent l).policy u w = 0 :=
    fun l => Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ (hm l)
  have hS1s : ∀ l : Strategy, ((cfg wp hw).S1agent l).score w u = 0 := by
    intro l
    show rpow (((cfg wp hw).L0agent l).policy u w) 1 = 0
    rw [hL0 l]; exact Real.zero_rpow one_ne_zero
  have hS1 : ∀ l : Strategy, (cfg wp hw).S1 l w u = 0 :=
    fun l => Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ (hS1s l)
  show wp w * ∑ l : Strategy, 1 * (cfg wp hw).S1 l w u = 0
  simp [hS1]

-- --------------------------------------------------------------------------
-- Helper lemmas: S1 = 1 at matching worlds, S1 = 0 at cross worlds
--
-- For indicator meanings, each (strategy, utterance) pair picks out exactly
-- one matching world. L0 concentrates all mass there, so L0.policy = 1.
-- Then rpow(1, 1) = 1, and S1 concentrates all mass on u (by case analysis
-- on the 5×5 Utterance×Weather grid), so S1 = 1. At cross (strategy, world)
-- pairs, meaning = 0 propagates through: L0 → rpow → S1 = 0.
-- --------------------------------------------------------------------------

-- Literal strategy helpers

private theorem L0_literal_totalScore_eq (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    ((cfg wp hw).L0agent .literal).totalScore u =
    (cfg wp hw).meaning .literal u u.toWeather := by
  show ∑ w : Weather, (cfg wp hw).meaning .literal u w =
       (cfg wp hw).meaning .literal u u.toWeather
  rw [Finset.sum_eq_single u.toWeather]
  · intro b _ hb
    show (if rhetoricalMeaning .literal u b then (1 : ℝ) else 0) = 0
    have : rhetoricalMeaning .literal u b = false := by
      cases u <;> cases b <;> simp_all [rhetoricalMeaning, Utterance.toWeather] <;> decide
    simp [this]
  · intro h; exact (h (Finset.mem_univ _)).elim

private theorem meaning_literal_match (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    (cfg wp hw).meaning .literal u u.toWeather = 1 := by
  show (if rhetoricalMeaning .literal u u.toWeather then (1 : ℝ) else 0) = 1
  have : rhetoricalMeaning .literal u u.toWeather = true := by
    cases u <;> simp [rhetoricalMeaning, Utterance.toWeather] <;> decide
  simp [this]

private theorem L0_literal_policy_one (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    ((cfg wp hw).L0agent .literal).policy u u.toWeather = 1 := by
  apply Core.RationalAction.policy_eq_one_of_totalScore_eq
  · exact L0_literal_totalScore_eq wp hw u
  · show 0 < (cfg wp hw).meaning .literal u u.toWeather
    rw [meaning_literal_match]; exact one_pos

private theorem S1_literal_totalScore_eq (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    ((cfg wp hw).S1agent .literal).totalScore u.toWeather =
    ((cfg wp hw).S1agent .literal).score u.toWeather u := by
  show ∑ u' : Utterance, rpow (((cfg wp hw).L0agent .literal).policy u' u.toWeather) 1 =
       rpow (((cfg wp hw).L0agent .literal).policy u u.toWeather) 1
  rw [Finset.sum_eq_single u]
  · intro u' _ hne
    have hm : (cfg wp hw).meaning .literal u' u.toWeather = 0 := by
      show (if rhetoricalMeaning .literal u' u.toWeather then (1 : ℝ) else 0) = 0
      have : rhetoricalMeaning .literal u' u.toWeather = false := by
        cases u <;> cases u' <;> simp_all [rhetoricalMeaning, Utterance.toWeather] <;> decide
      simp [this]
    have : ((cfg wp hw).L0agent .literal).policy u' u.toWeather = 0 :=
      Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ hm
    rw [this]; exact Real.zero_rpow one_ne_zero
  · intro h; exact (h (Finset.mem_univ _)).elim

private theorem S1_literal_one (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    (cfg wp hw).S1 .literal u.toWeather u = 1 := by
  apply Core.RationalAction.policy_eq_one_of_totalScore_eq
  · exact S1_literal_totalScore_eq wp hw u
  · have hp := L0_literal_policy_one wp hw u
    have : ((cfg wp hw).S1agent .literal).score u.toWeather u = 1 := by
      simp only [RSA.RSAConfig.S1agent]; simp only [hp]
      exact Real.one_rpow 1
    linarith

-- Ironic strategy helpers

private theorem L0_ironic_totalScore_eq (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    ((cfg wp hw).L0agent .ironic).totalScore u =
    (cfg wp hw).meaning .ironic u (opposite u.toWeather) := by
  show ∑ w : Weather, (cfg wp hw).meaning .ironic u w =
       (cfg wp hw).meaning .ironic u (opposite u.toWeather)
  rw [Finset.sum_eq_single (opposite u.toWeather)]
  · intro b _ hb
    show (if rhetoricalMeaning .ironic u b then (1 : ℝ) else 0) = 0
    have : rhetoricalMeaning .ironic u b = false := by
      cases u <;> cases b <;>
        simp_all [rhetoricalMeaning, Utterance.toWeather, opposite] <;> decide
    simp [this]
  · intro h; exact (h (Finset.mem_univ _)).elim

private theorem meaning_ironic_match (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    (cfg wp hw).meaning .ironic u (opposite u.toWeather) = 1 := by
  show (if rhetoricalMeaning .ironic u (opposite u.toWeather) then (1 : ℝ) else 0) = 1
  have : rhetoricalMeaning .ironic u (opposite u.toWeather) = true := by
    cases u <;> simp [rhetoricalMeaning, Utterance.toWeather, opposite] <;> decide
  simp [this]

private theorem L0_ironic_policy_one (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    ((cfg wp hw).L0agent .ironic).policy u (opposite u.toWeather) = 1 := by
  apply Core.RationalAction.policy_eq_one_of_totalScore_eq
  · exact L0_ironic_totalScore_eq wp hw u
  · show 0 < (cfg wp hw).meaning .ironic u (opposite u.toWeather)
    rw [meaning_ironic_match]; exact one_pos

private theorem S1_ironic_totalScore_eq (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    ((cfg wp hw).S1agent .ironic).totalScore (opposite u.toWeather) =
    ((cfg wp hw).S1agent .ironic).score (opposite u.toWeather) u := by
  show ∑ u' : Utterance, rpow (((cfg wp hw).L0agent .ironic).policy u' (opposite u.toWeather)) 1 =
       rpow (((cfg wp hw).L0agent .ironic).policy u (opposite u.toWeather)) 1
  rw [Finset.sum_eq_single u]
  · intro u' _ hne
    have hm : (cfg wp hw).meaning .ironic u' (opposite u.toWeather) = 0 := by
      show (if rhetoricalMeaning .ironic u' (opposite u.toWeather) then (1 : ℝ) else 0) = 0
      have : rhetoricalMeaning .ironic u' (opposite u.toWeather) = false := by
        cases u <;> cases u' <;>
          simp_all [rhetoricalMeaning, Utterance.toWeather, opposite] <;> decide
      simp [this]
    have : ((cfg wp hw).L0agent .ironic).policy u' (opposite u.toWeather) = 0 :=
      Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ hm
    rw [this]; exact Real.zero_rpow one_ne_zero
  · intro h; exact (h (Finset.mem_univ _)).elim

private theorem S1_ironic_one (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) :
    (cfg wp hw).S1 .ironic (opposite u.toWeather) u = 1 := by
  apply Core.RationalAction.policy_eq_one_of_totalScore_eq
  · exact S1_ironic_totalScore_eq wp hw u
  · have hp := L0_ironic_policy_one wp hw u
    have : ((cfg wp hw).S1agent .ironic).score (opposite u.toWeather) u = 1 := by
      simp only [RSA.RSAConfig.S1agent]; simp only [hp]
      exact Real.one_rpow 1
    linarith

-- Cross-strategy zeros

private theorem S1_ironic_at_literal_zero (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) (hne : u.toWeather ≠ opposite u.toWeather) :
    (cfg wp hw).S1 .ironic u.toWeather u = 0 := by
  have hm : (cfg wp hw).meaning .ironic u u.toWeather = 0 := by
    show (if rhetoricalMeaning .ironic u u.toWeather then (1 : ℝ) else 0) = 0
    have : rhetoricalMeaning .ironic u u.toWeather = false := by
      cases u <;> simp_all [rhetoricalMeaning, Utterance.toWeather, opposite] <;> decide
    simp [this]
  have hL0 : ((cfg wp hw).L0agent .ironic).policy u u.toWeather = 0 :=
    Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ hm
  have hS1s : ((cfg wp hw).S1agent .ironic).score u.toWeather u = 0 := by
    show rpow (((cfg wp hw).L0agent .ironic).policy u u.toWeather) 1 = 0
    rw [hL0]; exact Real.zero_rpow one_ne_zero
  exact Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ hS1s

private theorem S1_literal_at_ironic_zero (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) (hne : u.toWeather ≠ opposite u.toWeather) :
    (cfg wp hw).S1 .literal (opposite u.toWeather) u = 0 := by
  have hm : (cfg wp hw).meaning .literal u (opposite u.toWeather) = 0 := by
    show (if rhetoricalMeaning .literal u (opposite u.toWeather) then (1 : ℝ) else 0) = 0
    have : rhetoricalMeaning .literal u (opposite u.toWeather) = false := by
      cases u <;> simp_all [rhetoricalMeaning, Utterance.toWeather, opposite] <;> decide
    simp [this]
  have hL0 : ((cfg wp hw).L0agent .literal).policy u (opposite u.toWeather) = 0 :=
    Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ hm
  have hS1s : ((cfg wp hw).S1agent .literal).score (opposite u.toWeather) u = 0 := by
    show rpow (((cfg wp hw).L0agent .literal).policy u (opposite u.toWeather)) 1 = 0
    rw [hL0]; exact Real.zero_rpow one_ne_zero
  exact Core.RationalAction.policy_eq_zero_of_score_eq_zero _ _ _ hS1s

-- --------------------------------------------------------------------------
-- L1 score = world prior at matching worlds
-- --------------------------------------------------------------------------

/-- L1's unnormalized score at the literal world equals the world prior.
    At w = u.toWeather, S1(.literal, w, u) = 1 and S1(.ironic, w, u) = 0,
    so L1_score = wp(w) · (1·1 + 1·0) = wp(w). -/
private theorem L1_score_at_literal (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) (hne : u.toWeather ≠ opposite u.toWeather) :
    (cfg wp hw).L1agent.score u u.toWeather = wp u.toWeather := by
  show wp u.toWeather * ∑ l : Strategy, 1 * (cfg wp hw).S1 l u.toWeather u = wp u.toWeather
  have h1 : (cfg wp hw).S1 .literal u.toWeather u = 1 := S1_literal_one wp hw u
  have h0 : (cfg wp hw).S1 .ironic u.toWeather u = 0 :=
    S1_ironic_at_literal_zero wp hw u hne
  simp only [RSA.RSAConfig.S1] at h1 h0 ⊢
  simp only [Finset.univ, Fintype.elems,
    Finset.sum_insert (show Strategy.literal ∉ ({Strategy.ironic} : Finset _) by decide),
    Finset.sum_singleton, h1, h0]
  ring

/-- L1's unnormalized score at the ironic world equals the world prior.
    At w = opposite(u.toWeather), S1(.ironic, w, u) = 1 and
    S1(.literal, w, u) = 0, so L1_score = wp(w) · (1·0 + 1·1) = wp(w). -/
private theorem L1_score_at_ironic (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) (hne : u.toWeather ≠ opposite u.toWeather) :
    (cfg wp hw).L1agent.score u (opposite u.toWeather) = wp (opposite u.toWeather) := by
  show wp (opposite u.toWeather) * ∑ l : Strategy, 1 * (cfg wp hw).S1 l (opposite u.toWeather) u =
       wp (opposite u.toWeather)
  have h1 : (cfg wp hw).S1 .ironic (opposite u.toWeather) u = 1 := S1_ironic_one wp hw u
  have h0 : (cfg wp hw).S1 .literal (opposite u.toWeather) u = 0 :=
    S1_literal_at_ironic_zero wp hw u hne
  simp only [RSA.RSAConfig.S1] at h1 h0 ⊢
  simp only [Finset.univ, Fintype.elems,
    Finset.sum_insert (show Strategy.literal ∉ ({Strategy.ironic} : Finset _) by decide),
    Finset.sum_singleton, h0, h1]
  ring

-- --------------------------------------------------------------------------
-- Main structural theorem
-- --------------------------------------------------------------------------

/-- Irony in (RSA)² reduces to a prior comparison: L1 assigns higher
    probability to the ironic reading iff the world prior favors the
    antonym weather state over the literal one.

    This is the paper's core structural claim formalized: affect dimensions
    and QUD projection are unnecessary for irony — context (the world prior)
    alone determines whether an utterance is interpreted ironically. The
    entire model's behavior for non-midpoint utterances is captured by a
    single inequality: wp(opposite(u.toWeather)) > wp(u.toWeather).

    Proof: L1_score at each matching world equals wp (the S1 values are
    deterministic — either 0 or 1 — so the prior passes through unchanged).
    Then the biconditional follows from `policy_gt_of_score_gt` and its
    contrapositive. -/
theorem irony_iff_prior_favors_antonym (wp : Weather → ℝ) (hw : ∀ s, 0 ≤ wp s)
    (u : Utterance) (hne : u.toWeather ≠ opposite u.toWeather) :
    (cfg wp hw).L1 u (opposite u.toWeather) > (cfg wp hw).L1 u u.toWeather ↔
    wp (opposite u.toWeather) > wp u.toWeather := by
  have hs_lit := L1_score_at_literal wp hw u hne
  have hs_iron := L1_score_at_ironic wp hw u hne
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have hscore : (cfg wp hw).L1agent.score u u.toWeather ≥
                  (cfg wp hw).L1agent.score u (opposite u.toWeather) := by
      rw [hs_lit, hs_iron]; exact hle
    exact absurd h (Core.RationalAction.policy_not_gt_of_score_le _ _ _ _ hscore)
  · intro h
    apply Core.RationalAction.policy_gt_of_score_gt
    rw [hs_iron, hs_lit]; exact h

end Structural

end Phenomena.Nonliteral.Irony.Studies.SpinosoDiPiano2025
