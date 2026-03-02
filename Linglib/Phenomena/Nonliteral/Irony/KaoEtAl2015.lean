import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict

/-!
# @cite{kao-goodman-2015} — Let's Talk (Ironically) About the Weather @cite{kao-goodman-2015}
@cite{bergen-goodman-2015}

Proceedings of the 37th Annual Meeting of the Cognitive Science Society.

## The Model

Extension of Kao et al.'s (2014) QUD-based RSA to irony. The central claim is
that irony emerges from pragmatic reasoning when the listener considers that
the speaker may be communicating **arousal** (emotional intensity) rather than
just state or valence. Without an arousal goal, the model produces hyperbole
(nonliteral, same valence); with arousal, it produces irony (nonliteral,
flipped valence, high arousal).

**Domain**: 5 weather states (terrible, bad, ok, good, amazing) × 2 valence
(negative, positive) × 2 arousal (low, high) = 20 world states. 5 utterances
(= weather states). 3 QUDs (state, valence, arousal).

- **L0**: L0(w|u) ∝ P(valence, arousal | state) · ⟦u⟧(w)
- **S1**: QUD-projected: S1(u|q,w) ∝ exp(λ · log[Σ_{w': π(w',q)=π(w,q)} L0(w'|u)])
- **L1**: L1(w|u) ∝ P(w) · Σ_q P(q) · S1(u|q,w)

Fitted parameters: λ = 1, P(q_state) = 0.3, P(q_valence) = 0.3,
P(q_arousal) = 0.4 (footnote 5).

## Context-Dependence

The paper's model is evaluated across 9 weather contexts × 5 utterances = 45
conditions (Experiment 1). Each context has different weather state priors P(s),
while the affect priors P(A|s) are context-independent.

The key demonstration is **context-dependence**: the same utterance "terrible"
is ironic in pleasant weather (valence flip, high arousal) and literal in
terrible weather (no flip). We formalize this with two representative contexts:

- **Pleasant weather** (`pleasantCfg`): good/amazing weather dominant, terrible
  rare. "Terrible" is ironic — the listener infers positive valence and high
  arousal despite the negative literal content.
- **Terrible weather** (`terribleCfg`): terrible/bad weather dominant, amazing
  rare. "Terrible" is literal — the listener infers negative valence matching
  the literal content.

## Priors

Weather priors approximate representative contexts from Experiment 1 (Figure 3).
Affect priors are derived from Figure 4's PCA-based valence and arousal curves
(Experiment 1). Valence follows an S-curve; arousal follows a symmetric U-curve
(high at both extremes, low at neutral).

## Qualitative Findings

| # | Finding                  | Config          | Description                                          |
|---|--------------------------|-----------------|------------------------------------------------------|
| 1 | ironic_nonliteral        | pleasantCfg     | P(¬terrible \| "terrible") > P(terrible)             |
| 2 | ironic_valence_flip      | pleasantCfg     | P(positive \| "terrible") > P(negative)              |
| 3 | ironic_high_arousal      | pleasantCfg     | P(high \| "terrible") > P(low)                       |
| 4 | no_irony_without_arousal | pleasant (no q_a)| Valence-only: P(negative) > P(positive)             |
| 5 | literal_state            | terribleCfg     | P(terrible \| "terrible") > P(¬terrible)             |
| 6 | literal_no_flip          | terribleCfg     | P(negative \| "terrible") > P(positive)              |

Findings 2 + 4 establish the core mechanistic claim: arousal enables irony.
Findings 2 + 6 demonstrate context-dependence: same utterance, opposite
valence inference depending on the weather prior.
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Irony.KaoEtAl2015

open Real (exp log exp_pos)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Weather states double as utterance types. 5 states from the paper:
    terrible, bad, ok (= paper's "neutral"), good, amazing. -/
inductive Weather where
  | terrible | bad | ok | good | amazing
  deriving DecidableEq, BEq, Repr

/-- Communicative goals (QUDs). The paper's central claim is that
    arousal as a QUD is what enables ironic interpretation. -/
inductive Goal where
  | state | valence | arousal
  deriving DecidableEq, BEq, Repr

/-- World = weather × positive? × high arousal?
    - `w.1` : weather state
    - `w.2.1` : `true` = positive valence, `false` = negative valence
    - `w.2.2` : `true` = high arousal, `false` = low arousal -/
abbrev World := Weather × Bool × Bool

instance : Fintype Weather where
  elems := {.terrible, .bad, .ok, .good, .amazing}
  complete := fun x => by cases x <;> simp

instance : Fintype Goal where
  elems := {.state, .valence, .arousal}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Affect Priors (Experiment 1, context-independent)
-- ============================================================================

/-- Affect prior: P(valence, arousal | weather state) (unnormalized).

    Derived from Experiment 1 (Figure 4). The paper fits beta distributions
    to participants' emotion ratings projected onto valence and arousal
    dimensions via PCA (circumplex model of affect, Russell 1980).

    Valence P(positive|s) follows an S-curve across weather states:
      terrible=1%, bad=15%, ok=50%, good=85%, amazing=99%

    Arousal P(high|s) follows a symmetric U-curve (high at both extremes):
      terrible=90%, bad=40%, ok=10%, good=40%, amazing=90%

    Joint = product of independent valence and arousal components.
    Each state sums to 1000 (unnormalized).

    The table is symmetric: terrible ↔ amazing and bad ↔ good
    (swap positive ↔ negative). -/
def affectPrior (st : Weather) (positive high : Bool) : ℝ :=
  match st, positive, high with
  -- terrible: P(pos)=1%, P(high)=90%
  | .terrible, false, false => 99      -- neg × low   (99 × 1)
  | .terrible, false, true  => 891     -- neg × high  (99 × 9)
  | .terrible, true,  false => 1       -- pos × low   (1 × 1)
  | .terrible, true,  true  => 9       -- pos × high  (1 × 9)
  -- bad: P(pos)=15%, P(high)=40%
  | .bad,      false, false => 510     -- neg × low   (85 × 6)
  | .bad,      false, true  => 340     -- neg × high  (85 × 4)
  | .bad,      true,  false => 90      -- pos × low   (15 × 6)
  | .bad,      true,  true  => 60      -- pos × high  (15 × 4)
  -- ok (= paper's "neutral"): P(pos)=50%, P(high)=10%
  | .ok,       false, false => 450     -- neg × low   (50 × 9)
  | .ok,       false, true  => 50      -- neg × high  (50 × 1)
  | .ok,       true,  false => 450     -- pos × low   (50 × 9)
  | .ok,       true,  true  => 50      -- pos × high  (50 × 1)
  -- good: P(pos)=85%, P(high)=40%
  | .good,     false, false => 90      -- neg × low   (15 × 6)
  | .good,     false, true  => 60      -- neg × high  (15 × 4)
  | .good,     true,  false => 510     -- pos × low   (85 × 6)
  | .good,     true,  true  => 340     -- pos × high  (85 × 4)
  -- amazing: P(pos)=99%, P(high)=90%
  | .amazing,  false, false => 1       -- neg × low   (1 × 1)
  | .amazing,  false, true  => 9       -- neg × high  (1 × 9)
  | .amazing,  true,  false => 99      -- pos × low   (99 × 1)
  | .amazing,  true,  true  => 891     -- pos × high  (99 × 9)

-- ============================================================================
-- §3. Literal Semantics
-- ============================================================================

/-- L0 meaning: affect prior when utterance matches weather state, 0 otherwise.

    L0(w|u) ∝ P(valence, arousal | state) · ⟦u = state⟧.
    The paper's L0 includes the full state prior P(s) = P(weather) × P(A|weather),
    but since ⟦u⟧ restricts to a single weather state, P(weather) is constant
    within L0's normalization and cancels. It enters only at L1 via worldPrior. -/
def meaning (_q : Goal) (u : Weather) (w : World) : ℝ :=
  if u == w.1 then affectPrior w.1 w.2.1 w.2.2 else 0

-- ============================================================================
-- §4. QUD Projection
-- ============================================================================

/-- Project a world onto the QUD-relevant dimension.
    Returns a natural number encoding the equivalence class. -/
def project (w : World) (q : Goal) : ℕ :=
  match q with
  | .state   => match w.1 with
    | .terrible => 0 | .bad => 1 | .ok => 2 | .good => 3 | .amazing => 4
  | .valence => if w.2.1 then 1 else 0
  | .arousal => if w.2.2 then 1 else 0

/-- Sum L0 over the QUD equivalence class of w under goal q.

    This is the key mechanism: when the QUD is arousal, "terrible" and
    "amazing" weather states are equivalent (both high arousal), creating
    a pragmatic pathway from one to the other that crosses the valence
    boundary. -/
noncomputable def qudProject (q : Goal) (f : World → ℝ) (w : World) : ℝ :=
  (Finset.univ.filter (fun w' => project w' q = project w q)).sum f

-- ============================================================================
-- §5. RSAConfig (parametric in weather prior and goal prior)
-- ============================================================================

open RSA in
/-- Irony model, parametric in weather context and goal prior.

    S1 score uses exp(λ · log(projected_L0)). With λ = 1 (fitted),
    this is just the projected L0 score. The exp/log form matches the
    reifier's expMulLogSub pattern for efficient native_decide proofs. -/
@[reducible] noncomputable def cfg
    (wp : Weather → ℝ) (gp : Goal → ℝ)
    (hw : ∀ s, 0 ≤ wp s) (hg : ∀ g, 0 ≤ gp g) :
    RSAConfig Weather World where
  Latent := Goal
  meaning := meaning
  meaning_nonneg := by
    intro q u ⟨st, v, a⟩; simp only [meaning]
    split <;> (try exact le_refl 0)
    cases st <;> cases v <;> cases a <;> simp [affectPrior]
  s1Score l0 α q w u :=
    let projected := qudProject q (l0 u) w
    if projected = 0 then 0
    else exp (α * log projected)
  s1Score_nonneg _ _ _ _ _ _ _ := by
    simp only; split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := one_pos
  worldPrior := fun w => wp w.1 * affectPrior w.1 w.2.1 w.2.2
  worldPrior_nonneg := by
    intro ⟨st, v, a⟩; apply mul_nonneg
    · exact hw st
    · cases st <;> cases v <;> cases a <;> simp [affectPrior]
  latentPrior := fun _ g => gp g
  latentPrior_nonneg := fun _ g => hg g

-- ============================================================================
-- §6. Context-Specific Weather Priors (Experiment 1)
-- ============================================================================

/-- Pleasant weather context (e.g., "nice day in California").
    Approximates a context from Experiment 1 (Figure 3) where good/amazing
    weather is dominant and terrible weather is rare. -/
def pleasantWeather : Weather → ℝ
  | .terrible => 1
  | .bad      => 5
  | .ok       => 50
  | .good     => 300
  | .amazing  => 500

/-- Terrible weather context (e.g., "storm day").
    Symmetric to pleasantWeather: terrible/bad dominant, amazing rare. -/
def terribleWeather : Weather → ℝ
  | .terrible => 500
  | .bad      => 300
  | .ok       => 50
  | .good     => 5
  | .amazing  => 1

-- ============================================================================
-- §7. Goal Priors (fitted parameters)
-- ============================================================================

/-- Fitted QUD prior (footnote 5): P(state) = 0.3, P(valence) = 0.3,
    P(arousal) = 0.4. Unnormalized integers [3, 3, 4]. -/
def fittedGoals : Goal → ℝ
  | .state => 3 | .valence => 3 | .arousal => 4

/-- Valence-only ablation: arousal QUD removed. This produces hyperbole
    but NOT irony — the paper's key mechanistic test (Table 1). -/
def valenceOnlyGoals : Goal → ℝ
  | .state => 1 | .valence => 1 | .arousal => 0

-- ============================================================================
-- §8. Model Configurations
-- ============================================================================

/-- Full model in pleasant weather context — irony emerges. -/
noncomputable abbrev pleasantCfg :=
  cfg pleasantWeather fittedGoals
    (fun s => by cases s <;> simp [pleasantWeather])
    (fun g => by cases g <;> simp [fittedGoals])

/-- Full model in terrible weather context — literal interpretation. -/
noncomputable abbrev terribleCfg :=
  cfg terribleWeather fittedGoals
    (fun s => by cases s <;> simp [terribleWeather])
    (fun g => by cases g <;> simp [fittedGoals])

/-- Ablation: pleasant weather without arousal QUD. Produces hyperbole
    but not irony (Table 1 comparison). -/
noncomputable abbrev pleasantValenceOnlyCfg :=
  cfg pleasantWeather valenceOnlyGoals
    (fun s => by cases s <;> simp [pleasantWeather])
    (fun g => by cases g <;> simp [valenceOnlyGoals])

-- ============================================================================
-- §9. Bridge Theorems
-- ============================================================================

section Theorems

open RSA.RSAConfig

-- --------------------------------------------------------------------------
-- Ironic interpretation: "terrible" in pleasant weather
-- --------------------------------------------------------------------------

/-- Nonliteral interpretation: the listener infers the weather is NOT terrible.
    P(state ≠ terrible | "terrible", pleasant) > P(state = terrible | "terrible", pleasant). -/
theorem ironic_nonliteral :
    pleasantCfg.L1_marginal .terrible (fun w => w.1 != .terrible) >
    pleasantCfg.L1_marginal .terrible (fun w => w.1 == .terrible) := by
  rsa_predict

/-- Valence flip — the hallmark of irony. Despite "terrible" literally
    conveying negative affect, the pragmatic listener in a pleasant weather
    context infers that the speaker actually feels *positively*.
    This is the paper's central prediction (Figure 5, Figure 6). -/
theorem ironic_valence_flip :
    pleasantCfg.L1_marginal .terrible (fun w => w.2.1 == true) >
    pleasantCfg.L1_marginal .terrible (fun w => w.2.1 == false) := by
  rsa_predict

/-- Ironic speech carries high arousal — the speaker is emotionally
    engaged, not flat. -/
theorem ironic_high_arousal :
    pleasantCfg.L1_marginal .terrible (fun w => w.2.2 == true) >
    pleasantCfg.L1_marginal .terrible (fun w => w.2.2 == false) := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Core mechanistic claim: arousal enables irony (Table 1)
-- --------------------------------------------------------------------------

/-- Without arousal as a communicative goal, "terrible" does NOT flip
    valence — the listener infers negative affect (matching the literal
    content). The model produces hyperbole but not irony.

    Combined with `ironic_valence_flip`, this pair establishes the paper's
    central argument: arousal is the mechanism that enables the pragmatic
    pathway from negative to positive valence (Table 1). -/
theorem no_irony_without_arousal :
    pleasantValenceOnlyCfg.L1_marginal .terrible (fun w => w.2.1 == false) >
    pleasantValenceOnlyCfg.L1_marginal .terrible (fun w => w.2.1 == true) := by
  rsa_predict

-- --------------------------------------------------------------------------
-- Context-dependence: "terrible" in terrible weather is literal
-- --------------------------------------------------------------------------

/-- In terrible weather, "terrible" is interpreted literally — the listener
    correctly infers the weather IS terrible. The same utterance that is
    ironic in pleasant weather (theorem 1) is literal here. -/
theorem literal_state :
    terribleCfg.L1_marginal .terrible (fun w => w.1 == .terrible) >
    terribleCfg.L1_marginal .terrible (fun w => w.1 != .terrible) := by
  rsa_predict

/-- In terrible weather, "terrible" does NOT flip valence — the listener
    infers negative affect, matching the literal content. Contrast with
    `ironic_valence_flip` where the same utterance produces the opposite
    inference in pleasant weather. -/
theorem literal_no_flip :
    terribleCfg.L1_marginal .terrible (fun w => w.2.1 == false) >
    terribleCfg.L1_marginal .terrible (fun w => w.2.1 == true) := by
  rsa_predict

end Theorems

end Phenomena.Nonliteral.Irony.KaoEtAl2015
