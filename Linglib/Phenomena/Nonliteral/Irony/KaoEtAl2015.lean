import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kao, Levy & Goodman (2015) — A Computational Model of Irony @cite{kao-levy-goodman-2015}

Proceedings of the 37th Annual Meeting of the Cognitive Science Society.

## The Model

Extension of Kao et al.'s (2014) QUD-based RSA to irony. The central claim is
that irony emerges from pragmatic reasoning when the listener considers that
the speaker may be communicating **arousal** (emotional intensity) rather than
just state or valence. Without an arousal goal, the model produces hyperbole
(nonliteral, same valence); with arousal, it produces irony (nonliteral,
flipped valence, high arousal).

**Domain**: 3 weather states (terrible, ok, amazing) × 2 valence (negative,
positive) × 2 arousal (low, high) = 12 world states. 3 utterances
(= weather states). 3 QUDs (state, valence, arousal).

- **L0**: L0(w|u) ∝ P(valence, arousal | state) · ⟦u⟧(w)
- **S1**: QUD-projected: S1(u|q,w) ∝ [Σ_{w': π(w',q)=π(w,q)} L0(w'|u)]^α
- **L1**: L1(w|u) ∝ P(w) · Σ_q P(q) · S1(u|q,w)

Parameters: α = 1, P(terrible) = 1/991, P(ok) = P(amazing) = 495/991.
Fitted QUD prior: P(state) = 0.3, P(valence) = 0.3, P(arousal) = 0.4.

## The Argument

The paper's central contribution is a mechanistic account of **why irony works**.
When the speaker says "The weather is terrible" in a context where terrible
weather is unlikely:

- If the listener considers only **state** and **valence** goals, the
  best interpretation is hyperbole: the weather is merely ok (nonliteral),
  and the speaker feels negatively (same valence as literal content).

- If the listener also considers an **arousal** goal, the ironic reading
  becomes available: saying "terrible" communicates high arousal (because
  L0("terrible") → high arousal). The listener infers the weather is
  actually amazing (also high arousal), the speaker feels positively
  (valence flip), and the speaker is emotionally aroused.

The arousal QUD creates a pragmatic pathway from "terrible" to "amazing"
that crosses the valence boundary. Without it, the model cannot bridge
from negative to positive valence, and irony does not emerge.

## Qualitative Findings

| # | Finding                 | Theorem                    | Description                                    |
|---|------------------------|----------------------------|------------------------------------------------|
| 1 | ironic_nonliteral      | `ironic_nonliteral`        | P(¬terrible \| "terrible") > P(terrible)       |
| 2 | ironic_valence_flip    | `ironic_valence_flip`      | P(positive \| "terrible") > P(negative)        |
| 3 | ironic_high_arousal    | `ironic_high_arousal`      | P(high \| "terrible") > P(low)                 |
| 4 | no_irony_without_arousal | `no_irony_without_arousal` | Valence-only: P(negative) > P(positive)      |
| 5 | literal_state          | `literal_state`            | P(ok \| "ok") > P(¬ok)                         |
| 6 | literal_low_arousal    | `literal_low_arousal`      | P(low \| "ok") > P(high)                       |

Findings 2 + 4 together establish the paper's core argument: arousal is the
mechanism that enables irony. The full model (finding 2) flips valence;
removing arousal (finding 4) eliminates the flip, leaving only hyperbole.
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Irony.KaoEtAl2015

open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Empirical Findings
-- ============================================================================

/-- The 6 qualitative findings from Kao, Levy & Goodman (2015).
    Findings 1–3 characterize irony; finding 4 identifies the mechanism;
    findings 5–6 verify literal interpretation. -/
inductive Finding where
  /-- Nonliteral interpretation: P(state ≠ terrible | "terrible") >
      P(state = terrible | "terrible"). The listener infers the weather
      is NOT actually terrible. -/
  | ironic_nonliteral
  /-- Valence flip: P(positive | "terrible") > P(negative | "terrible").
      The hallmark of irony — the speaker's affect is opposite to the
      literal content. This is what distinguishes irony from hyperbole. -/
  | ironic_valence_flip
  /-- High arousal: P(high | "terrible") > P(low | "terrible").
      Ironic speech carries heightened emotional intensity
      (Colston & O'Brien 2000). -/
  | ironic_high_arousal
  /-- Without arousal QUD, no valence flip: P(negative | "terrible") >
      P(positive | "terrible"). This is the paper's core mechanistic
      claim — removing arousal as a communicative goal eliminates
      ironic interpretation, leaving only hyperbole. -/
  | no_irony_without_arousal
  /-- Literal state inference: P(ok | "ok") > P(¬ok | "ok").
      Non-extreme utterances receive literal interpretations. -/
  | literal_state
  /-- Low arousal for neutral: P(low | "ok") > P(high | "ok").
      "Ok" weather is boring — the model correctly infers low
      emotional intensity for non-extreme states. -/
  | literal_low_arousal
  deriving DecidableEq, BEq, Repr

def findings : List Finding :=
  [.ironic_nonliteral, .ironic_valence_flip, .ironic_high_arousal,
   .no_irony_without_arousal, .literal_state, .literal_low_arousal]

-- ============================================================================
-- §2. Domain Types
-- ============================================================================

/-- Weather states double as utterance types. -/
inductive Weather where
  | terrible | ok | amazing
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
  elems := {.terrible, .ok, .amazing}
  complete := fun x => by cases x <;> simp

instance : Fintype Goal where
  elems := {.state, .valence, .arousal}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §3. Empirical Priors
-- ============================================================================

/-- Weather state prior (unnormalized). Terrible weather is rare;
    ok and amazing are equally likely. From Experiment 1. -/
def weatherPrior : Weather → ℝ
  | .terrible => 1
  | .ok       => 495
  | .amazing  => 495

/-- Affect prior: P(valence, arousal | weather state) (unnormalized).

    Each entry is the product of the valence and arousal conditionals:
    - Valence: P(neg|terrible) = 99/100, P(neg|ok) = 50/100, P(neg|amazing) = 1/100
    - Arousal: P(low|terrible) = 1/10, P(low|ok) = 9/10, P(low|amazing) = 1/10

    Extreme weather (terrible, amazing) has high arousal and polarized
    valence; neutral weather (ok) has low arousal and balanced valence.
    This asymmetry is the foundation of the irony mechanism. -/
def affectPrior (st : Weather) (positive high : Bool) : ℝ :=
  match st, positive, high with
  | .terrible, false, false => 99      -- neg, low   (99 × 1)
  | .terrible, false, true  => 891     -- neg, high  (99 × 9)
  | .terrible, true,  false => 1       -- pos, low   (1 × 1)
  | .terrible, true,  true  => 9       -- pos, high  (1 × 9)
  | .ok,       false, false => 450     -- neg, low   (50 × 9)
  | .ok,       false, true  => 50      -- neg, high  (50 × 1)
  | .ok,       true,  false => 450     -- pos, low   (50 × 9)
  | .ok,       true,  true  => 50      -- pos, high  (50 × 1)
  | .amazing,  false, false => 1       -- neg, low   (1 × 1)
  | .amazing,  false, true  => 9       -- neg, high  (1 × 9)
  | .amazing,  true,  false => 99      -- pos, low   (99 × 1)
  | .amazing,  true,  true  => 891     -- pos, high  (99 × 9)

-- ============================================================================
-- §4. Literal Semantics
-- ============================================================================

/-- L0 meaning: affect prior when utterance matches weather state, 0 otherwise.

    The affect prior is baked into L0 following RSAConfig convention:
    L0(w|u) ∝ P(valence, arousal | state) · ⟦u = state⟧.
    The weather state prior cancels in L0's normalization (constant
    within each state), so it enters only at L1 via worldPrior. -/
def meaning (_q : Goal) (u : Weather) (w : World) : ℝ :=
  if u == w.1 then affectPrior w.1 w.2.1 w.2.2 else 0

-- ============================================================================
-- §5. QUD Projection
-- ============================================================================

/-- Project a world onto the QUD-relevant dimension.
    Returns a natural number encoding the equivalence class. -/
def project (w : World) (q : Goal) : ℕ :=
  match q with
  | .state   => match w.1 with | .terrible => 0 | .ok => 1 | .amazing => 2
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
-- §6. RSAConfig
-- ============================================================================

open RSA in
/-- Irony model, parametric in QUD prior.

    S1 score is rpow(projected_L0, α). With α = 1 (fitted),
    S1 simply selects utterances proportional to their QUD-projected
    L0 score — no exponentiation needed. -/
@[reducible] noncomputable def cfg (goalPrior : Goal → ℝ)
    (hp : ∀ g, 0 ≤ goalPrior g) :
    RSAConfig Weather World where
  Latent := Goal
  meaning := meaning
  meaning_nonneg := by
    intro q u ⟨st, v, a⟩; simp only [meaning]
    split <;> (try exact le_refl 0)
    cases st <;> cases v <;> cases a <;> simp [affectPrior]
  s1Score l0 α q w u := rpow (qudProject q (l0 u) w) α
  s1Score_nonneg _ _ _ _ u hl _ :=
    rpow_nonneg (Finset.sum_nonneg (fun w' _ => hl u w')) _
  α := 1
  α_pos := by positivity
  worldPrior := fun w => weatherPrior w.1 * affectPrior w.1 w.2.1 w.2.2
  worldPrior_nonneg := by
    intro ⟨st, v, a⟩; apply mul_nonneg
    · cases st <;> simp [weatherPrior]
    · cases st <;> cases v <;> cases a <;> simp [affectPrior]
  latentPrior := fun _ g => goalPrior g
  latentPrior_nonneg := fun _ g => hp g

/-- Full model with fitted QUD prior: P(state) = 0.3, P(valence) = 0.3,
    P(arousal) = 0.4. Unnormalized integers [3, 3, 4]. -/
noncomputable abbrev fittedCfg :=
  cfg (fun g => match g with | .state => 3 | .valence => 3 | .arousal => 4)
    (fun g => by cases g <;> positivity)

/-- Valence-only model: arousal QUD removed. This produces hyperbole
    but NOT irony — the paper's key ablation. -/
noncomputable abbrev valenceOnlyCfg :=
  cfg (fun g => match g with | .state => 1 | .valence => 1 | .arousal => 0)
    (fun g => by cases g <;> simp)

-- ============================================================================
-- §7. Bridge Theorems
-- ============================================================================

section Theorems

open RSA.RSAConfig

-- Ironic interpretation: "terrible" when terrible weather is unlikely

set_option maxHeartbeats 400000 in
/-- Nonliteral interpretation: the listener infers the weather is NOT terrible. -/
theorem ironic_nonliteral :
    fittedCfg.L1 .terrible (.ok, false, false) +
    fittedCfg.L1 .terrible (.ok, false, true) +
    fittedCfg.L1 .terrible (.ok, true, false) +
    fittedCfg.L1 .terrible (.ok, true, true) +
    fittedCfg.L1 .terrible (.amazing, false, false) +
    fittedCfg.L1 .terrible (.amazing, false, true) +
    fittedCfg.L1 .terrible (.amazing, true, false) +
    fittedCfg.L1 .terrible (.amazing, true, true) >
    fittedCfg.L1 .terrible (.terrible, false, false) +
    fittedCfg.L1 .terrible (.terrible, false, true) +
    fittedCfg.L1 .terrible (.terrible, true, false) +
    fittedCfg.L1 .terrible (.terrible, true, true) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Valence flip — the hallmark of irony. Despite "terrible" literally
    conveying negative affect, the pragmatic listener infers that the
    speaker actually feels *positively*. -/
theorem ironic_valence_flip :
    fittedCfg.L1 .terrible (.terrible, true, false) +
    fittedCfg.L1 .terrible (.terrible, true, true) +
    fittedCfg.L1 .terrible (.ok, true, false) +
    fittedCfg.L1 .terrible (.ok, true, true) +
    fittedCfg.L1 .terrible (.amazing, true, false) +
    fittedCfg.L1 .terrible (.amazing, true, true) >
    fittedCfg.L1 .terrible (.terrible, false, false) +
    fittedCfg.L1 .terrible (.terrible, false, true) +
    fittedCfg.L1 .terrible (.ok, false, false) +
    fittedCfg.L1 .terrible (.ok, false, true) +
    fittedCfg.L1 .terrible (.amazing, false, false) +
    fittedCfg.L1 .terrible (.amazing, false, true) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Ironic speech carries high arousal — the speaker is emotionally
    engaged, not flat. -/
theorem ironic_high_arousal :
    fittedCfg.L1 .terrible (.terrible, false, true) +
    fittedCfg.L1 .terrible (.terrible, true, true) +
    fittedCfg.L1 .terrible (.ok, false, true) +
    fittedCfg.L1 .terrible (.ok, true, true) +
    fittedCfg.L1 .terrible (.amazing, false, true) +
    fittedCfg.L1 .terrible (.amazing, true, true) >
    fittedCfg.L1 .terrible (.terrible, false, false) +
    fittedCfg.L1 .terrible (.terrible, true, false) +
    fittedCfg.L1 .terrible (.ok, false, false) +
    fittedCfg.L1 .terrible (.ok, true, false) +
    fittedCfg.L1 .terrible (.amazing, false, false) +
    fittedCfg.L1 .terrible (.amazing, true, false) := by
  rsa_predict

-- The paper's core mechanistic claim: arousal enables irony

set_option maxHeartbeats 400000 in
/-- Without arousal as a communicative goal, "terrible" does NOT flip
    valence — the listener infers negative affect (matching the literal
    content). The model produces hyperbole but not irony.

    Combined with `ironic_valence_flip`, this pair of theorems establishes
    the paper's central argument: arousal is what enables the pragmatic
    pathway from negative to positive valence. -/
theorem no_irony_without_arousal :
    valenceOnlyCfg.L1 .terrible (.terrible, false, false) +
    valenceOnlyCfg.L1 .terrible (.terrible, false, true) +
    valenceOnlyCfg.L1 .terrible (.ok, false, false) +
    valenceOnlyCfg.L1 .terrible (.ok, false, true) +
    valenceOnlyCfg.L1 .terrible (.amazing, false, false) +
    valenceOnlyCfg.L1 .terrible (.amazing, false, true) >
    valenceOnlyCfg.L1 .terrible (.terrible, true, false) +
    valenceOnlyCfg.L1 .terrible (.terrible, true, true) +
    valenceOnlyCfg.L1 .terrible (.ok, true, false) +
    valenceOnlyCfg.L1 .terrible (.ok, true, true) +
    valenceOnlyCfg.L1 .terrible (.amazing, true, false) +
    valenceOnlyCfg.L1 .terrible (.amazing, true, true) := by
  rsa_predict

-- Literal interpretation: non-extreme utterances

set_option maxHeartbeats 400000 in
/-- "Ok" is interpreted literally — the listener correctly infers
    the weather is ok. -/
theorem literal_state :
    fittedCfg.L1 .ok (.ok, false, false) +
    fittedCfg.L1 .ok (.ok, false, true) +
    fittedCfg.L1 .ok (.ok, true, false) +
    fittedCfg.L1 .ok (.ok, true, true) >
    fittedCfg.L1 .ok (.terrible, false, false) +
    fittedCfg.L1 .ok (.terrible, false, true) +
    fittedCfg.L1 .ok (.terrible, true, false) +
    fittedCfg.L1 .ok (.terrible, true, true) +
    fittedCfg.L1 .ok (.amazing, false, false) +
    fittedCfg.L1 .ok (.amazing, false, true) +
    fittedCfg.L1 .ok (.amazing, true, false) +
    fittedCfg.L1 .ok (.amazing, true, true) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Neutral weather → low arousal. "Ok" conveys that the speaker
    is emotionally flat, in contrast to ironic "terrible" which
    conveys high arousal. -/
theorem literal_low_arousal :
    fittedCfg.L1 .ok (.terrible, false, false) +
    fittedCfg.L1 .ok (.terrible, true, false) +
    fittedCfg.L1 .ok (.ok, false, false) +
    fittedCfg.L1 .ok (.ok, true, false) +
    fittedCfg.L1 .ok (.amazing, false, false) +
    fittedCfg.L1 .ok (.amazing, true, false) >
    fittedCfg.L1 .ok (.terrible, false, true) +
    fittedCfg.L1 .ok (.terrible, true, true) +
    fittedCfg.L1 .ok (.ok, false, true) +
    fittedCfg.L1 .ok (.ok, true, true) +
    fittedCfg.L1 .ok (.amazing, false, true) +
    fittedCfg.L1 .ok (.amazing, true, true) := by
  rsa_predict

end Theorems

-- ============================================================================
-- §8. Verification
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
noncomputable def formalize : Finding → Prop
  | .ironic_nonliteral =>
      fittedCfg.L1 .terrible (.ok, false, false) +
      fittedCfg.L1 .terrible (.ok, false, true) +
      fittedCfg.L1 .terrible (.ok, true, false) +
      fittedCfg.L1 .terrible (.ok, true, true) +
      fittedCfg.L1 .terrible (.amazing, false, false) +
      fittedCfg.L1 .terrible (.amazing, false, true) +
      fittedCfg.L1 .terrible (.amazing, true, false) +
      fittedCfg.L1 .terrible (.amazing, true, true) >
      fittedCfg.L1 .terrible (.terrible, false, false) +
      fittedCfg.L1 .terrible (.terrible, false, true) +
      fittedCfg.L1 .terrible (.terrible, true, false) +
      fittedCfg.L1 .terrible (.terrible, true, true)
  | .ironic_valence_flip =>
      fittedCfg.L1 .terrible (.terrible, true, false) +
      fittedCfg.L1 .terrible (.terrible, true, true) +
      fittedCfg.L1 .terrible (.ok, true, false) +
      fittedCfg.L1 .terrible (.ok, true, true) +
      fittedCfg.L1 .terrible (.amazing, true, false) +
      fittedCfg.L1 .terrible (.amazing, true, true) >
      fittedCfg.L1 .terrible (.terrible, false, false) +
      fittedCfg.L1 .terrible (.terrible, false, true) +
      fittedCfg.L1 .terrible (.ok, false, false) +
      fittedCfg.L1 .terrible (.ok, false, true) +
      fittedCfg.L1 .terrible (.amazing, false, false) +
      fittedCfg.L1 .terrible (.amazing, false, true)
  | .ironic_high_arousal =>
      fittedCfg.L1 .terrible (.terrible, false, true) +
      fittedCfg.L1 .terrible (.terrible, true, true) +
      fittedCfg.L1 .terrible (.ok, false, true) +
      fittedCfg.L1 .terrible (.ok, true, true) +
      fittedCfg.L1 .terrible (.amazing, false, true) +
      fittedCfg.L1 .terrible (.amazing, true, true) >
      fittedCfg.L1 .terrible (.terrible, false, false) +
      fittedCfg.L1 .terrible (.terrible, true, false) +
      fittedCfg.L1 .terrible (.ok, false, false) +
      fittedCfg.L1 .terrible (.ok, true, false) +
      fittedCfg.L1 .terrible (.amazing, false, false) +
      fittedCfg.L1 .terrible (.amazing, true, false)
  | .no_irony_without_arousal =>
      valenceOnlyCfg.L1 .terrible (.terrible, false, false) +
      valenceOnlyCfg.L1 .terrible (.terrible, false, true) +
      valenceOnlyCfg.L1 .terrible (.ok, false, false) +
      valenceOnlyCfg.L1 .terrible (.ok, false, true) +
      valenceOnlyCfg.L1 .terrible (.amazing, false, false) +
      valenceOnlyCfg.L1 .terrible (.amazing, false, true) >
      valenceOnlyCfg.L1 .terrible (.terrible, true, false) +
      valenceOnlyCfg.L1 .terrible (.terrible, true, true) +
      valenceOnlyCfg.L1 .terrible (.ok, true, false) +
      valenceOnlyCfg.L1 .terrible (.ok, true, true) +
      valenceOnlyCfg.L1 .terrible (.amazing, true, false) +
      valenceOnlyCfg.L1 .terrible (.amazing, true, true)
  | .literal_state =>
      fittedCfg.L1 .ok (.ok, false, false) +
      fittedCfg.L1 .ok (.ok, false, true) +
      fittedCfg.L1 .ok (.ok, true, false) +
      fittedCfg.L1 .ok (.ok, true, true) >
      fittedCfg.L1 .ok (.terrible, false, false) +
      fittedCfg.L1 .ok (.terrible, false, true) +
      fittedCfg.L1 .ok (.terrible, true, false) +
      fittedCfg.L1 .ok (.terrible, true, true) +
      fittedCfg.L1 .ok (.amazing, false, false) +
      fittedCfg.L1 .ok (.amazing, false, true) +
      fittedCfg.L1 .ok (.amazing, true, false) +
      fittedCfg.L1 .ok (.amazing, true, true)
  | .literal_low_arousal =>
      fittedCfg.L1 .ok (.terrible, false, false) +
      fittedCfg.L1 .ok (.terrible, true, false) +
      fittedCfg.L1 .ok (.ok, false, false) +
      fittedCfg.L1 .ok (.ok, true, false) +
      fittedCfg.L1 .ok (.amazing, false, false) +
      fittedCfg.L1 .ok (.amazing, true, false) >
      fittedCfg.L1 .ok (.terrible, false, true) +
      fittedCfg.L1 .ok (.terrible, true, true) +
      fittedCfg.L1 .ok (.ok, false, true) +
      fittedCfg.L1 .ok (.ok, true, true) +
      fittedCfg.L1 .ok (.amazing, false, true) +
      fittedCfg.L1 .ok (.amazing, true, true)

/-- The RSA model accounts for all 6 findings from Kao et al. (2015). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact ironic_nonliteral
  · exact ironic_valence_flip
  · exact ironic_high_arousal
  · exact no_irony_without_arousal
  · exact literal_state
  · exact literal_low_arousal

end Phenomena.Nonliteral.Irony.KaoEtAl2015
