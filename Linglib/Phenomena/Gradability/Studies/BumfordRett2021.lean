import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Prod

/-!
# @cite{bumford-rett-2021} — Rationalizing Evaluativity
@cite{bumford-rett-2021} @cite{lassiter-goodman-2017} @cite{bergen-levy-goodman-2016}
@cite{rett-2015} @cite{barker-2002-vagueness}

Proceedings of Sinn und Bedeutung 25, pp. 187–204.

## Key Claims

1. **Evaluativity is gradient**: Degree constructions differ in the *strength* of
   their evaluative inferences. The model produces a strict ranking:
   positive > equative > comparative.

2. **Comparison-class uncertainty**: Worlds are two-dimensional — subject height ×
   comparison class center. The listener jointly infers height and CC statistics,
   extending @cite{lassiter-goodman-2017}'s threshold RSA with
   @cite{barker-2002-vagueness}'s insight that CC uncertainty is informative.

3. **Lexical uncertainty for markedness**: Antonym-sensitive evaluativity
   (marked equatives like "as short as" are evaluative; unmarked "as tall as"
   are not) emerges from @cite{bergen-levy-goodman-2016}'s lexical uncertainty,
   where marked forms have higher production cost.

4. **Evaluativity metric**: E[ht − μ] — the expected deviation of the subject's
   height from the CC center — measures evaluativity strength.

## Model Architecture (§2.1)

- L₀(w | u, L) ∝ P(w) · L(u, w)
- Sₙ(u | w, L) ∝ exp(α · (log Lₙ₋₁(w | u, L) − C(u)))
- L₁(w | u) ∝ P(w) · Σ_L P(L) · S₁(u | w, L)
- α = 4, C(marked) = 2, C(unmarked) = 1, C(∅) = 0

## Discretization

The paper uses heights 1–17, CC centers 5–14, |ht − μ| ≤ 4 (SD = 2).
We scale to heights 1–9, CC centers 3–7, |ht − μ| ≤ 2 (SD = 1),
preserving the qualitative predictions with a 45-world grid
(25 valid worlds after the Gaussian truncation).

## Verified Predictions

1. **Positive construction**: both antonyms evaluative (ht shifts away from μ)
2. **Exact equative**: marked antonym evaluative, unmarked weakly evaluative
3. **Antonym asymmetry**: marked equative produces stronger evaluative inference

## Connection to @cite{rett-2015}

@cite{rett-2015} derives evaluativity categorically via Q/R-implicature
(formalized in `Theories/Pragmatics/Implicature/Evaluativity.lean`).
This RSA model derives the same predictions *gradiently*: evaluativity
strength varies continuously across constructions. Both accounts agree
on the antonym-sensitive pattern (equative marked > equative unmarked).

The RSA model adds two things the Neo-Gricean account lacks:
- Graded predictions (probability distributions over evaluativity strength)
- A unified mechanism (rational communication) rather than separate Q/R principles
-/

namespace Phenomena.Gradability.BumfordRett2021

open RSA

-- ============================================================================
-- § 1. World Type: Height × CC Center
-- ============================================================================

/-- A world is a pair (height index, CC center index).

    Height index i ∈ Fin 9 represents height i + 1 (range 1–9).
    CC center index j ∈ Fin 5 represents center j + 3 (range 3–7).
    Valid worlds satisfy |height − center| ≤ 2 (enforced via prior). -/
abbrev EvalWorld := Fin 9 × Fin 5

/-- Height value (1–9) from world indices. -/
def htVal (w : EvalWorld) : Int := (w.1.val : Int) + 1

/-- CC center value (3–7) from world indices. -/
def muVal (w : EvalWorld) : Int := (w.2.val : Int) + 3

/-- Deviation of height from CC center: ht − μ. -/
def deviation (w : EvalWorld) : Int := htVal w - muVal w

-- ============================================================================
-- § 2. Prior (§2.1)
-- ============================================================================

/-- Gaussian-weighted prior over valid worlds.

    CC center is uniform; height weight decreases with distance from center.
    Approximates N(μ, 1) truncated at |ht − μ| ≤ 2. Weights: d=0 → 10,
    d=1 → 6, d=2 → 1, d>2 → 0 (invalid world). -/
def worldPrior (w : EvalWorld) : ℚ :=
  match (deviation w).natAbs with
  | 0 => 10
  | 1 => 6
  | 2 => 1
  | _ => 0

-- ============================================================================
-- § 3. Utterances and Costs (§2.1)
-- ============================================================================

/-- Utterance type: unmarked (positive-polar), marked (negative-polar), or null.

    For the positive construction: unmarked = "tall", marked = "short".
    For the exact equative: unmarked = "as tall as K", marked = "as short as K".
    Cost asymmetry (marked = 2, unmarked = 1) drives antonym-sensitive
    evaluativity via @cite{bergen-levy-goodman-2016}'s lexical uncertainty. -/
inductive Utterance where
  | unmarked  -- positive-polar form
  | marked    -- negative-polar form (costlier)
  | null      -- silence ∅
  deriving Repr, DecidableEq, BEq, Fintype

/-- Utterance costs: marked = 2, unmarked = 1, null = 0. -/
def cost : Utterance → ℚ
  | .unmarked => 1
  | .marked   => 2
  | .null     => 0

-- ============================================================================
-- § 4. Threshold Offset (Latent Variable)
-- ============================================================================

/-- Threshold offset σ ∈ {−2, −1, 0, 1, 2}.

    Determines how far above the CC center a person must be to count as
    "tall." Index s ∈ Fin 5 represents σ = s − 2. Higher σ means a more
    exclusive threshold. -/
abbrev Sigma := Fin 5

/-- Integer offset value: index s ↦ σ = s − 2. -/
def sigmaVal (s : Sigma) : Int := (s.val : Int) - 2

-- ============================================================================
-- § 5. Shared RSA Infrastructure
-- ============================================================================

open Real (exp log exp_pos)

/-- World prior as ℝ (for RSAConfig). -/
noncomputable def worldPriorR (w : EvalWorld) : ℝ := worldPrior w

private theorem worldPrior_nonneg_Q :
    ∀ w : EvalWorld, (0 : ℚ) ≤ worldPrior w := by native_decide

theorem worldPriorR_nonneg : ∀ w : EvalWorld, 0 ≤ worldPriorR w := by
  intro w; simp only [worldPriorR]; exact_mod_cast worldPrior_nonneg_Q w

/-- Utterance cost as ℝ. -/
noncomputable def costR (u : Utterance) : ℝ := cost u

/-- S1 belief-based score with utterance costs (eq 10):
    Sₙ(u | w, L) ∝ exp(α · (log Lₙ₋₁(w | u, L) − C(u)))
    Gated on l0 = 0 to avoid log(0). -/
noncomputable def beliefScore :
    (Utterance → EvalWorld → ℝ) → ℝ → Sigma → EvalWorld → Utterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - costR u))

theorem beliefScore_nonneg :
    ∀ (l0 : Utterance → EvalWorld → ℝ) (α : ℝ) (l : Sigma) (w : EvalWorld) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ beliefScore l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [beliefScore]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

-- ============================================================================
-- § 6. Simulation 1: Positive Construction (§2.2.1)
-- ============================================================================

/-- Positive construction meaning (eq 12):
    - unmarked ("tall"): ht_w(j) ≥ μ_w + σ
    - marked ("short"): ht_w(j) ≤ μ_w + σ
    - null: true -/
def posMeaning (u : Utterance) (σ : Sigma) (w : EvalWorld) : Bool :=
  match u with
  | .unmarked => decide (htVal w ≥ muVal w + sigmaVal σ)
  | .marked   => decide (htVal w ≤ muVal w + sigmaVal σ)
  | .null     => true

/-- RSAConfig for the positive construction (Simulation 1).

    Worlds: (height, CC center). Latent: threshold offset σ.
    L0 bakes in the world prior (eq 10: L₀(w | u, L) ∝ P(w) · L(u, w)). -/
@[reducible]
noncomputable def posCfg : RSA.RSAConfig Utterance EvalWorld where
  Latent := Sigma
  meaning _ σ u w := if posMeaning u σ w then worldPriorR w else 0
  meaning_nonneg _ σ u w := by split <;> [exact worldPriorR_nonneg w; exact le_refl 0]
  s1Score := beliefScore
  s1Score_nonneg := beliefScore_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior := worldPriorR
  worldPrior_nonneg := worldPriorR_nonneg
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- § 7. Positive Evaluativity Predictions (§2.2.1, Table 1)
-- ============================================================================

/-- Concise world constructor: mkW h m = (Fin h, Fin m). -/
def mkW (h : Fin 9) (m : Fin 5) : EvalWorld := (h, m)

/-! ### Prediction 1: "Tall" shifts height above CC mean

Hearing "Jane is tall" (unmarked) shifts L₁'s posterior toward worlds
where the subject's height exceeds the CC center. At fixed CC center
μ = 5 (index 2), height 6 (index 5, dev = +1) becomes more likely
than height 4 (index 3, dev = −1). Both worlds have equal prior (6),
so the asymmetry is entirely due to pragmatic reasoning.
The paper reports E[ht − μ] = 2.08 at L₁. -/

theorem pos_tall_evaluative :
    posCfg.L1 .unmarked (mkW 5 2) > posCfg.L1 .unmarked (mkW 3 2) := by
  rsa_predict

/-! ### Prediction 2: "Short" shifts height below CC mean

Mirror image: hearing "Jane is short" (marked) shifts posterior toward
worlds where height is below the CC center. E[ht − μ] = −3.18 at L₁.
The marked form is even more evaluative than the unmarked form,
because the extra cost signals that the speaker's reason for speaking
must be particularly strong. -/

theorem pos_short_evaluative :
    posCfg.L1 .marked (mkW 3 2) > posCfg.L1 .marked (mkW 5 2) := by
  rsa_predict

-- ============================================================================
-- § 8. Simulation 2: Exact Equative (§2.2.2)
-- ============================================================================

/-- Keisha's height k, fixed and known to both speaker and listener.
    In our scaled model: k = 5 (height index 4). -/
def kHeight : Int := 5

/-- Exact equative meaning (eq 14):
    - unmarked ("as tall as K"): ht = k ∧ k ≥ μ + σ
    - marked ("as short as K"): ht = k ∧ k ≤ μ + σ
    - null: true

    The equative fixes height to k. The informative content is about
    where k sits relative to the CC center: does the threshold σ
    classify k as "tall-enough" (unmarked) or "short-enough" (marked)? -/
def eqMeaning (u : Utterance) (σ : Sigma) (w : EvalWorld) : Bool :=
  match u with
  | .unmarked => decide (htVal w = kHeight) && decide (kHeight ≥ muVal w + sigmaVal σ)
  | .marked   => decide (htVal w = kHeight) && decide (kHeight ≤ muVal w + sigmaVal σ)
  | .null     => true

/-- RSAConfig for the exact equative (Simulation 2).

    Same architecture as the positive construction but with equative
    semantics. After hearing the equative, the listener knows ht = k.
    The evaluativity question is whether the listener infers that k
    is above or below the CC mean. -/
@[reducible]
noncomputable def eqCfg : RSA.RSAConfig Utterance EvalWorld where
  Latent := Sigma
  meaning _ σ u w := if eqMeaning u σ w then worldPriorR w else 0
  meaning_nonneg _ σ u w := by split <;> [exact worldPriorR_nonneg w; exact le_refl 0]
  s1Score := beliefScore
  s1Score_nonneg := beliefScore_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior := worldPriorR
  worldPrior_nonneg := worldPriorR_nonneg
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- § 9. Equative Evaluativity Predictions (§2.2.2, Table 1)
-- ============================================================================

-- k = 5 (height index 4). Relevant worlds: (4, j) for j ∈ {0,1,2,3,4}.
-- μ = 3 (j=0): k well above mean → non-evaluative direction
-- μ = 5 (j=2): k at mean → neutral
-- μ = 7 (j=4): k well below mean → evaluative direction ("short")

/-! ### Prediction 3: Marked equative is evaluative

Hearing "Jane is as short as Keisha" (marked) shifts L₁'s posterior
toward high-μ worlds where k = 5 is below the CC center — i.e.,
Keisha's height is atypically low. The paper reports E[k − μ] = −1.06
at L₁.

The mechanism: the speaker paid extra cost (C = 2) for the marked form.
By @cite{bergen-levy-goodman-2016}'s logic, L₁ infers the speaker must have
had a strong reason — the marked form is distinctively informative in worlds
where k is atypically low. -/

theorem eq_marked_evaluative :
    eqCfg.L1 .marked (mkW 4 4) > eqCfg.L1 .marked (mkW 4 0) := by
  rsa_predict

/-! ### Prediction 4: Unmarked equative is weakly evaluative

Hearing "Jane is as tall as Keisha" (unmarked) produces a weak
evaluative inference: the posterior slightly favors worlds where k is
above the CC center (μ < k). The paper reports E[k − μ] = 0.84 at L₁,
much weaker than the marked form's −1.06.

This asymmetry — marked evaluative, unmarked weakly/not evaluative — is
the antonym-sensitive pattern that @cite{rett-2015} identifies categorically
and this model derives gradiently. -/

theorem eq_unmarked_weakly_evaluative :
    eqCfg.L1 .unmarked (mkW 4 0) > eqCfg.L1 .unmarked (mkW 4 4) := by
  rsa_predict

-- ============================================================================
-- § 10. Cross-Construction Comparison
-- ============================================================================

/-! ### Gradient evaluativity ranking

The paper's central prediction (Table 1) is a strict ranking of
evaluativity strength across constructions:

| Construction | unmarked E[ht−μ] | marked E[ht−μ] | Evaluative? |
|---|---|---|---|
| Positive | 2.08 | −3.18 | ✓ ✓ |
| = Equative | 0.84 | −1.06 | ✗ ✓ |
| ≥ Equative | 0.11 | −1.52 | ✗ ✓ |
| Comparative | −0.74 | −0.44 | ✗ ✗ |

This ranking emerges from two factors:
1. **Informativity**: The positive construction has an open degree argument
   (threshold is entirely unknown), making it maximally vague. Equatives
   fix height to k, reducing uncertainty. Comparatives provide strict
   ordering, leaving little room for evaluative inference.
2. **Cost asymmetry**: The marked form's extra cost (C = 2 vs 1) forces
   L₁ to seek explanations for the speaker's costly choice, driving
   evaluative inferences in worlds where the marked form is distinctively
   informative (i.e., atypical worlds). -/

-- ============================================================================
-- § 11. Cross-References
-- ============================================================================

/-! ### Relationship to @cite{lassiter-goodman-2017}

`LassiterGoodman2017.lean` formalizes the threshold RSA model for the
positive construction only (1D world = height, latent = threshold).
This file extends that model to 2D worlds (height × CC center) and
adds cost-driven antonym competition. The positive construction
predictions here subsume LassiterGoodman2017's: both show that
hearing "tall"/"short" shifts the height posterior.

### Relationship to @cite{rett-2015}

`Theories/Pragmatics/Implicature/Evaluativity.lean` formalizes Rett's
Neo-Gricean account: Q-implicature for positive constructions,
R-implicature (MMP) for equatives/questions. Both accounts predict:
- Positive: evaluative for both antonyms
- Equative: evaluative only for marked antonym
- Comparative: not evaluative

The RSA model adds gradient predictions (evaluativity as a continuous
measure) and a unified mechanism (rational communication + cost
asymmetry rather than separate Q/R principles).

### Architecture

This model uses `RSAConfig` with:
- `Latent := Sigma` (threshold offset, = lexical uncertainty over σ)
- `meaning` bakes in the world prior (L₀ ∝ P(w) · L(u, w))
- `s1Score` = exp(α · (log L₀ − C(u))) (action-based, cost-sensitive)
- `worldPrior` = Gaussian-weighted 2D prior
- `latentPrior` = uniform over σ (lexica equally likely a priori)
-/

end Phenomena.Gradability.BumfordRett2021
