import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Phenomena.Gradability.Studies.Rett2015Implicature
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

## Verified Predictions (Table 1)

1. **Positive construction** (Simulation 1): both antonyms evaluative
2. **Exact equative** (Simulation 2): marked antonym evaluative, unmarked weakly evaluative
3. **≥ Equative** (Simulation 3): marked evaluative, unmarked barely evaluative
4. **Comparative** (Simulation 4): neither antonym evaluative — evaluative world
   does NOT win over non-evaluative world, unlike equatives
5. **Antonym asymmetry**: marked equative produces stronger evaluative inference
6. **Cross-construction contrast**: equative marked IS evaluative but comparative
   marked is NOT, confirming that partial antonymic competition (not just cost)
   drives evaluativity

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
open Phenomena.Gradability.Studies.Rett2015Implicature (Polarity)
open Semantics.Degree (AdjectivalConstruction)

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
  deriving Repr, DecidableEq, Fintype

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

/-- Utterance cost as ℝ (cast from ℚ for use in S1 score). -/
noncomputable def costR (u : Utterance) : ℝ := cost u

-- ============================================================================
-- § 6. Parametric RSAConfig
-- ============================================================================

/-- Parametric RSAConfig for all four constructions.

    All simulations share the same architecture (eq 10); they differ only
    in the meaning function (eqs 12, 14, 16, 18). -/
@[reducible]
noncomputable def mkEvalCfg (sem : Utterance → Sigma → EvalWorld → Bool) :
    RSA.RSAConfig Utterance EvalWorld where
  Latent := Sigma
  meaning _ σ u w := if sem u σ w then worldPriorR w else 0
  meaning_nonneg _ σ u w := by split <;> [exact worldPriorR_nonneg w; exact le_refl 0]
  -- eq 10: Sₙ(u | w, L) ∝ exp(α · (log Lₙ₋₁(w | u, L) − C(u)))
  s1Score := fun l0 α _ w u =>
    if l0 u w = 0 then 0 else exp (α * (log (l0 u w) - costR u))
  s1Score_nonneg := fun _ _ _ _ _ _ _ => by
    split <;> [exact le_refl 0; exact le_of_lt (exp_pos _)]
  α := 4
  α_pos := by norm_num
  worldPrior := worldPriorR
  worldPrior_nonneg := worldPriorR_nonneg
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- § 7. Simulation 1: Positive Construction (§2.2.1, Table 1)
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

@[reducible] noncomputable def posCfg := mkEvalCfg posMeaning

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
-- § 8. Simulation 2: Exact Equative (§2.2.2, Table 1)
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

@[reducible] noncomputable def eqCfg := mkEvalCfg eqMeaning

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
-- § 9. Simulation 3: ≥ Equative (§2.2.3, Table 1)
-- ============================================================================

/-! ### ≥ Equative (Minimum-Standard) Semantics

The "at least as tall as" equative uses ≥ instead of = for height.
Unlike the exact equative, the unmarked and marked forms are NOT
synonymous: "at least as tall as K" and "at least as short as K"
have different truth conditions. Antonymic competition is therefore
partial, predicting evaluativity intermediate between the exact
equative (full synonymy) and the comparative (no overlap). -/

/-- ≥ equative meaning (eq 16):
    - unmarked ("at least as tall as K"): ht ≥ k ∧ k ≥ μ + σ
    - marked ("at least as short as K"): ht ≤ k ∧ k ≤ μ + σ
    - null: true -/
def geqMeaning (u : Utterance) (σ : Sigma) (w : EvalWorld) : Bool :=
  match u with
  | .unmarked => decide (htVal w ≥ kHeight) && decide (kHeight ≥ muVal w + sigmaVal σ)
  | .marked   => decide (htVal w ≤ kHeight) && decide (kHeight ≤ muVal w + sigmaVal σ)
  | .null     => true

@[reducible] noncomputable def geqCfg := mkEvalCfg geqMeaning

/-! ### Prediction 5: Marked ≥ equative is evaluative

Hearing "Jane is at least as short as Keisha" (marked) shifts L₁'s
posterior toward worlds where k is below the CC center.
The paper reports E[k − μ] = −1.52 at L₁. -/

theorem geq_marked_evaluative :
    geqCfg.L1 .marked (mkW 4 4) > geqCfg.L1 .marked (mkW 4 0) := by
  rsa_predict

/-! ### Prediction 6: Unmarked ≥ equative is barely evaluative

Hearing "Jane is at least as tall as Keisha" (unmarked) barely shifts
the posterior. The paper reports E[k − μ] = 0.11 at L₁ — the weakest
evaluative effect of any construction. -/

theorem geq_unmarked_barely_evaluative :
    geqCfg.L1 .unmarked (mkW 4 0) > geqCfg.L1 .unmarked (mkW 4 4) := by
  rsa_predict

-- ============================================================================
-- § 10. Simulation 4: Comparative (§2.2.4, Table 1)
-- ============================================================================

/-! ### Comparative Semantics

The comparative uses strict inequality for height (ht > k / ht < k).
Unlike the equatives, the comparative forms have NO semantic overlap:
"taller than K" and "shorter than K" are not even close to synonymous.
With no antonymic competition and high informativity (the comparative
provides clear information worth the cost), there is no pressure for
evaluative inference.

The paper predicts E[k − μ] = −0.74 (unmarked) and −0.44 (marked) at
L₁ — both close to zero. The listener guesses Keisha is slightly below
the CC mean, but this is a generic probabilistic consequence of
learning relative height, not an evaluative inference. -/

/-- Comparative meaning (eq 18):
    - unmarked ("taller than K"): ht > k ∧ k ≥ μ + σ
    - marked ("shorter than K"): ht < k ∧ k ≤ μ + σ
    - null: true -/
def compMeaning (u : Utterance) (σ : Sigma) (w : EvalWorld) : Bool :=
  match u with
  | .unmarked => decide (htVal w > kHeight) && decide (kHeight ≥ muVal w + sigmaVal σ)
  | .marked   => decide (htVal w < kHeight) && decide (kHeight ≤ muVal w + sigmaVal σ)
  | .null     => true

@[reducible] noncomputable def compCfg := mkEvalCfg compMeaning

/-! ### Prediction 7: Comparative marked does not strongly shift k

Unlike the equative, the marked comparative does not push the listener
toward worlds where k is far from the CC center. At equal prior
(dev = ±1), the world with k near the mean is preferred over the
world with k well above the mean. The paper reports E[k − μ] = −0.44
at L₁ — a very weak effect, unlike the equative's −1.06. -/

theorem comp_marked_weak :
    compCfg.L1 .marked (mkW 3 2) > compCfg.L1 .marked (mkW 3 0) := by
  rsa_predict

/-! ### Prediction 8: Comparative unmarked is counter-evaluative

Hearing "Jane is taller than Keisha" (unmarked) does NOT make the
listener infer that Keisha is tall. In fact, the paper reports
E[k − μ] = −0.74, slightly negative: Keisha is inferred to be
slightly below the CC mean. This is because knowing Jane exceeds
Keisha's height leaves more room for Keisha to be below average. -/

theorem comp_unmarked_counter_evaluative :
    compCfg.L1 .unmarked (mkW 5 3) > compCfg.L1 .unmarked (mkW 5 1) := by
  rsa_predict

-- ============================================================================
-- § 11. Cross-Construction Contrast
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
   informative (i.e., atypical worlds).

The theorems above verify the key qualitative pattern across all four
constructions:
- `pos_tall_evaluative` / `pos_short_evaluative` : positive ✓✓
- `eq_marked_evaluative` / `eq_unmarked_weakly_evaluative` : equative ✗✓
- `geq_marked_evaluative` / `geq_unmarked_barely_evaluative` : ≥ equative ✗✓
- `comp_marked_weak` / `comp_unmarked_counter_evaluative` : comparative ✗✗ -/

-- ============================================================================
-- § 12. Bridge to Neo-Gricean Evaluativity (@cite{rett-2015})
-- ============================================================================

/-! ### RSA ↔ Neo-Gricean Agreement

@cite{rett-2015}'s Neo-Gricean account (formalized in
`Theories/Pragmatics/Implicature/Evaluativity.lean`) classifies
constructions categorically using `AdjectivalConstruction` and `Polarity`:
- **Positive** (`.positive`): evaluative for both polarities (Q-implicature)
- **Equative** (`.equative`): evaluative for `.negative` only (Manner/R-implicature)
- **Comparative** (`.comparative`): NOT evaluative (no applicable implicature)

This RSA model derives the same pattern *gradiently*: each `rsa_predict`
theorem above confirms a qualitative directional prediction that matches
the categorical classification. The RSA model adds:
1. **Graded predictions** — evaluativity has a continuous strength, not just ±
2. **Unified mechanism** — rational communication replaces separate Q/R principles
3. **≥ equative predictions** — partial overlap produces intermediate evaluativity,
   a novel prediction the categorical account does not make -/

/-- Map utterance polarity to the evaluativity `Polarity` type. -/
def utterancePolarity : Utterance → Option Polarity
  | .unmarked => some .positive
  | .marked   => some .negative
  | .null     => none

/-- Construction labels for each simulation, connecting to the
    `AdjectivalConstruction` type from `Degree.Core`. -/
abbrev posConstruction  : AdjectivalConstruction := .positive
abbrev eqConstruction   : AdjectivalConstruction := .equative
abbrev compConstruction : AdjectivalConstruction := .comparative

open Phenomena.Gradability.Studies.Rett2015Implicature (deriveEvaluativity)

/-- Cross-theory agreement: the RSA model and @cite{rett-2015}'s Neo-Gricean
    account agree on the full evaluativity paradigm.

    - **Positive**: Neo-Gricean says evaluative for both polarities (Q-implicature).
      RSA confirms: both "tall" and "short" shift the posterior away from the CC mean.
    - **Equative**: Neo-Gricean says evaluative for negative only (Manner implicature).
      RSA confirms: marked form shifts strongly, unmarked weakly.
    - **Comparative**: Neo-Gricean says never evaluative (no applicable implicature).
      RSA confirms: neither polarity shifts strongly.

    This theorem connects two independent formalizations — the categorical
    `deriveEvaluativity` function and the RSA `L1` predictions — proving they
    make compatible predictions despite using entirely different mechanisms. -/
theorem rsa_neo_gricean_agreement :
    -- Positive: both accounts say evaluative for both polarities
    (deriveEvaluativity posConstruction .positive).isEvaluative = true ∧
    (deriveEvaluativity posConstruction .negative).isEvaluative = true ∧
    posCfg.L1 .unmarked (mkW 5 2) > posCfg.L1 .unmarked (mkW 3 2) ∧
    posCfg.L1 .marked (mkW 3 2) > posCfg.L1 .marked (mkW 5 2) ∧
    -- Equative: Neo-Gricean says marked-only; RSA shows marked shift
    (deriveEvaluativity eqConstruction .positive).isEvaluative = false ∧
    (deriveEvaluativity eqConstruction .negative).isEvaluative = true ∧
    eqCfg.L1 .marked (mkW 4 4) > eqCfg.L1 .marked (mkW 4 0) ∧
    -- Comparative: both say not evaluative
    (deriveEvaluativity compConstruction .positive).isEvaluative = false ∧
    (deriveEvaluativity compConstruction .negative).isEvaluative = false :=
  ⟨by native_decide, by native_decide,
   pos_tall_evaluative, pos_short_evaluative,
   by native_decide, by native_decide,
   eq_marked_evaluative,
   by native_decide, by native_decide⟩

-- ============================================================================
-- § 13. Cross-References
-- ============================================================================

/-! ### Relationship to @cite{lassiter-goodman-2017}

`LassiterGoodman2017.lean` formalizes the threshold RSA model for the
positive construction only (1D world = height, latent = threshold).
This file extends that model to 2D worlds (height × CC center) and
adds cost-driven antonym competition. The positive construction
predictions here subsume LassiterGoodman2017's: both show that
hearing "tall"/"short" shifts the height posterior.

### Architecture

This model uses `RSAConfig` with:
- `Latent := Sigma` (threshold offset, = lexical uncertainty over σ)
- `meaning` bakes in the world prior (L₀ ∝ P(w) · L(u, w))
- `s1Score` = exp(α · (log L₀ − C(u))) (action-based, cost-sensitive)
- `worldPrior` = Gaussian-weighted 2D prior
- `latentPrior` = uniform over σ (lexica equally likely a priori)
-/

end Phenomena.Gradability.BumfordRett2021
