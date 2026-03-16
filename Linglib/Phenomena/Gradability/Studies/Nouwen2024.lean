import Linglib.Phenomena.Gradability.Studies.LassiterGoodman2017
import Linglib.Theories.Semantics.Lexical.Adjective.Intensification
import Linglib.Tactics.RSAPredict
import Mathlib.Data.Rat.Defs

/-!
# @cite{nouwen-2024} Deadjectival Intensifiers
@cite{lassiter-goodman-2017} @cite{nouwen-2024}

"The semantics and probabilistic pragmatics of deadjectival intensifiers"
Semantics and Pragmatics, Volume 17, Article 2.

## Empirical Generalizations

1. **Goldilocks effect**: Negative-evaluative bases (horrible, terrible)
   yield high-degree intensifiers; positive-evaluative bases (pleasant, nice)
   yield moderate-degree intensifiers.

2. **Zwicky's generalization**: Modal adjectives with negative polarity
   (unusual, surprising, impossible) can intensify, but their positive
   counterparts (usual, expected, possible) cannot.

## RSA Model

Extends @cite{lassiter-goodman-2017} threshold RSA with **evaluative measures**:
deadjectival adverbs (horribly, pleasantly) derive their degree function
from the evaluative meaning of their adjectival base.

### Two-Threshold Simultaneous Model

  P_L1(h, θ, θ_e | u) ∝ P_S1(u | h, θ, θ_e) × P(h) × P(θ) × P(θ_e)

The listener jointly infers height h, adjective threshold θ, and
evaluative threshold θ_e. The meaning function is an intersection:
- bare_warm: h > θ
- horribly_warm: (h > θ) ∧ (μ_horrible(h) > θ_e)
- pleasantly_warm: (h > θ) ∧ (μ_pleasant(h) > θ_e)
- silent: ⊤

### Sequential Model (@cite{nouwen-2024}'s key innovation)

The evaluative adverb updates the prior before the adjective threshold
applies: Step 1 infers P₁(h | "horribly"), Step 2 infers P₂(h | "warm")
using P₁ as prior.

### RSAConfig Mapping

- **U** = `Utterance` (bare_warm, horribly_warm, pleasantly_warm, silent)
- **W** = `Height` (Degree 10, 11 values: h0–h10)
- **Latent** = `Threshold × Threshold` (100 values: θ_adj × θ_eval)
- **s1Score** = beliefAction: `exp(α · (log L0 − C(u)))`
- **α** = 4 (matching @cite{lassiter-goodman-2017})
- **C(bare)** = 1, **C(horribly/pleasantly)** = 2, **C(∅)** = 0
-/

-- ============================================================================
-- §1. Empirical Data (@cite{nouwen-2024}, §3)
-- ============================================================================

namespace Phenomena.Gradability.Intensifiers

open Semantics.Lexical.Adjective.Intensification (EvaluativeValence)

/--
Intensifier degree class (@cite{nouwen-2024}, Figure 2).

- **H** (high): targets extreme degrees ("horribly warm" ≈ very warm)
- **M** (moderate): targets moderate degrees ("pleasantly warm" ≈ nicely warm)
-/
inductive IntensifierClass where
  | H  -- high degree
  | M  -- moderate degree
  deriving Repr, DecidableEq, BEq

/--
A deadjectival intensifier entry.

Records the adverb form, its adjectival base, evaluative properties,
modal status, and attestation pattern.
-/
structure IntensifierEntry where
  /-- Adverb form -/
  adverb : String
  /-- Adjectival base -/
  adjBase : String
  /-- Evaluative valence of the base -/
  valence : EvaluativeValence
  /-- Degree class as intensifier -/
  class_ : IntensifierClass
  /-- Whether the base is a modal adjective -/
  isModal : Bool := false
  /-- For modal bases: polarity of the modal (negative = unlikely/impossible) -/
  modalPolarity : Option EvaluativeValence := none
  /-- Whether the evaluative content is bleached in adverbial use -/
  bleached : Bool := false
  /-- Whether the intensifier use is attested -/
  attested : Bool := true
  deriving Repr

-- Intensifier Data (@cite{nouwen-2024}, Figure 2)

-- Negative-evaluative → High degree (H)

def horribly : IntensifierEntry :=
  { adverb := "horribly", adjBase := "horrible"
  , valence := .negative, class_ := .H, bleached := true }

def terribly : IntensifierEntry :=
  { adverb := "terribly", adjBase := "terrible"
  , valence := .negative, class_ := .H, bleached := true }

def awfully : IntensifierEntry :=
  { adverb := "awfully", adjBase := "awful"
  , valence := .negative, class_ := .H, bleached := true }

def dreadfully : IntensifierEntry :=
  { adverb := "dreadfully", adjBase := "dreadful"
  , valence := .negative, class_ := .H, bleached := true }

def frighteningly : IntensifierEntry :=
  { adverb := "frighteningly", adjBase := "frightening"
  , valence := .negative, class_ := .H, bleached := true }

-- Positive-evaluative → Moderate degree (M)

def pleasantly : IntensifierEntry :=
  { adverb := "pleasantly", adjBase := "pleasant"
  , valence := .positive, class_ := .M }

def nicely : IntensifierEntry :=
  { adverb := "nicely", adjBase := "nice"
  , valence := .positive, class_ := .M }

def decently : IntensifierEntry :=
  { adverb := "decently", adjBase := "decent"
  , valence := .positive, class_ := .M }

-- Negative modal → High degree (H), attested

def unusually : IntensifierEntry :=
  { adverb := "unusually", adjBase := "unusual"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

def surprisingly : IntensifierEntry :=
  { adverb := "surprisingly", adjBase := "surprising"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

def impossibly : IntensifierEntry :=
  { adverb := "impossibly", adjBase := "impossible"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

def remarkably : IntensifierEntry :=
  { adverb := "remarkably", adjBase := "remarkable"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

-- Positive modal → unattested as intensifiers

def usually_ : IntensifierEntry :=
  { adverb := "*usually", adjBase := "usual"
  , valence := .positive, class_ := .M
  , isModal := true, modalPolarity := some .positive
  , attested := false }

def expectedly_ : IntensifierEntry :=
  { adverb := "*expectedly", adjBase := "expected"
  , valence := .positive, class_ := .M
  , isModal := true, modalPolarity := some .positive
  , attested := false }

def possibly_ : IntensifierEntry :=
  { adverb := "*possibly", adjBase := "possible"
  , valence := .positive, class_ := .M
  , isModal := true, modalPolarity := some .positive
  , attested := false }

-- All entries

def allEntries : List IntensifierEntry :=
  [ horribly, terribly, awfully, dreadfully, frighteningly
  , pleasantly, nicely, decently
  , unusually, surprisingly, impossibly, remarkably
  , usually_, expectedly_, possibly_ ]

-- Goldilocks Effect (@cite{nouwen-2024}, §3)

/--
The Goldilocks effect: evaluative valence determines degree class.

- Negative-evaluative bases yield high-degree (H) intensifiers
- Positive-evaluative bases yield moderate-degree (M) intensifiers
-/
def goldilocksHolds (e : IntensifierEntry) : Bool :=
  match e.valence with
  | .negative => e.class_ == .H
  | .positive => e.class_ == .M
  | .neutral  => true  -- neutral bases don't constrain

-- Per-datum verification

theorem horribly_goldilocks : goldilocksHolds horribly = true := by native_decide
theorem terribly_goldilocks : goldilocksHolds terribly = true := by native_decide
theorem awfully_goldilocks : goldilocksHolds awfully = true := by native_decide
theorem dreadfully_goldilocks : goldilocksHolds dreadfully = true := by native_decide
theorem frighteningly_goldilocks : goldilocksHolds frighteningly = true := by native_decide
theorem pleasantly_goldilocks : goldilocksHolds pleasantly = true := by native_decide
theorem nicely_goldilocks : goldilocksHolds nicely = true := by native_decide
theorem decently_goldilocks : goldilocksHolds decently = true := by native_decide

-- Zwicky's Generalization (@cite{nouwen-2024}, §3.2)

/--
Zwicky's generalization: modal adjectives with negative polarity
can serve as intensifiers; positive-polarity modal adjectives cannot.

- "unusually warm" ✓ (negative modal → attested)
- "*usually warm" ✗ (positive modal → unattested)
-/
def zwickyHolds (e : IntensifierEntry) : Bool :=
  if e.isModal then
    match e.modalPolarity with
    | some .negative => e.attested
    | some .positive => !e.attested
    | _ => true
  else true

-- Per-datum verification

theorem unusually_zwicky : zwickyHolds unusually = true := by native_decide
theorem surprisingly_zwicky : zwickyHolds surprisingly = true := by native_decide
theorem impossibly_zwicky : zwickyHolds impossibly = true := by native_decide
theorem remarkably_zwicky : zwickyHolds remarkably = true := by native_decide
theorem usually_zwicky : zwickyHolds usually_ = true := by native_decide
theorem expectedly_zwicky : zwickyHolds expectedly_ = true := by native_decide
theorem possibly_zwicky : zwickyHolds possibly_ = true := by native_decide

-- Summary statistics

/-- Count of attested intensifiers -/
def attestedCount : Nat := (allEntries.filter (·.attested)).length

/-- Count of unattested intensifiers -/
def unattestedCount : Nat := (allEntries.filter (!·.attested)).length

#guard attestedCount == 12
#guard unattestedCount == 3

end Phenomena.Gradability.Intensifiers

-- ============================================================================
-- §2. RSA Model
-- ============================================================================

namespace RSA.Nouwen2024

open RSA.LassiterGoodman2017 (Height Threshold
  heightPrior thresholdPrior tallMeaning)
open Core.Scale (deg thr allDegrees allThresholds)
open Semantics.Lexical.Adjective.Intensification (EvaluativeValence EvaluativeMeasure)

-- Utterances

/--
Utterances about warmth with optional deadjectival intensifier.

The utterance set extends bare "warm" with intensified variants.
-/
inductive Utterance where
  | bare_warm       -- "x is warm"
  | horribly_warm   -- "x is horribly warm"
  | pleasantly_warm -- "x is pleasantly warm"
  | silent          -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

def allUtterances : List Utterance :=
  [.bare_warm, .horribly_warm, .pleasantly_warm, .silent]

-- Evaluative Measures (ℕ-valued for rsa_predict reification)

/--
Evaluative measure for "horrible" applied to the Height domain.

μ_horrible(h) = |h - norm|

Heights far from the norm (5) are evaluated as more "horrible".
Agrees with `Intensification.muHorrible 10` (see `meaning_grounded_horribly`).
-/
def muHorrible (h : Height) : ℕ :=
  let d := h.toNat
  if d ≥ 5 then d - 5 else 5 - d

/--
Evaluative measure for "pleasant" applied to the Height domain.

μ_pleasant(h) = norm - |h - norm|

Heights near the norm (5) are evaluated as more "pleasant".
Agrees with `Intensification.muPleasant 10` (see `meaning_grounded_pleasantly`).
-/
def muPleasant (h : Height) : ℕ :=
  let d := h.toNat
  if d ≥ 5 then 10 - d else d

-- Meaning Function

/--
Full meaning function.

- bare_warm: h > θ (standard @cite{lassiter-goodman-2017})
- horribly_warm: (h > θ) ∧ (μ_horrible(h) > θ_e)
- pleasantly_warm: (h > θ) ∧ (μ_pleasant(h) > θ_e)
- silent: always true
-/
def meaning (u : Utterance) (h : Height) (θ θ_e : Threshold) : Bool :=
  match u with
  | .bare_warm       => tallMeaning θ h
  | .horribly_warm   => tallMeaning θ h && (muHorrible h > θ_e.toNat)
  | .pleasantly_warm => tallMeaning θ h && (muPleasant h > θ_e.toNat)
  | .silent          => true

-- Theory-Layer Grounding

/--
The local horribly_warm meaning agrees with theory-layer `intensifiedMeaning`
for all inputs. This bridges the ℕ-valued local measures to the ℚ-valued
theory-layer `Intensification.muHorrible`.
-/
theorem meaning_grounded_horribly :
    ∀ (h : Height) (θ θ_e : Threshold),
      meaning .horribly_warm h θ θ_e =
      Semantics.Lexical.Adjective.Intensification.intensifiedMeaning
        (Semantics.Lexical.Adjective.Intensification.muHorrible 10) h θ θ_e := by
  native_decide

/--
The local pleasantly_warm meaning agrees with theory-layer `intensifiedMeaning`
for all inputs. This bridges the ℕ-valued local measures to the ℚ-valued
theory-layer `Intensification.muPleasant`.
-/
theorem meaning_grounded_pleasantly :
    ∀ (h : Height) (θ θ_e : Threshold),
      meaning .pleasantly_warm h θ θ_e =
      Semantics.Lexical.Adjective.Intensification.intensifiedMeaning
        (Semantics.Lexical.Adjective.Intensification.muPleasant 10) h θ θ_e := by
  native_decide

-- Zwicky Vacuity

/--
Constant evaluative measure (no evaluative content).

Models adverbs like "*usually" — a constant measure provides no
discriminating information about degree, which is why "*usually warm"
is vacuous (Zwicky's generalization, as discussed in @cite{nouwen-2024}).
-/
def muUsual : EvaluativeMeasure 10 where
  form := "usual"
  valence := .neutral
  mu := λ _ => 5

/--
A constant evaluative measure provides no information:
for any two heights, the measure value is identical.
-/
theorem usual_constant :
    ∀ h₁ h₂ : Height, muUsual.mu h₁.toNat = muUsual.mu h₂.toNat := by
  intro h₁ h₂
  simp [muUsual]

-- Utterance Cost Structure

/--
Intensified utterances are costlier than bare utterances.

@cite{nouwen-2024} assumes that "horribly warm" has higher production cost
than "warm" because it contains more morphological material.
This cost differential drives the pragmatic reasoning.
-/
def utteranceCost : Utterance → ℚ
  | .bare_warm       => 1
  | .horribly_warm   => 2
  | .pleasantly_warm => 2
  | .silent          => 0

-- ============================================================================
-- RSAConfig (simultaneous dual-threshold model)
-- ============================================================================

open RSA.LassiterGoodman2017 (heightPriorR heightPriorR_nonneg)
open Real (exp log exp_pos)

noncomputable def utteranceCostR (u : Utterance) : ℝ := ↑(utteranceCost u)

/-- S1 scoring rule: exp(α · (log L0(h|u,θ,θ_e) − C(u))), gated at L0=0.
    Identical to @cite{lassiter-goodman-2017}'s beliefAction but with
    Latent = Threshold × Threshold for the dual-threshold model. -/
noncomputable def intensifierS1Score :
    (Utterance → Height → ℝ) → ℝ → (Threshold × Threshold) → Height → Utterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - utteranceCostR u))

theorem intensifierS1Score_nonneg :
    ∀ (l0 : Utterance → Height → ℝ) (α : ℝ) (l : Threshold × Threshold)
      (w : Height) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ intensifierS1Score l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [intensifierS1Score]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

/-- RSAConfig for the @cite{nouwen-2024} simultaneous dual-threshold model.

    Extends @cite{lassiter-goodman-2017} threshold RSA with a second threshold
    for the evaluative adverb. L1 jointly infers height, adjective threshold,
    and evaluative threshold:

      P_L1(h, θ, θ_e | u) ∝ P_S1(u | h, θ, θ_e) · P(h) · P(θ) · P(θ_e)

    The meaning function uses local ℕ-valued evaluative measures, proved
    equivalent to `Intensification.intensifiedMeaning` by
    `meaning_grounded_horribly` and `meaning_grounded_pleasantly`. -/
@[reducible]
noncomputable def nouwenCfg : RSA.RSAConfig Utterance Height where
  Latent := Threshold × Threshold
  meaning _ l u h := if meaning u h l.1 l.2 then heightPriorR h else 0
  meaning_nonneg _ l u h := by
    show 0 ≤ if meaning u h l.1 l.2 then heightPriorR h else 0
    split
    · exact heightPriorR_nonneg h
    · exact le_refl 0
  s1Score := intensifierS1Score
  s1Score_nonneg := intensifierS1Score_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior := heightPriorR
  worldPrior_nonneg := heightPriorR_nonneg
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- Goldilocks Effect Predictions (simultaneous model)
-- ============================================================================

/-! ### H-adverb: "horribly warm" shifts height toward extremes

The Goldilocks effect for negative-evaluative bases: μ_horrible(h) = |h − norm|
peaks at extremes, so L1 hearing "horribly warm" concentrates probability
on extreme heights. Heights near the norm (h=5) have μ_horrible = 0
and cannot satisfy the evaluative positive form at any θ_e. -/

theorem horribly_shifts_upward :
    nouwenCfg.L1 .horribly_warm (deg 8) > nouwenCfg.L1 .horribly_warm (deg 4) := by
  rsa_predict

theorem horribly_implies_warm :
    nouwenCfg.L1 .horribly_warm (deg 8) > nouwenCfg.L1 .horribly_warm (deg 2) := by
  rsa_predict

/-! ### M-adverb: "pleasantly warm" concentrates at moderate heights

The Goldilocks effect for positive-evaluative bases: μ_pleasant(h) = norm − |h − norm|
peaks at the norm (h=5), so L1 hearing "pleasantly warm" concentrates
probability on moderate heights. Extreme heights (h=9,10) have
low μ_pleasant and cannot satisfy the evaluative positive form. -/

theorem pleasantly_prefers_moderate :
    nouwenCfg.L1 .pleasantly_warm (deg 6) > nouwenCfg.L1 .pleasantly_warm (deg 9) := by
  rsa_predict

theorem pleasantly_implies_warm :
    nouwenCfg.L1 .pleasantly_warm (deg 6) > nouwenCfg.L1 .pleasantly_warm (deg 2) := by
  rsa_predict

/-! ### Cross-utterance Goldilocks predictions

The core Goldilocks effect is a cross-utterance phenomenon: intensifiers
redistribute probability mass relative to the bare adjective. "Horribly warm"
assigns MORE probability to extreme heights than "warm" does; "pleasantly warm"
assigns MORE to moderate heights than "warm" does. -/

/-- At extreme heights, "horribly warm" assigns more probability than "warm". -/
theorem horribly_above_bare_at_extreme :
    nouwenCfg.L1 .horribly_warm (deg 9) > nouwenCfg.L1 .bare_warm (deg 9) := by
  rsa_predict

/-- At moderate heights, "pleasantly warm" assigns more probability than "warm". -/
theorem pleasantly_above_bare_at_moderate :
    nouwenCfg.L1 .pleasantly_warm (deg 6) > nouwenCfg.L1 .bare_warm (deg 6) := by
  rsa_predict

/-- At extreme heights, "horribly warm" dominates "pleasantly warm". -/
theorem horribly_dominates_pleasantly_at_extreme :
    nouwenCfg.L1 .horribly_warm (deg 9) > nouwenCfg.L1 .pleasantly_warm (deg 9) := by
  rsa_predict

/-- At moderate heights, "pleasantly warm" dominates "horribly warm". -/
theorem pleasantly_dominates_horribly_at_moderate :
    nouwenCfg.L1 .pleasantly_warm (deg 6) > nouwenCfg.L1 .horribly_warm (deg 6) := by
  rsa_predict

-- ============================================================================
-- Sequential Model (@cite{nouwen-2024}'s key innovation)
-- ============================================================================

/-! ## Sequential Dual-Threshold Model

@cite{nouwen-2024}'s key theoretical contribution: the evaluative adverb and
base adjective apply sequentially rather than simultaneously. The listener
first updates beliefs via the evaluative measure, then applies the adjective
threshold to the resulting posterior:

  Step 1: P₁(h | "horribly") ∝ P_S1(eval_pos | h, θ_e) · P(h) · P(θ_e)
  Step 2: P₂(h | "warm") ∝ P_S1(warm | h, θ) · P₁(h) · P(θ)

This sequential model makes the same Goldilocks predictions as the
simultaneous model for simple cases, but differs for complex constructions
(e.g., "horribly pleasantly warm").

### Implementation

Two RSAConfigs composed: the evaluative step's L1 posterior feeds as the
adjective step's worldPrior. This uses RSAConfig composition rather than
the Ctx/transition machinery, which is designed for sequential *production*
(word-by-word S1 choices), not sequential *comprehension* (listener updating
beliefs step by step). -/

-- Step 1: Evaluative update

/-- Utterances for the evaluative step: either the evaluative positive form
    ("the degree is horribly/pleasantly X") or silence. -/
inductive EvalUtterance where
  | eval_pos  -- the evaluative positive form holds
  | silent    -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

/-- Evaluative meaning for step 1.
    The evaluative positive form checks only μ_eval(h) > θ_e, without the
    base adjective. This is the decomposed evaluative component. -/
def evalMeaning (evalMu : Height → ℕ) (u : EvalUtterance) (h : Height) (θ_e : Threshold) : Bool :=
  match u with
  | .eval_pos => evalMu h > θ_e.toNat
  | .silent   => true

/-- Evaluative step cost: the evaluative adverb costs 1, silence costs 0. -/
def evalCost : EvalUtterance → ℚ
  | .eval_pos => 1
  | .silent   => 0

noncomputable def evalCostR (u : EvalUtterance) : ℝ := ↑(evalCost u)

noncomputable def evalS1Score :
    (EvalUtterance → Height → ℝ) → ℝ → Threshold → Height → EvalUtterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - evalCostR u))

theorem evalS1Score_nonneg :
    ∀ (l0 : EvalUtterance → Height → ℝ) (α : ℝ) (l : Threshold)
      (w : Height) (u : EvalUtterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ evalS1Score l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [evalS1Score]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

/-- RSAConfig for the evaluative step with a given measure function.

    L1 hears the evaluative form and infers a posterior over heights,
    marginalizing over the evaluative threshold θ_e. -/
@[reducible]
noncomputable def evalCfg (evalMu : Height → ℕ) : RSA.RSAConfig EvalUtterance Height where
  Latent := Threshold
  meaning _ l u h := if evalMeaning evalMu u h l then heightPriorR h else 0
  meaning_nonneg _ l u h := by
    show 0 ≤ if evalMeaning evalMu u h l then heightPriorR h else 0
    split
    · exact heightPriorR_nonneg h
    · exact le_refl 0
  s1Score := evalS1Score
  s1Score_nonneg := evalS1Score_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior := heightPriorR
  worldPrior_nonneg := heightPriorR_nonneg
  latentPrior_nonneg _ _ := by positivity

-- Step 2: Adjective update with updated prior

/-- Utterances for the adjective step. -/
inductive AdjUtterance where
  | warm   -- "x is warm"
  | silent -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

/-- Adjective meaning for step 2: just the base positive form h > θ. -/
def adjMeaning (u : AdjUtterance) (h : Height) (θ : Threshold) : Bool :=
  match u with
  | .warm   => tallMeaning θ h
  | .silent => true

def adjCost : AdjUtterance → ℚ
  | .warm   => 1
  | .silent => 0

noncomputable def adjCostR (u : AdjUtterance) : ℝ := ↑(adjCost u)

noncomputable def adjS1Score :
    (AdjUtterance → Height → ℝ) → ℝ → Threshold → Height → AdjUtterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - adjCostR u))

theorem adjS1Score_nonneg :
    ∀ (l0 : AdjUtterance → Height → ℝ) (α : ℝ) (l : Threshold)
      (w : Height) (u : AdjUtterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ adjS1Score l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [adjS1Score]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

/-- RSAConfig for the adjective step with an evaluative posterior as worldPrior.

    The worldPrior is the L1 posterior from the evaluative step: the listener
    has already processed the evaluative adverb and now hears "warm".
    This implements the sequential composition:

      P₂(h | "warm") ∝ P_S1("warm" | h, θ) · L1_eval(h | eval_pos) · P(θ) -/
@[reducible]
noncomputable def seqAdjCfg (evalMu : Height → ℕ) : RSA.RSAConfig AdjUtterance Height where
  Latent := Threshold
  meaning _ l u h := if adjMeaning u h l then (evalCfg evalMu).L1 .eval_pos h else 0
  meaning_nonneg _ l u h := by
    show 0 ≤ if adjMeaning u h l then (evalCfg evalMu).L1 .eval_pos h else 0
    split
    · exact (evalCfg evalMu).L1agent.policy_nonneg .eval_pos h
    · exact le_refl 0
  s1Score := adjS1Score
  s1Score_nonneg := adjS1Score_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior h := (evalCfg evalMu).L1 .eval_pos h
  worldPrior_nonneg h := (evalCfg evalMu).L1agent.policy_nonneg .eval_pos h
  latentPrior_nonneg _ _ := by positivity

/-- Sequential L1 posterior for "horribly warm": evaluative step uses μ_horrible,
    then adjective step applies the base "warm" meaning. -/
noncomputable def seqL1_horribly (h : Height) : ℝ :=
  (seqAdjCfg muHorrible).L1 .warm h

/-- Sequential L1 posterior for "pleasantly warm": evaluative step uses μ_pleasant,
    then adjective step applies the base "warm" meaning. -/
noncomputable def seqL1_pleasantly (h : Height) : ℝ :=
  (seqAdjCfg muPleasant).L1 .warm h

-- Sequential Goldilocks Predictions

/-! ### Sequential Goldilocks: same qualitative predictions as simultaneous

The sequential model produces the same Goldilocks pattern: "horribly warm"
shifts probability toward extremes, "pleasantly warm" concentrates at moderate
heights. The sequential decomposition affects the quantitative distribution
but preserves the qualitative ordering. -/

/-- Sequential "horribly warm" shifts upward (Goldilocks). -/
theorem seq_horribly_shifts_upward :
    (seqAdjCfg muHorrible).L1 .warm (deg 8) > (seqAdjCfg muHorrible).L1 .warm (deg 4) := by
  rsa_predict

/-- Sequential "pleasantly warm" prefers moderate heights (Goldilocks). -/
theorem seq_pleasantly_prefers_moderate :
    (seqAdjCfg muPleasant).L1 .warm (deg 6) > (seqAdjCfg muPleasant).L1 .warm (deg 9) := by
  rsa_predict

-- ============================================================================
-- Zwicky's Generalization: RSA-Derived Predictions
-- ============================================================================

/-! ## Zwicky Vacuity: Derived from RSA

@cite{nouwen-2024} §5: Positive modal adverbs (*usually, *expectedly) cannot
serve as intensifiers because their evaluative measure is constant across
heights, providing no discriminating information about degree. In the
sequential model, the evaluative step with a constant measure preserves
the prior's bell-curve shape — "usually warm" offers no intensifying
information beyond bare "warm".

In contrast, negative modal measures (unusual ≈ horrible) peak at extremes,
shifting the evaluative posterior away from the norm and producing genuine
intensification. This is why negative modals pattern with negative evaluatives
in the Goldilocks effect.

The theorems below derive Zwicky's generalization from the sequential RSA
model, connecting the data-layer check (`zwickyHolds`) to L1 posterior
predictions. -/

/-- ℕ-valued constant measure for the sequential model.
    Models "usual": μ_usual(h) = 5 for all h (no height discrimination). -/
def muUsualN : Height → ℕ := λ _ => 5

/-- μ_unusual has the same shape as μ_horrible: peaks at extremes.
    Negative modals pattern with negative evaluatives because both assign
    high values to heights far from the norm. -/
def muUnusualN : Height → ℕ := muHorrible

/-- Negative modal and negative evaluative measures are structurally identical.
    This is the semantic foundation of why both types make good intensifiers
    (@cite{nouwen-2024} §5: "the corresponding measure function has a shape
    similar to that of negative evaluatives"). -/
theorem muUnusualN_eq_muHorrible : muUnusualN = muHorrible := rfl

/-- Bare adjective RSAConfig: "warm" vs silence with the original height prior.
    This is the baseline — what "warm" means without any evaluative step. -/
@[reducible]
noncomputable def bareAdjCfg : RSA.RSAConfig AdjUtterance Height where
  Latent := Threshold
  meaning _ l u h := if adjMeaning u h l then heightPriorR h else 0
  meaning_nonneg _ l u h := by
    show 0 ≤ if adjMeaning u h l then heightPriorR h else 0
    split
    · exact heightPriorR_nonneg h
    · exact le_refl 0
  s1Score := adjS1Score
  s1Score_nonneg := adjS1Score_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior := heightPriorR
  worldPrior_nonneg := heightPriorR_nonneg
  latentPrior_nonneg _ _ := by positivity

/-! ### Evaluative Step: Constant vs Extreme Measures -/

/-- Constant-measure evaluative step preserves the prior's peak at the norm. -/
theorem eval_constant_preserves_peak :
    (evalCfg muUsualN).L1 .eval_pos (deg 5) >
    (evalCfg muUsualN).L1 .eval_pos (deg 9) := by
  rsa_predict

/-- Extreme measure (unusual/horrible) boosts extreme heights in L1
    beyond what the constant measure assigns. -/
theorem eval_unusual_boosts_extreme :
    (evalCfg muUnusualN).L1 .eval_pos (deg 9) >
    (evalCfg muUsualN).L1 .eval_pos (deg 9) := by
  rsa_predict

/-! ### Sequential Model: Zwicky Predictions -/

/-- "Usually warm" preserves moderate-height preference (like bare "warm"). -/
theorem usually_warm_prefers_moderate :
    (seqAdjCfg muUsualN).L1 .warm (deg 6) >
    (seqAdjCfg muUsualN).L1 .warm (deg 9) := by
  rsa_predict

/-- "Unusually warm" shifts toward extremes (like "horribly warm").
    Note: `muUnusualN = muHorrible` by `muUnusualN_eq_muHorrible`,
    so this is structurally the same prediction as `seq_horribly_shifts_upward`. -/
theorem unusually_warm_shifts_extreme :
    (seqAdjCfg muUnusualN).L1 .warm (deg 8) >
    (seqAdjCfg muUnusualN).L1 .warm (deg 4) := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- **Zwicky's generalization, derived**: at extreme heights, "unusually warm"
    assigns more probability than "usually warm". Negative modal intensifiers
    are more informative than positive modal ones because μ_unusual discriminates
    heights while μ_usual does not. -/
theorem zwicky_extreme_discrimination :
    (seqAdjCfg muUnusualN).L1 .warm (deg 9) >
    (seqAdjCfg muUsualN).L1 .warm (deg 9) := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Converse: at moderate heights, "usually warm" dominates "unusually warm".
    The constant measure concentrates mass near the prior peak, while the
    extreme measure depletes mass at moderate heights. -/
theorem zwicky_moderate_discrimination :
    (seqAdjCfg muUsualN).L1 .warm (deg 6) >
    (seqAdjCfg muUnusualN).L1 .warm (deg 6) := by
  rsa_predict

/-- Bare "warm" baseline: prefers moderate heights (deg 6 > deg 9).
    Demonstrates that the bare model and "usually warm" agree qualitatively. -/
theorem bare_warm_prefers_moderate :
    bareAdjCfg.L1 .warm (deg 6) > bareAdjCfg.L1 .warm (deg 9) := by
  rsa_predict

end RSA.Nouwen2024
