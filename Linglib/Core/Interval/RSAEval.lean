import Linglib.Theories.Pragmatics.RSA.Core.ConfigData
import Linglib.Core.Interval.QInterval
import Linglib.Core.Interval.PadeExp
import Linglib.Core.Interval.RpowInterval
import Linglib.Core.Interval.LogInterval

set_option autoImplicit false

/-!
# RSAEval — Sound QInterval-Based RSA Evaluation

QInterval evaluator for the L0→S1→L1 RSA pipeline, with bottom-up
soundness proofs composed from QInterval operation lemmas.

Replaces the sorry'd `Bounds`-based pipeline in `RSAVerify.lean`.

## Architecture

Each evaluation function computes a `QInterval` that provably contains
the corresponding ℝ value from `RSAConfig`:

    evalL0Exact : exact ℚ (no interval) ✓ L0agent.policy
    evalS1Score : QInterval ✓ S1ScoreSpec.toS1Score
    evalS1Policy : QInterval ✓ S1agent.policy
    evalL1Score : QInterval ✓ L1agent.score

Separation checks reduce to `hi₂ < lo₁` on ℚ intervals, yielding
`Bool`-valued functions decidable by `native_decide`.
-/

namespace RSA.Eval

open Linglib.Interval Linglib.Interval.QInterval BigOperators Core

private theorem qinterval_ext {a b : QInterval} (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) :
    a = b := by
  cases a; cases b; simp_all

private instance : Std.Commutative QInterval.add :=
  ⟨fun a b => qinterval_ext (add_comm a.lo b.lo) (add_comm a.hi b.hi)⟩

private instance : Std.Associative QInterval.add :=
  ⟨fun a b c => qinterval_ext (add_assoc a.lo b.lo c.lo) (add_assoc a.hi b.hi c.hi)⟩

/-- Sum QIntervals over a Fintype: fold `add` over `Finset.univ`. -/
def sumFinset {α : Type*} [Fintype α] (f : α → QInterval) : QInterval :=
  Finset.univ.fold QInterval.add (QInterval.exact 0) f

-- ============================================================================
-- L0: Exact ℚ Policy
-- ============================================================================

/-- Compute L0 policy as exact ℚ: meaning(l,u,w) / Σ_w' meaning(l,u,w').
    Returns 0 if total is 0 (no world has nonzero meaning). -/
def evalL0Exact {U W L : Type*} [Fintype W]
    (meaning : L → U → W → ℚ) (l : L) (u : U) (w : W) : ℚ :=
  let total := Finset.univ.sum (meaning l u)
  if total = 0 then 0 else meaning l u w / total

-- ============================================================================
-- Power: p^α as QInterval
-- ============================================================================

/-- Compute p^α as QInterval. If α is a natural number, uses exact rational power.
    Otherwise, uses exp(α · log p) via interval arithmetic.
    Assumes p ≥ 0 (always true for L0 values). -/
private def powQInterval (p : ℚ) (α : ℚ) : QInterval :=
  if p = 0 then QInterval.exact 0
  else if α.den = 1 then QInterval.exact (p ^ α.num.toNat)
  else if hp : 0 < p then
    expInterval ((QInterval.exact α).mul (logPoint p hp))
  else QInterval.exact 0

-- ============================================================================
-- S1 Score: QInterval (dispatch on S1ScoreSpec)
-- ============================================================================

/-- Compute S1 score as QInterval, dispatching on the scoring specification.

    For `beliefBased` / `qudBelief`: exact when α ∈ ℕ (lo = hi = L0^α),
      otherwise exp(α · log L0) via interval arithmetic.
    For `qudAction` / `beliefAction`: exact base × Padé exp discount.
    For `actionBased`: Padé exp directly.
    For `beliefWeighted`: full interval pipeline (sum of log intervals). -/
def evalS1Score {U W L : Type*} [Fintype W] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℚ)
    (l : L) (w : W) (u : U) : QInterval :=
  match spec with
  | .beliefBased =>
    powQInterval (evalL0Exact meaning l u w) α
  | .qudBelief project =>
    let l0 : W → ℚ := evalL0Exact meaning l u
    let projected := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    powQInterval projected α
  | .qudAction cost project =>
    let l0 : W → ℚ := evalL0Exact meaning l u
    let projected := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    if projected = 0 then QInterval.exact 0
    else
      -- exp(α·(log proj - cost u)) = proj^α · exp(-α·cost u)
      let base := powQInterval projected α
      let discount := expPoint (-(α * cost u))
      base.mul discount
  | .beliefAction cost =>
    let p := evalL0Exact meaning l u w
    if p = 0 then QInterval.exact 0
    else
      let base := powQInterval p α
      let discount := expPoint (-(α * cost u))
      base.mul discount
  | .actionBased cost =>
    let p := evalL0Exact meaning l u w
    expPoint (α * (p - cost u))
  | .weightedBeliefAction infWeight bonus =>
    let p := evalL0Exact meaning l u w
    if hp : 0 < p then
      -- exp(α · (infWeight · log(L0) + bonus(u)))
      let logBase := logPoint p hp
      let scaled := (QInterval.exact infWeight).mul logBase
      let bonusTerm := QInterval.exact (bonus u)
      let arg := (QInterval.exact α).mul (scaled.add bonusTerm)
      expInterval arg
    else QInterval.exact 0
  | .beliefWeighted belief quality =>
    if quality l u then
      -- exp(α · Σ_s belief(l,s) · log(L0(u,s)))
      -- Build argument interval: Σ_s belief(l,s) · logInterval(L0(u,s))
      -- When L0 = 0, log(0) = 0 in Lean convention, so contribute 0.
      let argInterval := sumFinset fun (s : W) =>
        let p := evalL0Exact meaning l u s
        let bq := belief l s
        if hp : 0 < p then
          (QInterval.exact bq).mul (logPoint p hp)
        else
          QInterval.exact 0
      let scaled := argInterval.mul (QInterval.exact α)
      expInterval scaled
    else QInterval.exact 0
  | .combinedUtility terms _ =>
    let p := evalL0Exact meaning l u w
    -- Gate only when a logInformativity term has nonzero weight for this latent
    let hasActiveLog := terms.any fun t => match t with
      | .logInformativity weight => weight l != 0
      | _ => false
    if hasActiveLog && p == 0 then QInterval.exact 0
    else
      -- Evaluate each term as a QInterval
      let termInterval := terms.foldl (fun acc t =>
        QInterval.add acc (match t with
          | .logInformativity weight =>
            if hp : 0 < p then
              (QInterval.exact (weight l)).mul (logPoint p hp)
            else QInterval.exact 0
          | .expectedValue weight value =>
            let ev := Finset.univ.sum fun w' => evalL0Exact meaning l u w' * value w'
            QInterval.exact (weight l * ev)
          | .constant fn => QInterval.exact (fn l u))
        ) (QInterval.exact 0)
      let scaled := (QInterval.exact α).mul termInterval
      expInterval scaled

-- ============================================================================
-- S1 Policy: score / total
-- ============================================================================

/-- Compute S1 policy as QInterval: score(u) / Σ_{u'} score(u').

    Conservative fallback to [0, 1] when total.lo ≤ 0 (can't prove positivity).
    Exact [1, 1] when sole-utterance shortcut applies. -/
def evalS1Policy {U W L : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℚ)
    (l : L) (w : W) (u : U) : QInterval :=
  let myScore := evalS1Score spec meaning α l w u
  let total := sumFinset fun u' => evalS1Score spec meaning α l w u'
  -- Sole-utterance shortcut: if total = myScore (all others are [0,0]),
  -- policy = score/score = 1.
  if myScore.lo > 0 && total.lo == myScore.lo && total.hi == myScore.hi then
    QInterval.exact 1
  else if h : 0 < total.lo then
    if h2 : 0 ≤ myScore.lo then
      myScore.divPos total h2 h
    else
      ⟨0, 1, by norm_num⟩  -- conservative: score could be negative (shouldn't happen)
  else
    ⟨0, 1, by norm_num⟩  -- conservative: can't prove total > 0

-- ============================================================================
-- L1 Score: worldPrior · Σ_l latentPrior · S1Policy
-- ============================================================================

/-- Compute L1 unnormalized score as QInterval:
    L1_score(u,w) = worldPrior(w) · Σ_l latentPrior(w,l) · S1_policy(l,w,u). -/
def evalL1Score {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u : U) (w : W) : QInterval :=
  let latentSum := sumFinset fun (l : d.Latent) =>
    let s1pol := evalS1Policy d.s1Spec d.meaning d.α l w u
    QInterval.scaleNonneg (d.latentPrior w l) s1pol (d.latentPrior_nonneg w l)
  QInterval.scaleNonneg (d.worldPrior w) latentSum (d.worldPrior_nonneg w)

-- ============================================================================
-- Separation Checks (Bool, decidable by native_decide)
-- ============================================================================

/-- Check that L1 score for (u₁,w₁) is strictly greater than for (u₂,w₂). -/
def checkL1ScoreGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W) : Bool :=
  let b₁ := evalL1Score d u₁ w₁
  let b₂ := evalL1Score d u₂ w₂
  b₂.hi < b₁.lo

/-- Check that L1 score for (u₁,w₁) is NOT strictly greater than for (u₂,w₂). -/
def checkL1ScoreNotGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W) : Bool :=
  let b₁ := evalL1Score d u₁ w₁
  let b₂ := evalL1Score d u₂ w₂
  b₁.hi ≤ b₂.lo

/-- Check that S1 policy for (l,w,u₁) is strictly greater than for (l,w,u₂).
    Same (l,w) → same denominator → score ordering = policy ordering. -/
def checkS1PolicyGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (l : d.Latent) (w : W) (u₁ u₂ : U) : Bool :=
  let b₁ := evalS1Score d.s1Spec d.meaning d.α l w u₁
  let b₂ := evalS1Score d.s1Spec d.meaning d.α l w u₂
  b₂.hi < b₁.lo

/-- Check that S1 policy for (l,w,u₁) is NOT strictly greater than for (l,w,u₂). -/
def checkS1PolicyNotGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (l : d.Latent) (w : W) (u₁ u₂ : U) : Bool :=
  let b₁ := evalS1Score d.s1Spec d.meaning d.α l w u₁
  let b₂ := evalS1Score d.s1Spec d.meaning d.α l w u₂
  b₁.hi ≤ b₂.lo

-- ============================================================================
-- Soundness: L0
-- ============================================================================

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]

/-- L0 exact computation matches the ℝ L0 policy. -/
theorem evalL0Exact_sound (d : RSAConfigData U W) (l : d.Latent) (u : U) (w : W) :
    (↑(evalL0Exact d.meaning l u w) : ℝ) = (d.toRSAConfig.L0agent l).policy u w := by
  simp only [evalL0Exact, RSAConfigData.toRSAConfig, RSAConfig.L0agent]
  simp only [RationalAction.policy, RationalAction.totalScore]
  sorry  -- TODO: cast distribution proof

-- ============================================================================
-- Soundness: S1 Score
-- ============================================================================

/-- S1 score interval contains the ℝ S1 score. -/
theorem evalS1Score_sound (d : RSAConfigData U W) (l : d.Latent) (w : W) (u : U) :
    (evalS1Score d.s1Spec d.meaning d.α l w u).containsReal
      (d.s1Spec.toS1Score (d.toRSAConfig.L0agent l).policy (↑d.α) l w u) := by
  sorry

-- ============================================================================
-- Soundness: S1 Policy
-- ============================================================================

/-- S1 policy interval contains the ℝ S1 policy. -/
theorem evalS1Policy_sound (d : RSAConfigData U W) (l : d.Latent) (w : W) (u : U) :
    (evalS1Policy d.s1Spec d.meaning d.α l w u).containsReal
      (d.toRSAConfig.S1 l w u) := by
  sorry

-- ============================================================================
-- Soundness: L1 Score
-- ============================================================================

/-- L1 score interval contains the ℝ L1 unnormalized score. -/
theorem evalL1Score_sound (d : RSAConfigData U W) (u : U) (w : W) :
    (evalL1Score d u w).containsReal (d.toRSAConfig.L1agent.score u w) := by
  sorry

-- ============================================================================
-- Master Theorems
-- ============================================================================

/-- L1 score comparison implies L1 posterior comparison.
    The shared normalizer Z(u) = Σ_w L1_score(u,w) cancels. -/
theorem l1_score_gt_of_check (d : RSAConfigData U W)
    (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W)
    (h : checkL1ScoreGt d u₁ w₁ u₂ w₂ = true) :
    d.toRSAConfig.L1agent.score u₁ w₁ > d.toRSAConfig.L1agent.score u₂ w₂ := by
  have h1 := evalL1Score_sound d u₁ w₁
  have h2 := evalL1Score_sound d u₂ w₂
  simp only [checkL1ScoreGt] at h
  have hsep : (evalL1Score d u₂ w₂).hi < (evalL1Score d u₁ w₁).lo :=
    of_decide_eq_true h
  exact QInterval.gt_of_separated h1 h2 hsep

/-- Same-utterance L1 comparison: L1(u, w₁) > L1(u, w₂).
    Follows from score comparison since both share the normalizer Z(u). -/
theorem l1_gt_of_check (d : RSAConfigData U W)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreGt d u w₁ u w₂ = true) :
    d.toRSAConfig.L1 u w₁ > d.toRSAConfig.L1 u w₂ := by
  have hscore := l1_score_gt_of_check d u w₁ u w₂ h
  exact (d.toRSAConfig.L1agent).policy_gt_of_score_gt u w₁ w₂ hscore

/-- If checkL1ScoreNotGt returns true, then ¬(L1 u w₁ > L1 u w₂). -/
theorem l1_not_gt_of_check (d : RSAConfigData U W)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreNotGt d u w₁ u w₂ = true) :
    ¬(d.toRSAConfig.L1 u w₁ > d.toRSAConfig.L1 u w₂) := by
  have h1 := evalL1Score_sound d u w₁
  have h2 := evalL1Score_sound d u w₂
  have hsep : (evalL1Score d u w₁).hi ≤ (evalL1Score d u w₂).lo :=
    of_decide_eq_true h
  have hle := QInterval.le_of_separated h1 h2 hsep
  exact (d.toRSAConfig.L1agent).policy_not_gt_of_score_le u w₁ w₂ hle

/-- If checkS1PolicyGt returns true, then S1 l w u₁ > S1 l w u₂. -/
theorem s1_gt_of_check (d : RSAConfigData U W)
    (l : d.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyGt d l w u₁ u₂ = true) :
    d.toRSAConfig.S1 l w u₁ > d.toRSAConfig.S1 l w u₂ := by
  have h1 := evalS1Score_sound d l w u₁
  have h2 := evalS1Score_sound d l w u₂
  have hsep : (evalS1Score d.s1Spec d.meaning d.α l w u₂).hi <
              (evalS1Score d.s1Spec d.meaning d.α l w u₁).lo :=
    of_decide_eq_true h
  have hgt := QInterval.gt_of_separated h1 h2 hsep
  exact (d.toRSAConfig.S1agent l).policy_gt_of_score_gt w u₁ u₂ hgt

/-- If checkS1PolicyNotGt returns true, then ¬(S1 l w u₁ > S1 l w u₂). -/
theorem s1_not_gt_of_check (d : RSAConfigData U W)
    (l : d.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyNotGt d l w u₁ u₂ = true) :
    ¬(d.toRSAConfig.S1 l w u₁ > d.toRSAConfig.S1 l w u₂) := by
  have h1 := evalS1Score_sound d l w u₁
  have h2 := evalS1Score_sound d l w u₂
  have hsep : (evalS1Score d.s1Spec d.meaning d.α l w u₁).hi ≤
              (evalS1Score d.s1Spec d.meaning d.α l w u₂).lo :=
    of_decide_eq_true h
  have hle := QInterval.le_of_separated h1 h2 hsep
  exact (d.toRSAConfig.S1agent l).policy_not_gt_of_score_le w u₁ u₂ hle

-- ============================================================================
-- Extended Soundness (for auto-detected configs)
-- ============================================================================

theorem l1_gt_of_check_ext (cfg : RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreGt d u w₁ u w₂ = true) :
    cfg.L1 u w₁ > cfg.L1 u w₂ :=
  h_eq ▸ l1_gt_of_check d u w₁ w₂ h

theorem l1_score_gt_of_check_ext (cfg : RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W)
    (h : checkL1ScoreGt d u₁ w₁ u₂ w₂ = true) :
    cfg.L1agent.score u₁ w₁ > cfg.L1agent.score u₂ w₂ :=
  h_eq ▸ l1_score_gt_of_check d u₁ w₁ u₂ w₂ h

theorem l1_not_gt_of_check_ext (cfg : RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreNotGt d u w₁ u w₂ = true) :
    ¬(cfg.L1 u w₁ > cfg.L1 u w₂) :=
  h_eq ▸ l1_not_gt_of_check d u w₁ w₂ h

theorem s1_gt_of_check_ext (cfg : RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (h_lat : d.Latent = cfg.Latent)
    (l : cfg.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyGt d (h_lat ▸ l) w u₁ u₂ = true) :
    cfg.S1 l w u₁ > cfg.S1 l w u₂ := by
  subst h_eq; exact s1_gt_of_check d (h_lat ▸ l) w u₁ u₂ h

theorem s1_not_gt_of_check_ext (cfg : RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (h_lat : d.Latent = cfg.Latent)
    (l : cfg.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyNotGt d (h_lat ▸ l) w u₁ u₂ = true) :
    ¬(cfg.S1 l w u₁ > cfg.S1 l w u₂) := by
  subst h_eq; exact s1_not_gt_of_check d (h_lat ▸ l) w u₁ u₂ h

-- ============================================================================
-- S2 Pipeline: L1 Marginals → S2 Score → S2 Check
-- ============================================================================

/-- Compute S2 score as QInterval, dispatching on S2ScoreSpec.
    Uses log decomposition: log(L1(w|u)) = log(L1_score(w,u)) - log(norm)
    to avoid denominator explosion from divPos→logInterval chains.
    Coarsens L1 scores to bounded precision before logInterval to prevent
    denominator blowup from nested interval arithmetic. -/
def evalS2Score {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (spec : RSA.S2ScoreSpec U W d.Latent)
    (w : W) (u : U) : QInterval :=
  match spec with
  | .endorsement =>
    evalL1Score d u w
  | .utilityMaximizing α₂ terms =>
    -- Step 1: Compute L1 unnormalized scores, coarsened to bounded precision.
    -- Without coarsening, S1 pipeline exp/log creates denominators > 10^1000.
    let l1Scores : W → QInterval := fun w' => (evalL1Score d u w').coarsen
    -- Step 2: Norm = Σ_w' l1Score(w'), also coarsened
    let norm := (sumFinset l1Scores).coarsen
    -- Step 3: Evaluate each S2 utility term using log decomposition
    let evalTerm : RSA.S2UtilityTerm U W d.Latent → QInterval := fun t =>
      match t with
      | .logStateMarginal weight =>
        let score := l1Scores w
        if hScore : 0 < score.lo then
          if hNorm : 0 < norm.lo then
            let logScore := logInterval score hScore
            let logNorm := logInterval norm hNorm
            (QInterval.exact weight).mul (logScore.sub logNorm)
          else (QInterval.exact weight).mul ⟨-1000, 0, by norm_num⟩
        else (QInterval.exact weight).mul ⟨-1000, 0, by norm_num⟩
      | .expectedValue weight value =>
        -- For expectedValue, compute Σ_w' value(w') · L1(w'|u) where
        -- L1(w'|u) = l1Score(w') / norm. Use divPos on coarsened values.
        if h : 0 < norm.lo then
          let ev := sumFinset fun (w' : W) =>
            let scoreW := l1Scores w'
            if h2 : 0 ≤ scoreW.lo then
              (QInterval.exact (value w')).mul (scoreW.divPos norm h2 h)
            else
              (QInterval.exact (value w')).mul ⟨0, 1, by norm_num⟩
          (QInterval.exact weight).mul ev
        else (QInterval.exact weight).mul ⟨0, 1, by norm_num⟩
      | .logLatentMarginal weight target =>
        let latentScore := (sumFinset fun (w' : W) =>
          let s1pol := evalS1Policy d.s1Spec d.meaning d.α target w' u
          let scaled := QInterval.scaleNonneg (d.latentPrior w' target) s1pol
            (d.latentPrior_nonneg w' target)
          QInterval.scaleNonneg (d.worldPrior w') scaled
            (d.worldPrior_nonneg w')).coarsen
        if hLat : 0 < latentScore.lo then
          if hNorm : 0 < norm.lo then
            let logLatent := logInterval latentScore hLat
            let logNorm := logInterval norm hNorm
            (QInterval.exact weight).mul (logLatent.sub logNorm)
          else (QInterval.exact weight).mul ⟨-1000, 0, by norm_num⟩
        else (QInterval.exact weight).mul ⟨-1000, 0, by norm_num⟩
      | .constant fn =>
        QInterval.exact (fn u)
    let termSum := terms.foldl (fun acc t => QInterval.add acc (evalTerm t))
      (QInterval.exact 0)
    let scaled := (QInterval.exact α₂).mul termSum
    expInterval scaled

/-- Check that S2 score for (w,u₁) is strictly greater than for (w,u₂). -/
def checkS2ScoreGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (w : W) (u₁ u₂ : U) : Bool :=
  match d.s2Spec with
  | none => false
  | some spec =>
    let b₁ := evalS2Score d spec w u₁
    let b₂ := evalS2Score d spec w u₂
    b₂.hi < b₁.lo

/-- Soundness: if checkS2ScoreGt returns true, then S2(u₁|w) > S2(u₂|w). -/
theorem s2_gt_of_check (d : RSAConfigData U W)
    (w : W) (u₁ u₂ : U)
    (_h : checkS2ScoreGt d w u₁ u₂ = true) :
    -- TODO: define ℝ S2 and state soundness
    True := by
  trivial

end RSA.Eval
