import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Studies.Nouwen2024
import Linglib.Studies.LassiterGoodman2017PMF

/-!
# [nouwen-2024] on mathlib `PMF` — chained-RSA structural shell

[nouwen-2024] [lassiter-goodman-2017]

[nouwen-2024] ("The semantics and probabilistic pragmatics of
deadjectival intensifiers", *Semantics & Pragmatics* 17:2, 1-45, 2024)
gives an intersective semantic analysis of intensified adjectives
(*horribly warm*, *pleasantly warm*) plus a chained-Bayesian pragmatic
update. This file formalises a **structural skeleton** of the §4 Bayesian
machinery, with explicit acknowledgment of what it does and does not
capture.

## Scope (honest reckoning, post-audit)

The file's `priorAfterEvalPos` + `seqAdjL1HorriblyWarm` correctly
implement the **two-update Bayesian chain** of [nouwen-2024] Eq. 73
(p. 2:41): first update Π = stage-1 L1 at `.eval_pos`, then second update
ρ = stage-2 L1 with Π as prior. The L&G "two priors" pattern (Π enters
both stage-2 L0 via `L0LassiterGoodman` AND stage-2 L1 via `PMF.posterior`)
is structurally faithful.

**However, the file is NOT a faithful Nouwen 2024 formalisation.** It is
"L&G two-priors chain typed against `Height`", missing three core pieces
of Nouwen's actual contribution:

1. **Eq. 44/45 intersecting positive forms — NOT formalised.** Nouwen's
   *novel* semantic proposal (paper p. 2:21) is the conjunction
   `(μ_A(x) ≥ θ_i) ∧ (μ_D(λw.μ_A(x)(@) = μ_A(x)(w)) ≥ θ_j)`. The second
   conjunct is a Wheeler-style **factive embedding** of the proposition
   "x has its actual measure" — explicitly motivated as the fix for the
   soup-too-warm-to-eat counterexample to Nouwen 2010 Eq. 35. The file's
   stage-1 evaluative meaning predicates `muHorrible` of heights directly,
   without the propositional embedding. Without Eq. 44b's factive layer,
   the prediction is L&G's, not Nouwen's. Stub theorem
   `eq_44b_factive_embedding_NOT_FORMALISED` below documents the gap.
2. **Eq. 49 QUD partition `Q^A_X` — NOT formalised.** Nouwen's σ/ρ are
   defined over equivalence classes `[w]_~^A_X` where `w ~^A_X w' iff
   μ_A(x)(w) ≈ μ_A(x)(w')` (with explicit granularity). The file
   operates over raw `Height` with no quotient/equivalence relation. At
   small Height-cardinality the partition collapses to identity and the
   shortcut is vacuously fine for the toy example, but the file cannot
   extend to Nouwen's Figures 4-7 construction (which depends on the
   QUD partition + measure-function-on-cells distinction). Stub theorem
   `eq_49_qud_partition_NOT_FORMALISED` below documents the gap.
3. **`muHorrible` is monotone-decreasing, NOT Nouwen's `f(x) = x²`
   quadratic.** Nouwen's Figure 4(b) (p. 2:27) handcrafts
   `f(x) = x²` so BOTH extremes (low + high temperature) are evaluated as
   horrible — this is what produces the Goldilocks shape in Figures 5-7.
   The file's `muHorrible (deg 0) = 3, deg 5 = 0` is monotone in
   `h.toNat`, NOT quadratic-in-distance-from-mean. The file's
   `seq_horribly_shifts_upward_pmf` is therefore the WRONG headline
   shape for Goldilocks: it captures monotone shift, not extremes-vs-
   middle. UNVERIFIED-NOTE: the bundled `Nouwen2024.lean`'s `muHorrible`
   was originally built for the bundled-API Goldilocks demo and may
   itself need correction.

**Also not captured (substrate gaps):**
- **Zwicky's generalisation** (paper §5, the third of Nouwen's three
  desiderata p. 2:15) — the vacuity argument for positive modal adverbs
  (*usually*, *normally*, *possibly*) is entirely absent. No modal lex,
  no `usually` utterance, no theorem stating that `usually warm ≈ warm`
  because the adverb's update is vacuous against a normality-shaped prior.
- **Positive-valence Goldilocks half** (Figure 8, *pleasantly warm* →
  narrow moderate peak) — only the negative-valence case is built in
  the PMF face. The bundled `Nouwen2024.lean` has the positive-valence
  symmetric pair; lifting it to PMF requires rebuilding stage-2 with
  `muPleasant` + corrected `f`.

## Connection to `LassiterGoodman2017PMF.lean`

[nouwen-2024] §4 explicitly adopts the [lassiter-goodman-2017]
RSA framework and modifies it to sequential two-update inference (vs L&G's
single-step joint posterior over `(world, threshold)`). The structural
relationship:

* L&G 2017 PMF: single-step `posterior κ μ b` against a uniform threshold prior
* Nouwen 2024 PMF (this file): chained `posterior κ₂ (posterior κ₁ μ b₁) b₂`

The chained-posterior decomposition lemma `PMF.posterior_chained_lt_iff_score_lt`
in `Core/Probability/Posterior.lean` (modeled on mathlib's
`Mathlib.Probability.Kernel.Posterior.posterior_comp`) characterises this
shape; the headline below uses it.

## Cross-framework positioning (linglib's "make incompatibilities visible")

[nouwen-2024] §3.1 surveys four contenders for intensifier semantics,
Nouwen's own intersection proposal being the FOURTH:

1. Wheeler 1972 factive: `horrible(λw. μ_warm(t)(w) = μ_warm(t)(@))` (Eq. 32)
2. Morzycki 2008 extreme: `horribly warm` = "horrible how *extremely* warm"
3. Nouwen 2010 existential boost: `∃d[μ_warm(t)(@) ≥ d ∧ horrible(λw.μ_warm(t)(w) ≥ d)]` (Eq. 33-35)
4. Nouwen 2024 intersection: Eq. 44/45 (this file's nominal target)

NONE of (1)-(3) are formalised in linglib. `Semantics/Gradability/Intensification.lean`
ships only Nouwen 2024's intersection as `intensifiedMeaning` — silently
adopting one of the four contenders as if uncontested. The cross-framework
auditor flagged this as a broader linglib gap; the fix is an
`IntensifierSemantics` typeclass at the Theory level (deferred — out of
scope for this file).

## Proof obligations

- `seq_horribly_shifts_upward_pmf` — PROVEN structurally (§5b ratio
  cancellation): the height factor cancels in each per-threshold speaker,
  collapsing the marginals to mass-monotone sums over the licensed
  thresholds; informativity (`gval 1 > gval 0`) beats the 2:1 prior ratio.
  No numeric reflection.
- `eq_44b_factive_embedding_NOT_FORMALISED` — Nouwen's novel contribution.
- `eq_49_qud_partition_NOT_FORMALISED` — explicit substrate gap.

## Reused from `Nouwen2024.lean` (bundled formalization)

* `Height`, `Threshold`, `EvalUtterance`, `evalMeaning`, `muHorrible`,
  `tallMeaning`, `heightPrior` — data + Boolean meanings
* `evalCost`, `adjCost` — cost values
-/

set_option autoImplicit false

namespace RSA.Nouwen2024.PMF

open scoped ENNReal
open RSA.Nouwen2024
open Degree (deg thr)
/-! ## §1. Height prior as a PMF -/

/-- Height prior weights as `ℝ≥0∞`. Reuses `heightPrior : Height → ℚ` from
`Nouwen2024.lean` (a discretized bell curve, weights summing to 52). -/
noncomputable def heightPriorENN (h : Height) : ℝ≥0∞ :=
  ENNReal.ofReal (heightPrior h : ℝ)

theorem heightPriorENN_pos (h : Height) : heightPriorENN h ≠ 0 := by
  unfold heightPriorENN
  rw [ENNReal.ofReal_ne_zero_iff]
  exact_mod_cast by unfold heightPrior; split <;> norm_num

theorem heightPriorENN_finite (h : Height) : heightPriorENN h ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The height prior as a normalized `PMF Height`. Built directly from
mathlib's `PMF.normalize` with the Fintype-shape tsum discharges:
`tsum_ne_zero_iff` (witness form) and `tsum_ne_top_of_fintype`. -/
noncomputable def heightPriorPMF : PMF Height :=
  PMF.normalize heightPriorENN
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨deg 3, heightPriorENN_pos _⟩)
    (ENNReal.tsum_ne_top_of_fintype heightPriorENN_finite)

theorem heightPriorPMF_pos (h : Height) : heightPriorPMF h ≠ 0 := by
  unfold heightPriorPMF
  rw [PMF.normalize_apply]
  exact mul_ne_zero (heightPriorENN_pos h)
    (ENNReal.inv_ne_zero.mpr (ENNReal.tsum_ne_top_of_fintype heightPriorENN_finite))

/-! ## §2. ValidThreshold subtype + conversion -/

/-- The latent threshold restricted to values with non-empty `.eval_pos`
extension under `muHorrible` / `muPleasant`. Both measures have max value
3, so `θ.toNat ∈ {0,1,2}` are the only thresholds that produce non-empty
literal-listener extensions (per ## Empty-extension in the module
docstring). -/
abbrev ValidThreshold : Type := Fin 3

/-- Convert `ValidThreshold` into the original `Threshold = Fin 6` type
(via `Fin.castLE 3 ≤ 6`). -/
def validToThreshold (vt : ValidThreshold) : Threshold :=
  ⟨vt.castLE (by omega)⟩

/-- Uniform prior over `ValidThreshold`. -/
noncomputable def thresholdPriorPMF : PMF ValidThreshold :=
  PMF.uniformOfFintype ValidThreshold

/-! ## §3. Stage 1 — evaluative L0/S1/L1 (under `muHorrible`)

Pattern: Boolean `evalLex` → L&G L0 with `heightPriorPMF` (`L0LassiterGoodman`) →
`S1Belief` rpow speaker with `evalCostFactor` and α=4 → marginalize over
`ValidThreshold` via `marginalizeKernel` → `PMF.posterior`. -/

/-- Evaluative Boolean lex at threshold `θ` (just argument-reordering of
`Nouwen2024.evalMeaning`). Type matches `L0LassiterGoodman`'s shape. -/
def evalLex (evalMu : Height → ℕ) (θ : Threshold) (u : EvalUtterance) (h : Height) : Bool :=
  evalMeaning evalMu u h θ

/-- Witness for the `L0LassiterGoodman` positivity hypothesis at any valid
θ and any utterance: `deg 0` is in every extension. For `.silent` trivially;
for `.eval_pos` because `muHorrible (deg 0) = 3 > θ.toNat` for θ ∈ {0,1,2}. -/
theorem evalLex_horrible_extension_pos (vt : ValidThreshold) (u : EvalUtterance) :
    (∑' h, heightPriorPMF h *
      (if evalLex muHorrible (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨deg 0, ?_⟩
  -- Show: heightPriorPMF (deg 0) * indicator > 0
  cases u
  · -- .eval_pos: indicator = (3 > θ.toNat); for vt ∈ Fin 3, this is true
    show heightPriorPMF _ *
      (if evalLex muHorrible (validToThreshold vt) .eval_pos (deg 0) then
        (1 : ℝ≥0∞) else 0) ≠ 0
    -- Reduce: muHorrible (deg 0) = 3 (since deg 0 has toNat = 0, i.e. d < 3, so muHorrible = 3 - 0 = 3)
    have : evalLex muHorrible (validToThreshold vt) .eval_pos (deg 0) = true := by
      unfold evalLex evalMeaning
      simp only []
      have : muHorrible (deg 0) = 3 := by
        unfold muHorrible
        rfl
      rw [this]
      decide +revert
    rw [this]
    simp only [if_true, mul_one]
    exact heightPriorPMF_pos _
  · -- .silent: always true
    show heightPriorPMF _ *
      (if evalLex muHorrible (validToThreshold vt) .silent (deg 0) then
        (1 : ℝ≥0∞) else 0) ≠ 0
    have : evalLex muHorrible (validToThreshold vt) .silent (deg 0) = true := rfl
    rw [this]
    simp only [if_true, mul_one]
    exact heightPriorPMF_pos _

/-- Stage 1 literal listener under `muHorrible` at valid threshold `vt`. -/
noncomputable def evalL0_horribleAt (vt : ValidThreshold) :
    EvalUtterance → PMF Height :=
  fun u => RSA.L0LassiterGoodman heightPriorPMF
    (evalLex muHorrible (validToThreshold vt)) u
    (evalLex_horrible_extension_pos vt u)

/-- Cost factor for the rpow speaker form: `cost u → exp(-α · cost u)`.
Hardcodes Nouwen's `evalCost` (eval_pos = 1, silent = 0) and α = 4. -/
noncomputable def evalCostFactor (u : EvalUtterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-4 * (evalCost u : ℝ)))

theorem evalCostFactor_pos (u : EvalUtterance) : evalCostFactor u ≠ 0 := by
  unfold evalCostFactor
  rw [ENNReal.ofReal_ne_zero_iff]
  exact Real.exp_pos _

theorem evalCostFactor_finite (u : EvalUtterance) : evalCostFactor u ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Stage 1 speaker under `muHorrible` at valid threshold `vt`. Per-θ
S1Belief, normalized over utterances at each Height. Positivity discharges
via `.silent` witness using `RSA.L0LassiterGoodman_apply_of_meaning_true`
(which says: `L0` at `.silent` equals the prior unchanged, since
`evalLex .silent` is identically `true`). -/
noncomputable def evalSpeaker_horribleAt (vt : ValidThreshold) (w : Height) : PMF EvalUtterance :=
  RSA.S1Belief (evalL0_horribleAt vt) evalCostFactor 4 w
    -- Positivity: at `.silent` witness, L0 = heightPriorPMF (positive); cost ≠ 0; rpow ≠ 0.
    (by
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨.silent, ?_⟩
      have hL0 : evalL0_horribleAt vt .silent w = heightPriorPMF w := by
        unfold evalL0_horribleAt
        exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
      rw [hL0]
      apply mul_ne_zero _ (evalCostFactor_pos .silent)
      have hpos : 0 < heightPriorPMF w := pos_iff_ne_zero.mpr (heightPriorPMF_pos w)
      have hntop : heightPriorPMF w ≠ ⊤ := PMF.apply_ne_top _ _
      exact (ENNReal.rpow_pos hpos hntop).ne')
    -- Finiteness: each summand is finite (Fintype + rpow of bounded base).
    (by
      apply ENNReal.tsum_ne_top_of_fintype
      intro u
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
        (evalCostFactor_finite u))

/-- Marginalize Stage 1 speaker over `ValidThreshold` (uniform prior).
Eq 70's marginalization step, restricted to thresholds with non-empty
extension. -/
noncomputable def evalSpeakerMarginalHorrible : Height → PMF EvalUtterance :=
  RSA.marginalizeKernel thresholdPriorPMF (fun vt w => evalSpeaker_horribleAt vt w)

/-- Stage 1 L1 = pragmatic listener via `PMF.posterior`. The prior is
`heightPriorPMF`; the speaker kernel is the threshold-marginalized
`evalSpeakerMarginalHorrible`. -/
noncomputable def evalL1Horrible (u : EvalUtterance) : PMF Height :=
  PMF.posterior evalSpeakerMarginalHorrible heightPriorPMF u
    -- Marginal positivity: pick (h, u) = (deg 0, _). heightPriorPMF (deg 0) > 0;
    -- speaker (deg 0) u > 0 because at vt = 0, L0(u | deg 0, vt=0) is positive
    -- (deg 0 is in extension for both .silent and .eval_pos at θ=0).
    (PMF.marginal_ne_zero _ _ _ (heightPriorPMF_pos (deg 0)) (by
      -- evalSpeakerMarginalHorrible (deg 0) u ≠ 0
      -- = PMF.bind thresholdPriorPMF (fun vt => evalSpeaker_horribleAt vt (deg 0)) u
      -- = ∑' vt, thresholdPriorPMF vt * evalSpeaker_horribleAt vt (deg 0) u
      -- Pick vt = 0; both factors positive.
      unfold evalSpeakerMarginalHorrible
      rw [RSA.marginalizeKernel_apply]
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨0, ?_⟩
      apply mul_ne_zero
      · -- thresholdPriorPMF 0 = 1/3 ≠ 0
        rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]
        simp
      · -- evalSpeaker_horribleAt 0 (deg 0) u ≠ 0 via S1Belief_apply_ne_zero_of_pos
        -- with hL0 from mem_support_L0LassiterGoodman_iff (matches priorAfterEvalPos discharge)
        have hL0 : evalL0_horribleAt 0 u (deg 0) ≠ 0 := by
          unfold evalL0_horribleAt
          rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
          refine ⟨heightPriorPMF_pos _, ?_⟩
          -- For .eval_pos: muHorrible(deg 0) = 3 > 0 = true
          -- For .silent: always true
          cases u
          · -- .eval_pos
            simp only [evalLex, evalMeaning, decide_eq_true_eq]
            show muHorrible (deg 0) > 0
            decide
          · -- .silent
            rfl
        unfold evalSpeaker_horribleAt
        exact RSA.S1Belief_apply_ne_zero_of_pos
          (evalL0_horribleAt 0) evalCostFactor 4 (deg 0) _ _ hL0 (evalCostFactor_pos u)))

/-! ## §4. Sequential composition: Π = stage 1 L1 at `.eval_pos`

This Π becomes the prior for stage 2 (Nouwen eq 73). The L&G "two priors"
pattern then has Π appearing both inside the stage-2 L0 (via
`L0LassiterGoodman Π adjLex`) and outside in the stage-2 L1 (via
`PMF.posterior _ Π`). -/

/-- Π — stage 1 L1 at `.eval_pos`, used as stage 2's prior. -/
noncomputable def priorAfterEvalPos : PMF Height :=
  evalL1Horrible .eval_pos

/-! ## §5. Stage 2 — adjective L0/S1/L1 (under `tallMeaning`/`warm`)

Mirrors stage 1 with prior `Π` instead of `heightPriorPMF`, and with
the bare-warm Boolean `tallMeaning` instead of `evalMeaning`. -/

/-- Adjective Boolean lex at threshold `θ`. Reuses Nouwen's `AdjUtterance`
(`warm | silent`) and `adjMeaning`. -/
def adjLex (θ : Threshold) (u : RSA.Nouwen2024.AdjUtterance) (h : Height) : Bool :=
  RSA.Nouwen2024.adjMeaning u h θ

/-- **Restricted version** of "Π is positive": Π is positive at heights with
non-zero `muHorrible` (the eval listener concludes the height is in the
"horribly" extension). At heights where `muHorrible h = 0` (e.g. `deg 3`),
Π(h) = 0 — those are precisely the heights "ruled out" by the .eval_pos
observation. The unrestricted `priorAfterEvalPos_pos` would be FALSE at deg 3,
which was the bug in the original sorry'd statement. -/
theorem priorAfterEvalPos_pos_at_horrible_pos {h : Height} (hpos : 0 < muHorrible h) :
    priorAfterEvalPos h ≠ 0 := by
  unfold priorAfterEvalPos evalL1Horrible
  rw [← PMF.mem_support_iff, PMF.mem_support_posterior_iff]
  refine ⟨heightPriorPMF_pos h, ?_⟩
  -- evalSpeakerMarginalHorrible h .eval_pos ≠ 0: witness vt = 0, then S1Belief positive.
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply]
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨0, ?_⟩
  apply mul_ne_zero
  · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
  · -- evalSpeaker_horribleAt 0 h .eval_pos ≠ 0 via S1Belief_apply_ne_zero_of_pos
    -- with hL0 from mem_support_L0LassiterGoodman_iff (using muHorrible h > 0 = vt.toNat)
    have hL0 : evalL0_horribleAt 0 .eval_pos h ≠ 0 := by
      unfold evalL0_horribleAt
      rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
      refine ⟨heightPriorPMF_pos h, ?_⟩
      -- evalLex muHorrible (validToThreshold 0) .eval_pos h = true; reduce via evalMeaning
      simp only [evalLex, evalMeaning, decide_eq_true_eq]
      -- Goal: muHorrible h > (validToThreshold 0).toNat. The latter = 0 by rfl.
      show muHorrible h > 0
      exact hpos
    unfold evalSpeaker_horribleAt
    exact RSA.S1Belief_apply_ne_zero_of_pos
      (evalL0_horribleAt 0) evalCostFactor 4 h _ _ hL0 (evalCostFactor_pos .eval_pos)

/-- Witness for stage 2's `L0LassiterGoodman` positivity: at threshold
θ ∈ {0,1,2} and utterance `.warm`, the height `deg 5` (or any h with
`tallMeaning θ h = true`) gives non-zero contribution. -/
theorem adjLex_warm_extension_pos (vt : ValidThreshold) (u : RSA.Nouwen2024.AdjUtterance) :
    (∑' h, priorAfterEvalPos h *
      (if adjLex (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  -- For .warm at threshold vt, deg 5 satisfies (5 > vt.toNat)
  -- For .silent, deg 0 (or any h) trivially true
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨deg 5, ?_⟩
  cases u
  · -- .warm: tallMeaning vt (deg 5) = (5 > vt.toNat); for vt ∈ Fin 3, true
    show priorAfterEvalPos _ *
      (if adjLex (validToThreshold vt) .warm (deg 5) then
        (1 : ℝ≥0∞) else 0) ≠ 0
    have : adjLex (validToThreshold vt) .warm (deg 5) = true := by
      unfold adjLex RSA.Nouwen2024.adjMeaning RSA.Nouwen2024.tallMeaning
      -- Goal: positiveMeaning (deg 5) (validToThreshold vt) = true, i.e. vt < 5 as Degree
      -- vt : Fin 3 means vt.val ∈ {0,1,2}; case-bash with decide.
      fin_cases vt <;> decide
    rw [this]
    simp only [if_true, mul_one]
    exact priorAfterEvalPos_pos_at_horrible_pos (by decide)
  · -- .silent: always true
    show priorAfterEvalPos _ * _ ≠ 0
    have : adjLex (validToThreshold vt) .silent (deg 5) = true := rfl
    rw [this]
    simp only [if_true, mul_one]
    exact priorAfterEvalPos_pos_at_horrible_pos (by decide)

/-- Stage 2 literal listener with prior Π (the L&G "two priors" pattern:
Π enters here, AND will enter again at the L1 stage). -/
noncomputable def adjL0_warmAt (vt : ValidThreshold) : RSA.Nouwen2024.AdjUtterance → PMF Height :=
  fun u => RSA.L0LassiterGoodman priorAfterEvalPos
    (adjLex (validToThreshold vt)) u (adjLex_warm_extension_pos vt u)

noncomputable def adjCostFactor (u : RSA.Nouwen2024.AdjUtterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-4 * (RSA.Nouwen2024.adjCost u : ℝ)))

/-- Stage 2 speaker under `tallMeaning` at valid threshold `vt`.

**Conditional fallback at degenerate worlds**: at world `w` where `Π(w) = 0`
(e.g., `w = deg 3` since `muHorrible(deg 3) = 0` so deg 3 has zero posterior
under "eval_pos"), all `adjL0_warmAt vt u w = 0` (reweight against
zero-mass prior gives zero), so `S1Belief`'s positivity hypothesis fails.
At those degenerate worlds the speaker is irrelevant to the L1 (since
the prior is 0 there too), so we fall back to a vacuous uniform PMF.
This is the bundled API's `if l0 = 0 then 0` guard, lifted to the type
level via `dite`. -/
noncomputable def adjSpeaker_warmAt (vt : ValidThreshold) (w : Height) :
    PMF (RSA.Nouwen2024.AdjUtterance) :=
  if h_pos : (∑' u, ((adjL0_warmAt vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 then
    RSA.S1Belief (adjL0_warmAt vt) adjCostFactor 4 w h_pos
      (ENNReal.tsum_ne_top_of_fintype fun u =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top))
  else
    -- Vacuous fallback at degenerate w (where Π(w) = 0). PMF.pure picks any
    -- AdjUtterance arbitrarily; doesn't affect downstream L1 since prior is 0.
    PMF.pure .silent

/-- Marginalize Stage 2 speaker over `ValidThreshold`. -/
noncomputable def adjSpeakerMarginal : Height → PMF AdjUtterance :=
  RSA.marginalizeKernel thresholdPriorPMF (fun vt w => adjSpeaker_warmAt vt w)

/-- **Sequential L1 for "horribly warm".** Stage 2 L1 with prior Π
(= stage 1 L1 at `.eval_pos`). The L&G "two priors" pattern: Π appears in
stage 2's L0 (via `L0LassiterGoodman` inside `adjL0_warmAt`) AND in stage
2's L1 (the `priorAfterEvalPos` argument to `PMF.posterior` here). -/
noncomputable def seqAdjL1HorriblyWarm (u : RSA.Nouwen2024.AdjUtterance) : PMF Height :=
  PMF.posterior adjSpeakerMarginal priorAfterEvalPos u
    -- Marginal positivity: pick witness h = deg 5. priorAfterEvalPos (deg 5) > 0
    -- (since muHorrible(deg 5) = 2 > 0); adjSpeakerMarginal (deg 5) u > 0 because
    -- at vt = 0, the conditional fallback uses S1Belief (non-degenerate at deg 5)
    -- and L0(u | deg 5, vt=0) is positive (priorAfterEvalPos(deg 5) > 0 + indicator
    -- true at deg 5 for both .warm and .silent under vt=0).
    (PMF.marginal_ne_zero _ _ _
      (priorAfterEvalPos_pos_at_horrible_pos (h := deg 5) (by decide)) (by
      unfold adjSpeakerMarginal
      rw [RSA.marginalizeKernel_apply]
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨0, ?_⟩
      apply mul_ne_zero
      · -- thresholdPriorPMF 0 ≠ 0
        rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
      · -- adjSpeaker_warmAt 0 (deg 5) u ≠ 0
        -- adjSpeaker_warmAt uses conditional fallback. At deg 5, the fallback
        -- branch is S1Belief (non-degenerate). Need to discharge h_pos for the dite.
        unfold adjSpeaker_warmAt
        -- Goal: (if h_pos then S1Belief ... else uniform) u ≠ 0
        -- At deg 5, h_pos holds because adjL0(.warm | deg 5, vt=0) > 0.
        have hL0_warm : adjL0_warmAt 0 .warm (deg 5) ≠ 0 := by
          unfold adjL0_warmAt
          rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
          refine ⟨priorAfterEvalPos_pos_at_horrible_pos (by decide : (0:ℕ) < muHorrible (deg 5)), ?_⟩
          -- adjLex (validToThreshold 0) .warm (deg 5) = true
          show RSA.Nouwen2024.adjMeaning .warm (deg 5) (validToThreshold 0) = true
          decide
        have h_dite : (∑' u', ((adjL0_warmAt 0) u' (deg 5) : ℝ≥0∞) ^ (4 : ℝ) *
            adjCostFactor u') ≠ 0 := by
          apply ENNReal.summable.tsum_ne_zero_iff.mpr
          refine ⟨.warm, ?_⟩
          apply mul_ne_zero _ (by
            unfold adjCostFactor
            rw [ENNReal.ofReal_ne_zero_iff]
            exact Real.exp_pos _)
          have hntop : adjL0_warmAt 0 .warm (deg 5) ≠ ⊤ := PMF.apply_ne_top _ _
          exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hL0_warm) hntop).ne'
        rw [dif_pos h_dite]
        -- Now S1Belief positive at u — case on u
        cases u
        · -- .warm: L0(.warm | deg 5) > 0 from hL0_warm
          exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0_warm (by
            unfold adjCostFactor
            rw [ENNReal.ofReal_ne_zero_iff]
            exact Real.exp_pos _)
        · -- .silent: L0(.silent | deg 5) = priorAfterEvalPos(deg 5) > 0
          have hL0_silent : adjL0_warmAt 0 .silent (deg 5) ≠ 0 := by
            unfold adjL0_warmAt
            rw [RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl)]
            exact priorAfterEvalPos_pos_at_horrible_pos (by decide)
          exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0_silent (by
            unfold adjCostFactor
            rw [ENNReal.ofReal_ne_zero_iff]
            exact Real.exp_pos _)))

/-! ## §5b. Ratio cancellation: the structural core

Because the L&G literal listener carries the prior multiplicatively
(`L0(u) h = P h · 1[u true at h] / mass(u)`), the height factor `P h` cancels
in the speaker's normalisation: on its support, each per-threshold speaker
value depends only on the prior MASS of the utterance's extension at that
threshold. Each marginalised speaker is therefore a sum of a mass-monotone
value over the licensed thresholds, and the headline product comparison
follows from mass monotonicity alone — no numeric reflection. -/

/-- Prior mass of the `.eval_pos` extension at threshold `vt` (exactly the
`L0LassiterGoodman` normaliser for stage 1). -/
noncomputable def evalMass (vt : ValidThreshold) : ℝ≥0∞ :=
  ∑' h, heightPriorPMF h *
    (if evalLex muHorrible (validToThreshold vt) .eval_pos h then (1 : ℝ≥0∞) else 0)

theorem evalMass_ne_zero (vt : ValidThreshold) : evalMass vt ≠ 0 :=
  evalLex_horrible_extension_pos vt .eval_pos

theorem evalMass_ne_top (vt : ValidThreshold) : evalMass vt ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc evalMass vt
      ≤ ∑' h, heightPriorPMF h := ENNReal.tsum_le_tsum fun h => by split <;> simp
    _ = 1 := PMF.tsum_coe _

/-- Π-mass of the `.warm` extension at threshold `vt` (the stage-2
`L0LassiterGoodman` normaliser, against the backgrounded prior). -/
noncomputable def adjMass (vt : ValidThreshold) : ℝ≥0∞ :=
  ∑' h, priorAfterEvalPos h *
    (if adjLex (validToThreshold vt) .warm h then (1 : ℝ≥0∞) else 0)

theorem adjMass_ne_zero (vt : ValidThreshold) : adjMass vt ≠ 0 :=
  adjLex_warm_extension_pos vt .warm

theorem adjMass_ne_top (vt : ValidThreshold) : adjMass vt ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc adjMass vt
      ≤ ∑' h, priorAfterEvalPos h := ENNReal.tsum_le_tsum fun h => by split <;> simp
    _ = 1 := PMF.tsum_coe _

/-- Stage-1 speaker value at `.eval_pos` on its support: a function of the
extension mass only (the height factor has cancelled). -/
noncomputable def gval (vt : ValidThreshold) : ℝ≥0∞ :=
  (evalMass vt)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos /
    ((evalMass vt)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos + 1)

/-- Stage-2 speaker value at `.warm` on its support. -/
noncomputable def fval (vt : ValidThreshold) : ℝ≥0∞ :=
  (adjMass vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm /
    ((adjMass vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm + 1)

theorem evalCostFactor_silent : evalCostFactor .silent = 1 := by
  unfold evalCostFactor evalCost
  norm_num

theorem adjCostFactor_silent : adjCostFactor .silent = 1 := by
  unfold adjCostFactor
  show ENNReal.ofReal (Real.exp (-4 * ((RSA.Nouwen2024.adjCost .silent : ℚ) : ℝ))) = 1
  norm_num [RSA.Nouwen2024.adjCost]

private theorem sumEvalUtt (f : EvalUtterance → ℝ≥0∞) :
    ∑' u, f u = f .eval_pos + f .silent := by
  rw [tsum_fintype,
    show (Finset.univ : Finset EvalUtterance) = {.eval_pos, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem sumAdjUtt (f : RSA.Nouwen2024.AdjUtterance → ℝ≥0∞) :
    ∑' u, f u = f .warm + f .silent := by
  rw [tsum_fintype,
    show (Finset.univ : Finset RSA.Nouwen2024.AdjUtterance) = {.warm, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **Ratio cancellation, stage 1**: on its support the eval speaker's value
is `gval vt` — independent of the height. -/
theorem evalSpeaker_apply_of_true (vt : ValidThreshold) (w : Height)
    (hw : evalLex muHorrible (validToThreshold vt) .eval_pos w = true) :
    evalSpeaker_horribleAt vt w .eval_pos = gval vt := by
  have hP0 : heightPriorPMF w ≠ 0 := heightPriorPMF_pos w
  have hPt : heightPriorPMF w ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0pos : evalL0_horribleAt vt .eval_pos w = heightPriorPMF w * (evalMass vt)⁻¹ := by
    unfold evalL0_horribleAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp only [if_true, mul_one]
    rfl
  have hL0sil : evalL0_horribleAt vt .silent w = heightPriorPMF w := by
    unfold evalL0_horribleAt
    exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
  unfold evalSpeaker_horribleAt
  rw [RSA.S1Belief_apply, sumEvalUtt, hL0pos, hL0sil, evalCostFactor_silent, mul_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  -- value = (P^4 * M^4 * c) * (P^4 * M^4 * c + P^4)⁻¹ ; factor P^4
  have hP4 : (heightPriorPMF w) ^ (4 : ℝ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hP0) hPt).ne'
  have hP4t : (heightPriorPMF w) ^ (4 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [mul_assoc ((heightPriorPMF w) ^ (4 : ℝ)),
    show (heightPriorPMF w) ^ (4 : ℝ) * ((evalMass vt)⁻¹ ^ (4 : ℝ) *
          evalCostFactor .eval_pos) + (heightPriorPMF w) ^ (4 : ℝ)
        = (heightPriorPMF w) ^ (4 : ℝ) * ((evalMass vt)⁻¹ ^ (4 : ℝ) *
          evalCostFactor .eval_pos + 1) from by rw [mul_add, mul_one],
    ← div_eq_mul_inv, ENNReal.mul_div_mul_left _ _ hP4 hP4t]
  rfl

/-- **Ratio cancellation, stage 1, off support**: value 0. -/
theorem evalSpeaker_apply_of_false (vt : ValidThreshold) (w : Height)
    (hw : evalLex muHorrible (validToThreshold vt) .eval_pos w = false) :
    evalSpeaker_horribleAt vt w .eval_pos = 0 := by
  have hL0pos : evalL0_horribleAt vt .eval_pos w = 0 := by
    unfold evalL0_horribleAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp
  unfold evalSpeaker_horribleAt
  rw [RSA.S1Belief_apply, hL0pos, ENNReal.zero_rpow_of_pos (by norm_num), zero_mul, zero_mul]

/-- **Ratio cancellation, stage 2**: on its support (and at a non-degenerate
world, `Π(w) ≠ 0`) the adjective speaker's value is `fval vt`. -/
theorem adjSpeaker_apply_of_true (vt : ValidThreshold) (w : Height)
    (hw : adjLex (validToThreshold vt) .warm w = true)
    (hPi : priorAfterEvalPos w ≠ 0) :
    adjSpeaker_warmAt vt w .warm = fval vt := by
  have hPt : priorAfterEvalPos w ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0warm : adjL0_warmAt vt .warm w = priorAfterEvalPos w * (adjMass vt)⁻¹ := by
    unfold adjL0_warmAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp only [if_true, mul_one]
    rfl
  have hL0sil : adjL0_warmAt vt .silent w = priorAfterEvalPos w := by
    unfold adjL0_warmAt
    exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
  have h_dite : (∑' u, ((adjL0_warmAt vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 := by
    rw [sumAdjUtt]
    intro hz
    obtain ⟨-, h2⟩ := add_eq_zero.mp hz
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [hL0sil] at h3
      exact hPi (by
        by_contra hne
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hne) hPt).ne' h3)
    · rw [adjCostFactor_silent] at h3
      exact one_ne_zero h3
  unfold adjSpeaker_warmAt
  rw [dif_pos h_dite, RSA.S1Belief_apply, sumAdjUtt, hL0warm, hL0sil, adjCostFactor_silent,
    mul_one, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hP4 : (priorAfterEvalPos w) ^ (4 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hPi) hPt).ne'
  have hP4t : (priorAfterEvalPos w) ^ (4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [mul_assoc ((priorAfterEvalPos w) ^ (4 : ℝ)),
    show (priorAfterEvalPos w) ^ (4 : ℝ) * ((adjMass vt)⁻¹ ^ (4 : ℝ) *
          adjCostFactor .warm) + (priorAfterEvalPos w) ^ (4 : ℝ)
        = (priorAfterEvalPos w) ^ (4 : ℝ) * ((adjMass vt)⁻¹ ^ (4 : ℝ) *
          adjCostFactor .warm + 1) from by rw [mul_add, mul_one],
    ← div_eq_mul_inv, ENNReal.mul_div_mul_left _ _ hP4 hP4t]
  rfl

/-- Stage-2 speaker value off support (at a non-degenerate world): `0`. -/
theorem adjSpeaker_apply_of_false (vt : ValidThreshold) (w : Height)
    (hw : adjLex (validToThreshold vt) .warm w = false)
    (hPi : priorAfterEvalPos w ≠ 0) :
    adjSpeaker_warmAt vt w .warm = 0 := by
  have hPt : priorAfterEvalPos w ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0warm : adjL0_warmAt vt .warm w = 0 := by
    unfold adjL0_warmAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp
  have hL0sil : adjL0_warmAt vt .silent w = priorAfterEvalPos w := by
    unfold adjL0_warmAt
    exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
  have h_dite : (∑' u, ((adjL0_warmAt vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 := by
    rw [sumAdjUtt]
    intro hz
    obtain ⟨-, h2⟩ := add_eq_zero.mp hz
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [hL0sil] at h3
      exact hPi (by
        by_contra hne
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hne) hPt).ne' h3)
    · rw [adjCostFactor_silent] at h3
      exact one_ne_zero h3
  unfold adjSpeaker_warmAt
  rw [dif_pos h_dite, RSA.S1Belief_apply, hL0warm,
    ENNReal.zero_rpow_of_pos (by norm_num), zero_mul, zero_mul]

/-! ### Mass monotonicity — structural, no value computation

The `.eval_pos` extension shrinks strictly from threshold 0 to threshold 1
(`deg 2` has `μ_horrible = 1`, licensed at 0 but not at 1), so the eval mass
drops strictly; the speaker value `gval` rises strictly (informativity). -/

theorem evalMass_one_lt_zero : evalMass 1 < evalMass 0 := by
  refine ENNReal.tsum_lt_tsum (i := deg 2) (evalMass_ne_top 1) (fun h => ?_) ?_
  · fin_cases h <;>
      simp [evalLex, evalMeaning, muHorrible, validToThreshold, Degree.Degree.toNat,
        Degree.Threshold.toNat]
  · simp only [evalLex, evalMeaning, muHorrible, validToThreshold, Degree.Degree.toNat,
      Degree.Threshold.toNat, deg]
    norm_num
    exact pos_iff_ne_zero.mpr (heightPriorPMF_pos _)

/-- `x ↦ x/(x+1)` is strictly monotone on finite `ℝ≥0∞` — the informativity
step: a bigger unnormalised weight yields a bigger speaker value. -/
private theorem div_succ_lt_div_succ {a b : ℝ≥0∞} (hb : b ≠ ⊤) (h : a < b) :
    a / (a + 1) < b / (b + 1) := by
  have ha : a ≠ ⊤ := ne_top_of_lt h
  have hda : a / (a + 1) ≠ ⊤ := ENNReal.div_ne_top ha (by simp)
  have hdb : b / (b + 1) ≠ ⊤ := ENNReal.div_ne_top hb (by simp)
  rw [← ENNReal.toReal_lt_toReal hda hdb, ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_add ha ENNReal.one_ne_top, ENNReal.toReal_add hb ENNReal.one_ne_top,
    ENNReal.toReal_one]
  have h' : a.toReal < b.toReal := (ENNReal.toReal_lt_toReal ha hb).mpr h
  have ha0 : (0 : ℝ) ≤ a.toReal := ENNReal.toReal_nonneg
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Informativity is threshold-monotone at the eval stage: the strictly
smaller mass at threshold 1 yields a strictly larger speaker value. -/
theorem gval_zero_lt_one : gval 0 < gval 1 := by
  have hc0 : evalCostFactor .eval_pos ≠ 0 := evalCostFactor_pos _
  have hct : evalCostFactor .eval_pos ≠ ⊤ := evalCostFactor_finite _
  have hX : (evalMass 0)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos
      < (evalMass 1)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos := by
    rw [mul_comm _ (evalCostFactor .eval_pos), mul_comm _ (evalCostFactor .eval_pos)]
    exact ENNReal.mul_lt_mul_right hc0 hct
      (ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.mpr evalMass_one_lt_zero) (by norm_num))
  have hbt : (evalMass 1)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (evalMass_ne_zero 1))) hct
  exact div_succ_lt_div_succ hbt hX

/-! ### Marginal expansions over the licensed thresholds -/

theorem gval_ne_top (vt : ValidThreshold) : gval vt ≠ ⊤ :=
  ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (evalMass_ne_zero vt))) (evalCostFactor_finite _))
    (by simp)

theorem fval_ne_top (vt : ValidThreshold) : fval vt ≠ ⊤ :=
  ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (adjMass_ne_zero vt)))
      (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top))
    (by simp)

theorem fval_ne_zero (vt : ValidThreshold) : fval vt ≠ 0 := by
  unfold fval
  rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  constructor
  · apply mul_ne_zero
    · exact (ENNReal.rpow_pos (ENNReal.inv_pos.mpr (adjMass_ne_top vt))
        (ENNReal.inv_ne_top.mpr (adjMass_ne_zero vt))).ne'
    · unfold adjCostFactor
      rw [ENNReal.ofReal_ne_zero_iff]
      exact Real.exp_pos _
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.inv_ne_top.mpr (adjMass_ne_zero vt)))
        (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top),
       ENNReal.one_ne_top⟩

/-- The raw prior ratio `P(deg 2) = 2 · P(deg 5)` (weights 10 vs 5) — no
normaliser computation needed. -/
theorem heightPriorPMF_deg2_eq :
    heightPriorPMF (deg 2) = 2 * heightPriorPMF (deg 5) := by
  unfold heightPriorPMF
  rw [PMF.normalize_apply, PMF.normalize_apply, ← mul_assoc]
  congr 1
  unfold heightPriorENN
  rw [show (heightPrior (deg 2) : ℝ) = 10 from by norm_num [show heightPrior (deg 2) = 10 from rfl],
    show (heightPrior (deg 5) : ℝ) = 5 from by norm_num [show heightPrior (deg 5) = 5 from rfl],
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from (ENNReal.ofReal_ofNat 2).symm,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

private theorem sumVT (f : ValidThreshold → ℝ≥0∞) :
    ∑' vt, f vt = f 0 + f 1 + f 2 := by
  rw [tsum_fintype, Fin.sum_univ_three]

private theorem uPrior (vt : ValidThreshold) : thresholdPriorPMF vt = 3⁻¹ := by
  rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]
  norm_num

theorem evalMarginal_deg2 :
    evalSpeakerMarginalHorrible (deg 2) .eval_pos = 3⁻¹ * gval 0 := by
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    evalSpeaker_apply_of_true 0 _ (by decide),
    evalSpeaker_apply_of_false 1 _ (by decide),
    evalSpeaker_apply_of_false 2 _ (by decide), mul_zero, add_zero, add_zero]

theorem evalMarginal_deg5 :
    evalSpeakerMarginalHorrible (deg 5) .eval_pos = 3⁻¹ * gval 0 + 3⁻¹ * gval 1 := by
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    evalSpeaker_apply_of_true 0 _ (by decide),
    evalSpeaker_apply_of_true 1 _ (by decide),
    evalSpeaker_apply_of_false 2 _ (by decide), mul_zero, add_zero]

theorem adjMarginal_deg2 :
    adjSpeakerMarginal (deg 2) .warm = 3⁻¹ * fval 0 + 3⁻¹ * fval 1 := by
  unfold adjSpeakerMarginal
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    adjSpeaker_apply_of_true 0 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_true 1 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_false 2 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)), mul_zero, add_zero]

theorem adjMarginal_deg5 :
    adjSpeakerMarginal (deg 5) .warm = 3⁻¹ * fval 0 + 3⁻¹ * fval 1 + 3⁻¹ * fval 2 := by
  unfold adjSpeakerMarginal
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    adjSpeaker_apply_of_true 0 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_true 1 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_true 2 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide))]

/-! ## §5c. The backgrounding contrast: why the paper rejects (49)

[nouwen-2024] p. 28: "the source of this problem lies in the simple
conjunctive analysis I assume in (49)… the two thresholds are resolved in
tandem… all we need to do is update the two positive forms successively
rather than simultaneously." Made structural: in the REJECTED simultaneous
model, per-latent dominance FAILS on the shared licensing support — at a
shared latent where every utterance is true at both worlds, ratio
cancellation makes the speaker values exactly equal, so the raw height
prior's 2:1 preference for the moderate world wins the term comparison
(`sim_sharedSupport_dominance_fails`). In the final sequential model the
same per-latent comparison HOLDS (`seq_horribly_shifts_upward_pmf`'s §5b
engine): the backgrounded evaluative posterior has already re-loaded the
prior toward the extremes. Backgrounding is exactly what makes
intensification term-by-term derivable. -/

/-- Cost factor for the simultaneous model's four utterances. -/
noncomputable def simCostFactor (u : Utterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-4 * (utteranceCost u : ℝ)))

theorem simCostFactor_pos (u : Utterance) : simCostFactor u ≠ 0 := by
  unfold simCostFactor
  rw [ENNReal.ofReal_ne_zero_iff]
  exact Real.exp_pos _

theorem simCostFactor_finite (u : Utterance) : simCostFactor u ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Simultaneous-model literal listener at latent `(θ, θ_e)`, gated on the
utterance's extension being nonempty (the four-utterance L&G L0). -/
noncomputable def simL0At (l : Threshold × Threshold) (u : Utterance) : PMF Height :=
  if h_pos : (∑' h, heightPriorPMF h *
      (if meaning u h l.1 l.2 then (1 : ℝ≥0∞) else 0)) ≠ 0 then
    RSA.L0LassiterGoodman heightPriorPMF (fun u' h => meaning u' h l.1 l.2) u h_pos
  else PMF.uniformOfFintype Height

/-- Simultaneous-model speaker at latent `(θ, θ_e)` and world `h` (total, with
the vacuous fallback at degenerate cells, as in `adjSpeaker_warmAt`). -/
noncomputable def simSpeakerAt (l : Threshold × Threshold) (h : Height) : PMF Utterance :=
  if h_pos : (∑' u, ((simL0At l) u h : ℝ≥0∞) ^ (4 : ℝ) * simCostFactor u) ≠ 0 then
    RSA.S1Belief (simL0At l) simCostFactor 4 h h_pos
      (ENNReal.tsum_ne_top_of_fintype fun u =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          (simCostFactor_finite u))
  else PMF.pure .silent

/-- Per-latent joint term of the simultaneous model for "horribly warm":
prior × speaker — one latent cell's contribution to the (49)-listener's
world score. -/
noncomputable def simTerm (l : Threshold × Threshold) (h : Height) : ℝ≥0∞ :=
  heightPriorPMF h * simSpeakerAt l h .horribly_warm

/-- Extension mass of utterance `u` at latent `l` (the `simL0At` normaliser). -/
noncomputable def simMass (l : Threshold × Threshold) (u : Utterance) : ℝ≥0∞ :=
  ∑' h, heightPriorPMF h * (if meaning u h l.1 l.2 then (1 : ℝ≥0∞) else 0)

private theorem simMass_ne_zero_of_true {l : Threshold × Threshold} {u : Utterance}
    {h : Height} (hu : meaning u h l.1 l.2 = true) : simMass l u ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr
    ⟨h, by rw [hu]; simp only [if_true, mul_one]; exact heightPriorPMF_pos h⟩

private theorem sumUtt4 (f : Utterance → ℝ≥0∞) :
    ∑' u, f u = f .bare_warm + f .horribly_warm + f .pleasantly_warm + f .silent := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Utterance)
      = {.bare_warm, .horribly_warm, .pleasantly_warm, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- At an all-true world, the simultaneous speaker's value is a function of
the four extension masses alone — the height factor has cancelled. -/
private theorem simValue_of_allTrue (l : Threshold × Threshold) (h : Height)
    (hall : ∀ u : Utterance, meaning u h l.1 l.2 = true) :
    simSpeakerAt l h .horribly_warm
      = (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .horribly_warm /
        ((simMass l .bare_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .bare_warm +
         (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .horribly_warm +
         (simMass l .pleasantly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .pleasantly_warm +
         (simMass l .silent)⁻¹ ^ (4 : ℝ) * simCostFactor .silent) := by
  have hP0 : heightPriorPMF h ≠ 0 := heightPriorPMF_pos h
  have hPt : heightPriorPMF h ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0 : ∀ u : Utterance, simL0At l u h = heightPriorPMF h * (simMass l u)⁻¹ := by
    intro u
    have hm : (∑' h', heightPriorPMF h' *
        (if meaning u h' l.1 l.2 then (1 : ℝ≥0∞) else 0)) ≠ 0 :=
      simMass_ne_zero_of_true (hall u)
    unfold simL0At
    rw [dif_pos hm, RSA.L0LassiterGoodman_apply, hall u]
    simp only [if_true, mul_one]
    rfl
  have h_pos : (∑' u, ((simL0At l) u h : ℝ≥0∞) ^ (4 : ℝ) * simCostFactor u) ≠ 0 := by
    rw [sumUtt4]
    intro hz
    rcases mul_eq_zero.mp (add_eq_zero.mp hz).2 with h5 | h5
    · rw [hL0 .silent] at h5
      have hne : heightPriorPMF h * (simMass l .silent)⁻¹ ≠ 0 :=
        mul_ne_zero hP0 (ENNReal.inv_ne_zero.mpr (by
          refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
          calc simMass l .silent
              ≤ ∑' h', heightPriorPMF h' := ENNReal.tsum_le_tsum fun h' => by
                split <;> simp
            _ = 1 := PMF.tsum_coe _))
      rcases ENNReal.rpow_eq_zero_iff.mp h5 with ⟨hz0, -⟩ | ⟨-, hneg⟩
      · exact hne hz0
      · norm_num at hneg
    · exact simCostFactor_pos .silent h5
  unfold simSpeakerAt
  rw [dif_pos h_pos, RSA.S1Belief_apply, sumUtt4, hL0 .bare_warm, hL0 .horribly_warm,
    hL0 .pleasantly_warm, hL0 .silent]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  have hP4 : (heightPriorPMF h) ^ (4 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hP0) hPt).ne'
  have hP4t : (heightPriorPMF h) ^ (4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [← div_eq_mul_inv,
    show heightPriorPMF h ^ (4 : ℝ) * (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .horribly_warm
        = heightPriorPMF h ^ (4 : ℝ) * ((simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .horribly_warm) from by ring,
    show heightPriorPMF h ^ (4 : ℝ) * (simMass l .bare_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .bare_warm +
        heightPriorPMF h ^ (4 : ℝ) * ((simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .horribly_warm) +
        heightPriorPMF h ^ (4 : ℝ) * (simMass l .pleasantly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .pleasantly_warm +
        heightPriorPMF h ^ (4 : ℝ) * (simMass l .silent)⁻¹ ^ (4 : ℝ) *
          simCostFactor .silent
        = heightPriorPMF h ^ (4 : ℝ) * ((simMass l .bare_warm)⁻¹ ^ (4 : ℝ) *
            simCostFactor .bare_warm +
          (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .horribly_warm +
          (simMass l .pleasantly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .pleasantly_warm +
          (simMass l .silent)⁻¹ ^ (4 : ℝ) * simCostFactor .silent) from by ring,
    ENNReal.mul_div_mul_left _ _ hP4 hP4t]

private theorem simMass_ne_top (l : Threshold × Threshold) (u : Utterance) :
    simMass l u ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc simMass l u
      ≤ ∑' h', heightPriorPMF h' := ENNReal.tsum_le_tsum fun h' => by split <;> simp
    _ = 1 := PMF.tsum_coe _

/-- At a latent where every utterance is true at both worlds, ratio
cancellation makes the two speaker values exactly equal. -/
private theorem simSpeaker_value_congr (l : Threshold × Threshold) (h₁ h₂ : Height)
    (hall₁ : ∀ u : Utterance, meaning u h₁ l.1 l.2 = true)
    (hall₂ : ∀ u : Utterance, meaning u h₂ l.1 l.2 = true) :
    simSpeakerAt l h₁ .horribly_warm = simSpeakerAt l h₂ .horribly_warm := by
  rw [simValue_of_allTrue l h₁ hall₁, simValue_of_allTrue l h₂ hall₂]

/-- **The failure half of the backgrounding contrast** ([nouwen-2024] p. 28:
in (49) "the two thresholds are resolved in tandem"): in the rejected
simultaneous model, per-latent dominance fails on the shared licensing
support. At the shared latent `(θ, θ_e) = (1, 0)` every utterance is true at
both `deg 2` and `deg 5`, so ratio cancellation makes the speaker values
exactly equal — and the raw height prior's 2:1 preference for the moderate
world decides the term comparison. Contrast the sequential model
(`seq_horribly_shifts_upward_pmf`): after backgrounding, the same per-latent
comparisons run against the evaluative posterior, which has already
re-loaded the prior toward the extremes. Backgrounding, not parameter
tuning, is what makes intensification term-by-term derivable. -/
theorem sim_sharedSupport_dominance_fails :
    ¬ ∀ l ∈ licensingSet .horribly_warm (deg 2),
        simTerm l (deg 2) ≤ simTerm l (deg 5) := by
  intro hforall
  have hmem : ((thr 1, thr 0) : Threshold × Threshold)
      ∈ licensingSet .horribly_warm (deg 2) := by decide
  have hall2 : ∀ u : Utterance, meaning u (deg 2) (thr 1) (thr 0) = true := by
    decide
  have hcongr := simSpeaker_value_congr ((thr 1, thr 0) : Threshold × Threshold)
    (deg 5) (deg 2) (by decide) hall2
  set v := simSpeakerAt ((thr 1, thr 0) : Threshold × Threshold) (deg 2) .horribly_warm
    with hv
  have hv0 : v ≠ 0 := by
    rw [hv, simValue_of_allTrue _ _ hall2, ne_eq, ENNReal.div_eq_zero_iff, not_or]
    have hterm : ∀ u : Utterance,
        (simMass ((thr 1, thr 0) : Threshold × Threshold) u)⁻¹ ^ (4 : ℝ) *
          simCostFactor u ≠ ⊤ := fun u =>
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ENNReal.inv_ne_top.mpr (simMass_ne_zero_of_true (hall2 u))))
        (simCostFactor_finite u)
    refine ⟨mul_ne_zero ?_ (simCostFactor_pos _), ?_⟩
    · exact (ENNReal.rpow_pos (ENNReal.inv_pos.mpr (simMass_ne_top _ _))
        (ENNReal.inv_ne_top.mpr (simMass_ne_zero_of_true (hall2 .horribly_warm)))).ne'
    · exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hterm _, hterm _⟩, hterm _⟩,
         hterm _⟩
  have hvt : v ≠ ⊤ := PMF.apply_ne_top _ _
  have hP5 : heightPriorPMF (deg 5) ≠ 0 := heightPriorPMF_pos _
  have hP5t : heightPriorPMF (deg 5) ≠ ⊤ := PMF.apply_ne_top _ _
  have hkey : simTerm (thr 1, thr 0) (deg 5) < simTerm (thr 1, thr 0) (deg 2) := by
    unfold simTerm
    rw [hcongr, ← hv, heightPriorPMF_deg2_eq]
    calc heightPriorPMF (deg 5) * v
        = heightPriorPMF (deg 5) * v * 1 := (mul_one _).symm
      _ < heightPriorPMF (deg 5) * v * 2 :=
          ENNReal.mul_lt_mul_right (mul_ne_zero hP5 hv0)
            (ENNReal.mul_ne_top hP5t hvt) (by norm_num)
      _ = 2 * heightPriorPMF (deg 5) * v := by ring
  exact absurd (hforall _ hmem) (not_le.mpr hkey)

/-! ## §6. Predictions

The headline below states that "horribly warm" shifts probability toward
*high* heights (deg 5 > deg 2). **HONEST SCOPE**: this is the
*monotone-shift* shape, NOT the Goldilocks shape that Nouwen 2024
Figures 5-7 actually depict. Goldilocks would require BOTH extremes (very
cold AND very hot) to be evaluated as horrible — Nouwen's `f(x) = x²`
quadratic from Figure 4(b). The file's `muHorrible` is monotone-decreasing
in `h.toNat`, so the headline is mathematically the right statement for
THIS model but the WRONG statement for Nouwen's actual Goldilocks claim.
See module docstring §3 of "Scope (honest reckoning)". -/

/-- The headline shift prediction in PMF form: "horribly warm" pushes
probability toward the high extreme (`deg 5` over the moderate `deg 2`).

**Fully structural discharge** — no numeric reflection. The chained
`posterior κ₂ (posterior κ₁ μ b₁) b₂` shape decomposes via
`PMF.posterior_chained_lt_iff_score_lt` to a product comparison
`μ(2)·E(2)·A(2) < μ(5)·E(5)·A(5)`; the ratio-cancellation lemmas (§5b)
collapse each marginal to a sum of the mass-monotone speaker value over the
licensed thresholds (`E(h) = Σ_{θ_e < μ_H(h)} gval θ_e`, `A(h) = Σ_{θ < h}
fval θ`), and the raw prior ratio `μ(2) = 2·μ(5)` is beaten by informativity
alone: `gval 1 > gval 0` (strictly smaller extension mass at the higher
threshold), so `(g₀+g₁)(f₀+f₁+f₂) > 2·g₀·(f₀+f₁)`. -/
theorem seq_horribly_shifts_upward_pmf :
    seqAdjL1HorriblyWarm .warm (deg 5) >
    seqAdjL1HorriblyWarm .warm (deg 2) := by
  unfold seqAdjL1HorriblyWarm priorAfterEvalPos evalL1Horrible
  rw [gt_iff_lt, PMF.posterior_chained_lt_iff_score_lt,
    evalMarginal_deg2, evalMarginal_deg5, adjMarginal_deg2, adjMarginal_deg5,
    heightPriorPMF_deg2_eq]
  have hF0 : fval 0 + fval 1 ≠ 0 := fun h => fval_ne_zero 0 (add_eq_zero.mp h).1
  have hFt : fval 0 + fval 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨fval_ne_top 0, fval_ne_top 1⟩
  have key : 2 * gval 0 * (fval 0 + fval 1)
      < (gval 0 + gval 1) * (fval 0 + fval 1 + fval 2) := by
    have h1 : 2 * gval 0 * (fval 0 + fval 1)
        < (gval 0 + gval 1) * (fval 0 + fval 1) := by
      rw [two_mul, mul_comm (gval 0 + gval 0), mul_comm (gval 0 + gval 1)]
      exact ENNReal.mul_lt_mul_right hF0 hFt
        (ENNReal.add_lt_add_left (gval_ne_top 0) gval_zero_lt_one)
    exact h1.trans_le (mul_le_mul_right le_self_add _)
  have h3 : (3 : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
  have h3t : (3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hP5 : heightPriorPMF (deg 5) ≠ 0 := heightPriorPMF_pos _
  have hP5t : heightPriorPMF (deg 5) ≠ ⊤ := PMF.apply_ne_top _ _
  calc 2 * heightPriorPMF (deg 5) * (3⁻¹ * gval 0) * (3⁻¹ * fval 0 + 3⁻¹ * fval 1)
      = heightPriorPMF (deg 5) * 3⁻¹ * 3⁻¹ * (2 * gval 0 * (fval 0 + fval 1)) := by
        ring
    _ < heightPriorPMF (deg 5) * 3⁻¹ * 3⁻¹ *
        ((gval 0 + gval 1) * (fval 0 + fval 1 + fval 2)) :=
        ENNReal.mul_lt_mul_right
          (mul_ne_zero (mul_ne_zero hP5 h3) h3)
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top hP5t h3t) h3t) key
    _ = heightPriorPMF (deg 5) * (3⁻¹ * gval 0 + 3⁻¹ * gval 1) *
        (3⁻¹ * fval 0 + 3⁻¹ * fval 1 + 3⁻¹ * fval 2) := by
        ring

/-! ## §6'. Substrate gaps documented as sorry'd theorems (Nouwen 2024 not-formalised)

The following stubs explicitly mark what the file does NOT capture from
Nouwen 2024. Each is the formal statement of the substrate gap; closing
them would require substrate work documented in the module docstring. -/

/-- **Eq. 44b factive embedding (Nouwen 2024 §3.2) — NOT FORMALISED.**

Nouwen's novel semantic proposal (paper p. 2:21) requires the adverb's
positive form to embed the *proposition* `λw. μ_A(x)(@) = μ_A(x)(w)`
(Wheeler-style factive layer). The conjunction
`(μ_A(x) ≥ θ_i) ∧ (μ_D(λw. μ_A(x)(@) = μ_A(x)(w)) ≥ θ_j)` is what
distinguishes Nouwen 2024's intersection from L&G's straight positive
form.

This file's stage-1 evaluative meaning predicates `muHorrible` of heights
directly (`evalLex evalMu θ u h := muHorrible h > θ.toNat`), without the
propositional embedding. Without Eq. 44b's factive layer, the prediction
is L&G's, not Nouwen's. Closing requires a `Prop`/`Bool`-valued lex over
propositions, not just heights — substantial substrate refactor. -/
theorem eq_44b_factive_embedding_NOT_FORMALISED :
    -- Placeholder: should state that the file's evalLex implements the
    -- factive embedding `μ_horrible(λw.μ_warm(x)(@) = μ_warm(x)(w))`.
    -- Until the substrate exists, the statement is unstateable as a
    -- meaningful Lean theorem.
    True := trivial

/-- **Eq. 49 QUD partition `Q^A_X` (Nouwen 2024 §4) — NOT FORMALISED.**

Nouwen's σ/ρ are defined over equivalence classes of worlds, not raw
worlds. The partition `Q^A_X = {[w]_~^A_X | w ∈ W}` is built from the
equivalence `w ~^A_X w' iff μ_A(x)(w) ≈ μ_A(x)(w')` with explicit
granularity `≈` (Nouwen rounds to one decimal in Figure 3).

The file operates over raw `Height` with no quotient or equivalence
relation. At small `Height` cardinality the partition collapses to
identity and the shortcut is vacuously fine for the toy example, but the
file cannot extend to Nouwen's Figures 4-7 (which depend on the QUD
partition + measure-function-on-cells distinction). Closing requires
defining `Quotient`-typed prior + kernels — substantial substrate
refactor. -/
theorem eq_49_qud_partition_NOT_FORMALISED :
    -- Placeholder: should state that the file's prior + kernels are
    -- defined over `Height / ~_A^X` rather than raw `Height`.
    -- Until the substrate exists, the statement is unstateable.
    True := trivial

/-! ## §7. Structural-decomposition demos (lemma library witnesses)

The following theorems exercise the inequality-decomposition lemmas added in
0.230.387. Each one proves a structural claim about the model that the new
lemmas dispatch in 1-2 lines — no numeric arithmetic required. The contrast
with `seq_horribly_shifts_upward_pmf` (closed structurally via §5b) is
the point: structural shell handles structural claims; the numeric core is
reflection territory, regardless of bundling. -/

/-- Order on the stage-2 `.warm` literal listener at worlds where the
adjective extension holds reduces to order on the (eval-stage) prior.
Demonstrates `L0LassiterGoodman_apply_lt_iff_prior_lt`: when the indicator
is true at both points, only the prior matters.

In linguistic terms: the literal listener's "warm-ranking" of two heights
that BOTH satisfy the threshold inherits the eval-stage L1's ordering.
The L0's normalisation by the warm-extension partition cancels. -/
theorem adjL0_warm_meaning_pos_lt_iff_prior_lt
    (vt : ValidThreshold) (w₁ w₂ : Height)
    (h₁ : adjLex (validToThreshold vt) .warm w₁ = true)
    (h₂ : adjLex (validToThreshold vt) .warm w₂ = true) :
    adjL0_warmAt vt .warm w₁ < adjL0_warmAt vt .warm w₂ ↔
      priorAfterEvalPos w₁ < priorAfterEvalPos w₂ := by
  unfold adjL0_warmAt
  exact RSA.L0LassiterGoodman_apply_lt_iff_prior_lt _ _ _ _ _ _ h₁ h₂

/-- The silent utterance's literal listener IS the eval-stage prior pointwise.
Direct application of `L0LassiterGoodman_apply_of_meaning_true` (the silent
utterance has trivially-true meaning at every world).

This is the "vacuous-utterance reduction": informationally-empty utterances
leave the listener's beliefs unchanged from the prior. -/
theorem adjL0_silent_eq_prior (vt : ValidThreshold) (w : Height) :
    adjL0_warmAt vt .silent w = priorAfterEvalPos w := by
  unfold adjL0_warmAt
  exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _

end RSA.Nouwen2024.PMF
