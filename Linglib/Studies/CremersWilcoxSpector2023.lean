import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.Eval
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Mathlib.Data.ENNReal.Inv

/-!
# [cremers-wilcox-spector-2023]: Exhaustivity and Anti-Exhaustivity in RSA

"Exhaustivity and Anti-Exhaustivity in the RSA Framework: Testing the
Effect of Prior Beliefs." Cognitive Science 47(5), e13286.

## The Symmetry Problem

In baseline RSA, hearing "A" can *increase* belief in w_ab (where both A
and B are true) when priors are biased toward w_ab. This "anti-exhaustive"
behavior contradicts human interpretation — humans always exhaust "A" to
mean "A and not B."

## Key Result

Models with grammatical exhaustification (EXH-LU, RSA-LI) block
anti-exhaustivity regardless of prior bias. The EXH parse makes A false
in w_ab, so S1 never uses A to convey w_ab under that parse. The prior
bias is overridden by the structural asymmetry in meaning.

The paper's experimental data (comprehension task) found **no evidence of
anti-exhaustivity**: listeners consistently infer "A and not B" from "A",
regardless of prior bias. This supports grammatical models (EXH-LU,
RSA-LI, svRSA) over baseline RSA and wRSA.

## Domain

- **Worlds**: w_a (only A true), w_ab (A and B both true)
- **Utterances**: A (cost 0), A∧B (cost c), A∧¬B (cost c)
- **Parses** (EXH-LU): literal (A true in both worlds) vs exh (A true only in w_a)

## PMF stack

Each model is a latent-variable RSA model on mathlib `PMF`, with the latent
type the model's distinctive mechanism (parse / QUD / interpretation). For a
fixed config with latent meaning `meaning : Latent → Utterance → World → ℝ≥0∞`:

* `L0 lex u : PMF World` — `RSA.L0OfMeaning` (normalise the prior-weighted
  meaning over worlds), so `L0(w | u, lex) ∝ P(w) · ⟦u⟧_lex(w)` (eq. 1).
* `S1 lex w : PMF Utterance` — `RSA.S1Belief (L0 lex) (fun _ => 1) 2 w`
  (α = 2, no utterance cost): `S1(u | w, lex) ∝ L0(w | u, lex)^2`.
* `marginalSpeaker w : PMF Utterance` — `RSA.marginalizeKernel` of `S1`
  against the uniform `Latent` prior.
* `L1 u : PMF World` — `PMF.posterior marginalSpeaker (uniform World) u`.

The L1 anti-exhaustivity test is `L1(.A) .w_ab > L1(.A) .w_a`, which under a
uniform world prior reduces (via `PMF.posterior_lt_iff_kernel_lt_of_uniform`) to
`marginalSpeaker .w_ab .A > marginalSpeaker .w_a .A` — exactly the marginalised
speaker comparison `T(w) = Σ_l S1(.A | w, l)` of the paper (Appendix A.1).

## Prior Placement

The paper's L0 includes the prior (eq. 1): L0(w|u) ∝ P(w) · ⟦u⟧(w). The paper
also has P(w) at L1 (eq. 3): L1(w|u) ∝ P(w) · S1(u|w). So P(w) enters twice.
For the anti-exhaustivity classification at equal costs (Appendix A.1, eq. A.4)
the L1 prior is a constant factor that cancels in the comparison, so we use a
uniform world prior at L1 and bake `P(w)` into `meaning` for the prior-in-L0
models (baseline, EXH-LU, FREE-LU). For svRSA the prior does NOT enter meaning;
under the coarse QUD all A-true worlds collapse into one cell, neutralising the
prior's effect on S1 (Appendix A.3), which we encode by unit meaning weights.

## Anti-Exhaustivity Definition

The paper's definition (Eq. 6b, equal costs): L1(w_ab|A) > P(w_ab),
equivalently T(w_ab) > T(w_a) (Appendix A.1, eq. A.4), with
T(w) = Σ_l S1(A|w,l). With the uniform world prior this reduces to
`marginalSpeaker .w_ab .A > marginalSpeaker .w_a .A`.

## Utterance Costs

The paper includes costs c(A) = 0, c(A∧B) = c(A∧¬B) = c (eq. 2):
S1(u|w) ∝ L0(w|u)^α · exp(-λc(u)). With equal costs for A∧B and A∧¬B, the cost
terms cancel in the anti-exhaustivity condition (eq. 6b). We set all costs to 0
(`costFactor = fun _ => 1`); the analytic condition in
`antiExhaustivityCondition` handles the general case.

## Model Classification

The paper's 9 models fall into two groups by anti-exhaustivity behavior:

| # | Model | Mechanism | Anti-exhaustive? | Listener |
|---|-------|-----------|-----------------|--------|
| 1 | Baseline RSA | — | Yes | `baselineL1` |
| 2 | wRSA | Prior-in-L0 via background | Yes | `wRSAL1` |
| 3 | BwRSA | Bayesian wRSA | Yes (= wRSA at L1) | `wRSAL1` |
| 4 | svRSA1 | QUD blocks at S1 | No | `svRSAL1` |
| 5 | svRSA2 | QUD blocks at S1 | No | `svRSAL1` |
| 6 | FREE-LU | Free parse choice | Yes | `freeLUL1` |
| 7 | EXH-LU | EXH blocks at L0 | No | `exhLUL1` |
| 8 | RSA-LI1 | EXH blocks at L0 | No (= EXH-LU at L1) | `rsaLIL1` |
| 9 | RSA-LI2 | EXH blocks at L0 | No (= EXH-LU at L1) | `rsaLIL1` |

RSA-LI (Models 8–9) is [franke-bergen-2020]'s Lexical Intentions model;
at L1 with uniform P(i) and equal costs it equals EXH-LU (Table 1).
wRSA and BwRSA are identical at L1 (BwRSA adds a Bayesian S2 layer).
svRSA uses no prior in L0 meaning — QUD projection neutralizes it
(Appendix A.3), giving categorical blocking.

### wRSA is a joint world–background listener

wRSA's latent prior is **world-dependent**: P(w|b)·P(b) ([degen-etal-2015]) puts
the 3:1 bias on the `default_` background and a uniform world prior on `wonky`
(§4.1). Rather than a marginalised per-world speaker, the listener is jointly
uncertain about `(w, b)`: its world belief is the `World`-marginal of the
`(World × Background)` posterior, built with `RSA.jointPrior` + `RSA.jointListener`
(the world-dependent-latent-prior siblings of `marginalizeKernel`/`PMF.posterior`).
The anti-exhaustivity test reduces — via `RSA.jointListener_lt_iff_sum_score_lt`,
the marginal normaliser cancelling — to the latent-summed score comparison
`Σ_b μ(w_ab,b)·S1(.A|w_ab,b) > Σ_b μ(w_a,b)·S1(.A|w_a,b)`. The per-background
speaker reuses the file's proven closed forms: `default_` is `baselineS1` (biased
prior in L0) and `wonky` is `svRSAS1 .coarse` (unit meaning). The other four
configs have world-independent uniform latent priors and use the
`marginalizeKernel` stack.

## Connection to Other Formalizations

- `ExhaustivityLimit.lean`: proves RSA at α→∞ recovers Fox's exh,
  using the same IE infrastructure (`Exhaustification.Innocent.exhIE`)
  as our `exhMeaning`.
- `FrankeBergen2020.lean`: formalizes four RSA models (vanilla, LU, LI, GI)
  for nested quantifiers, using compositional exhaustification.
- `ScopeExpressivity.lean`: demonstrates the scope-blind vs scope-sensitive
  expressivity gap between standard RSA and compositional EXH.
- `PottsEtAl2016.lean`: the same latent-marginalisation PMF idiom
  (`L0OfMeaning`/`S1Belief`/`marginalizeKernel`/`PMF.posterior`) for embedded
  implicatures under lexical uncertainty.
-/

set_option autoImplicit false

open scoped ENNReal

namespace CremersWilcoxSpector2023

/-! ### Domain types -/

/-- Two-world model for exhaustivity.
    - `w_a`: A true, B false (A ∧ ¬B)
    - `w_ab`: A and B both true (A ∧ B)

    No w_b or w_none because we condition on A being true.
    The question is whether B is also true. -/
inductive CWSWorld where
  | w_a : CWSWorld
  | w_ab : CWSWorld
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Three utterances in the minimal exhaustivity domain. -/
inductive CWSUtterance where
  | A : CWSUtterance
  | AandB : CWSUtterance
  | AandNotB : CWSUtterance
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### Literal semantics -/

/-- Literal truth: which utterance is true in which world. -/
def literalTruth : CWSWorld → CWSUtterance → Bool
  | .w_a, .A => true
  | .w_a, .AandB => false
  | .w_a, .AandNotB => true
  | .w_ab, .A => true
  | .w_ab, .AandB => true
  | .w_ab, .AandNotB => false

/-- A is true in both worlds. -/
theorem A_true_everywhere : ∀ w, literalTruth w .A = true := by
  intro w; cases w <;> rfl

/-- A∧B only true in w_ab. -/
theorem AandB_only_in_wab : literalTruth .w_a .AandB = false ∧ literalTruth .w_ab .AandB = true := by
  constructor <;> rfl

/-- A∧¬B only true in w_a. -/
theorem AandNotB_only_in_wa : literalTruth .w_a .AandNotB = true ∧ literalTruth .w_ab .AandNotB = false := by
  constructor <;> rfl

/-! ### Exhaustification (Innocent Exclusion) -/

open Exhaustification (innocent predToFinset altsFromPreds)

/-- Alternatives for each utterance: A has scale-mate A∧B. -/
def alternatives (u : CWSUtterance) : List (CWSWorld → Bool) :=
  match u with
  | .A => [fun w => literalTruth w .A, fun w => literalTruth w .AandB]
  | _ => [fun w => literalTruth w u]

/-- Exhaustified meaning derived via Innocent Exclusion.
    IE negates A∧B (the non-entailed stronger alternative to A),
    giving EXH(A) = A ∧ ¬(A∧B) = A ∧ ¬B. -/
def exhMeaning (w : CWSWorld) (u : CWSUtterance) : Bool :=
  decide (w ∈ innocent.exh (altsFromPreds (alternatives u))
                    (predToFinset (fun w' => literalTruth w' u)))

/-- EXH(A) is only true in w_a — derived from IE, not stipulated. -/
theorem exhA_only_in_wa : exhMeaning .w_a .A = true ∧ exhMeaning .w_ab .A = false := by
  constructor <;> decide

/-- EXH(A∧B) unchanged: A∧B has no stronger alternative. -/
theorem exhAB_unchanged : ∀ w, exhMeaning w .AandB = literalTruth w .AandB := by
  decide

/-- EXH(A∧¬B) unchanged: A∧¬B has no stronger alternative. -/
theorem exhAnotB_unchanged : ∀ w, exhMeaning w .AandNotB = literalTruth w .AandNotB := by
  decide

/-- Per-cell `exhMeaning` values (derived from IE via `decide`), `@[simp]` so the
prior-weighted meaning functions reduce without re-evaluating Innocent Exclusion. -/
@[simp] private theorem exhMeaning_A_wa : exhMeaning .w_a .A = true := by decide
@[simp] private theorem exhMeaning_A_wab : exhMeaning .w_ab .A = false := by decide
@[simp] private theorem exhMeaning_AandB_wa : exhMeaning .w_a .AandB = false := by decide
@[simp] private theorem exhMeaning_AandB_wab : exhMeaning .w_ab .AandB = true := by decide
@[simp] private theorem exhMeaning_AandNotB_wa : exhMeaning .w_a .AandNotB = true := by decide
@[simp] private theorem exhMeaning_AandNotB_wab : exhMeaning .w_ab .AandNotB = false := by decide

/-! ### Parse-dependent meaning -/

/-- Parse = whether EXH is applied. -/
inductive CWSParse where
  | literal : CWSParse
  | exh : CWSParse
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Meaning with parse-dependent exhaustification. -/
def parseMeaning : CWSParse → CWSWorld → CWSUtterance → Bool
  | .literal, w, u => literalTruth w u
  | .exh, w, u => exhMeaning w u

/-! ### Prior weight and cost -/

/-- Prior weight for each world: 1:3 bias toward w_ab.

    Baked into `meaning` for prior-in-L0 models so that
    `L0(w|u) ∝ P(w) · ⟦u⟧(w)`, matching the paper's eq. (1). This makes S1
    asymmetric for utterances true in both worlds, which is the source of
    anti-exhaustivity. -/
def priorWeight : CWSWorld → ℝ
  | .w_a => 1
  | .w_ab => 3

/-- Utterance cost (Appendix A.1, eq. A.1). The paper uses c(A) = 0 and
    positive c for A∧B and A∧¬B, but with equal costs the classification
    is prior-determined (eq. 6b). We set all costs to 0; the general case
    is handled analytically by `antiExhaustivityCondition`. -/
def utteranceCost : CWSUtterance → ℝ
  | .A => 0
  | .AandB => 0
  | .AandNotB => 0

/-! ### Anti-exhaustivity condition (Eq. 6b) -/

/-- The paper's analytic condition for when baseline RSA is anti-exhaustive.

    Full condition (Eq. 6b): `log P(w_ab) - log P(w_a) > c(A∧¬B) - c(A∧B)`.
    When the cost of the exhaustive paraphrase A∧¬B exceeds the conjunctive
    alternative A∧B, the speaker's dispreference for the paraphrase makes
    anti-exhaustivity easier to trigger. With equal costs, any prior bias
    toward w_ab suffices. -/
def antiExhaustivityCondition (log_p_wab log_p_wa c_AnotB c_AB : ℚ) : Bool :=
  log_p_wab - log_p_wa > c_AnotB - c_AB

/-- Equal costs: anti-exhaustivity iff P(w_ab) > P(w_a) (i.e., log ratio > 0). -/
theorem equal_costs_reduces_to_prior (log_wab log_wa c : ℚ) :
    antiExhaustivityCondition log_wab log_wa c c = (log_wab > log_wa) := by
  simp [antiExhaustivityCondition, sub_self]

/-- Uniform prior with equal costs: no anti-exhaustivity. -/
theorem uniform_no_antiexh :
    antiExhaustivityCondition 0 0 1 1 = false := by
  simp only [antiExhaustivityCondition, decide_eq_false_iff_not]; norm_num

/-- Biased prior with equal costs: anti-exhaustivity triggered. -/
theorem biased_triggers_antiexh :
    antiExhaustivityCondition 3 1 1 1 = true := by
  simp only [antiExhaustivityCondition, decide_eq_true_iff]; norm_num

/-- Asymmetric costs can block anti-exhaustivity even with biased prior:
    if c(A∧¬B) is much more expensive than c(A∧B), the cost gap
    c(A∧¬B) - c(A∧B) exceeds the log prior ratio. -/
theorem cost_asymmetry_can_block :
    antiExhaustivityCondition 3 1 10 0 = false := by
  simp only [antiExhaustivityCondition, decide_eq_false_iff_not]; norm_num

/-! ### Shared sum unfolders and α = 2 score reduction

The PMF stack below reduces partition functions over `CWSWorld` / `CWSUtterance`
to concrete two/three-term sums via the `rfl` unfolders, and the speaker score
`(L0 u w)^(2:ℝ) · 1` to a nat power `(L0 u w)^(2:ℕ)` so it lands as
`ofReal (r^2)`. -/

/-- Sum-over-`CWSWorld` unfolder, proved by `rfl`. -/
theorem CWSWorld_sum_univ {β : Type*} [AddCommMonoid β] (f : CWSWorld → β) :
    ∑ i, f i = f .w_a + (f .w_ab + 0) := by rfl

/-- Sum-over-`CWSUtterance` unfolder, proved by `rfl`. -/
theorem CWSUtterance_sum_univ {β : Type*} [AddCommMonoid β] (f : CWSUtterance → β) :
    ∑ i, f i = f .A + (f .AandB + (f .AandNotB + 0)) := by rfl

/-- α = 2 score reduction: the speaker score `(L0 u w)^(2:ℝ) · 1` is the *square*
`(L0 u w)^(2:ℕ)`. The `(2:ℝ)` rpow becomes a `(2:ℕ)` power via
`ENNReal.rpow_natCast`; this is the α≠1 analogue of Potts' `rpow_one` collapse.
`local pmf_eval_simps` (file-local, not substrate-global) so partition functions
reduce squared L0 values. -/
theorem rpow_two_mul_one (x : ℝ≥0∞) : x ^ (2 : ℝ) * 1 = x ^ (2 : ℕ) := by
  rw [mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

attribute [local pmf_eval_simps] rpow_two_mul_one

/-- `ofReal r` squared (α = 2): `(ofReal r)^(2:ℕ) = ofReal (r^2)` for `0 ≤ r`.
Carries the squared L0 closed forms into the `Z` / `marginalSpeaker` arithmetic. -/
theorem sq_ofReal (r : ℝ) (hr : 0 ≤ r) :
    (ENNReal.ofReal r) ^ (2 : ℕ) = ENNReal.ofReal (r ^ 2) :=
  (ENNReal.ofReal_pow hr 2).symm

/-! ### Baseline RSA (Model 1)

Prior-in-L0, no latent (`Unit`): `meaning(u,w) = P(w) · ⟦u⟧(w)`, so
`L0(w_a|A) = 1/4, L0(w_ab|A) = 3/4`. With α = 2 the speaker is asymmetric:
`S1(A|w_ab) = 9/25 > 1/17 = S1(A|w_a)`. The speaker preferentially uses the
cheap utterance A when w_ab is true (L0 already favours w_ab given A), driving
genuine anti-exhaustivity (Eq. 6b, Fig. 1). With no latent, the marginal
speaker is `S1` itself. -/

/-- Baseline meaning: `P(w)·⟦u⟧(w)` lifted to `ℝ≥0∞`. -/
def baselineMeaning (u : CWSUtterance) (w : CWSWorld) : ℝ≥0∞ :=
  if literalTruth w u then ENNReal.ofReal (priorWeight w) else 0

theorem baselineMeaning_apply (u : CWSUtterance) (w : CWSWorld) :
    baselineMeaning u w = if literalTruth w u then ENNReal.ofReal (priorWeight w) else 0 := rfl

theorem baselineMeaning_ne_top (u : CWSUtterance) : (∑' w, baselineMeaning u w) ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype
    (fun w => by rw [baselineMeaning_apply]; split <;> simp [ENNReal.ofReal_ne_top])

theorem baselineMeaning_pos (u : CWSUtterance) : (∑' w, baselineMeaning u w) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  cases u
  · exact ⟨.w_a, by rw [baselineMeaning_apply]; simp [literalTruth, priorWeight]⟩
  · exact ⟨.w_ab, by rw [baselineMeaning_apply]; simp [literalTruth, priorWeight]⟩
  · exact ⟨.w_a, by rw [baselineMeaning_apply]; simp [literalTruth, priorWeight]⟩

/-- Baseline literal listener: `L0(w|u) ∝ P(w)·⟦u⟧(w)` (eq. 1). -/
noncomputable def baselineL0 (u : CWSUtterance) : PMF CWSWorld :=
  RSA.L0OfMeaning baselineMeaning u (baselineMeaning_pos u) (baselineMeaning_ne_top u)

private theorem baselineL0_ofReal (u : CWSUtterance) (w : CWSWorld) (r : ℝ)
    (h : baselineMeaning u w * (∑' w', baselineMeaning u w')⁻¹ = ENNReal.ofReal r) :
    baselineL0 u w = ENNReal.ofReal r := by
  unfold baselineL0; rw [RSA.L0OfMeaning_apply]; exact h

theorem baselineL0_A_wa : baselineL0 .A .w_a = ENNReal.ofReal (1/4) := by
  apply baselineL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [baselineMeaning_apply, literalTruth, priorWeight, ↓reduceIte, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem baselineL0_A_wab : baselineL0 .A .w_ab = ENNReal.ofReal (3/4) := by
  apply baselineL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [baselineMeaning_apply, literalTruth, priorWeight, ↓reduceIte, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem baselineL0_AandB_wa : baselineL0 .AandB .w_a = ENNReal.ofReal 0 := by
  apply baselineL0_ofReal; rw [baselineMeaning_apply]; simp [literalTruth]

theorem baselineL0_AandB_wab : baselineL0 .AandB .w_ab = ENNReal.ofReal 1 := by
  apply baselineL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [baselineMeaning_apply, literalTruth, priorWeight, Bool.false_eq_true, if_false,
    if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]; simp

theorem baselineL0_AandNotB_wa : baselineL0 .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply baselineL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [baselineMeaning_apply, literalTruth, priorWeight, Bool.false_eq_true, if_false,
    if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]; simp

theorem baselineL0_AandNotB_wab : baselineL0 .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply baselineL0_ofReal; rw [baselineMeaning_apply]; simp [literalTruth]

attribute [local pmf_eval_simps] CWSUtterance_sum_univ
  baselineL0_A_wa baselineL0_A_wab baselineL0_AandB_wa baselineL0_AandB_wab
  baselineL0_AandNotB_wa baselineL0_AandNotB_wab

/-- Baseline speaker normaliser at world `w`. -/
noncomputable def baselineZ (w : CWSWorld) : ℝ≥0∞ := ∑' u, (baselineL0 u w : ℝ≥0∞) ^ (2 : ℝ) * 1

theorem baselineZ_eq_sum (w : CWSWorld) : baselineZ w = ∑' u, (baselineL0 u w) ^ (2 : ℕ) := by
  unfold baselineZ; simp_rw [rpow_two_mul_one]

theorem baselineZ_ne_top (w : CWSWorld) : (∑' u, (baselineL0 u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ ∞ := by
  refine ENNReal.tsum_ne_top_of_fintype (fun u => ?_)
  rw [rpow_two_mul_one]; exact ENNReal.pow_ne_top (PMF.apply_ne_top _ _)

theorem baselineZ_ne_zero (w : CWSWorld) : (∑' u, (baselineL0 u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨.A, ?_⟩; rw [rpow_two_mul_one]; cases w
  · rw [baselineL0_A_wa]; simp
  · rw [baselineL0_A_wab]; simp

theorem baselineZ_wa : baselineZ .w_a = ENNReal.ofReal (17/16) := by
  rw [baselineZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1/4) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem baselineZ_wab : baselineZ .w_ab = ENNReal.ofReal (25/16) := by
  rw [baselineZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (3/4) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

/-- Baseline speaker (α = 2, no cost). With `Unit` latent this is the marginal
speaker the listener inverts. -/
noncomputable def baselineS1 (w : CWSWorld) : PMF CWSUtterance :=
  RSA.S1Belief baselineL0 (fun _ => 1) 2 w (baselineZ_ne_zero w) (baselineZ_ne_top w)

theorem baselineS1_apply (w : CWSWorld) (u : CWSUtterance) :
    baselineS1 w u =
      (baselineL0 u w) ^ (2 : ℝ) * 1 * (∑' u', (baselineL0 u' w : ℝ≥0∞) ^ (2 : ℝ) * 1)⁻¹ := by
  unfold baselineS1; rw [RSA.S1Belief_apply]

theorem baselineS1_A_wa : baselineS1 .w_a .A = ENNReal.ofReal (1/17) := by
  rw [baselineS1_apply, rpow_two_mul_one,
      show (∑' u', (baselineL0 u' .w_a : ℝ≥0∞) ^ (2 : ℝ) * 1) = baselineZ .w_a from rfl,
      baselineZ_wa, baselineL0_A_wa, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem baselineS1_A_wab : baselineS1 .w_ab .A = ENNReal.ofReal (9/25) := by
  rw [baselineS1_apply, rpow_two_mul_one,
      show (∑' u', (baselineL0 u' .w_ab : ℝ≥0∞) ^ (2 : ℝ) * 1) = baselineZ .w_ab from rfl,
      baselineZ_wab, baselineL0_A_wab, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem baseline_hMarg :
    PMF.marginal baselineS1 (PMF.uniformOfFintype CWSWorld) .A ≠ 0 := by
  refine PMF.marginal_ne_zero baselineS1 _ _ (a := CWSWorld.w_a) ?_ ?_
  · exact (PMF.uniformOfFintype CWSWorld).mem_support_iff CWSWorld.w_a |>.mp
      (PMF.mem_support_uniformOfFintype CWSWorld.w_a)
  · rw [baselineS1_A_wa]; simp

/-- Baseline pragmatic listener: Bayesian inversion of `baselineS1` against the
uniform world prior. -/
noncomputable def baselineL1 (u : CWSUtterance)
    (h : PMF.marginal baselineS1 (PMF.uniformOfFintype CWSWorld) u ≠ 0) : PMF CWSWorld :=
  PMF.posterior baselineS1 (PMF.uniformOfFintype CWSWorld) u h

/-! ### EXH-LU RSA (Models 7–9)

Parse is a latent variable; meaning under each parse bakes in the prior,
`meaning(p,u,w) = P(w)·⟦u⟧_p(w)`. Under the `exh` parse EXH(A) is false at
w_ab, so `L0(·|A, exh)` puts all mass on w_a and `S1(A|w_ab, exh) = 0`. The
exh-parse blocking (`S1(A|w_a, exh) = 1/2`) outweighs the literal parse's prior
amplification, giving `T(w_a) = 19/34 > 9/25 = T(w_ab)` despite the 3:1 bias.
With a uniform parse prior the marginal speaker halves these, so the listener
inverts `ms(w_a) = 19/68 > 9/50 = ms(w_ab)`.

RSA-LI (Models 8–9) is [franke-bergen-2020]'s Lexical Intentions model; at L1
with uniform P(i) and equal costs it equals EXH-LU (`rsaLI* := exhLU*`). -/

/-- Parse-dependent meaning lifted to `ℝ≥0∞` (prior baked in). -/
def parseMeaningE (p : CWSParse) (u : CWSUtterance) (w : CWSWorld) : ℝ≥0∞ :=
  if parseMeaning p w u then ENNReal.ofReal (priorWeight w) else 0

theorem parseMeaningE_apply (p : CWSParse) (u : CWSUtterance) (w : CWSWorld) :
    parseMeaningE p u w = if parseMeaning p w u then ENNReal.ofReal (priorWeight w) else 0 := rfl

theorem parseMeaningE_ne_top (p : CWSParse) (u : CWSUtterance) :
    (∑' w, parseMeaningE p u w) ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype
    (fun w => by rw [parseMeaningE_apply]; split <;> simp [ENNReal.ofReal_ne_top])

theorem parseMeaningE_pos (p : CWSParse) (u : CWSUtterance) :
    (∑' w, parseMeaningE p u w) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  cases p <;> cases u
  · exact ⟨.w_a, by rw [parseMeaningE_apply]; simp [parseMeaning, literalTruth, priorWeight]⟩
  · exact ⟨.w_ab, by rw [parseMeaningE_apply]; simp [parseMeaning, literalTruth, priorWeight]⟩
  · exact ⟨.w_a, by rw [parseMeaningE_apply]; simp [parseMeaning, literalTruth, priorWeight]⟩
  · exact ⟨.w_a, by rw [parseMeaningE_apply]; simp [parseMeaning, priorWeight]⟩
  · exact ⟨.w_ab, by rw [parseMeaningE_apply]; simp [parseMeaning, priorWeight]⟩
  · exact ⟨.w_a, by rw [parseMeaningE_apply]; simp [parseMeaning, priorWeight]⟩

/-- EXH-LU per-parse literal listener. -/
noncomputable def exhLUL0 (p : CWSParse) (u : CWSUtterance) : PMF CWSWorld :=
  RSA.L0OfMeaning (parseMeaningE p) u (parseMeaningE_pos p u) (parseMeaningE_ne_top p u)

private theorem exhLUL0_ofReal (p : CWSParse) (u : CWSUtterance) (w : CWSWorld) (r : ℝ)
    (h : parseMeaningE p u w * (∑' w', parseMeaningE p u w')⁻¹ = ENNReal.ofReal r) :
    exhLUL0 p u w = ENNReal.ofReal r := by
  unfold exhLUL0; rw [RSA.L0OfMeaning_apply]; exact h

/-- Closes an EXH-LU L0 cell that is uniquely true at `w` (value `1`). -/
private theorem exhLUL0_unique (p : CWSParse) (u : CWSUtterance) (w : CWSWorld)
    (h : parseMeaningE p u w * (∑' w', parseMeaningE p u w')⁻¹ = 1) :
    exhLUL0 p u w = ENNReal.ofReal 1 := by
  unfold exhLUL0; rw [RSA.L0OfMeaning_apply, h]; simp

-- literal parse: identical to baseline
theorem exhLUL0_lit_A_wa : exhLUL0 .literal .A .w_a = ENNReal.ofReal (1/4) := by
  apply exhLUL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [parseMeaningE_apply, parseMeaning, literalTruth, priorWeight, ↓reduceIte, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem exhLUL0_lit_A_wab : exhLUL0 .literal .A .w_ab = ENNReal.ofReal (3/4) := by
  apply exhLUL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [parseMeaningE_apply, parseMeaning, literalTruth, priorWeight, ↓reduceIte, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem exhLUL0_lit_AandB_wa : exhLUL0 .literal .AandB .w_a = ENNReal.ofReal 0 := by
  apply exhLUL0_ofReal; rw [parseMeaningE_apply]; simp [parseMeaning, literalTruth]

theorem exhLUL0_lit_AandB_wab : exhLUL0 .literal .AandB .w_ab = ENNReal.ofReal 1 := by
  apply exhLUL0_unique; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [parseMeaningE_apply, parseMeaning, literalTruth, priorWeight, Bool.false_eq_true,
    if_false, if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem exhLUL0_lit_AandNotB_wa : exhLUL0 .literal .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply exhLUL0_unique; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [parseMeaningE_apply, parseMeaning, literalTruth, priorWeight, Bool.false_eq_true,
    if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem exhLUL0_lit_AandNotB_wab : exhLUL0 .literal .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply exhLUL0_ofReal; rw [parseMeaningE_apply]; simp [parseMeaning, literalTruth]

-- exh parse: EXH(A) true only at w_a
theorem exhLUL0_exh_A_wa : exhLUL0 .exh .A .w_a = ENNReal.ofReal 1 := by
  apply exhLUL0_unique; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [parseMeaningE_apply, parseMeaning, exhMeaning_A_wa, exhMeaning_A_wab, priorWeight,
    Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem exhLUL0_exh_A_wab : exhLUL0 .exh .A .w_ab = ENNReal.ofReal 0 := by
  apply exhLUL0_ofReal; rw [parseMeaningE_apply]; simp [parseMeaning]

theorem exhLUL0_exh_AandB_wa : exhLUL0 .exh .AandB .w_a = ENNReal.ofReal 0 := by
  apply exhLUL0_ofReal; rw [parseMeaningE_apply]; simp [parseMeaning]

theorem exhLUL0_exh_AandB_wab : exhLUL0 .exh .AandB .w_ab = ENNReal.ofReal 1 := by
  apply exhLUL0_unique; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [parseMeaningE_apply, parseMeaning, exhMeaning_AandB_wa, exhMeaning_AandB_wab,
    priorWeight, Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem exhLUL0_exh_AandNotB_wa : exhLUL0 .exh .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply exhLUL0_unique; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [parseMeaningE_apply, parseMeaning, exhMeaning_AandNotB_wa, exhMeaning_AandNotB_wab,
    priorWeight, Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem exhLUL0_exh_AandNotB_wab : exhLUL0 .exh .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply exhLUL0_ofReal; rw [parseMeaningE_apply]; simp [parseMeaning]

attribute [local pmf_eval_simps]
  exhLUL0_lit_A_wa exhLUL0_lit_A_wab exhLUL0_lit_AandB_wa exhLUL0_lit_AandB_wab
  exhLUL0_lit_AandNotB_wa exhLUL0_lit_AandNotB_wab
  exhLUL0_exh_A_wa exhLUL0_exh_A_wab exhLUL0_exh_AandB_wa exhLUL0_exh_AandB_wab
  exhLUL0_exh_AandNotB_wa exhLUL0_exh_AandNotB_wab

/-- Sum-over-`CWSParse` unfolder, proved by `rfl`. -/
theorem CWSParse_sum_univ {β : Type*} [AddCommMonoid β] (f : CWSParse → β) :
    ∑ i, f i = f .literal + (f .exh + 0) := by rfl

noncomputable def exhLUZ (p : CWSParse) (w : CWSWorld) : ℝ≥0∞ :=
  ∑' u, (exhLUL0 p u w : ℝ≥0∞) ^ (2 : ℝ) * 1

theorem exhLUZ_eq_sum (p : CWSParse) (w : CWSWorld) :
    exhLUZ p w = ∑' u, (exhLUL0 p u w) ^ (2 : ℕ) := by unfold exhLUZ; simp_rw [rpow_two_mul_one]

theorem exhLUZ_ne_top (p : CWSParse) (w : CWSWorld) :
    (∑' u, (exhLUL0 p u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ ∞ := by
  refine ENNReal.tsum_ne_top_of_fintype (fun u => ?_)
  rw [rpow_two_mul_one]; exact ENNReal.pow_ne_top (PMF.apply_ne_top _ _)

theorem exhLUZ_ne_zero (p : CWSParse) (w : CWSWorld) :
    (∑' u, (exhLUL0 p u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  cases p <;> cases w
  · exact ⟨.A, by rw [rpow_two_mul_one, exhLUL0_lit_A_wa]; simp⟩
  · exact ⟨.A, by rw [rpow_two_mul_one, exhLUL0_lit_A_wab]; simp⟩
  · exact ⟨.A, by rw [rpow_two_mul_one, exhLUL0_exh_A_wa]; simp⟩
  · exact ⟨.AandB, by rw [rpow_two_mul_one, exhLUL0_exh_AandB_wab]; simp⟩

theorem exhLUZ_lit_wa : exhLUZ .literal .w_a = ENNReal.ofReal (17/16) := by
  rw [exhLUZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1/4) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem exhLUZ_lit_wab : exhLUZ .literal .w_ab = ENNReal.ofReal (25/16) := by
  rw [exhLUZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (3/4) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem exhLUZ_exh_wa : exhLUZ .exh .w_a = ENNReal.ofReal 2 := by
  rw [exhLUZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem exhLUZ_exh_wab : exhLUZ .exh .w_ab = ENNReal.ofReal 1 := by
  rw [exhLUZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

/-- EXH-LU per-parse speaker (α = 2, no cost). -/
noncomputable def exhLUS1 (p : CWSParse) (w : CWSWorld) : PMF CWSUtterance :=
  RSA.S1Belief (exhLUL0 p) (fun _ => 1) 2 w (exhLUZ_ne_zero p w) (exhLUZ_ne_top p w)

theorem exhLUS1_apply (p : CWSParse) (w : CWSWorld) (u : CWSUtterance) :
    exhLUS1 p w u =
      (exhLUL0 p u w) ^ (2 : ℝ) * 1 * (∑' u', (exhLUL0 p u' w : ℝ≥0∞) ^ (2 : ℝ) * 1)⁻¹ := by
  unfold exhLUS1; rw [RSA.S1Belief_apply]

theorem exhLUS1_lit_A_wa : exhLUS1 .literal .w_a .A = ENNReal.ofReal (1/17) := by
  rw [exhLUS1_apply, rpow_two_mul_one,
      show (∑' u', (exhLUL0 .literal u' .w_a : ℝ≥0∞) ^ (2 : ℝ) * 1) = exhLUZ .literal .w_a from rfl,
      exhLUZ_lit_wa, exhLUL0_lit_A_wa, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem exhLUS1_lit_A_wab : exhLUS1 .literal .w_ab .A = ENNReal.ofReal (9/25) := by
  rw [exhLUS1_apply, rpow_two_mul_one,
      show (∑' u', (exhLUL0 .literal u' .w_ab : ℝ≥0∞) ^ (2 : ℝ) * 1) = exhLUZ .literal .w_ab from rfl,
      exhLUZ_lit_wab, exhLUL0_lit_A_wab, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem exhLUS1_exh_A_wa : exhLUS1 .exh .w_a .A = ENNReal.ofReal (1/2) := by
  rw [exhLUS1_apply, rpow_two_mul_one,
      show (∑' u', (exhLUL0 .exh u' .w_a : ℝ≥0∞) ^ (2 : ℝ) * 1) = exhLUZ .exh .w_a from rfl,
      exhLUZ_exh_wa, exhLUL0_exh_A_wa, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem exhLUS1_exh_A_wab : exhLUS1 .exh .w_ab .A = ENNReal.ofReal 0 := by
  rw [exhLUS1_apply, rpow_two_mul_one, exhLUL0_exh_A_wab, sq_ofReal _ (le_refl 0)]; simp

/-- EXH-LU marginal speaker over a uniform parse prior. -/
noncomputable def exhLUMarginalSpeaker (w : CWSWorld) : PMF CWSUtterance :=
  RSA.marginalizeKernel (PMF.uniformOfFintype CWSParse) (fun p w => exhLUS1 p w) w

private theorem uniformParse_apply (p : CWSParse) :
    (PMF.uniformOfFintype CWSParse) p = ENNReal.ofReal (1/2) := by
  rw [PMF.uniformOfFintype_apply, show Fintype.card CWSParse = 2 from by decide,
      show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem exhLUMarginalSpeaker_apply (w : CWSWorld) (u : CWSUtterance) :
    exhLUMarginalSpeaker w u =
      ENNReal.ofReal (1/2) * exhLUS1 .literal w u +
        (ENNReal.ofReal (1/2) * exhLUS1 .exh w u + 0) := by
  unfold exhLUMarginalSpeaker
  rw [RSA.marginalizeKernel_apply, tsum_fintype, CWSParse_sum_univ,
      uniformParse_apply, uniformParse_apply]

theorem exhLU_ms_wa : exhLUMarginalSpeaker .w_a .A = ENNReal.ofReal (19/68) := by
  rw [exhLUMarginalSpeaker_apply, exhLUS1_lit_A_wa, exhLUS1_exh_A_wa, add_zero,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem exhLU_ms_wab : exhLUMarginalSpeaker .w_ab .A = ENNReal.ofReal (9/50) := by
  rw [exhLUMarginalSpeaker_apply, exhLUS1_lit_A_wab, exhLUS1_exh_A_wab,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), add_zero,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem exhLU_hMarg :
    PMF.marginal exhLUMarginalSpeaker (PMF.uniformOfFintype CWSWorld) .A ≠ 0 := by
  refine PMF.marginal_ne_zero exhLUMarginalSpeaker _ _ (a := CWSWorld.w_a) ?_ ?_
  · exact (PMF.uniformOfFintype CWSWorld).mem_support_iff CWSWorld.w_a |>.mp
      (PMF.mem_support_uniformOfFintype CWSWorld.w_a)
  · rw [exhLU_ms_wa]; simp

/-- EXH-LU pragmatic listener (also RSA-LI at L1). -/
noncomputable def exhLUL1 (u : CWSUtterance)
    (h : PMF.marginal exhLUMarginalSpeaker (PMF.uniformOfFintype CWSWorld) u ≠ 0) : PMF CWSWorld :=
  PMF.posterior exhLUMarginalSpeaker (PMF.uniformOfFintype CWSWorld) u h

/-- RSA-LI (Models 8–9): at L1 with uniform P(i) and equal costs, identical to
EXH-LU (Table 1 of [franke-bergen-2020]). -/
noncomputable abbrev rsaLIL1 := exhLUL1

/-! ### svRSA (Models 4–5) — [spector-2017] supervaluationist RSA

QUD is a latent variable, and the prior does **not** enter `meaning` (unit
weights). Under the coarse QUD `Q_A` (all A-true worlds in one cell), L0 is
uniform `1/2` over both worlds, so `S1(A|w, coarse) = 1/5` is world-independent
— the prior's effect on S1 is neutralised (Appendix A.3). Under the fine QUD
`Q_fine`, exh makes A false at w_ab, so `S1(A|w_ab, fine) = 0` while
`S1(A|w_a, fine) = 1/2`. With a uniform QUD prior the marginal speaker is
`ms(w_a) = 7/20 > 1/10 = ms(w_ab)`: **categorical blocking**
(`ms(w_a) = ms(w_ab) + (1/2)·S1(A|w_a, fine) > ms(w_ab)`), matching Appendix A.3.
The QUD values correspond to `Discourse.QUD.trivial` (coarse) and
`Discourse.QUD.exact` (fine). svRSA1 and svRSA2 differ only at S2; both block at
L1. -/

/-- QUD for svRSA. `coarse` = `Q_A`; `fine` = `Q_fine`. -/
inductive CWSQUD where
  | coarse : CWSQUD
  | fine : CWSQUD
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- svRSA meaning: unit weights (no prior). Coarse uses literal truth, fine uses
exhaustified truth. -/
def qudMeaning (q : CWSQUD) (u : CWSUtterance) (w : CWSWorld) : ℝ≥0∞ :=
  match q with
  | .coarse => if literalTruth w u then 1 else 0
  | .fine => if exhMeaning w u then 1 else 0

theorem qudMeaning_coarse_apply (u : CWSUtterance) (w : CWSWorld) :
    qudMeaning .coarse u w = if literalTruth w u then 1 else 0 := rfl

theorem qudMeaning_fine_apply (u : CWSUtterance) (w : CWSWorld) :
    qudMeaning .fine u w = if exhMeaning w u then 1 else 0 := rfl

theorem qudMeaning_ne_top (q : CWSQUD) (u : CWSUtterance) : (∑' w, qudMeaning q u w) ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype
    (fun w => by cases q <;> simp only [qudMeaning] <;> split <;> simp)

theorem qudMeaning_pos (q : CWSQUD) (u : CWSUtterance) : (∑' w, qudMeaning q u w) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  cases q <;> cases u
  · exact ⟨.w_a, by rw [qudMeaning_coarse_apply, if_pos (by simp [literalTruth])]; simp⟩
  · exact ⟨.w_ab, by rw [qudMeaning_coarse_apply, if_pos (by simp [literalTruth])]; simp⟩
  · exact ⟨.w_a, by rw [qudMeaning_coarse_apply, if_pos (by simp [literalTruth])]; simp⟩
  · exact ⟨.w_a, by rw [qudMeaning_fine_apply, if_pos (by simp)]; simp⟩
  · exact ⟨.w_ab, by rw [qudMeaning_fine_apply, if_pos (by simp)]; simp⟩
  · exact ⟨.w_a, by rw [qudMeaning_fine_apply, if_pos (by simp)]; simp⟩

noncomputable def svRSAL0 (q : CWSQUD) (u : CWSUtterance) : PMF CWSWorld :=
  RSA.L0OfMeaning (qudMeaning q) u (qudMeaning_pos q u) (qudMeaning_ne_top q u)

private theorem svRSAL0_ofReal (q : CWSQUD) (u : CWSUtterance) (w : CWSWorld) (r : ℝ)
    (h : qudMeaning q u w * (∑' w', qudMeaning q u w')⁻¹ = ENNReal.ofReal r) :
    svRSAL0 q u w = ENNReal.ofReal r := by
  unfold svRSAL0; rw [RSA.L0OfMeaning_apply]; exact h

private theorem svRSAL0_one (q : CWSQUD) (u : CWSUtterance) (w : CWSWorld)
    (h : qudMeaning q u w * (∑' w', qudMeaning q u w')⁻¹ = 1) :
    svRSAL0 q u w = ENNReal.ofReal 1 := by
  unfold svRSAL0; rw [RSA.L0OfMeaning_apply, h]; simp

-- coarse: uniform 1/2 on A-true worlds (both), 1 on uniquely-true cells
theorem svRSAL0_coarse_A_wa : svRSAL0 .coarse .A .w_a = ENNReal.ofReal (1/2) := by
  apply svRSAL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [qudMeaning_coarse_apply, literalTruth, ↓reduceIte, add_zero]
  rw [show (1 : ℝ≥0∞) + 1 = ENNReal.ofReal 2 by rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem svRSAL0_coarse_A_wab : svRSAL0 .coarse .A .w_ab = ENNReal.ofReal (1/2) := by
  apply svRSAL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [qudMeaning_coarse_apply, literalTruth, ↓reduceIte, add_zero]
  rw [show (1 : ℝ≥0∞) + 1 = ENNReal.ofReal 2 by rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem svRSAL0_coarse_AandB_wa : svRSAL0 .coarse .AandB .w_a = ENNReal.ofReal 0 := by
  apply svRSAL0_ofReal; rw [qudMeaning_coarse_apply]; simp [literalTruth]

theorem svRSAL0_coarse_AandB_wab : svRSAL0 .coarse .AandB .w_ab = ENNReal.ofReal 1 := by
  apply svRSAL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [qudMeaning_coarse_apply, literalTruth, Bool.false_eq_true, if_false, if_true,
    ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem svRSAL0_coarse_AandNotB_wa : svRSAL0 .coarse .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply svRSAL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [qudMeaning_coarse_apply, literalTruth, Bool.false_eq_true, if_false, if_true,
    ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem svRSAL0_coarse_AandNotB_wab : svRSAL0 .coarse .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply svRSAL0_ofReal; rw [qudMeaning_coarse_apply]; simp [literalTruth]

-- fine: exh truth, unit weights
theorem svRSAL0_fine_A_wa : svRSAL0 .fine .A .w_a = ENNReal.ofReal 1 := by
  apply svRSAL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [qudMeaning_fine_apply, exhMeaning_A_wa, exhMeaning_A_wab, Bool.false_eq_true,
    if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem svRSAL0_fine_A_wab : svRSAL0 .fine .A .w_ab = ENNReal.ofReal 0 := by
  apply svRSAL0_ofReal; rw [qudMeaning_fine_apply]; simp

theorem svRSAL0_fine_AandB_wa : svRSAL0 .fine .AandB .w_a = ENNReal.ofReal 0 := by
  apply svRSAL0_ofReal; rw [qudMeaning_fine_apply]; simp

theorem svRSAL0_fine_AandB_wab : svRSAL0 .fine .AandB .w_ab = ENNReal.ofReal 1 := by
  apply svRSAL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [qudMeaning_fine_apply, exhMeaning_AandB_wa, exhMeaning_AandB_wab, Bool.false_eq_true,
    if_false, if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem svRSAL0_fine_AandNotB_wa : svRSAL0 .fine .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply svRSAL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [qudMeaning_fine_apply, exhMeaning_AandNotB_wa, exhMeaning_AandNotB_wab,
    Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem svRSAL0_fine_AandNotB_wab : svRSAL0 .fine .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply svRSAL0_ofReal; rw [qudMeaning_fine_apply]; simp

attribute [local pmf_eval_simps]
  svRSAL0_coarse_A_wa svRSAL0_coarse_A_wab svRSAL0_coarse_AandB_wa svRSAL0_coarse_AandB_wab
  svRSAL0_coarse_AandNotB_wa svRSAL0_coarse_AandNotB_wab
  svRSAL0_fine_A_wa svRSAL0_fine_A_wab svRSAL0_fine_AandB_wa svRSAL0_fine_AandB_wab
  svRSAL0_fine_AandNotB_wa svRSAL0_fine_AandNotB_wab

/-- Sum-over-`CWSQUD` unfolder, proved by `rfl`. -/
theorem CWSQUD_sum_univ {β : Type*} [AddCommMonoid β] (f : CWSQUD → β) :
    ∑ i, f i = f .coarse + (f .fine + 0) := by rfl

noncomputable def svRSAZ (q : CWSQUD) (w : CWSWorld) : ℝ≥0∞ :=
  ∑' u, (svRSAL0 q u w : ℝ≥0∞) ^ (2 : ℝ) * 1

theorem svRSAZ_eq_sum (q : CWSQUD) (w : CWSWorld) :
    svRSAZ q w = ∑' u, (svRSAL0 q u w) ^ (2 : ℕ) := by unfold svRSAZ; simp_rw [rpow_two_mul_one]

theorem svRSAZ_ne_top (q : CWSQUD) (w : CWSWorld) :
    (∑' u, (svRSAL0 q u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ ∞ := by
  refine ENNReal.tsum_ne_top_of_fintype (fun u => ?_)
  rw [rpow_two_mul_one]; exact ENNReal.pow_ne_top (PMF.apply_ne_top _ _)

theorem svRSAZ_ne_zero (q : CWSQUD) (w : CWSWorld) :
    (∑' u, (svRSAL0 q u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  cases q <;> cases w
  · exact ⟨.A, by rw [rpow_two_mul_one, svRSAL0_coarse_A_wa]; simp⟩
  · exact ⟨.A, by rw [rpow_two_mul_one, svRSAL0_coarse_A_wab]; simp⟩
  · exact ⟨.A, by rw [rpow_two_mul_one, svRSAL0_fine_A_wa]; simp⟩
  · exact ⟨.AandB, by rw [rpow_two_mul_one, svRSAL0_fine_AandB_wab]; simp⟩

theorem svRSAZ_coarse_wa : svRSAZ .coarse .w_a = ENNReal.ofReal (5/4) := by
  rw [svRSAZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1/2) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem svRSAZ_coarse_wab : svRSAZ .coarse .w_ab = ENNReal.ofReal (5/4) := by
  rw [svRSAZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1/2) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem svRSAZ_fine_wa : svRSAZ .fine .w_a = ENNReal.ofReal 2 := by
  rw [svRSAZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem svRSAZ_fine_wab : svRSAZ .fine .w_ab = ENNReal.ofReal 1 := by
  rw [svRSAZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

noncomputable def svRSAS1 (q : CWSQUD) (w : CWSWorld) : PMF CWSUtterance :=
  RSA.S1Belief (svRSAL0 q) (fun _ => 1) 2 w (svRSAZ_ne_zero q w) (svRSAZ_ne_top q w)

theorem svRSAS1_apply (q : CWSQUD) (w : CWSWorld) (u : CWSUtterance) :
    svRSAS1 q w u =
      (svRSAL0 q u w) ^ (2 : ℝ) * 1 * (∑' u', (svRSAL0 q u' w : ℝ≥0∞) ^ (2 : ℝ) * 1)⁻¹ := by
  unfold svRSAS1; rw [RSA.S1Belief_apply]

theorem svRSAS1_coarse_A_wa : svRSAS1 .coarse .w_a .A = ENNReal.ofReal (1/5) := by
  rw [svRSAS1_apply, rpow_two_mul_one,
      show (∑' u', (svRSAL0 .coarse u' .w_a : ℝ≥0∞) ^ (2 : ℝ) * 1) = svRSAZ .coarse .w_a from rfl,
      svRSAZ_coarse_wa, svRSAL0_coarse_A_wa, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem svRSAS1_coarse_A_wab : svRSAS1 .coarse .w_ab .A = ENNReal.ofReal (1/5) := by
  rw [svRSAS1_apply, rpow_two_mul_one,
      show (∑' u', (svRSAL0 .coarse u' .w_ab : ℝ≥0∞) ^ (2 : ℝ) * 1) = svRSAZ .coarse .w_ab from rfl,
      svRSAZ_coarse_wab, svRSAL0_coarse_A_wab, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem svRSAS1_fine_A_wa : svRSAS1 .fine .w_a .A = ENNReal.ofReal (1/2) := by
  rw [svRSAS1_apply, rpow_two_mul_one,
      show (∑' u', (svRSAL0 .fine u' .w_a : ℝ≥0∞) ^ (2 : ℝ) * 1) = svRSAZ .fine .w_a from rfl,
      svRSAZ_fine_wa, svRSAL0_fine_A_wa, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem svRSAS1_fine_A_wab : svRSAS1 .fine .w_ab .A = ENNReal.ofReal 0 := by
  rw [svRSAS1_apply, rpow_two_mul_one, svRSAL0_fine_A_wab, sq_ofReal _ (le_refl 0)]; simp

noncomputable def svRSAMarginalSpeaker (w : CWSWorld) : PMF CWSUtterance :=
  RSA.marginalizeKernel (PMF.uniformOfFintype CWSQUD) (fun q w => svRSAS1 q w) w

private theorem uniformQUD_apply (q : CWSQUD) :
    (PMF.uniformOfFintype CWSQUD) q = ENNReal.ofReal (1/2) := by
  rw [PMF.uniformOfFintype_apply, show Fintype.card CWSQUD = 2 from by decide,
      show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem svRSAMarginalSpeaker_apply (w : CWSWorld) (u : CWSUtterance) :
    svRSAMarginalSpeaker w u =
      ENNReal.ofReal (1/2) * svRSAS1 .coarse w u +
        (ENNReal.ofReal (1/2) * svRSAS1 .fine w u + 0) := by
  unfold svRSAMarginalSpeaker
  rw [RSA.marginalizeKernel_apply, tsum_fintype, CWSQUD_sum_univ,
      uniformQUD_apply, uniformQUD_apply]

theorem svRSA_ms_wa : svRSAMarginalSpeaker .w_a .A = ENNReal.ofReal (7/20) := by
  rw [svRSAMarginalSpeaker_apply, svRSAS1_coarse_A_wa, svRSAS1_fine_A_wa, add_zero,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem svRSA_ms_wab : svRSAMarginalSpeaker .w_ab .A = ENNReal.ofReal (1/10) := by
  rw [svRSAMarginalSpeaker_apply, svRSAS1_coarse_A_wab, svRSAS1_fine_A_wab,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), add_zero,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem svRSA_hMarg :
    PMF.marginal svRSAMarginalSpeaker (PMF.uniformOfFintype CWSWorld) .A ≠ 0 := by
  refine PMF.marginal_ne_zero svRSAMarginalSpeaker _ _ (a := CWSWorld.w_a) ?_ ?_
  · exact (PMF.uniformOfFintype CWSWorld).mem_support_iff CWSWorld.w_a |>.mp
      (PMF.mem_support_uniformOfFintype CWSWorld.w_a)
  · rw [svRSA_ms_wa]; simp

/-- svRSA pragmatic listener. -/
noncomputable def svRSAL1 (u : CWSUtterance)
    (h : PMF.marginal svRSAMarginalSpeaker (PMF.uniformOfFintype CWSWorld) u ≠ 0) : PMF CWSWorld :=
  PMF.posterior svRSAMarginalSpeaker (PMF.uniformOfFintype CWSWorld) u h

/-! ### FREE-LU (Model 6) — [bergen-levy-goodman-2016]

Three interpretations as latent variables (literal / exh / antiExh), each with
the prior baked into `meaning`. The anti-exhaustive interpretation makes A mean
A∧B (true only at w_ab). With prior-in-L0, the literal parse is asymmetric
(`S1(A|w_ab, lit) = 9/25 > 1/17 = S1(A|w_a, lit)`), and the anti-exh parse
contributes `S1(A|w_ab, antiExh) = 1/2` at w_ab (`0` at w_a). So
`T(w_ab) = 9/25 + 0 + 1/2 = 43/50 > 19/34 = 1/17 + 1/2 + 0 = T(w_a)`. With the
uniform interpretation prior the marginal speaker is `ms(w_ab) = 43/150 >
19/102 = ms(w_a)`: genuine anti-exhaustivity, matching the paper. -/

/-- Interpretation for FREE-LU. `literal`, `exh` (A∧¬B), `antiExh` (A∧B). -/
inductive CWSInterpretation where
  | literal : CWSInterpretation
  | exh : CWSInterpretation
  | antiExh : CWSInterpretation
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Anti-exhaustive meaning: A means A ∧ B (true only in w_ab); A∧B and A∧¬B
unaffected. -/
def antiExhMeaning : CWSWorld → CWSUtterance → Bool
  | .w_a, .A => false
  | .w_ab, .A => true
  | w, u => literalTruth w u

/-- Meaning under each interpretation. -/
def interpMeaning : CWSInterpretation → CWSWorld → CWSUtterance → Bool
  | .literal => literalTruth
  | .exh => exhMeaning
  | .antiExh => antiExhMeaning

/-- FREE-LU meaning lifted to `ℝ≥0∞` (prior baked in). -/
def interpMeaningE (i : CWSInterpretation) (u : CWSUtterance) (w : CWSWorld) : ℝ≥0∞ :=
  if interpMeaning i w u then ENNReal.ofReal (priorWeight w) else 0

theorem interpMeaningE_apply (i : CWSInterpretation) (u : CWSUtterance) (w : CWSWorld) :
    interpMeaningE i u w = if interpMeaning i w u then ENNReal.ofReal (priorWeight w) else 0 := rfl

theorem interpMeaningE_ne_top (i : CWSInterpretation) (u : CWSUtterance) :
    (∑' w, interpMeaningE i u w) ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype
    (fun w => by rw [interpMeaningE_apply]; split <;> simp [ENNReal.ofReal_ne_top])

theorem interpMeaningE_pos (i : CWSInterpretation) (u : CWSUtterance) :
    (∑' w, interpMeaningE i u w) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  cases i <;> cases u
  · exact ⟨.w_a, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning, literalTruth])]; simp [priorWeight]⟩
  · exact ⟨.w_ab, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning, literalTruth])]; simp [priorWeight]⟩
  · exact ⟨.w_a, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning, literalTruth])]; simp [priorWeight]⟩
  · exact ⟨.w_a, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning])]; simp [priorWeight]⟩
  · exact ⟨.w_ab, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning])]; simp [priorWeight]⟩
  · exact ⟨.w_a, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning])]; simp [priorWeight]⟩
  · exact ⟨.w_ab, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning, antiExhMeaning])]; simp [priorWeight]⟩
  · exact ⟨.w_ab, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning, antiExhMeaning, literalTruth])]; simp [priorWeight]⟩
  · exact ⟨.w_a, by rw [interpMeaningE_apply, if_pos (by simp [interpMeaning, antiExhMeaning, literalTruth])]; simp [priorWeight]⟩

noncomputable def freeLUL0 (i : CWSInterpretation) (u : CWSUtterance) : PMF CWSWorld :=
  RSA.L0OfMeaning (interpMeaningE i) u (interpMeaningE_pos i u) (interpMeaningE_ne_top i u)

private theorem freeLUL0_ofReal (i : CWSInterpretation) (u : CWSUtterance) (w : CWSWorld) (r : ℝ)
    (h : interpMeaningE i u w * (∑' w', interpMeaningE i u w')⁻¹ = ENNReal.ofReal r) :
    freeLUL0 i u w = ENNReal.ofReal r := by
  unfold freeLUL0; rw [RSA.L0OfMeaning_apply]; exact h

private theorem freeLUL0_one (i : CWSInterpretation) (u : CWSUtterance) (w : CWSWorld)
    (h : interpMeaningE i u w * (∑' w', interpMeaningE i u w')⁻¹ = 1) :
    freeLUL0 i u w = ENNReal.ofReal 1 := by
  unfold freeLUL0; rw [RSA.L0OfMeaning_apply, h]; simp

-- only the `.A` cells (the prediction touches only S1 at .A) plus the full per-parse
-- Z need every cell; provide all 18.
theorem freeLUL0_lit_A_wa : freeLUL0 .literal .A .w_a = ENNReal.ofReal (1/4) := by
  apply freeLUL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, literalTruth, priorWeight, ↓reduceIte, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem freeLUL0_lit_A_wab : freeLUL0 .literal .A .w_ab = ENNReal.ofReal (3/4) := by
  apply freeLUL0_ofReal; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, literalTruth, priorWeight, ↓reduceIte, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem freeLUL0_lit_AandB_wa : freeLUL0 .literal .AandB .w_a = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning, literalTruth]

theorem freeLUL0_lit_AandB_wab : freeLUL0 .literal .AandB .w_ab = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, literalTruth, priorWeight, Bool.false_eq_true,
    if_false, if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_lit_AandNotB_wa : freeLUL0 .literal .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, literalTruth, priorWeight, Bool.false_eq_true,
    if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_lit_AandNotB_wab : freeLUL0 .literal .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning, literalTruth]

theorem freeLUL0_exh_A_wa : freeLUL0 .exh .A .w_a = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, exhMeaning_A_wa, exhMeaning_A_wab, priorWeight,
    Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_exh_A_wab : freeLUL0 .exh .A .w_ab = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning]

theorem freeLUL0_exh_AandB_wa : freeLUL0 .exh .AandB .w_a = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning]

theorem freeLUL0_exh_AandB_wab : freeLUL0 .exh .AandB .w_ab = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, exhMeaning_AandB_wa, exhMeaning_AandB_wab,
    priorWeight, Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_exh_AandNotB_wa : freeLUL0 .exh .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, exhMeaning_AandNotB_wa, exhMeaning_AandNotB_wab,
    priorWeight, Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_exh_AandNotB_wab : freeLUL0 .exh .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning]

theorem freeLUL0_anti_A_wa : freeLUL0 .antiExh .A .w_a = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning, antiExhMeaning]

theorem freeLUL0_anti_A_wab : freeLUL0 .antiExh .A .w_ab = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, antiExhMeaning, priorWeight, Bool.false_eq_true,
    if_false, if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_anti_AandB_wa : freeLUL0 .antiExh .AandB .w_a = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning, antiExhMeaning, literalTruth]

theorem freeLUL0_anti_AandB_wab : freeLUL0 .antiExh .AandB .w_ab = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, antiExhMeaning, literalTruth, priorWeight,
    Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero, zero_add]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_anti_AandNotB_wa : freeLUL0 .antiExh .AandNotB .w_a = ENNReal.ofReal 1 := by
  apply freeLUL0_one; rw [tsum_fintype, CWSWorld_sum_univ]
  simp only [interpMeaningE_apply, interpMeaning, antiExhMeaning, literalTruth, priorWeight,
    Bool.false_eq_true, if_false, if_true, ↓reduceIte, add_zero]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]

theorem freeLUL0_anti_AandNotB_wab : freeLUL0 .antiExh .AandNotB .w_ab = ENNReal.ofReal 0 := by
  apply freeLUL0_ofReal; rw [interpMeaningE_apply]; simp [interpMeaning, antiExhMeaning, literalTruth]

attribute [local pmf_eval_simps]
  freeLUL0_lit_A_wa freeLUL0_lit_A_wab freeLUL0_lit_AandB_wa freeLUL0_lit_AandB_wab
  freeLUL0_lit_AandNotB_wa freeLUL0_lit_AandNotB_wab
  freeLUL0_exh_A_wa freeLUL0_exh_A_wab freeLUL0_exh_AandB_wa freeLUL0_exh_AandB_wab
  freeLUL0_exh_AandNotB_wa freeLUL0_exh_AandNotB_wab
  freeLUL0_anti_A_wa freeLUL0_anti_A_wab freeLUL0_anti_AandB_wa freeLUL0_anti_AandB_wab
  freeLUL0_anti_AandNotB_wa freeLUL0_anti_AandNotB_wab

/-- Sum-over-`CWSInterpretation` unfolder, proved by `rfl`. -/
theorem CWSInterpretation_sum_univ {β : Type*} [AddCommMonoid β] (f : CWSInterpretation → β) :
    ∑ i, f i = f .literal + (f .exh + (f .antiExh + 0)) := by rfl

noncomputable def freeLUZ (i : CWSInterpretation) (w : CWSWorld) : ℝ≥0∞ :=
  ∑' u, (freeLUL0 i u w : ℝ≥0∞) ^ (2 : ℝ) * 1

theorem freeLUZ_eq_sum (i : CWSInterpretation) (w : CWSWorld) :
    freeLUZ i w = ∑' u, (freeLUL0 i u w) ^ (2 : ℕ) := by unfold freeLUZ; simp_rw [rpow_two_mul_one]

theorem freeLUZ_ne_top (i : CWSInterpretation) (w : CWSWorld) :
    (∑' u, (freeLUL0 i u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ ∞ := by
  refine ENNReal.tsum_ne_top_of_fintype (fun u => ?_)
  rw [rpow_two_mul_one]; exact ENNReal.pow_ne_top (PMF.apply_ne_top _ _)

theorem freeLUZ_ne_zero (i : CWSInterpretation) (w : CWSWorld) :
    (∑' u, (freeLUL0 i u w : ℝ≥0∞) ^ (2 : ℝ) * 1) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  cases i <;> cases w
  · exact ⟨.A, by rw [rpow_two_mul_one, freeLUL0_lit_A_wa]; simp⟩
  · exact ⟨.A, by rw [rpow_two_mul_one, freeLUL0_lit_A_wab]; simp⟩
  · exact ⟨.A, by rw [rpow_two_mul_one, freeLUL0_exh_A_wa]; simp⟩
  · exact ⟨.AandB, by rw [rpow_two_mul_one, freeLUL0_exh_AandB_wab]; simp⟩
  · exact ⟨.AandNotB, by rw [rpow_two_mul_one, freeLUL0_anti_AandNotB_wa]; simp⟩
  · exact ⟨.A, by rw [rpow_two_mul_one, freeLUL0_anti_A_wab]; simp⟩

theorem freeLUZ_lit_wa : freeLUZ .literal .w_a = ENNReal.ofReal (17/16) := by
  rw [freeLUZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1/4) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem freeLUZ_lit_wab : freeLUZ .literal .w_ab = ENNReal.ofReal (25/16) := by
  rw [freeLUZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (3/4) (by norm_num), sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

theorem freeLUZ_anti_wab : freeLUZ .antiExh .w_ab = ENNReal.ofReal 2 := by
  rw [freeLUZ_eq_sum, tsum_fintype]; pmf_eval_only
  rw [sq_ofReal (1:ℝ) (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
  ennreal_close

noncomputable def freeLUS1 (i : CWSInterpretation) (w : CWSWorld) : PMF CWSUtterance :=
  RSA.S1Belief (freeLUL0 i) (fun _ => 1) 2 w (freeLUZ_ne_zero i w) (freeLUZ_ne_top i w)

theorem freeLUS1_apply (i : CWSInterpretation) (w : CWSWorld) (u : CWSUtterance) :
    freeLUS1 i w u =
      (freeLUL0 i u w) ^ (2 : ℝ) * 1 * (∑' u', (freeLUL0 i u' w : ℝ≥0∞) ^ (2 : ℝ) * 1)⁻¹ := by
  unfold freeLUS1; rw [RSA.S1Belief_apply]

theorem freeLUS1_lit_A_wa : freeLUS1 .literal .w_a .A = ENNReal.ofReal (1/17) := by
  rw [freeLUS1_apply, rpow_two_mul_one,
      show (∑' u', (freeLUL0 .literal u' .w_a : ℝ≥0∞) ^ (2 : ℝ) * 1) = freeLUZ .literal .w_a from rfl,
      freeLUZ_lit_wa, freeLUL0_lit_A_wa, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem freeLUS1_lit_A_wab : freeLUS1 .literal .w_ab .A = ENNReal.ofReal (9/25) := by
  rw [freeLUS1_apply, rpow_two_mul_one,
      show (∑' u', (freeLUL0 .literal u' .w_ab : ℝ≥0∞) ^ (2 : ℝ) * 1) = freeLUZ .literal .w_ab from rfl,
      freeLUZ_lit_wab, freeLUL0_lit_A_wab, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

/-- exh interpretation: A false at w_a (`S1 = 0`). -/
theorem freeLUS1_exh_A_wa : freeLUS1 .exh .w_a .A = ENNReal.ofReal (1/2) := by
  rw [freeLUS1_apply, rpow_two_mul_one,
      show (∑' u', (freeLUL0 .exh u' .w_a : ℝ≥0∞) ^ (2 : ℝ) * 1) = freeLUZ .exh .w_a from rfl]
  -- freeLUZ .exh .w_a = 2 (A=1, AandB=0, AandNotB=1 squared)
  rw [show freeLUZ .exh .w_a = ENNReal.ofReal 2 by
        rw [freeLUZ_eq_sum, tsum_fintype]; pmf_eval_only
        rw [sq_ofReal (1:ℝ) (by norm_num)]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add]
        ennreal_close,
      freeLUL0_exh_A_wa, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem freeLUS1_exh_A_wab : freeLUS1 .exh .w_ab .A = ENNReal.ofReal 0 := by
  rw [freeLUS1_apply, rpow_two_mul_one, freeLUL0_exh_A_wab, sq_ofReal _ (le_refl 0)]; simp

theorem freeLUS1_anti_A_wa : freeLUS1 .antiExh .w_a .A = ENNReal.ofReal 0 := by
  rw [freeLUS1_apply, rpow_two_mul_one, freeLUL0_anti_A_wa, sq_ofReal _ (le_refl 0)]; simp

theorem freeLUS1_anti_A_wab : freeLUS1 .antiExh .w_ab .A = ENNReal.ofReal (1/2) := by
  rw [freeLUS1_apply, rpow_two_mul_one,
      show (∑' u', (freeLUL0 .antiExh u' .w_ab : ℝ≥0∞) ^ (2 : ℝ) * 1) = freeLUZ .antiExh .w_ab from rfl,
      freeLUZ_anti_wab, freeLUL0_anti_A_wab, sq_ofReal _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; norm_num

noncomputable def freeLUMarginalSpeaker (w : CWSWorld) : PMF CWSUtterance :=
  RSA.marginalizeKernel (PMF.uniformOfFintype CWSInterpretation) (fun i w => freeLUS1 i w) w

private theorem uniformInterp_apply (i : CWSInterpretation) :
    (PMF.uniformOfFintype CWSInterpretation) i = ENNReal.ofReal (1/3) := by
  rw [PMF.uniformOfFintype_apply, show Fintype.card CWSInterpretation = 3 from by decide,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem freeLUMarginalSpeaker_apply (w : CWSWorld) (u : CWSUtterance) :
    freeLUMarginalSpeaker w u =
      ENNReal.ofReal (1/3) * freeLUS1 .literal w u +
        (ENNReal.ofReal (1/3) * freeLUS1 .exh w u +
          (ENNReal.ofReal (1/3) * freeLUS1 .antiExh w u + 0)) := by
  unfold freeLUMarginalSpeaker
  rw [RSA.marginalizeKernel_apply, tsum_fintype, CWSInterpretation_sum_univ,
      uniformInterp_apply, uniformInterp_apply, uniformInterp_apply]

theorem freeLU_ms_wa : freeLUMarginalSpeaker .w_a .A = ENNReal.ofReal (19/102) := by
  rw [freeLUMarginalSpeaker_apply, freeLUS1_lit_A_wa, freeLUS1_exh_A_wa, freeLUS1_anti_A_wa,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), add_zero,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem freeLU_ms_wab : freeLUMarginalSpeaker .w_ab .A = ENNReal.ofReal (43/150) := by
  rw [freeLUMarginalSpeaker_apply, freeLUS1_lit_A_wab, freeLUS1_exh_A_wab, freeLUS1_anti_A_wab,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), add_zero,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem freeLU_hMarg :
    PMF.marginal freeLUMarginalSpeaker (PMF.uniformOfFintype CWSWorld) .A ≠ 0 := by
  refine PMF.marginal_ne_zero freeLUMarginalSpeaker _ _ (a := CWSWorld.w_a) ?_ ?_
  · exact (PMF.uniformOfFintype CWSWorld).mem_support_iff CWSWorld.w_a |>.mp
      (PMF.mem_support_uniformOfFintype CWSWorld.w_a)
  · rw [freeLU_ms_wa]; simp

/-- FREE-LU pragmatic listener. -/
noncomputable def freeLUL1 (u : CWSUtterance)
    (h : PMF.marginal freeLUMarginalSpeaker (PMF.uniformOfFintype CWSWorld) u ≠ 0) : PMF CWSWorld :=
  PMF.posterior freeLUMarginalSpeaker (PMF.uniformOfFintype CWSWorld) u h

/-! ### wRSA (Models 2–3) — [degen-etal-2015] joint world–background listener

wRSA's distinctive mechanism is a **world-dependent latent prior** `P(w|b)·P(b)`:
the background `b` is `wonky` (a uniform world prior) or `default_` (the 3:1
bias). The listener is jointly uncertain about `(w, b)`, so the model is a clean
`RSA.jointListener` over the joint prior `RSA.jointPrior`, with the world belief
read off as the `W`-marginal of the `(World × Background)` posterior — no
bundled-config encoding needed. The per-background speaker reuses the already-proven
closed forms: under `default_` the biased prior is baked into L0 (eq. 1 of §4.1),
so its speaker is `baselineS1`; under `wonky` it uses uniform-prior literal
meaning, the plain literal RSA speaker — which coincides by construction with
`svRSAS1 .coarse` (whose coarse QUD is the trivial partition), reused here to
avoid duplicating the closed forms rather than as a dependence on svRSA.

The anti-exhaustivity test `wRSAL1(.A) w_ab > wRSAL1(.A) w_a` reduces (via
`RSA.jointListener_lt_iff_sum_score_lt`, the marginal normaliser cancelling) to
the latent-summed score comparison
`Σ_b μ(w_ab,b)·S1(.A|w_ab,b) > Σ_b μ(w_a,b)·S1(.A|w_a,b)`. The prediction is
**anti-exhaustive** (`w_ab > w_a`), preserving the model's classification: even
averaging in the wonky (uniform) background, the biased `default_` background
amplifies S1 toward w_ab. -/

/-- Background assumption for wRSA: `wonky` (uniform prior over worlds) vs
`default_` (prior follows the bias). -/
inductive CWSBackground where
  | wonky : CWSBackground
  | default_ : CWSBackground
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- World prior conditioned on the background `P(w|b)`. Under `default_`, w_ab
gets 3× the weight of w_a (P(w_a)=1/4, P(w_ab)=3/4 — the 1:3 bias); under
`wonky`, both worlds are equally likely (1/2, 1/2). -/
noncomputable def worldGivenBg : CWSBackground → PMF CWSWorld
  | .wonky => PMF.ofFintype (fun _ => ENNReal.ofReal (1/2))
      (by rw [CWSWorld_sum_univ, add_zero,
              ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num)
  | .default_ => PMF.ofFintype
      (fun w => match w with | .w_a => ENNReal.ofReal (1/4) | .w_ab => ENNReal.ofReal (3/4))
      (by rw [CWSWorld_sum_univ, add_zero,
              ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num)

theorem worldGivenBg_wonky (w : CWSWorld) : worldGivenBg .wonky w = ENNReal.ofReal (1/2) := rfl
theorem worldGivenBg_default_wa : worldGivenBg .default_ .w_a = ENNReal.ofReal (1/4) := rfl
theorem worldGivenBg_default_wab : worldGivenBg .default_ .w_ab = ENNReal.ofReal (3/4) := rfl

/-- Background prior `P(b)`: uniform over `CWSBackground`. -/
noncomputable def bgPrior : PMF CWSBackground := PMF.uniformOfFintype CWSBackground

theorem bgPrior_apply (b : CWSBackground) : bgPrior b = ENNReal.ofReal (1/2) := by
  rw [bgPrior, PMF.uniformOfFintype_apply, show Fintype.card CWSBackground = 2 from by decide,
      show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The joint world–background prior `μ(w,b) = P(b)·P(w|b)` ([degen-etal-2015]). -/
noncomputable def wRSAJointPrior : PMF (CWSWorld × CWSBackground) :=
  RSA.jointPrior bgPrior worldGivenBg

/-- Per-background speaker, reusing this file's proven closed forms by shared
construction: `default_` bakes the biased prior into L0, so it is `baselineS1`;
`wonky` uses uniform-prior literal meaning, so it is the plain literal RSA
speaker (= `svRSAS1 .coarse`, whose coarse QUD is the trivial partition). -/
noncomputable def wRSAS1Kernel : CWSWorld × CWSBackground → PMF CWSUtterance
  | (w, .wonky) => svRSAS1 .coarse w
  | (w, .default_) => baselineS1 w

theorem wRSAJointPrior_apply (w : CWSWorld) (b : CWSBackground) :
    wRSAJointPrior (w, b) = bgPrior b * worldGivenBg b w := by
  rw [wRSAJointPrior, RSA.jointPrior_apply]

theorem wRSA_hMarg : PMF.marginal wRSAS1Kernel wRSAJointPrior .A ≠ 0 := by
  refine PMF.marginal_ne_zero wRSAS1Kernel _ _ (a := (CWSWorld.w_ab, CWSBackground.default_)) ?_ ?_
  · rw [wRSAJointPrior_apply, bgPrior_apply, worldGivenBg_default_wab]; simp
  · show baselineS1 .w_ab .A ≠ 0; rw [baselineS1_A_wab]; simp

/-- wRSA pragmatic listener: the world-marginal of the joint `(World ×
Background)` posterior (BwRSA is identical at L1). -/
noncomputable def wRSAL1 (u : CWSUtterance)
    (h : PMF.marginal wRSAS1Kernel wRSAJointPrior u ≠ 0) : PMF CWSWorld :=
  RSA.jointListener wRSAS1Kernel wRSAJointPrior u h

/-- Sum over the 2-element background latent. -/
private theorem background_sum {M : Type*} [AddCommMonoid M] (f : CWSBackground → M) :
    ∑ l, f l = f CWSBackground.wonky + f CWSBackground.default_ :=
  Fintype.sum_eq_add CWSBackground.wonky CWSBackground.default_ (by decide)
    (fun x ⟨_, _⟩ => by cases x <;> simp_all)

/-! ### Predictions

Each prediction reduces, under the uniform world prior, to a `marginalSpeaker`
comparison via `PMF.posterior_lt_iff_kernel_lt_of_uniform`, then to a rational
comparison via `ENNReal.ofReal_lt_ofReal_iff`. -/

/-- Baseline RSA is genuinely anti-exhaustive: `L1(.A) w_ab > L1(.A) w_a`.

    With prior-in-L0, S1 is asymmetric (`S1(A|w_ab) = 9/25 > 1/17 = S1(A|w_a)`)
    because `L0(w_ab|A) = 3/4 > 1/4 = L0(w_a|A)`. The speaker preferentially uses
    A when w_ab is true, since L0 already favours w_ab given A. This is the
    paper's central problematic prediction (Eq. 6b, Fig. 1). -/
theorem baseline_antiexhaustive :
    baselineL1 .A baseline_hMarg .w_ab > baselineL1 .A baseline_hMarg .w_a := by
  rw [baselineL1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      baselineS1_A_wa, baselineS1_A_wab]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- EXH-LU blocks anti-exhaustivity: even with prior-in-L0 and 3:1 bias,
    `L1(.A) w_a > L1(.A) w_ab`. The exh parse contributes `S1(A|w_a, exh) = 1/2`
    but `S1(A|w_ab, exh) = 0`, outweighing the literal parse's prior
    amplification: `ms(w_a) = 19/68 > 9/50 = ms(w_ab)`. -/
theorem exhlu_blocks_antiexhaustivity :
    exhLUL1 .A exhLU_hMarg .w_a > exhLUL1 .A exhLU_hMarg .w_ab := by
  rw [exhLUL1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      exhLU_ms_wab, exhLU_ms_wa]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- EXH(A) is false in w_ab — the structural basis for blocking. -/
theorem exh_meaning_blocks_wab : exhMeaning .w_ab .A = false := exhMeaning_A_wab

/-- RSA-LI blocks anti-exhaustivity (same as EXH-LU at L1). -/
theorem rsali_blocks_antiexhaustivity :
    rsaLIL1 .A exhLU_hMarg .w_a > rsaLIL1 .A exhLU_hMarg .w_ab :=
  exhlu_blocks_antiexhaustivity

/-- svRSA blocks anti-exhaustivity **categorically** (Appendix A.3): under the
    coarse QUD `S1(A|w, coarse) = 1/5` for both worlds, and under the fine QUD
    `S1(A|w_ab, fine) = 0` while `S1(A|w_a, fine) = 1/2`. So
    `ms(w_a) = 7/20 > 1/10 = ms(w_ab)`. -/
theorem svRSA_blocks_antiexhaustivity :
    svRSAL1 .A svRSA_hMarg .w_a > svRSAL1 .A svRSA_hMarg .w_ab := by
  rw [svRSAL1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      svRSA_ms_wab, svRSA_ms_wa]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- FREE-LU is genuinely anti-exhaustive: with prior-in-L0 the literal parse's
    S1 asymmetry makes the anti-exh interpretation dominant at w_ab.
    `ms(w_ab) = 43/150 > 19/102 = ms(w_a)`. -/
theorem freelu_antiexhaustive :
    freeLUL1 .A freeLU_hMarg .w_ab > freeLUL1 .A freeLU_hMarg .w_a := by
  rw [freeLUL1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      freeLU_ms_wa, freeLU_ms_wab]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- wRSA is anti-exhaustive: the `default_` background bakes the biased prior into
    L0, making S1 asymmetric; even averaging in the wonky (uniform) background,
    the biased background dominates. Reduces to the latent-summed score comparison
    `Σ_b μ(w_ab,b)·S1(.A|w_ab,b) > Σ_b μ(w_a,b)·S1(.A|w_a,b)`, i.e.
    `1/20 + 27/200 > 1/20 + 1/136`. -/
theorem wRSA_biased_antiexhaustive :
    wRSAL1 .A wRSA_hMarg .w_ab > wRSAL1 .A wRSA_hMarg .w_a := by
  rw [wRSAL1, gt_iff_lt, RSA.jointListener_lt_iff_sum_score_lt,
      background_sum (fun b => wRSAJointPrior (.w_a, b) * wRSAS1Kernel (.w_a, b) .A),
      background_sum (fun b => wRSAJointPrior (.w_ab, b) * wRSAS1Kernel (.w_ab, b) .A)]
  simp only [wRSAJointPrior_apply, bgPrior_apply, worldGivenBg_wonky, worldGivenBg_default_wa,
    worldGivenBg_default_wab]
  show ENNReal.ofReal (1/2) * ENNReal.ofReal (1/2) * svRSAS1 .coarse .w_a .A +
        ENNReal.ofReal (1/2) * ENNReal.ofReal (1/4) * baselineS1 .w_a .A <
       ENNReal.ofReal (1/2) * ENNReal.ofReal (1/2) * svRSAS1 .coarse .w_ab .A +
        ENNReal.ofReal (1/2) * ENNReal.ofReal (3/4) * baselineS1 .w_ab .A
  rw [svRSAS1_coarse_A_wa, svRSAS1_coarse_A_wab, baselineS1_A_wa, baselineS1_A_wab,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! ### Classification

The paper's central result: the 9 RSA models fall into two groups. The
**anti-exhaustive** group (baseline, wRSA/BwRSA, FREE-LU) lets the prior bias
amplify through S1, predicting listeners infer w_ab from "A" — contradicting the
experimental data. The **exhaustive** group (EXH-LU, RSA-LI1/2, svRSA1/2) blocks
anti-exhaustivity via grammatical exhaustification or QUD gating, matching the
data. -/

theorem antiexhaustive_group :
    baselineL1 .A baseline_hMarg .w_ab > baselineL1 .A baseline_hMarg .w_a ∧
    wRSAL1 .A wRSA_hMarg .w_ab > wRSAL1 .A wRSA_hMarg .w_a ∧
    freeLUL1 .A freeLU_hMarg .w_ab > freeLUL1 .A freeLU_hMarg .w_a :=
  ⟨baseline_antiexhaustive, wRSA_biased_antiexhaustive, freelu_antiexhaustive⟩

theorem exhaustive_group :
    exhLUL1 .A exhLU_hMarg .w_a > exhLUL1 .A exhLU_hMarg .w_ab ∧
    rsaLIL1 .A exhLU_hMarg .w_a > rsaLIL1 .A exhLU_hMarg .w_ab ∧
    svRSAL1 .A svRSA_hMarg .w_a > svRSAL1 .A svRSA_hMarg .w_ab :=
  ⟨exhlu_blocks_antiexhaustivity, rsali_blocks_antiexhaustivity, svRSA_blocks_antiexhaustivity⟩

end CremersWilcoxSpector2023
