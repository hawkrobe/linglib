import Mathlib.Data.Rat.Defs
import Linglib.Theories.Semantics.Exhaustification.Innocent
import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Tactics.RSAPredict

/-!
# @cite{cremers-wilcox-spector-2023}: Exhaustivity and Anti-Exhaustivity in RSA

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

## Prior Placement

The paper's L0 includes the prior (eq. 1): L0(w|u) ∝ P(w) · ⟦u⟧(w).
The paper also has P(w) at L1 (eq. 3): L1(w|u) ∝ P(w) · S1(u|w).
So P(w) enters twice — in L0 and L1.

For models where prior biases L0 (baseline, EXH-LU, wRSA, FREE-LU), we
bake P(w) into `meaning` and set `worldPrior = 1`. This is equivalent to
double-counting for anti-exhaustivity classification (Appendix A.1, eq. A.4):
L1(w_ab|A) > P(w_ab) ⟺ T(w_ab) > T(w_a) where T(w) = Σ_l P(l)·S1(A|w,l),
regardless of worldPrior. With worldPrior = 1, L1_score(w) = T(w), so
the comparison `L1(.A, .w_ab) > L1(.A, .w_a)` IS the anti-exhaustivity test.

For svRSA, the prior does NOT enter meaning. Under Q_A (coarse QUD), QUD
projection aggregates all A-true worlds into one cell, making
L0(Q_A(w)|A) = 1 for all w. This neutralizes the prior's effect on S1,
giving world-independent S1 under Q_A (Appendix A.3). Our encoding
captures this by using uniform weights in meaning under both QUDs:
L0(w|A, coarse) = 1/2 for both worlds.

## Anti-Exhaustivity Definition

The paper's definition (Eq. 6b, equal costs): L1(w_ab|A) > P(w_ab),
equivalently T(w_ab) > T(w_a) (Appendix A.1, eq. A.4). With our encoding
(worldPrior = 1), this reduces to `L1(.A, .w_ab) > L1(.A, .w_a)`.

## Utterance Costs

The paper includes costs c(A) = 0, c(A∧B) = c(A∧¬B) = c (eq. 2):
S1(u|w) ∝ exp(λ(log L0(w|u) - c(u))) = L0(w|u)^λ · exp(-λc(u)).
With equal costs for A∧B and A∧¬B, the cost terms cancel in the
anti-exhaustivity condition (eq. 6b): the classification depends only on
the log-prior ratio. We set all costs to 0 in our configs; the analytic
condition in `antiExhaustivityCondition` handles the general case.

## Model Classification

The paper's 9 models fall into two groups by anti-exhaustivity behavior:

| # | Model | Mechanism | Anti-exhaustive? | Config |
|---|-------|-----------|-----------------|--------|
| 1 | Baseline RSA | — | Yes | `baselineBiased` |
| 2 | wRSA | Prior-in-L0 via background | Yes | `wRSABiased` |
| 3 | BwRSA | Bayesian wRSA | Yes (= wRSA at L1) | `wRSABiased` |
| 4 | svRSA1 | QUD blocks at S1 | No | `svRSABiased` |
| 5 | svRSA2 | QUD blocks at S1 | No | `svRSABiased` |
| 6 | FREE-LU | Free parse choice | Yes | `freeLUBiased` |
| 7 | EXH-LU | EXH blocks at L0 | No | `exhLUBiased` |
| 8 | RSA-LI1 | EXH blocks at L0 | No (= EXH-LU at L1) | `rsaLIBiased` |
| 9 | RSA-LI2 | EXH blocks at L0 | No (= EXH-LU at L1) | `rsaLIBiased` |

All 9 models are encoded as `RSAConfig` instances. Each model's
distinctive mechanism maps to a different `Latent` type and `meaning`.
Costs enter S1 via `utteranceCost` (= 0, so exp(-λ·0) = 1 is implicit);
the analytic condition `antiExhaustivityCondition` handles general costs.

RSA-LI (Models 8–9) is @cite{franke-bergen-2020}'s Lexical Intentions model;
at L1 with uniform P(i) and equal costs it equals EXH-LU (Table 1).
wRSA and BwRSA are identical at L1 (BwRSA adds a Bayesian S2 layer).
svRSA uses no prior in L0 meaning — QUD projection neutralizes it
(Appendix A.3), giving categorical blocking.

## Connection to Other Formalizations

- `ExhaustivityLimit.lean`: proves RSA at α→∞ recovers Fox's exh,
  using the same IE infrastructure (`Exhaustification.Innocent.exhIE`)
  as our `exhMeaning`.
- `FrankeBergen2020.lean`: formalizes four RSA models (vanilla, LU, LI, GI)
  for nested quantifiers, using compositional exhaustification.
- `ScopeExpressivity.lean`: demonstrates the scope-blind vs scope-sensitive
  expressivity gap between standard RSA and compositional EXH.
-/

set_option autoImplicit false

namespace CremersWilcoxSpector2023

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Two-world model for exhaustivity.
    - `w_a`: A true, B false (A ∧ ¬B)
    - `w_ab`: A and B both true (A ∧ B)

    No w_b or w_none because we condition on A being true.
    The question is whether B is also true. -/
inductive CWSWorld where
  | w_a : CWSWorld
  | w_ab : CWSWorld
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CWSWorld where
  elems := {.w_a, .w_ab}
  complete := fun x => by cases x <;> simp

/-- Three utterances in the minimal exhaustivity domain. -/
inductive CWSUtterance where
  | A : CWSUtterance
  | AandB : CWSUtterance
  | AandNotB : CWSUtterance
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CWSUtterance where
  elems := {.A, .AandB, .AandNotB}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Literal Semantics
-- ============================================================================

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

-- ============================================================================
-- §3. Exhaustification (Innocent Exclusion)
-- ============================================================================

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
  constructor <;> native_decide

/-- EXH(A∧B) unchanged: A∧B has no stronger alternative. -/
theorem exhAB_unchanged : ∀ w, exhMeaning w .AandB = literalTruth w .AandB := by
  native_decide

/-- EXH(A∧¬B) unchanged: A∧¬B has no stronger alternative. -/
theorem exhAnotB_unchanged : ∀ w, exhMeaning w .AandNotB = literalTruth w .AandNotB := by
  native_decide

-- ============================================================================
-- §4. Parse-Dependent Meaning
-- ============================================================================

/-- Parse = whether EXH is applied. -/
inductive CWSParse where
  | literal : CWSParse
  | exh : CWSParse
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CWSParse where
  elems := {.literal, .exh}
  complete := fun x => by cases x <;> simp

/-- Meaning with parse-dependent exhaustification. -/
def parseMeaning : CWSParse → CWSWorld → CWSUtterance → Bool
  | .literal, w, u => literalTruth w u
  | .exh, w, u => exhMeaning w u

-- ============================================================================
-- §5. Prior Weight
-- ============================================================================

/-- Prior weight for each world: 1:3 bias toward w_ab.

    Baked into `meaning` so that L0(w|u) ∝ P(w) · ⟦u⟧(w), matching
    the paper's eq. (1). This makes S1 asymmetric for utterances
    true in both worlds, which is the source of anti-exhaustivity. -/
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

-- ============================================================================
-- §6. Anti-Exhaustivity Condition (Eq. 6b)
-- ============================================================================

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
    antiExhaustivityCondition 0 0 1 1 = false := by native_decide

/-- Biased prior with equal costs: anti-exhaustivity triggered. -/
theorem biased_triggers_antiexh :
    antiExhaustivityCondition 3 1 1 1 = true := by native_decide

/-- Asymmetric costs can block anti-exhaustivity even with biased prior:
    if c(A∧¬B) is much more expensive than c(A∧B), the cost gap
    c(A∧¬B) - c(A∧B) exceeds the log prior ratio. -/
theorem cost_asymmetry_can_block :
    antiExhaustivityCondition 3 1 10 0 = false := by native_decide

-- ============================================================================
-- §7. RSA Configurations
-- ============================================================================

open Real (rpow rpow_nonneg)

/-- Baseline RSA (Model 1) with biased prior (1:3 toward w_ab).

    Prior enters L0 via `meaning`: `meaning(u,w) = P(w) · ⟦u⟧(w)`.
    Since A is true in both worlds, L0(w_a|A) = 1/4, L0(w_ab|A) = 3/4.
    S1 is asymmetric: S1(A|w_ab) = 9/25 > S1(A|w_a) = 1/17 (at α=2).
    This drives genuine anti-exhaustivity: the speaker preferentially
    uses A when w_ab is true (because L0 already favors w_ab given A). -/
noncomputable def baselineBiased : RSA.RSAConfig CWSUtterance CWSWorld where
  meaning _ _ u w := if literalTruth w u then priorWeight w else 0
  meaning_nonneg _ _ _ w := by split <;> (try cases w) <;> simp [priorWeight]
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun _ => 1
  worldPrior_nonneg := fun _ => le_of_lt one_pos
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

/-- EXH-LU RSA (Model 7) with biased prior.

    Parse is a latent variable; meaning under each parse includes the
    prior: `meaning(p,u,w) = P(w) · ⟦u⟧_p(w)`. Under the exh parse,
    EXH(A) is false at w_ab, so meaning = P(w_ab) · 0 = 0 and
    S1(A|w_ab, exh) = 0. The exh parse's blocking contribution
    (S1(A|w_a, exh) = 1/2) outweighs the literal parse's prior
    amplification, giving T(w_a) > T(w_ab) despite the 3:1 bias. -/
noncomputable def exhLUBiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSParse
  meaning _ p u w := if parseMeaning p w u then priorWeight w else 0
  meaning_nonneg _ _ _ w := by split <;> (try cases w) <;> simp [priorWeight]
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun _ => 1
  worldPrior_nonneg := fun _ => le_of_lt one_pos
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

-- ============================================================================
-- §8. Predictions (Models 1, 7)
-- ============================================================================

/-- Baseline RSA is genuinely anti-exhaustive: L1(w_ab|A) > L1(w_a|A).

    With prior-in-L0, S1 is asymmetric: S1(A|w_ab) = 9/25 > 1/17 = S1(A|w_a)
    because L0(w_ab|A) = 3/4 > 1/4 = L0(w_a|A). The speaker preferentially
    uses the cheap utterance A when w_ab is true, since L0 already assigns
    high probability to w_ab. This is the paper's central problematic
    prediction (Eq. 6b, Fig. 1). -/
theorem baseline_antiexhaustive :
    baselineBiased.L1 .A .w_ab > baselineBiased.L1 .A .w_a := by
  rsa_predict

/-- EXH-LU blocks anti-exhaustivity: even with prior-in-L0 and 3:1 bias,
    L1 correctly infers w_a from "A". The exh parse contributes
    S1(A|w_a, exh) = 1/2 but S1(A|w_ab, exh) = 0, which outweighs
    the literal parse's prior amplification (S1(A|w_ab, lit) = 9/25
    vs S1(A|w_a, lit) = 1/17). Total: T(w_a) = 19/34 > 9/25 = T(w_ab). -/
theorem exhlu_blocks_antiexhaustivity :
    exhLUBiased.L1 .A .w_a > exhLUBiased.L1 .A .w_ab := by
  rsa_predict

/-- EXH(A) is false in w_ab — the structural basis for blocking. -/
theorem exh_meaning_blocks_wab :
    exhMeaning .w_ab .A = false := by rfl

-- ============================================================================
-- §9. Additional Domain Types (Models 2–6, 8–9)
-- ============================================================================

/-- Background assumption for wRSA (@cite{degen-etal-2015}).
    - `wonky`: unusual situation, uniform prior over worlds
    - `default_`: default assumption, prior follows the bias -/
inductive CWSBackground where
  | wonky : CWSBackground
  | default_ : CWSBackground
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CWSBackground where
  elems := {.wonky, .default_}
  complete := fun x => by cases x <;> simp

/-- QUD for svRSA (@cite{spector-2017}).
    - `coarse`: Q_A — is A true? Corresponds to `Discourse.QUD.trivial`.
      All A-true worlds are equivalent; QUD projection gives L0 = 1.
    - `fine`: Q_fine — which world? Corresponds to `Discourse.QUD.exact`.
      Each world is its own cell; S1(A|w_ab) = 0 under exh interpretation. -/
inductive CWSQUD where
  | coarse : CWSQUD
  | fine : CWSQUD
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CWSQUD where
  elems := {.coarse, .fine}
  complete := fun x => by cases x <;> simp

/-- Interpretation for FREE-LU (@cite{bergen-levy-goodman-2016}).
    - `literal`: A true in both worlds
    - `exh`: A ∧ ¬B (true only in w_a)
    - `antiExh`: A ∧ B (true only in w_ab) -/
inductive CWSInterpretation where
  | literal : CWSInterpretation
  | exh : CWSInterpretation
  | antiExh : CWSInterpretation
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CWSInterpretation where
  elems := {.literal, .exh, .antiExh}
  complete := fun x => by cases x <;> simp

/-- Anti-exhaustive meaning: A means A ∧ B (true only in w_ab).
    A∧B and A∧¬B are unaffected (already fully specified). -/
def antiExhMeaning : CWSWorld → CWSUtterance → Bool
  | .w_a, .A => false
  | .w_ab, .A => true
  | w, u => literalTruth w u

/-- Meaning under each interpretation (for FREE-LU and EXH-LU). -/
def interpMeaning : CWSInterpretation → CWSWorld → CWSUtterance → Bool
  | .literal => literalTruth
  | .exh => exhMeaning
  | .antiExh => antiExhMeaning

-- ============================================================================
-- §10. RSA Configurations (Models 2–6, 8–9)
-- ============================================================================

/-- wRSA (Models 2–3) with biased prior. BwRSA is identical at L1.

    Background is a latent variable. Under the default background, the
    prior P(w|default) = P(w) is baked into meaning (matching the paper's
    eq. 1 in §4.1: L0(w|u,b) ∝ P(w|b) · ⟦u⟧(w)). Under the wonky
    background, P(w|wonky) = uniform, so meaning uses unit weights.

    The world-dependent `latentPrior` encodes P(w|b) × P(b): under
    `default_`, w_ab gets 3× the weight of w_a; under `wonky`, both
    worlds get equal weight. `worldPrior` is uniform since the prior
    enters through `meaning` (for L0) and `latentPrior` (for L1). -/
noncomputable def wRSABiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSBackground
  meaning _ b u w := match b with
    | .wonky => if literalTruth w u then 1 else 0
    | .default_ => if literalTruth w u then priorWeight w else 0
  meaning_nonneg _ b _ w := by cases b <;> simp only [] <;> split <;> (try cases w) <;> simp [priorWeight]
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun _ => 1
  worldPrior_nonneg := fun _ => le_of_lt one_pos
  latentPrior := fun w b => match w, b with
    | _, .wonky => 1
    | .w_a, .default_ => 1
    | .w_ab, .default_ => 3
  latentPrior_nonneg := fun w b => by cases w <;> cases b <;> positivity

/-- svRSA (Models 4–5) — @cite{spector-2017} supervaluationist RSA.

    The paper's svRSA (§4.2, eqs 3–8) has S1 compute expected utility over
    interpretations i, parameterized by QUD Q. The key structural properties
    (Appendix A.3, B.3) are:

    1. Under Q_A (coarse): QUD projection makes L0(Q_A(w)|A) = 1 for all w
       (all A-true worlds are in one cell). So S1(A|w, Q_A) is the same at
       both worlds — the prior's effect on S1 is neutralized.

    2. Under Q_fine: the exh interpretation makes A false at w_ab, so
       S1(A|w_ab, Q_fine) = 0 (log(0) = -∞ kills the expected utility).

    Our encoding approximates this by NOT including the prior in L0 meaning.
    Under coarse QUD, L0(w|A) = 1/2 for both worlds → S1 world-independent.
    Under fine QUD, exhMeaning makes A false at w_ab → S1(A|w_ab) = 0.

    This gives **categorical blocking**: T(w_a) = T(w_ab) + S1(A|w_a, fine)
    > T(w_ab) for any positive S1(A|w_a, fine), matching Appendix A.3.
    Concretely: T(w_a) = 1/5 + 1/2 = 7/10 > 1/5 = T(w_ab).

    The QUD values correspond to `Discourse.QUD.trivial` (coarse, Q_A) and
    `Discourse.QUD.exact` (fine, Q_fine) from `Core/Discourse/QUD.lean`.

    svRSA1 and svRSA2 differ only at S2 (production); both block at L1. -/
noncomputable def svRSABiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSQUD
  meaning _ q u w :=
    match q with
    | .coarse => if literalTruth w u then (1 : ℝ) else 0
    | .fine => if exhMeaning w u then (1 : ℝ) else 0
  meaning_nonneg _ q _ _ := by cases q <;> simp only [] <;> split <;> norm_num
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun _ => 1
  worldPrior_nonneg := fun _ => le_of_lt one_pos
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

/-- FREE-LU (Model 6) with biased prior, prior-in-L0.

    Three interpretations as latent variables: literal, exhaustive,
    and anti-exhaustive. With prior-in-L0, the literal parse is
    asymmetric (S1(A|w_ab, lit) = 9/25 > 1/17 = S1(A|w_a, lit)),
    making the anti-exh contribution dominant at w_ab.
    Total: T(w_ab) = 9/25 + 0 + 1/2 = 43/50 > 19/34 = T(w_a).
    This is genuine anti-exhaustivity, matching the paper's prediction. -/
noncomputable def freeLUBiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSInterpretation
  meaning _ i u w := if interpMeaning i w u then priorWeight w else 0
  meaning_nonneg _ _ _ w := by split <;> (try cases w) <;> simp [priorWeight]
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun _ => 1
  worldPrior_nonneg := fun _ => le_of_lt one_pos
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

/-- RSA-LI (Models 8–9) — @cite{franke-bergen-2020} Lexical Intentions.

    The paper's RSA-LI (§4.4, eqs 1–6 on p.18) has S1 jointly choose
    (utterance, interpretation): S1(u,i|w) ∝ exp(λ·U1(u,i|w)), normalized
    over all (u',i') pairs. EXH-LU instead has S1(u|w,i) normalized per-i.

    At L1, both give L1(w|u) ∝ P(w)·Σ_i S1(A|w,i) — the difference is
    only in how S1 is normalized. With uniform P(i) and equal costs
    (c(A∧B) ≤ c(A∧¬B)), both block anti-exhaustivity at L1 (Appendix B.5).

    The structural reason (same for both): S1 never prefers A over A∧¬B
    at w_a (A∧¬B is at least as informative and has exh-compatible meaning),
    so S1(A|w_ab) ≤ S1(A|w_a) under both normalizations.

    We alias `rsaLIBiased := exhLUBiased`. The models differ at S2
    (RSA-LI's S2 cannot select a specific meaning, unlike EXH-LU's). -/
noncomputable def rsaLIBiased : RSA.RSAConfig CWSUtterance CWSWorld := exhLUBiased

-- ============================================================================
-- §11. Predictions (Models 2–6, 8–9)
-- ============================================================================

/-- wRSA is anti-exhaustive: the default background bakes the biased prior
    into L0, making S1 asymmetric. Even with the wonky background
    (uniform L0) averaging in, the biased background dominates. -/
theorem wRSA_biased_antiexhaustive :
    wRSABiased.L1 .A .w_ab > wRSABiased.L1 .A .w_a := by
  rsa_predict

/-- svRSA blocks anti-exhaustivity **categorically** (Appendix A.3).

    Under Q_A (coarse), S1(A|w, coarse) = 1/5 for both worlds (L0 is
    uniform since no prior in meaning). Under Q_fine, S1(A|w_ab, fine) = 0
    (exh(A) false at w_ab) while S1(A|w_a, fine) = 1/2. So
    T(w_a) = 1/5 + 1/2 = 7/10 > 1/5 = T(w_ab). The blocking is structural:
    T(w_a) = T(w_ab) + S1(A|w_a, fine) > T(w_ab) for any parameters. -/
theorem svRSA_biased_exhaustive :
    svRSABiased.L1 .A .w_a > svRSABiased.L1 .A .w_ab := by
  rsa_predict

/-- FREE-LU is genuinely anti-exhaustive: with prior-in-L0, the literal
    parse's S1 asymmetry makes the anti-exh interpretation dominant at w_ab.
    T(w_ab) = 9/25 + 0 + 1/2 = 43/50 > 19/34 = 1/17 + 1/2 + 0 = T(w_a). -/
theorem freelu_biased_antiexhaustive :
    freeLUBiased.L1 .A .w_ab > freeLUBiased.L1 .A .w_a := by
  rsa_predict

/-- RSA-LI blocks anti-exhaustivity (same as EXH-LU). -/
theorem rsali_blocks_antiexhaustivity :
    rsaLIBiased.L1 .A .w_a > rsaLIBiased.L1 .A .w_ab := by
  rsa_predict

-- ============================================================================
-- §12. Classification
-- ============================================================================

/-- The paper's central result: 9 RSA models fall into two groups.

    **Anti-exhaustive** (L1(w_ab|A) > L1(w_a|A), i.e., L1(w_ab|A) > P(w_ab)):
    baseline RSA, wRSA (+ BwRSA at L1), FREE-LU. These models allow
    the prior bias to amplify through S1, predicting that listeners
    hearing "A" will infer w_ab — contradicting experimental data.

    **Exhaustive** (L1(w_a|A) > L1(w_ab|A) despite biased prior):
    EXH-LU, RSA-LI1/2 (= EXH-LU at L1), svRSA1/2. These models have
    grammatical exhaustification or QUD-based gating that blocks
    anti-exhaustivity, correctly predicting the experimental data. -/
theorem antiexhaustive_group :
    baselineBiased.L1 .A .w_ab > baselineBiased.L1 .A .w_a ∧
    wRSABiased.L1 .A .w_ab > wRSABiased.L1 .A .w_a ∧
    freeLUBiased.L1 .A .w_ab > freeLUBiased.L1 .A .w_a :=
  ⟨baseline_antiexhaustive, wRSA_biased_antiexhaustive,
   freelu_biased_antiexhaustive⟩

theorem exhaustive_group :
    exhLUBiased.L1 .A .w_a > exhLUBiased.L1 .A .w_ab ∧
    rsaLIBiased.L1 .A .w_a > rsaLIBiased.L1 .A .w_ab ∧
    svRSABiased.L1 .A .w_a > svRSABiased.L1 .A .w_ab :=
  ⟨exhlu_blocks_antiexhaustivity, rsali_blocks_antiexhaustivity,
   svRSA_biased_exhaustive⟩

end CremersWilcoxSpector2023
