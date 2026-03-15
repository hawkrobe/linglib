import Mathlib.Data.Rat.Defs
import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Theories.Pragmatics.RSA.Core.Config
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

## Prior Convention

The paper defines anti-exhaustivity as `L1(w_ab|A) > P(w_ab)`: the
posterior exceeds the prior. This requires S1 to be *asymmetric* across
worlds for utterance A, which happens when the prior enters L0:
`L0(w|u) ∝ P(w) · ⟦u⟧(w)`.

`RSAConfig` places the prior at L1 only: `L0(w|u) ∝ ⟦u⟧(w)`. For
utterances true in both worlds (like bare A), L0 = 1/2 in both worlds
and S1 is symmetric: S1(A|w_a) = S1(A|w_ab). This means
`L1(w_ab|A) = P(w_ab)` exactly — the posterior merely reproduces the
prior with no amplification. Baseline RSA under our encoding is
**prior-following**, not prior-amplifying.

For models that need prior-in-L0 (wRSA), we bake it into `meaning`:
the meaning for A under the default background weights worlds by
P(w|b), so L0 already reflects the bias and S1 becomes asymmetric.

## Anti-Exhaustivity Definition

The paper's definition (Eq. 6b, equal costs): `L1(w_ab|A) > P(w_ab)`.
Our theorems instead prove **world comparison**: `L1(w_ab|A) > L1(w_a|A)`.
These are equivalent for the baseline model (Appendix A.1, eq. A.4)
but diverge for models with latent variables. For the exhaustive group,
both definitions agree: if L1(w_a|A) > L1(w_ab|A) despite P(w_ab) > P(w_a),
then certainly L1(w_ab|A) < P(w_ab).

## Model Classification

The paper's 9 models fall into three groups by anti-exhaustivity behavior:

| # | Model | Mechanism | L1(w_ab) > L1(w_a)? | Config |
|---|-------|-----------|---------------------|--------|
| 1 | Baseline RSA | — | Yes (prior-following) | `baselineBiased` |
| 2 | wRSA | Prior-in-L0 via background | Yes (genuine) | `wRSABiased` |
| 3 | BwRSA | Bayesian wRSA | Yes (= wRSA at L1) | `wRSABiased` |
| 4 | svRSA1 | QUD blocks at S1 | No | `svRSABiased` |
| 5 | svRSA2 | QUD blocks at S1 | No | `svRSABiased` |
| 6 | FREE-LU | Free parse choice | Yes (prior-following) | `freeLUBiased` |
| 7 | EXH-LU | EXH blocks at L0 | No | `exhLUBiased` |
| 8 | RSA-LI1 | EXH blocks at L0 | No (= EXH-LU at L1) | `rsaLIBiased` |
| 9 | RSA-LI2 | EXH blocks at L0 | No (= EXH-LU at L1) | `rsaLIBiased` |

All 9 models are encoded as `RSAConfig` instances. The key insight is that
each model's distinctive mechanism maps to a different combination of
`Latent` type, `meaning` function, and `s1Score` rule.

RSA-LI (Models 8–9) is essentially GI-RSA from @cite{franke-bergen-2020},
formalized in `FrankeBergen2020.lean` using the same IE infrastructure.
wRSA and BwRSA are identical at L1 level (BwRSA adds a Bayesian S2 layer).

## Connection to Other Formalizations

- `CompareExhaustivity.lean`: proves RSA at α→∞ recovers Fox's exh,
  using the same IE infrastructure (`applyIEBool`) as our `exhMeaning`.
- `FrankeBergen2020.lean`: formalizes GI-RSA (= RSA-LI) for nested
  quantifiers, also using `applyIEBool` for grammatical parses.
- `CompareRSAExh.lean`: demonstrates the scope-blind vs scope-sensitive
  expressivity gap between standard RSA and compositional EXH.
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023

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
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype CWSWorld where
  elems := {.w_a, .w_ab}
  complete := fun x => by cases x <;> simp

/-- Three utterances in the minimal exhaustivity domain. -/
inductive CWSUtterance where
  | A : CWSUtterance
  | AandB : CWSUtterance
  | AandNotB : CWSUtterance
  deriving DecidableEq, BEq, Repr, Inhabited

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

open Exhaustification (applyIEBool)

/-- All worlds for IE enumeration. -/
def allWorlds : List CWSWorld := [.w_a, .w_ab]

/-- Alternatives for each utterance: A has scale-mate A∧B. -/
def alternatives (u : CWSUtterance) : List (CWSWorld → Bool) :=
  match u with
  | .A => [fun w => literalTruth w .A, fun w => literalTruth w .AandB]
  | _ => [fun w => literalTruth w u]

/-- Exhaustified meaning derived via Innocent Exclusion.
    IE negates A∧B (the non-entailed stronger alternative to A),
    giving EXH(A) = A ∧ ¬(A∧B) = A ∧ ¬B. -/
def exhMeaning (w : CWSWorld) (u : CWSUtterance) : Bool :=
  applyIEBool allWorlds (fun w' => literalTruth w' u) (alternatives u) w

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
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype CWSParse where
  elems := {.literal, .exh}
  complete := fun x => by cases x <;> simp

/-- Meaning with parse-dependent exhaustification. -/
def parseMeaning : CWSParse → CWSWorld → CWSUtterance → Bool
  | .literal, w, u => literalTruth w u
  | .exh, w, u => exhMeaning w u

-- ============================================================================
-- §5. Anti-Exhaustivity Condition (Eq. 6b)
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

/-- Biased prior with equal costs: anti-exhaustivity triggered.
    log(3/4) - log(1/4) > 0 (encoded as log ratio = 1 > 0). -/
theorem biased_triggers_antiexh :
    antiExhaustivityCondition 3 1 1 1 = true := by native_decide

/-- Asymmetric costs can block anti-exhaustivity even with biased prior:
    if c(A∧¬B) is much more expensive than c(A∧B), the cost gap
    c(A∧¬B) - c(A∧B) exceeds the log prior ratio. -/
theorem cost_asymmetry_can_block :
    antiExhaustivityCondition 3 1 10 0 = false := by native_decide

-- ============================================================================
-- §6. RSA Configurations
-- ============================================================================

open Real (rpow rpow_nonneg)

/-- Baseline RSA (Model 1) with biased prior (1:3 toward w_ab).
    Literal semantics only, no exhaustification, `Latent = Unit`. -/
noncomputable def baselineBiased : RSA.RSAConfig CWSUtterance CWSWorld where
  meaning _ _ u w := if literalTruth w u then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun | .w_a => 1 | .w_ab => 3
  worldPrior_nonneg := fun w => by cases w <;> positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

/-- EXH-LU RSA (Model 7) with biased prior.
    Parse is a latent variable; meaning under each parse is determined
    by Innocent Exclusion. Under the exh parse, EXH(A) = A ∧ ¬B is
    false in w_ab, blocking anti-exhaustivity. -/
noncomputable def exhLUBiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSParse
  meaning _ p u w := if parseMeaning p w u then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun | .w_a => 1 | .w_ab => 3
  worldPrior_nonneg := fun w => by cases w <;> positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

-- ============================================================================
-- §7. Predictions
-- ============================================================================

/-- Baseline RSA with biased prior: L1(w_ab|A) > L1(w_a|A).

    Since A is true in both worlds and RSAConfig puts the prior at L1 only,
    L0 = 1/2 in both worlds and S1 is symmetric: S1(A|w_a) = S1(A|w_ab).
    So L1 merely reproduces the 3:1 prior — this is **prior-following**,
    not anti-exhaustivity. L1(w_ab|A) = P(w_ab) = 3/4 exactly, not > 3/4.

    The paper's version (prior inside L0) gives genuine anti-exhaustivity:
    S1 amplifies the prior bias, making L1(w_ab|A) > P(w_ab). This
    amplification requires prior-in-L0, which our encoding reserves for
    models that explicitly need it (wRSA). -/
theorem baseline_prior_following :
    baselineBiased.L1 .A .w_ab > baselineBiased.L1 .A .w_a := by
  rsa_predict

/-- EXH-LU blocks anti-exhaustivity: even with 3:1 biased prior,
    L1 correctly infers w_a from "A" because the exhaustified parse
    (EXH(A) = A ∧ ¬B) kills w_ab. The EXH parse contributes zero
    speaker probability for A in w_ab, overriding the prior bias. -/
theorem exhlu_blocks_antiexhaustivity :
    exhLUBiased.L1 .A .w_a > exhLUBiased.L1 .A .w_ab := by
  rsa_predict

/-- EXH(A) is false in w_ab — the structural basis for blocking. -/
theorem exh_meaning_blocks_wab :
    exhMeaning .w_ab .A = false := by rfl

-- ============================================================================
-- §8. Additional Domain Types (Models 2–6, 8–9)
-- ============================================================================

/-- Background assumption for wRSA (@cite{degen-etal-2015}).
    - `wonky`: unusual situation, uniform prior over worlds
    - `default_`: default assumption, prior follows the bias -/
inductive CWSBackground where
  | wonky : CWSBackground
  | default_ : CWSBackground
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype CWSBackground where
  elems := {.wonky, .default_}
  complete := fun x => by cases x <;> simp

/-- QUD for svRSA (@cite{spector-2017-svRSA}).
    - `coarse`: is A true? (trivial in this domain — A is always true)
    - `fine`: which world? (distinguishes w_a from w_ab) -/
inductive CWSQUD where
  | coarse : CWSQUD
  | fine : CWSQUD
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
-- §9. RSA Configurations (Models 2–6, 8–9)
-- ============================================================================

/-- wRSA (Models 2–3) with biased prior. BwRSA is identical at L1.

    Background is a latent variable. Under the default background, the
    prior is baked into L0 (matching the paper's convention for wRSA).
    Under the wonky background, L0 uses uniform weights.

    The world-dependent `latentPrior` encodes P(w|b) × P(b): under
    `default_`, w_ab gets 3× the weight of w_a; under `wonky`, both
    worlds get equal weight. `worldPrior` is uniform since the prior
    already enters through `meaning` and `latentPrior`. -/
noncomputable def wRSABiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSBackground
  meaning _ b u w := match b with
    | .wonky => if literalTruth w u then 1 else 0
    | .default_ => if literalTruth w u then
        (match w with | .w_a => 1 | .w_ab => 3) else 0
  meaning_nonneg _ b _ w := by cases b <;> simp only [] <;> split <;> (try cases w) <;> positivity
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

/-- svRSA (Models 4–5) with biased (3:1) prior.

    QUD is a latent variable. Under the fine QUD, `meaning` uses
    `exhMeaning`: exh(A) is false at w_ab, so L0 assigns 0 there,
    and rpow(0, α) = 0 in S1 — the speaker cannot use A to convey
    w_ab under Q_fine. Under the coarse QUD, literal meaning applies
    and S1 is symmetric (A is uninformative about worlds under Q_A).

    The paper proves svRSA blocks anti-exhaustivity **categorically**
    for any prior (Appendix A.3: L1(w_ab|A) ≤ P(w_ab) always). Our
    encoding captures the mechanism: S1(A|w_ab, fine) = 0 zeros out
    the fine QUD contribution, leaving only the symmetric coarse
    contribution for w_ab. This suffices to overcome a 3:1 prior.

    svRSA1 and svRSA2 differ only at S2 (production); both block
    anti-exhaustivity at L1 (comprehension). -/
noncomputable def svRSABiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSQUD
  meaning _ q u w :=
    if (match q with | .coarse => literalTruth w u | .fine => exhMeaning w u)
    then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun | .w_a => 1 | .w_ab => 3
  worldPrior_nonneg := fun w => by cases w <;> positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

/-- FREE-LU (Model 6) with biased prior.

    Three interpretations as latent variables: literal, exhaustive,
    and anti-exhaustive. The exh and anti-exh interpretations
    symmetrically cancel (each singles out one world for A), leaving
    only the literal interpretation plus the prior to break the tie.

    **Encoding note**: The paper predicts genuine anti-exhaustivity for
    FREE-LU (L1(w_ab|A) > P(w_ab)) because its L0 includes the prior,
    amplifying the bias. Our encoding (prior at L1 only) gives
    prior-following instead. The qualitative group membership (same
    group as baseline) is preserved either way. -/
noncomputable def freeLUBiased : RSA.RSAConfig CWSUtterance CWSWorld where
  Latent := CWSInterpretation
  meaning _ i u w := if interpMeaning i w u then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  worldPrior := fun | .w_a => 1 | .w_ab => 3
  worldPrior_nonneg := fun w => by cases w <;> positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos

/-- RSA-LI (Models 8–9) is structurally identical to EXH-LU at L1.

    The difference is at production: RSA-LI's S1 jointly chooses
    (utterance, interpretation), while EXH-LU's S1 is per-interpretation.
    At L1, both marginalize over interpretations with the same literal
    and exhaustified meanings. With uniform interpretation priors and
    zero costs, RSA-LI2 = EXH-LU exactly (noted in the paper, Table 1).

    We alias `rsaLIBiased := exhLUBiased` rather than duplicating. -/
noncomputable def rsaLIBiased : RSA.RSAConfig CWSUtterance CWSWorld := exhLUBiased

-- ============================================================================
-- §10. Predictions (Models 2–6, 8–9)
-- ============================================================================

/-- wRSA is anti-exhaustive: the default background bakes the biased prior
    into L0, making S1 asymmetric. Even with the wonky background
    (uniform L0) averaging in, the biased background dominates. -/
theorem wRSA_biased_antiexhaustive :
    wRSABiased.L1 .A .w_ab > wRSABiased.L1 .A .w_a := by
  rsa_predict

/-- svRSA blocks anti-exhaustivity: the fine QUD zeros out S1(A|w_ab)
    because exh(A) is false at w_ab. The coarse QUD is symmetric (A is
    uninformative about worlds under Q_A). Despite the 3:1 prior bias,
    the fine QUD's contribution to w_a (S1(A|w_a, fine) = 1/2) outweighs
    the prior's pull toward w_ab. -/
theorem svRSA_biased_exhaustive :
    svRSABiased.L1 .A .w_a > svRSABiased.L1 .A .w_ab := by
  rsa_predict

/-- FREE-LU is prior-following: the anti-exhaustive interpretation
    (A means A ∧ B) symmetrically counterbalances the exhaustive
    interpretation. With S1 symmetric for A across worlds (exh and
    anti-exh cancel out), L1 merely follows the 3:1 prior. -/
theorem freelu_biased_prior_following :
    freeLUBiased.L1 .A .w_ab > freeLUBiased.L1 .A .w_a := by
  rsa_predict

/-- RSA-LI blocks anti-exhaustivity (same as EXH-LU). -/
theorem rsali_blocks_antiexhaustivity :
    rsaLIBiased.L1 .A .w_a > rsaLIBiased.L1 .A .w_ab := by
  rsa_predict

-- ============================================================================
-- §11. Classification
-- ============================================================================

/-- The paper's central result: 9 RSA models fall into two groups.

    **Prior-following / anti-exhaustive** (L1(w_ab|A) > L1(w_a|A)):
    baseline (prior-following only), wRSA (genuinely anti-exhaustive
    via prior-in-L0), BwRSA (= wRSA at L1), FREE-LU (prior-following,
    exh and anti-exh interpretations cancel).

    **Exhaustive** (L1(w_a|A) > L1(w_ab|A) despite biased prior):
    EXH-LU, RSA-LI1/2 (= EXH-LU at L1), svRSA1/2.

    Models with grammatical exhaustification (EXH-LU, RSA-LI) or
    QUD-based gating (svRSA) block anti-exhaustivity. Models that
    rely only on informativity-cost tradeoffs (baseline, wRSA) or
    allow unconstrained strengthening (FREE-LU) do not. -/
theorem prior_following_group :
    baselineBiased.L1 .A .w_ab > baselineBiased.L1 .A .w_a ∧
    wRSABiased.L1 .A .w_ab > wRSABiased.L1 .A .w_a ∧
    freeLUBiased.L1 .A .w_ab > freeLUBiased.L1 .A .w_a :=
  ⟨baseline_prior_following, wRSA_biased_antiexhaustive,
   freelu_biased_prior_following⟩

theorem exhaustive_group :
    exhLUBiased.L1 .A .w_a > exhLUBiased.L1 .A .w_ab ∧
    rsaLIBiased.L1 .A .w_a > rsaLIBiased.L1 .A .w_ab ∧
    svRSABiased.L1 .A .w_a > svRSABiased.L1 .A .w_ab :=
  ⟨exhlu_blocks_antiexhaustivity, rsali_blocks_antiexhaustivity,
   svRSA_biased_exhaustive⟩

end Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023
