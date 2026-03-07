import Mathlib.Data.Rat.Defs
import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Basic
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

## Domain

- **Worlds**: w_a (only A true), w_ab (A and B both true)
- **Utterances**: A (cost 0), A∧B (cost c), A∧¬B (cost c)
- **Parses** (EXH-LU): literal (A true in both worlds) vs exh (A true only in w_a)

## Anti-Exhaustivity Condition (Eq. 6b)

L1(w_ab | A) > P(w_ab) iff log(P(w_ab)) - log(P(w_a)) > c(A∧¬B) - c(A∧B)

## Formalized Predictions

| Theorem | Model | Prior | Prediction |
|---------|-------|-------|------------|
| `baseline_biased_antiexhaustive` | Baseline | 3:1 biased | L1(w_ab\|A) > L1(w_a\|A) |
| `exhlu_blocks_antiexhaustivity` | EXH-LU | 3:1 biased | L1(w_a\|A) > L1(w_ab\|A) |

## Model Comparison (paper covers 9 models; we formalize baseline + EXH-LU)

| # | Model | Anti-exhaustive? | Formalized? |
|---|-------|-----------------|-------------|
| 1 | Baseline RSA | Yes (biased prior) | ✓ |
| 2 | wRSA | Yes (can be) | — |
| 3 | BwRSA | Yes (can be) | — |
| 4 | svRSA1 | No (QUD blocks) | — |
| 5 | svRSA2 | No (QUD blocks) | — |
| 6 | FREE-LU | Yes (at L1) | — |
| 7 | EXH-LU | No (EXH blocks) | ✓ |
| 8 | RSA-LI1 | No (EXH blocks) | — |
| 9 | RSA-LI2 | No (EXH blocks) | — |

RSA-LI (Models 8–9) is essentially GI-RSA from @cite{franke-bergen-2020},
formalized in `FrankeBergen2020.lean` using the same IE infrastructure.
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

open NeoGricean.Exhaustivity (applyIEBool)

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

/-- Equal-cost anti-exhaustivity condition (simplified from Eq. 6b).

    The full condition from Eq. 6b is:
    `L1(w_ab|A) > P(w_ab) iff log(P(w_ab)) - log(P(w_a)) > c(A∧¬B) - c(A∧B)`
    (log-odds exceeds cost difference; this holds for all λ > 0 since λ
    scales both exponents and the logistic function is monotone).

    With equal costs (`c(A∧¬B) = c(A∧B)`), this simplifies to `P(w_ab) > P(w_a)`:
    any prior bias toward w_ab triggers anti-exhaustivity. -/
def antiExhaustivityHolds_equalCosts (p_wab p_wa : ℚ) : Bool :=
  p_wab > p_wa

/-- With uniform prior, no anti-exhaustivity. -/
theorem uniform_no_antiexh :
    antiExhaustivityHolds_equalCosts (1/2) (1/2) = false := by native_decide

/-- With 3:1 bias, anti-exhaustivity is triggered. -/
theorem biased_triggers_antiexh :
    antiExhaustivityHolds_equalCosts (3/4) (1/4) = true := by native_decide

-- ============================================================================
-- §6. RSA Configurations
-- ============================================================================

open Real (rpow rpow_nonneg)

/-- Baseline RSA (Model 1) with biased prior.
    No EXH, literal semantics only.
    Prior 1:3 in favor of w_ab (both A and B true). -/
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

/-- Baseline RSA with biased prior is anti-exhaustive: hearing "A"
    makes the listener MORE confident in w_ab (both true) than w_a.
    This contradicts human behavior — humans always exhaust "A"
    to mean "A and not B." -/
theorem baseline_biased_antiexhaustive :
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

end Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023
