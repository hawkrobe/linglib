import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Phenomena.Quantification.Studies.ScontrasPearl2021
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scontras & Pearl (2021) §4 — Two-Not RSA Model @cite{scontras-pearl-2021}

The two-not model extends the every-not model (§3) to "two horses didn't jump"
with n=4 horses. The key innovation: when n exceeds the numeral's value,
exact vs at-least numeral semantics produce different truth conditions and
thus different RSA predictions.

## Model Structure (eqs 5–11)

Domain: "Two horses didn't jump" with n=4 horses. 5 world states
(0–4 jumped). 2 utterances (null, twoNot). 10 latent states
(2 scopes × 5 QUDs).

- **L0**: L0(w|u,i) ∝ ⟦u⟧ᵢ(w)   (literal semantics)
- **S1**: S1(u|w,i,q) ∝ [L0(q(w)|u,i,q)]^α   (QUD-projected)
- **L1**: L1(w,i,q|u) ∝ P(w) · P(i) · P(q) · S1(u|w,i,q)
- **S2**: S2(u|w) ∝ L1(w|u)   (endorsement)

Parameters: α = 1. P(w) = Binomial(4, b_suc).

## QUDs (eq 7)

Five QUD partitions over 5-world domain:
- how-many?: identity — {w0}, {w1}, {w2}, {w3}, {w4}
- all?: did all jump? — {w0,w1,w2,w3} vs {w4}
- none?: did none jump? — {w0} vs {w1,w2,w3,w4}
- two=?: did exactly two jump? — {w2} vs {w0,w1,w3,w4}
- two≥?: did at least two jump? — {w0,w1} vs {w2,w3,w4}

## Central Claim (§4.2)

Under exact semantics, surface scope pinpoints w=2 as the unique true world,
giving maximum informativity → high S2 endorsement at w=2.
Under at-least semantics, surface scope is true at {w0,w1,w2}, diluting
informativity → lower S2 endorsement at w=2.

This predicts that adults endorse "two horses didn't jump" more readily
in 2-of-4 contexts under exact numeral semantics — converging with
Kennedy (2015) and acquisition data from Musolino (2004).

## References

- Scontras, G. & Pearl, L. (2021). When pragmatics matters more for
  truth-value judgments. *Glossa* 6(1): 110.
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Studies.ScontrasPearl2021TwoNot

open BigOperators
open Real (rpow rpow_nonneg)
open Phenomena.Quantification.Studies.ScontrasPearl2021
  (JumpOutcome4 ScopeReading NumeralReading twoNotTruth)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

instance : Fintype JumpOutcome4 where
  elems := {.w0, .w1, .w2, .w3, .w4}
  complete := fun x => by cases x <;> simp

instance : Fintype ScopeReading where
  elems := {.surface, .inverse}
  complete := fun x => by cases x <;> simp

instance : Fintype NumeralReading where
  elems := {.exact, .atLeast}
  complete := fun x => by cases x <;> simp

/-- Utterances: null (silence) or "two horses didn't jump". -/
inductive Utt where
  | null    -- silence (always true, uninformative baseline)
  | twoNot  -- "two horses didn't jump" (scopally ambiguous)
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Utt where
  elems := {.null, .twoNot}
  complete := fun x => by cases x <;> simp

/-- QUDs for the two-not model (eq 7). Five partitions over the 5-world domain.
    The two numeral-specific QUDs (two=?, two≥?) are added because
    explicitly mentioning a numeral makes that cardinality potentially
    relevant to the topic of conversation. -/
inductive QUD5 where
  | howMany    -- "How many horses jumped?" — identity partition
  | all_       -- "Did all the horses jump?" — {w0..w3} vs {w4}
  | none_      -- "Did none of the horses jump?" — {w0} vs {w1..w4}
  | twoExact   -- "Did exactly two horses jump?" — {w2} vs {w0,w1,w3,w4}
  | twoAtLeast -- "Did at least two horses jump?" — {w0,w1} vs {w2,w3,w4}
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype QUD5 where
  elems := {.howMany, .all_, .none_, .twoExact, .twoAtLeast}
  complete := fun x => by cases x <;> simp

/-- Flattened latent variable: scope reading × QUD.
    2 scopes × 5 QUDs = 10 constructors. -/
inductive Latent10 where
  | surfHowMany | surfAll | surfNone | surfTwoExact | surfTwoAtLeast
  | invHowMany  | invAll  | invNone  | invTwoExact  | invTwoAtLeast
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Latent10 where
  elems := { .surfHowMany, .surfAll, .surfNone, .surfTwoExact, .surfTwoAtLeast,
             .invHowMany,  .invAll,  .invNone,  .invTwoExact,  .invTwoAtLeast }
  complete := fun x => by cases x <;> simp

/-- Extract scope reading from latent variable. -/
def Latent10.scope : Latent10 → ScopeReading
  | .surfHowMany | .surfAll | .surfNone | .surfTwoExact | .surfTwoAtLeast => .surface
  | .invHowMany  | .invAll  | .invNone  | .invTwoExact  | .invTwoAtLeast  => .inverse

/-- Extract QUD from latent variable. -/
def Latent10.qud : Latent10 → QUD5
  | .surfHowMany | .invHowMany => .howMany
  | .surfAll     | .invAll     => .all_
  | .surfNone    | .invNone    => .none_
  | .surfTwoExact   | .invTwoExact   => .twoExact
  | .surfTwoAtLeast | .invTwoAtLeast => .twoAtLeast

-- ============================================================================
-- §2. Truth Conditions
-- ============================================================================

/-- RSA meaning for the two-not model, parameterized by numeral reading.
    Null utterance is always true (uninformative baseline). -/
def uttMeaning (nr : NumeralReading) : ScopeReading → Utt → JumpOutcome4 → Bool
  | _, .null, _ => true
  | s, .twoNot, w => twoNotTruth nr s w

/-- Exact semantics truth table (eq 6a). -/
theorem exact_truth_table :
    uttMeaning .exact .surface .twoNot .w0 = false ∧
    uttMeaning .exact .surface .twoNot .w1 = false ∧
    uttMeaning .exact .surface .twoNot .w2 = true ∧
    uttMeaning .exact .surface .twoNot .w3 = false ∧
    uttMeaning .exact .surface .twoNot .w4 = false ∧
    uttMeaning .exact .inverse .twoNot .w0 = true ∧
    uttMeaning .exact .inverse .twoNot .w1 = true ∧
    uttMeaning .exact .inverse .twoNot .w2 = false ∧
    uttMeaning .exact .inverse .twoNot .w3 = true ∧
    uttMeaning .exact .inverse .twoNot .w4 = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At-least semantics truth table (eq 6b). -/
theorem atLeast_truth_table :
    uttMeaning .atLeast .surface .twoNot .w0 = true ∧
    uttMeaning .atLeast .surface .twoNot .w1 = true ∧
    uttMeaning .atLeast .surface .twoNot .w2 = true ∧
    uttMeaning .atLeast .surface .twoNot .w3 = false ∧
    uttMeaning .atLeast .surface .twoNot .w4 = false ∧
    uttMeaning .atLeast .inverse .twoNot .w0 = true ∧
    uttMeaning .atLeast .inverse .twoNot .w1 = true ∧
    uttMeaning .atLeast .inverse .twoNot .w2 = false ∧
    uttMeaning .atLeast .inverse .twoNot .w3 = false ∧
    uttMeaning .atLeast .inverse .twoNot .w4 = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §3. QUD Projection
-- ============================================================================

/-- QUD projection for the 5-world domain (eq 4, extended).
    Explicit case analysis, kernel-reducible. -/
def qudProject (q : QUD5) (f : JumpOutcome4 → ℝ) (w : JumpOutcome4) : ℝ :=
  match q, w with
  -- howMany?: identity — each world is its own equivalence class
  | .howMany, .w0 => f .w0
  | .howMany, .w1 => f .w1
  | .howMany, .w2 => f .w2
  | .howMany, .w3 => f .w3
  | .howMany, .w4 => f .w4
  -- all?: {w0,w1,w2,w3} vs {w4}
  | .all_, .w0 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w1 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w2 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w3 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w4 => f .w4
  -- none?: {w0} vs {w1,w2,w3,w4}
  | .none_, .w0 => f .w0
  | .none_, .w1 => f .w1 + f .w2 + f .w3 + f .w4
  | .none_, .w2 => f .w1 + f .w2 + f .w3 + f .w4
  | .none_, .w3 => f .w1 + f .w2 + f .w3 + f .w4
  | .none_, .w4 => f .w1 + f .w2 + f .w3 + f .w4
  -- twoExact?: {w2} vs {w0,w1,w3,w4}
  | .twoExact, .w2 => f .w2
  | .twoExact, .w0 => f .w0 + f .w1 + f .w3 + f .w4
  | .twoExact, .w1 => f .w0 + f .w1 + f .w3 + f .w4
  | .twoExact, .w3 => f .w0 + f .w1 + f .w3 + f .w4
  | .twoExact, .w4 => f .w0 + f .w1 + f .w3 + f .w4
  -- twoAtLeast?: {w0,w1} vs {w2,w3,w4}
  | .twoAtLeast, .w0 => f .w0 + f .w1
  | .twoAtLeast, .w1 => f .w0 + f .w1
  | .twoAtLeast, .w2 => f .w2 + f .w3 + f .w4
  | .twoAtLeast, .w3 => f .w2 + f .w3 + f .w4
  | .twoAtLeast, .w4 => f .w2 + f .w3 + f .w4

theorem qudProject_nonneg {q : QUD5} {f : JumpOutcome4 → ℝ} {w : JumpOutcome4}
    (hf : ∀ w, 0 ≤ f w) : 0 ≤ qudProject q f w := by
  cases q <;> cases w <;> simp only [qudProject] <;>
    linarith [hf .w0, hf .w1, hf .w2, hf .w3, hf .w4]

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

/-- Two-not RSA model, parameterized by numeral reading and priors.
    Same architecture as the every-not model: S1 uses QUD-projected rpow
    with α = 1, L0 does not incorporate the world prior. -/
noncomputable def cfg
    (nr : NumeralReading)
    (worldPr : JumpOutcome4 → ℝ) (hwp : ∀ w, 0 ≤ worldPr w)
    (scopePr : ScopeReading → ℝ) (hsp : ∀ s, 0 ≤ scopePr s)
    (qudPr : QUD5 → ℝ) (hqp : ∀ q, 0 ≤ qudPr q) :
    RSA.RSAConfig Utt JumpOutcome4 where
  Latent := Latent10
  meaning lat u w := if uttMeaning nr lat.scope u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α lat w u := rpow (qudProject lat.qud (l0 u) w) α
  s1Score_nonneg _ _ _ _ u hl _ :=
    rpow_nonneg (qudProject_nonneg (fun w => hl u w)) _
  α := 1
  α_pos := one_pos
  worldPrior := worldPr
  worldPrior_nonneg := hwp
  latentPrior _w lat := scopePr lat.scope * qudPr lat.qud
  latentPrior_nonneg _w lat := mul_nonneg (hsp lat.scope) (hqp lat.qud)

-- ============================================================================
-- §5. Configurations
-- ============================================================================

/-! World priors follow Binomial(4, b_suc), unnormalized.

    The paper's central 2-of-4 predictions (Figure 7) use b_suc = 0.1
    with low P(inverse) = 0.1 (surface scope bias), matching the baseline
    parameters from the every-not model that produce low 1-of-2 endorsement.

    Binomial(4, 0.1) ∝ C(4,k) · 1^k · 9^(4-k) = (6561, 2916, 486, 36, 1). -/

/-- Baseline exact config: b_suc = 0.1, P(inv) = 0.1 (surface scope bias).
    Matches Figure 7 right panel, red bar (S2 ≈ 0.8). -/
noncomputable abbrev exactBaselineCfg :=
  cfg .exact
    (fun w => match w with | .w0 => 6561 | .w1 => 2916 | .w2 => 486 | .w3 => 36 | .w4 => 1)
    (fun w => by cases w <;> positivity)
    (fun s => match s with | .surface => 9 | .inverse => 1)
    (fun s => by cases s <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Baseline at-least config: same parameters, at-least numeral semantics.
    Matches Figure 7 left panel, red bar (S2 ≈ 0.1). -/
noncomputable abbrev atleastBaselineCfg :=
  cfg .atLeast
    (fun w => match w with | .w0 => 6561 | .w1 => 2916 | .w2 => 486 | .w3 => 36 | .w4 => 1)
    (fun w => by cases w <;> positivity)
    (fun s => match s with | .surface => 9 | .inverse => 1)
    (fun s => by cases s <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Symmetric exact config: b_suc = 0.5, uniform scope/QUD.
    Binomial(4, 0.5) ∝ (1, 4, 6, 4, 1). -/
noncomputable abbrev exactSymCfg :=
  cfg .exact
    (fun w => match w with | .w0 => 1 | .w1 => 4 | .w2 => 6 | .w3 => 4 | .w4 => 1)
    (fun w => by cases w <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Symmetric at-least config: b_suc = 0.5, uniform scope/QUD. -/
noncomputable abbrev atleastSymCfg :=
  cfg .atLeast
    (fun w => match w with | .w0 => 1 | .w1 => 4 | .w2 => 6 | .w3 => 4 | .w4 => 1)
    (fun w => by cases w <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

-- ============================================================================
-- §6. Key Predictions (§4.2)
-- ============================================================================

/-! The paper's central claims for the 2-of-4 context (Figure 7).

    Under exact semantics with low base rate (b_suc = 0.1) and surface scope
    bias (P(inv) = 0.1), surface scope pinpoints w=2 as the unique true world,
    giving maximum informativity → high S2 endorsement at w=2.

    Under at-least semantics with the same parameters, surface scope is true
    at {w0,w1,w2}, diluting informativity → low S2 endorsement at w=2.

    The 1-of-2 vs 2-of-4 asymmetry: these SAME "baseline" parameters produce
    low endorsement (27.5%) in the 1-of-2 context but high endorsement in the
    2-of-4 context, but ONLY under exact numeral semantics. This is the
    paper's key argument for exact semantics as the basic numeral meaning.

    S2 predictions may require sorry because the state space
    (5 worlds × 10 latents × 2 utterances = 100 S1 scores) exceeds
    the heartbeat budget for kernel-level proof checking. -/

/-- Under exact semantics with baseline parameters (b_suc=0.1, P(inv)=0.1),
    S2 endorsement of "two horses didn't jump" at w=2 exceeds 1/2.
    Surface scope pinpoints w=2 as the unique true world, giving maximum
    informativity (Figure 7 right, red bar ≈ 0.8). -/
theorem exact_baseline_endorsement_high :
    exactBaselineCfg.S2 .w2 .twoNot > (1 : ℝ) / 2 := by
  -- TODO: 100 S1 entries may exceed heartbeat limits
  sorry

/-- Under at-least semantics with baseline parameters, S2 endorsement
    at w=2 is lower than under exact semantics.
    Exact surface has 1 true world; at-least surface has 3.
    (Figure 7: right panel > left panel at matching P(inv).) -/
theorem exact_vs_atleast_endorsement :
    exactBaselineCfg.S2 .w2 .twoNot > atleastBaselineCfg.S2 .w2 .twoNot := by
  -- TODO: cross-config comparison with 200 S1 entries
  sorry

-- ============================================================================
-- §7. Informativity Contrasts
-- ============================================================================

/-- The key informativity contrast: under exact semantics, surface scope
    has exactly 1 true world (w2), while under at-least it has 3 (w0–w2).
    This drives the endorsement difference via S1 informativity. -/
theorem exact_surface_singleton :
    (List.filter (uttMeaning .exact .surface .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 1 := by
  native_decide

theorem atLeast_surface_triple :
    (List.filter (uttMeaning .atLeast .surface .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 3 := by
  native_decide

/-- Exact inverse has 4 true worlds (w0,w1,w3,w4) — very uninformative.
    Since w2 is the only world where surface scope is true, inverse scope
    contributes nothing at w2 (it's false there), explaining why surface
    scope dominates the S2 prediction under exact semantics. -/
theorem exact_inverse_quad :
    (List.filter (uttMeaning .exact .inverse .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 4 := by
  native_decide

/-- At-least inverse has 2 true worlds (w0,w1) — more informative than
    exact inverse's 4, but still less informative than exact surface's 1. -/
theorem atLeast_inverse_double :
    (List.filter (uttMeaning .atLeast .inverse .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 2 := by
  native_decide

end Phenomena.Quantification.Studies.ScontrasPearl2021TwoNot
