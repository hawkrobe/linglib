import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Linglib.Phenomena.Quantification.Studies.ScontrasPearl2021
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Theories.Semantics.Montague.Scope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scontras & Pearl (2021) — Scope Ambiguity RSA Model

@cite{scontras-pearl-2021}

"When pragmatics matters more for truth-value judgments:
An investigation of quantifier scope ambiguity"
*Glossa* 6(1): 110.

## The Model (eqs 1–8)

Domain: "Every horse didn't jump" with n=2 horses. 3 world states
(0, 1, 2 jumped). 2 utterances (null, everyNot). 6 latent states
(2 scopes × 3 QUDs).

- **L0**: L0(w|u,i) ∝ ⟦u⟧ᵢ(w)   (literal semantics, no world prior; footnote 6)
- **S1**: S1(u|w,i,q) ∝ [L0(q(w)|u,i,q)]^α   (QUD-projected; eq 5)
- **L1**: L1(w,i,q|u) ∝ P(w) · P(i) · P(q) · S1(u|w,i,q)   (eq 7)
- **S2**: S2(u|w) ∝ Σ_{i,q} L1(w,i,q|u) = L1(w|u)   (eq 8)
- **Endorsement**: P(endorse u | w_obs) = S2(u|w_obs)

Parameters: α = 1 (footnote 12). P(w) = Binomial(n, b_suc).

## QUDs (eqs 3–4)

Three QUD partitions over worlds:
- how-many?: identity — partitions {w0}, {w1}, {w2}
- all?: w = n? — partitions {w0,w1} vs {w2}
- none?: w = 0? — partitions {w0} vs {w1,w2}

## S2 vs L1 (eq 8)

The paper models endorsement as S2, not L1. S2(u|w) ∝ P_{L1}(w|u),
using the **normalized** L1 posterior. This matters because:
- L1 conditions on the heard utterance (same normalizer for all worlds)
- S2 conditions on the observed world (different normalizer per world)
- worldPrior enters S2 through L1's normalization denominator, so
  different worldPriors produce different S2 values

The S2 ordering S2(everyNot|w0) > S2(everyNot|w1) > S2(everyNot|w2)
is **robust** across all prior configurations, even when L1 orderings
vary (e.g., highBaseCfg reverses L1 ordering but preserves S2 ordering).

## Compositional Grounding

The truth conditions `scopeTruth` are grounded in linglib's formal semantics
infrastructure via `every_sem` (`Quantifier.lean`), `ScopeConfig`/`ScopeDerivation`
(`Montague/Scope.lean`), and `FiniteModel`/`Model` (`Montague/Basic.lean`):
- Surface (∀>¬): `every_sem horseModel horse_sem (λh.¬jump(h))(w)`
- Inverse (¬>∀): `¬(every_sem horseModel horse_sem (jump)(w))`

See `surface_from_every_sem`, `inverse_from_every_sem`, and
`scopeDerivation_matches_scopeTruth`.

## Key Findings (Figure 2)

S2 endorsement for "every horse didn't jump" in the partial world (w=1).
The "Paper value" column is S&P's computed model predictions (not experimental
data — S&P is a modeling paper explaining Musolino & Lidz 2003 findings):

| Config | S2(everyNot|w=1) | Paper value |
|--------|-----------------|-------------|
| b_suc=0.1 (baseline) | 0.288 | ~0.29 |
| b_suc=0.5 (default) | 0.506 | ~0.48 |
| b_suc=0.9 (high base rate) | 0.796 | ~0.80 |

The S2 ordering w0 > w1 > w2 is **robust** across all prior configurations,
even when L1 orderings vary (e.g., highBaseCfg reverses L1 ordering).

## Developmental Continuity (§3.3)

The same model architecture explains both child and adult behavior.
Children's isomorphic (surface-scope) preference follows from low `b_suc`
priors. Adult-like inverse scope access emerges from supportive contexts
(high `b_suc`, all?-biased QUD) — the same model, different priors.

## References

- Scontras, G. & Pearl, L. (2021). When pragmatics matters more for
  truth-value judgments. *Glossa* 6(1): 110.
- Goodman, N.D. & Frank, M.C. (2016). Pragmatic language interpretation
  as probabilistic inference. *TiCS* 20(11): 818-829.
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Studies.ScontrasPearl2021RSA

open BigOperators
open Real (rpow rpow_nonneg)
open Phenomena.Quantification.Studies.ScontrasPearl2021 (JumpOutcome ScopeReading scopeTruth)
open Semantics.Montague (Model)
open Semantics.Lexical.Determiner.Quantifier (every_sem FiniteModel)
open Semantics.Scope (ScopeConfig ScopeDerivation)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

instance : Fintype JumpOutcome where
  elems := {.zero, .one, .two}
  complete := fun x => by cases x <;> simp

instance : Fintype ScopeReading where
  elems := {.surface, .inverse}
  complete := fun x => by cases x <;> simp

/-- Utterances: null (silence) or "Every horse didn't jump". -/
inductive Utt where
  | null     -- silence (always true, uninformative baseline)
  | everyNot -- "Every horse didn't jump" (scopally ambiguous)
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Utt where
  elems := {.null, .everyNot}
  complete := fun x => by cases x <;> simp

/-- QUDs partition worlds by the question under discussion (eqs 3–4).
    Three QUD partitions for n=2 worlds. -/
inductive QUD where
  | howMany -- "How many horses jumped?" — {w0}, {w1}, {w2} (identity)
  | all_    -- "Did all the horses jump?" — {w0,w1} vs {w2}
  | none_   -- "Did none of the horses jump?" — {w0} vs {w1,w2}
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype QUD where
  elems := {.howMany, .all_, .none_}
  complete := fun x => by cases x <;> simp

/-- Flattened latent variable: scope reading × QUD.
    Flat inductive avoids Prod, keeping proof terms tractable for
    the kernel checker. -/
inductive Latent where
  | surfHowMany  -- surface scope, how-many? QUD
  | surfAll      -- surface scope, all? QUD
  | surfNone     -- surface scope, none? QUD
  | invHowMany   -- inverse scope, how-many? QUD
  | invAll       -- inverse scope, all? QUD
  | invNone      -- inverse scope, none? QUD
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Latent where
  elems := {.surfHowMany, .surfAll, .surfNone, .invHowMany, .invAll, .invNone}
  complete := fun x => by cases x <;> simp

/-- Extract scope reading from latent variable. -/
def Latent.scope : Latent → ScopeReading
  | .surfHowMany | .surfAll | .surfNone => .surface
  | .invHowMany | .invAll | .invNone => .inverse

/-- Extract QUD from latent variable. -/
def Latent.qud : Latent → QUD
  | .surfHowMany | .invHowMany => .howMany
  | .surfAll | .invAll => .all_
  | .surfNone | .invNone => .none_

-- ============================================================================
-- §2. Truth Conditions
-- ============================================================================

/-- RSA meaning derived from the data file's `scopeTruth`.
    Null utterance is always true (uninformative baseline). -/
def uttMeaning : ScopeReading → Utt → JumpOutcome → Bool
  | _, .null, _ => true
  | s, .everyNot, w => scopeTruth s w

/-- Truth table verification against the paper's equations (3a-b). -/
theorem truth_table :
    uttMeaning .surface .everyNot .zero = true ∧
    uttMeaning .surface .everyNot .one = false ∧
    uttMeaning .surface .everyNot .two = false ∧
    uttMeaning .inverse .everyNot .zero = true ∧
    uttMeaning .inverse .everyNot .one = true ∧
    uttMeaning .inverse .everyNot .two = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §3. Compositional Grounding
-- ============================================================================

/-- 2-horse domain for grounding truth conditions in quantifier semantics. -/
inductive Horse where | h1 | h2 deriving DecidableEq

/-- Jump predicate for each world state. In the 1-horse world, exactly h1
    jumped (the choice is arbitrary; only cardinality matters for the
    universally quantified sentence). -/
def jumpIn : JumpOutcome → Horse → Bool
  | .zero, _ => false
  | .one, .h1 => true | .one, .h2 => false
  | .two, _ => true

/-- Horse model as a Montague `Model`. -/
def horseModel : Model := { Entity := Horse, decEq := inferInstance }

instance : FiniteModel horseModel where
  elements := [.h1, .h2]
  complete := fun x => by cases x <;> simp
  nodup := by simp [List.nodup_cons, List.mem_cons, List.mem_singleton]

/-- Restrictor: all entities are horses (trivial for this model). -/
def horse_sem : horseModel.interpTy (.e ⇒ .t) := fun _ => true

/-- Scope predicate: did entity h jump in world w? -/
def jumpIn_sem (w : JumpOutcome) : horseModel.interpTy (.e ⇒ .t) :=
  fun h => jumpIn w h

/-- Surface scope: ⟦every⟧(horse)(λx.¬jump(x))(w). -/
def everyNotJumped_surface (w : JumpOutcome) : Bool :=
  every_sem horseModel horse_sem (fun h => !jumpIn_sem w h)

/-- Inverse scope: ¬⟦every⟧(horse)(jump)(w). -/
def everyNotJumped_inverse (w : JumpOutcome) : Bool :=
  !(every_sem horseModel horse_sem (jumpIn_sem w))

/-- Surface scope grounding: `scopeTruth .surface` derives from
    compositional ⟦every⟧(horse)(λx.¬jump(x)), not stipulation. -/
theorem surface_from_every_sem :
    ∀ w, scopeTruth .surface w = every_sem horseModel horse_sem (fun h => !jumpIn_sem w h) := by
  intro w; cases w <;> rfl

/-- Inverse scope grounding: `scopeTruth .inverse` derives from
    negating the compositional ⟦every⟧(horse)(jump). -/
theorem inverse_from_every_sem :
    ∀ w, scopeTruth .inverse w = !(every_sem horseModel horse_sem (jumpIn_sem w)) := by
  intro w; cases w <;> rfl

/-- Map Montague `ScopeConfig` to data file's `ScopeReading`. -/
def scopeConfigToReading : ScopeConfig → ScopeReading
  | .surface => .surface
  | .inverse => .inverse

/-- Map data file's `ScopeReading` to Montague `ScopeConfig`. -/
def readingToScopeConfig : ScopeReading → ScopeConfig
  | .surface => .surface
  | .inverse => .inverse

/-- "Every horse didn't jump" as a `ScopeDerivation`: a single syntactic form
    with multiple semantic values indexed by scope configuration. -/
def everyHorseDidntJump (w : JumpOutcome) : ScopeDerivation horseModel .t where
  surface := "Every horse didn't jump"
  meaningAt
    | .surface => every_sem horseModel horse_sem (fun h => !jumpIn_sem w h)
    | .inverse => !(every_sem horseModel horse_sem (jumpIn_sem w))

/-- The `ScopeDerivation`'s `meaningAt` matches `scopeTruth` for both readings. -/
theorem scopeDerivation_matches_scopeTruth :
    ∀ (s : ScopeConfig) (w : JumpOutcome),
    (everyHorseDidntJump w).meaningAt s = scopeTruth (scopeConfigToReading s) w := by
  intro s w; cases s <;> cases w <;> rfl

/-- RSA meaning is grounded in `ScopeDerivation`: the meaning function used
    by the RSA config matches the compositional scope derivation. -/
theorem rsa_meaning_from_scope_derivation :
    ∀ (lat : Latent) (w : JumpOutcome),
    uttMeaning lat.scope .everyNot w =
    (everyHorseDidntJump w).meaningAt (readingToScopeConfig lat.scope) := by
  intro lat w; cases lat <;> cases w <;> rfl

-- ============================================================================
-- §4. QUD Projection
-- ============================================================================

/-- QUD answer function: q(w) → equivalence class identifier (eq 4).
    For howMany, each world is its own class (identity partition). -/
def qudAnswer : QUD → JumpOutcome → Fin 3
  | .howMany, .zero => 0  | .howMany, .one => 1  | .howMany, .two => 2
  | .all_,   w => if w == .two then 1 else 0
  | .none_,  w => if w == .zero then 1 else 0

/-- Inline QUD projection: explicit case analysis, kernel-reducible.
    For howMany, each world is its own equivalence class (identity partition).
    For all?/none?, worlds sharing an answer are aggregated. -/
def qudProjectInline (q : QUD) (f : JumpOutcome → ℝ) (w : JumpOutcome) : ℝ :=
  match q, w with
  -- howMany?: identity partition — each world is its own class
  | .howMany, .zero => f .zero
  | .howMany, .one  => f .one
  | .howMany, .two  => f .two
  -- all?: {w0,w1} vs {w2}
  | .all_,  .zero => f .zero + f .one
  | .all_,  .one  => f .zero + f .one
  | .all_,  .two  => f .two
  -- none?: {w0} vs {w1,w2}
  | .none_, .zero => f .zero
  | .none_, .one  => f .one + f .two
  | .none_, .two  => f .one + f .two

theorem qudProjectInline_nonneg {q : QUD} {f : JumpOutcome → ℝ} {w : JumpOutcome}
    (hf : ∀ w, 0 ≤ f w) : 0 ≤ qudProjectInline q f w := by
  cases q <;> cases w <;> simp only [qudProjectInline]
  all_goals first | exact hf _ | exact add_nonneg (hf _) (hf _)

-- ============================================================================
-- §5. RSAConfig
-- ============================================================================

/-- Scontras & Pearl (2021) RSA model, parametric in three priors (eq 7).
    S1 uses QUD-projected rpow with α = 1 (footnote 12).
    L0 does not incorporate the world prior (footnote 6). -/
noncomputable def cfg
    (worldPr : JumpOutcome → ℝ) (hwp : ∀ w, 0 ≤ worldPr w)
    (scopePr : ScopeReading → ℝ) (hsp : ∀ s, 0 ≤ scopePr s)
    (qudPr : QUD → ℝ) (hqp : ∀ q, 0 ≤ qudPr q) :
    RSA.RSAConfig Utt JumpOutcome where
  Latent := Latent
  meaning lat u w := if uttMeaning lat.scope u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α lat w u := rpow (qudProjectInline lat.qud (l0 u) w) α
  s1Score_nonneg _ _ _ _ u hl _ :=
    rpow_nonneg (qudProjectInline_nonneg (fun w => hl u w)) _
  α := 1
  α_pos := one_pos
  worldPrior := worldPr
  worldPrior_nonneg := hwp
  latentPrior _w lat := scopePr lat.scope * qudPr lat.qud
  latentPrior_nonneg _w lat := mul_nonneg (hsp lat.scope) (hqp lat.qud)

-- ============================================================================
-- §6. Configurations
-- ============================================================================

/-! World priors follow Binomial(2, b_suc), unnormalized:
    - b_suc = 0.1: P(w) ∝ (81, 18, 1)     — horses unlikely to jump
    - b_suc = 0.5: P(w) ∝ (1, 2, 1)        — symmetric
    - b_suc = 0.9: P(w) ∝ (1, 18, 81)      — horses likely to jump -/

/-- Baseline: low base rate (b_suc = 0.1), uniform scope, uniform QUD.
    Best fit to adult Experiment 1 data (§3.2, Figure 2 left). -/
noncomputable abbrev baselineCfg :=
  cfg (fun w => match w with | .zero => 81 | .one => 18 | .two => 1)
    (fun w => by cases w <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Default: symmetric prior (b_suc = 0.5), uniform scope, uniform QUD.
    Binomial(2, 0.5) ∝ (1, 2, 1). Paper's default parameter setting. -/
noncomputable abbrev defaultCfg :=
  cfg (fun w => match w with | .zero => 1 | .one => 2 | .two => 1)
    (fun w => by cases w <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- High base rate: b_suc = 0.9, uniform scope, uniform QUD.
    Tests robustness of S2 ordering to prior manipulation (Figure 2 left). -/
noncomputable abbrev highBaseCfg :=
  cfg (fun w => match w with | .zero => 1 | .one => 18 | .two => 81)
    (fun w => by cases w <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Supportive context: b_suc = 0.9 + all?-biased QUD (1:18:1 ≈ 0.05:0.9:0.05).
    Models the Gualmini et al. (2008) early-success manipulation, where context
    pragmatically supports inverse scope (§3.3, Figure 3). -/
noncomputable abbrev supportiveCfg :=
  cfg (fun w => match w with | .zero => 1 | .one => 18 | .two => 81)
    (fun w => by cases w <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)
    (fun q => match q with | .howMany => 1 | .all_ => 18 | .none_ => 1)
    (fun q => by cases q <;> positivity)

/-- Surface-only: P(inverse) = 0. Tests whether scope ambiguity is needed
    to produce intermediate endorsement. -/
noncomputable abbrev surfaceOnlyCfg :=
  cfg (fun w => match w with | .zero => 81 | .one => 18 | .two => 1)
    (fun w => by cases w <;> positivity)
    (fun s => match s with | .surface => 1 | .inverse => 0)
    (fun s => by cases s <;> positivity)
    (fun _ => 1) (fun _ => le_of_lt one_pos)

-- ============================================================================
-- §7. S2 Endorsement (eq 8)
-- ============================================================================

/-! S2 endorsement (eq 8) uses the generic `RSAConfig.S2` from
    `Theories/Pragmatics/RSA/Core/Config.lean`:
    S2(u|w) = S2agent.policy(w, u) where S2agent.score(w, u) = cfg.L1(u, w)
    (the **normalized** L1 posterior).

    The `rsa_predict` tactic handles S2 cross-world goals via `policy_gt_cross`,
    building compositional QInterval proofs for the cross-product comparison. -/

-- ============================================================================
-- §8. L1-Level Theorems
-- ============================================================================

-- L1 ordering for baseline: w0 > w1 > w2 (provable by rsa_predict).
-- This holds because L1(w|u) ∝ P(w) · Σ_l P(l) · S1(u|w,l), and at
-- b_suc=0.1 the high prior for w0 (81) dominates.

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- Baseline L1: 0-jumped > 1-jumped. Both scopes agree w=0 is true;
    high prior weight (81 vs 18). -/
theorem baseline_L1_w0_gt_w1 :
    baselineCfg.L1 .everyNot .zero > baselineCfg.L1 .everyNot .one := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- Baseline L1: 1-jumped > 2-jumped. Inverse scope makes w=1 true;
    moderate prior advantage (18 vs 1). -/
theorem baseline_L1_w1_gt_w2 :
    baselineCfg.L1 .everyNot .one > baselineCfg.L1 .everyNot .two := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- Scope ambiguity boosts partial-world endorsement.
    With both scopes active, L1(w=1) is higher than surface-only,
    because inverse scope directly makes w=1 true. -/
theorem ambiguity_boosts_partial :
    baselineCfg.L1 .everyNot .one > surfaceOnlyCfg.L1 .everyNot .one := by
  rsa_predict

-- ============================================================================
-- §9. S2 Endorsement Theorems (paper's main claims)
-- ============================================================================

-- The paper's central finding: S2 endorsement ordering w0 > w1 > w2 is
-- ROBUST across all prior configurations (Figure 2). At L1 level,
-- highBaseCfg reverses the ordering (w1 > w2 > w0), but S2 normalizing
-- per world restores the correct ordering.
--
-- S2 compares L1(u,w) / Σ_{u'} L1(u',w) across different worlds
-- (different denominators). worldPrior enters through L1's normalization
-- denominator, so different worldPriors produce different S2 values.
-- The `rsa_predict` tactic handles S2 cross-world goals via
-- `policy_gt_cross`, building compositional QInterval proofs.

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- Baseline S2: w0 > w1 (matches 92% > 59% in Experiment 1). -/
theorem baseline_S2_w0_gt_w1 :
    baselineCfg.S2 .zero .everyNot > baselineCfg.S2 .one .everyNot := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- Baseline S2: w1 > w2 (matches 59% > 18% in Experiment 1). -/
theorem baseline_S2_w1_gt_w2 :
    baselineCfg.S2 .one .everyNot > baselineCfg.S2 .two .everyNot := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- S2 ordering robust to high base rate (b_suc = 0.9).
    Even when L1 reverses (w1 > w2 > w0 at L1), S2 still orders w0 > w1. -/
theorem highBase_S2_w0_gt_w1 :
    highBaseCfg.S2 .zero .everyNot > highBaseCfg.S2 .one .everyNot := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- S2 ordering robust to high base rate: w1 > w2. -/
theorem highBase_S2_w1_gt_w2 :
    highBaseCfg.S2 .one .everyNot > highBaseCfg.S2 .two .everyNot := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- S2 ordering robust to symmetric prior (b_suc = 0.5). -/
theorem default_S2_w0_gt_w1 :
    defaultCfg.S2 .zero .everyNot > defaultCfg.S2 .one .everyNot := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
theorem default_S2_w1_gt_w2 :
    defaultCfg.S2 .one .everyNot > defaultCfg.S2 .two .everyNot := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
/-- S2 ordering robust under supportive context (b_suc = 0.9, all?-biased QUD). -/
theorem supportive_S2_w0_gt_w1 :
    supportiveCfg.S2 .zero .everyNot > supportiveCfg.S2 .one .everyNot := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxHeartbeats 800000 in
theorem supportive_S2_w1_gt_w2 :
    supportiveCfg.S2 .one .everyNot > supportiveCfg.S2 .two .everyNot := by
  rsa_predict

end Phenomena.Quantification.Studies.ScontrasPearl2021RSA
