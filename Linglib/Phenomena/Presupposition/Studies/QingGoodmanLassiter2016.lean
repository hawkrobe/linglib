import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Verb.ChangeOfState.Theory
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{qing-goodman-lassiter-2016}

A rational speech-act model of projective content. CogSci 2016, pp. 1110–1115.

The listener jointly infers the world state and the common ground (context set)
the speaker assumed. Under the right QUD, this derives presupposition projection
without any special semantic mechanism.

## The Model

- **L0** (eq. 5): L0(Q(w) | u, C, Q) ∝ Σ_{w'∈C∩⟦u⟧} δ_{Q(w)=Q(w')} · P(w')
- **S1** (eq. 6): S(u|w,C,Q) ∝ P(u) · L0(Q(w) | u, C, Q)^α
- **L1** (eq. 7): L(w,C | u, Q) ∝ P(w) · P(C) · S(u | w, C, Q)

Domain: 13 utterances × 4 worlds × 9 context sets. α = 6.

## Key Insight: QUD Projection and Context Set Inference

Under QUD_now ("Does John smoke now?"), S1 scores depend on `now(w)` only —
worlds with the same `now` value are indistinguishable (§8.1). This means
presupposition projection CANNOT be observed at the world marginal level.
Instead, projection surfaces in the **context set posterior** (L1_latent):
L1 infers the speaker assumed a context set entailing `past=T` (§8.5).

Under QUD_max (identity QUD), the past-now degeneracy breaks and projection
is visible directly at the world level (§8.4).

## Context Set Simplification

The paper uses 15 non-empty context sets (all 2^4 - 1 subsets of 4 worlds) with
5% noise added to eq. (8) to ensure nonzero priors. We model only the 9 context
sets derivable from observations about past/now, since the remaining 6 (e.g.,
`change = {(T,F),(F,T)}`) receive only the noise prior (≥18× lower) and do not
affect qualitative predictions.

## Connection to @cite{scontras-tonhauser-2025} and @cite{warstadt-2022}

All three papers implement the same mathematical structure with different
domains (change-of-state verbs, factives, genus-species). The latent variable
is called "context set" here and "private assumptions" in S&T, but the
computation is identical. See `ScontrasTonhauser2025.lean` for the factive
domain.
-/

set_option autoImplicit false

namespace QingGoodmanLassiter2016

open BigOperators
open Real (rpow rpow_nonneg)
-- ============================================================================
-- §1. World State
-- ============================================================================

/-- World state: (past, now) where past = John smoked, now = John smokes.
    Flat inductive for tactic enumerability. -/
inductive WorldState where
  | wTT  -- (past=T, now=T): smoked, still smokes
  | wTF  -- (past=T, now=F): smoked, quit (stopped)
  | wFT  -- (past=F, now=T): didn't smoke, started
  | wFF  -- (past=F, now=F): never smoked
  deriving DecidableEq, Repr, Inhabited, Fintype

def WorldState.past : WorldState → Bool
  | .wTT | .wTF => true
  | .wFT | .wFF => false

def WorldState.now : WorldState → Bool
  | .wTT | .wFT => true
  | .wTF | .wFF => false

-- ============================================================================
-- §2. Utterances (Table 1 + negations + silence)
-- ============================================================================

/-- Utterances about John's smoking habits.
    6 positive utterances from Table 1, their 6 negations, and silence. -/
inductive Utterance where
  | smokes              -- "John smokes"           {(T,T),(F,T)}
  | doesntSmoke         -- "John doesn't smoke"    {(T,F),(F,F)}
  | smoked              -- "John smoked"           {(T,T),(T,F)}
  | didntSmoke          -- "John didn't smoke"     {(F,T),(F,F)}
  | alwaysSmoked        -- "John has always smoked"  {(T,T)}
  | notAlwaysSmoked     -- "John hasn't always smoked" {(T,F),(F,T),(F,F)}
  | stoppedSmoking      -- "John stopped smoking"  {(T,F)}
  | notStoppedSmoking   -- "John didn't stop smoking" {(T,T),(F,T),(F,F)}
  | startedSmoking      -- "John started smoking"  {(F,T)}
  | notStartedSmoking   -- "John didn't start smoking" {(T,T),(T,F),(F,F)}
  | neverSmoked         -- "John has never smoked" {(F,F)}
  | notNeverSmoked      -- "John hasn't never smoked" {(T,T),(T,F),(F,T)}
  | silence             -- null utterance          {(T,T),(T,F),(F,T),(F,F)}
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §3. Literal Semantics
-- ============================================================================

/-- Literal truth conditions from Table 1. Negation of u is U - ⟦u⟧.

    The change-of-state utterances (stopped, started, always smoked) encode
    presupposition + assertion as a conjunction over two temporal projections
    of the world state. See bridge theorems below connecting these to the
    CoS theory in `Theories.Semantics.Verb.ChangeOfState.Theory`. -/
def literalMeaning : Utterance → WorldState → Bool
  | .smokes,            w => w.now
  | .doesntSmoke,       w => !w.now
  | .smoked,            w => w.past
  | .didntSmoke,        w => !w.past
  | .alwaysSmoked,      w => w.past && w.now
  | .notAlwaysSmoked,   w => !(w.past && w.now)
  | .stoppedSmoking,    w => w.past && !w.now
  | .notStoppedSmoking, w => !(w.past && !w.now)
  | .startedSmoking,    w => !w.past && w.now
  | .notStartedSmoking, w => !(!w.past && w.now)
  | .neverSmoked,       w => !w.past && !w.now
  | .notNeverSmoked,    w => !(!w.past && !w.now)
  | .silence,           _ => true

open Semantics.Verb.ChangeOfState (priorStatePresup resultStateAssertion)

/-- "Stopped smoking" = cessation presupposition (past=T) ∧ cessation assertion (now=F).

    The CoS theory operates on a single predicate P, but the QGL world model
    separates prior state (`past`) from current state (`now`). We use `·.past`
    for the presupposition and `·.now` for the assertion. -/
theorem stopped_matches_cessation (w : WorldState) :
    literalMeaning .stoppedSmoking w =
    (priorStatePresup .cessation (·.past) w &&
     resultStateAssertion .cessation (·.now) w) := rfl

/-- "Started smoking" = inception presupposition (past=F) ∧ inception assertion (now=T). -/
theorem started_matches_inception (w : WorldState) :
    literalMeaning .startedSmoking w =
    (priorStatePresup .inception (·.past) w &&
     resultStateAssertion .inception (·.now) w) := rfl

/-- "Always smoked" = continuation presupposition (past=T) ∧ continuation assertion (now=T). -/
theorem always_matches_continuation (w : WorldState) :
    literalMeaning .alwaysSmoked w =
    (priorStatePresup .continuation (·.past) w &&
     resultStateAssertion .continuation (·.now) w) := rfl

-- ============================================================================
-- §4. Context Sets (Common Ground)
-- ============================================================================

/-- Context sets: subsets of worlds representing common ground.
    These are the 9 context sets derivable from observations about past and now
    (eq. 8). The paper's full model uses 15 non-empty subsets with 5% noise;
    the omitted 6 (e.g., `change = {(T,F),(F,T)}`) have negligible prior. -/
inductive ContextSet where
  | pastTrue           -- +past: CG entails John smoked
  | pastFalse          -- -past: CG entails John didn't smoke
  | nowTrue            -- +now: CG entails John smokes
  | nowFalse           -- -now: CG entails John doesn't smoke
  | pastTrueNowTrue    -- +past+now
  | pastTrueNowFalse   -- +past-now
  | pastFalseNowTrue   -- -past+now
  | pastFalseNowFalse  -- -past-now
  | universe           -- no constraints
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- World-context compatibility: w ∈ C. -/
def compatibleBool : ContextSet → WorldState → Bool
  | .pastTrue,          w => w.past
  | .pastFalse,         w => !w.past
  | .nowTrue,           w => w.now
  | .nowFalse,          w => !w.now
  | .pastTrueNowTrue,   w => w.past && w.now
  | .pastTrueNowFalse,  w => w.past && !w.now
  | .pastFalseNowTrue,  w => !w.past && w.now
  | .pastFalseNowFalse, w => !w.past && !w.now
  | .universe,          _ => true

-- ============================================================================
-- §5. QUD
-- ============================================================================

/-- Questions under discussion. -/
inductive QUD where
  | now   -- "Does John smoke now?" (partitions by now)
  | max   -- Full world identification (identity QUD)
  | past  -- "Did John smoke?" (partitions by past)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- QUD aggregation: sums L0 probabilities over the QUD equivalence class.
    - now: sums over worlds with same now value
    - max: identity (no aggregation)
    - past: sums over worlds with same past value -/
def qudAggregate (qud : QUD) (f : WorldState → ℝ) (w : WorldState) : ℝ :=
  match qud, w with
  | .now,  .wTT => f .wTT + f .wFT
  | .now,  .wTF => f .wTF + f .wFF
  | .now,  .wFT => f .wTT + f .wFT
  | .now,  .wFF => f .wTF + f .wFF
  | .max,  w    => f w
  | .past, .wTT => f .wTT + f .wTF
  | .past, .wTF => f .wTT + f .wTF
  | .past, .wFT => f .wFT + f .wFF
  | .past, .wFF => f .wFT + f .wFF

theorem qudAggregate_nonneg {qud : QUD} {f : WorldState → ℝ} {w : WorldState}
    (hf : ∀ w, 0 ≤ f w) : 0 ≤ qudAggregate qud f w := by
  cases qud <;> cases w <;> simp only [qudAggregate]
  all_goals first | exact hf _ | exact add_nonneg (hf _) (hf _)

-- ============================================================================
-- §6. Priors
-- ============================================================================

/-- Utterance prior (eq. 1): Pr(u) ∝ 2^{-#content-words(u)}.
    Negation and auxiliaries excluded from count.
    - 2 content words: stopped/started/always/never smoking → 1/4
    - 1 content word: smokes/smoked → 1/2
    - 0 content words: silence → 1 -/
def utterancePrior : Utterance → ℚ
  | .smokes | .doesntSmoke | .smoked | .didntSmoke => 1/2
  | .alwaysSmoked | .notAlwaysSmoked
  | .stoppedSmoking | .notStoppedSmoking
  | .startedSmoking | .notStartedSmoking
  | .neverSmoked | .notNeverSmoked => 1/4
  | .silence => 1

theorem utterancePrior_nonneg (u : Utterance) : 0 ≤ utterancePrior u := by
  cases u <;> simp [utterancePrior]

/-- Context set prior (eq. 8): Pr(C) ∝ Σ_{CG⊆Obs} P(CG) · δ_{C=∩CG}.
    Each observation enters CG independently with probability 0.4.
    P(CG) = 0.4^|CG| × 0.6^(4-|CG|).
    - 0 observations (universe): 0.6^4 ∝ 9
    - 1 observation (single): 0.4 × 0.6^3 ∝ 6
    - 2 observations (pair): 0.4^2 × 0.6^2 ∝ 4 -/
def contextPrior : ContextSet → ℚ
  | .universe => 9
  | .pastTrue | .pastFalse | .nowTrue | .nowFalse => 6
  | .pastTrueNowTrue | .pastTrueNowFalse
  | .pastFalseNowTrue | .pastFalseNowFalse => 4

theorem contextPrior_pos (cs : ContextSet) : 0 < contextPrior cs := by
  cases cs <;> simp [contextPrior]

-- ============================================================================
-- §7. RSAConfig
-- ============================================================================

/-- RSA model parameterized by QUD. The paper's final model uses QUD_now with
    CG prior.

    - L0: meaning = compatibility ∧ literal truth (eq. 5)
    - S1: utterancePrior × rpow(qudAggregate(L0), α) (eq. 6)
    - L1: worldPrior × contextPrior × S1 (eq. 7) -/
noncomputable def cfg (qud : QUD) : RSA.RSAConfig Utterance WorldState where
  Latent := ContextSet
  meaning _ cs u w :=
    if compatibleBool cs w && literalMeaning u w then (1 : ℝ) else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α cs w u :=
    (utterancePrior u : ℝ) * rpow (qudAggregate qud (l0 u) w) α
  s1Score_nonneg _ _ _ _ u hl _ :=
    mul_nonneg (Rat.cast_nonneg.mpr (utterancePrior_nonneg u))
      (rpow_nonneg (qudAggregate_nonneg (fun w' => hl u w')) _)
  α := 6
  α_pos := by positivity
  worldPrior _ := 1
  worldPrior_nonneg _ := by norm_num
  latentPrior _ cs := (contextPrior cs : ℝ)
  latentPrior_nonneg _ cs := Rat.cast_nonneg.mpr (le_of_lt (contextPrior_pos cs))

/-- Final model: CG prior + QUD_now (paper's main prediction). -/
noncomputable abbrev cfgNow := cfg .now

/-- Comparison model: CG prior + QUD_max. -/
noncomputable abbrev cfgMax := cfg .max

/-- Comparison model: CG prior + QUD_past. -/
noncomputable abbrev cfgPast := cfg .past

-- ============================================================================
-- §8. L1 Predictions
-- ============================================================================

/-! ### §8.1 QUD_now symmetry

Under QUD_now, `qudAggregate` maps wTT and wFT to the same value (both
have now=T), so S1(cs, wTT, u) = S1(cs, wFT, u) for all cs. With uniform
worldPrior and w-independent latentPrior, L1(wTT) = L1(wFT). This means
presupposition projection **cannot** be measured by world marginal under
QUD_now — the past dimension is invisible to L1. -/

set_option maxHeartbeats 3200000 in
/-- **QUD_now symmetry**: wTT and wFT are indistinguishable.

    This is the structural reason why projection under QUD_now must be
    measured via context set inference (L1_latent), not world marginal. -/
theorem qud_now_wTT_eq_wFT :
    cfgNow.L1 .notStoppedSmoking .wTT =
    cfgNow.L1 .notStoppedSmoking .wFT := by
  rsa_predict

/-! ### §8.2 QUD answer

After hearing "didn't stop smoking" with QUD = "Does John smoke now?",
L1 correctly infers the QUD answer: John smokes (now=T). -/

set_option maxHeartbeats 3200000 in
/-- **QUD answer inference**: L1 infers now=T from "didn't stop smoking". -/
theorem qud_answer_now_true :
    cfgNow.L1_marginal .notStoppedSmoking (·.now) >
    cfgNow.L1_marginal .notStoppedSmoking (fun w => !w.now) := by
  rsa_predict

/-! ### §8.3 World elimination

Within worlds sharing the same past value, now=T dominates now=F.
"Didn't stop smoking" is literally false at wTF (past=T, now=F is exactly
"stopped smoking"), concentrating L1 mass on wTT. -/

set_option maxHeartbeats 3200000 in
/-- **Now=T dominates now=F** among past=T worlds. -/
theorem wTT_gt_wTF :
    cfgNow.L1 .notStoppedSmoking .wTT >
    cfgNow.L1 .notStoppedSmoking .wTF := by
  rsa_predict

/-! ### §8.4 Projection under QUD_max (Figure 1c)

Under the identity QUD, the past-now degeneracy of §8.1 breaks: S1 scores
depend on all world dimensions, so L1 can distinguish wTT from wFT. The
key asymmetry: under +past context, "didn't stop" narrows to exactly wTT
(maximally informative for the speaker), while under -past context it
spreads over both wFT and wFF (less informative). This makes wTT more
likely than wFT.

The paper observes that (T,T) = (F,F) under QUD_max (Figure 1c), so projection
is incomplete — the past=T marginal still equals the past=F marginal. Full
projection requires QUD_now + context set inference (§8.5). -/

set_option maxHeartbeats 3200000 in
/-- **Projection under QUD_max**: wTT > wFT. -/
theorem projection_under_qud_max :
    cfgMax.L1 .notStoppedSmoking .wTT >
    cfgMax.L1 .notStoppedSmoking .wFT := by
  rsa_predict

set_option maxHeartbeats 3200000 in
/-- **Incomplete projection under QUD_max**: wTT = wFF (Figure 1c).

    Under the identity QUD, (T,T) and (F,F) receive equal L1 probability.
    This means the past=T marginal equals the past=F marginal — projection
    is NOT captured at the world level under QUD_max. -/
theorem qud_max_incomplete_projection :
    cfgMax.L1 .notStoppedSmoking .wTT =
    cfgMax.L1 .notStoppedSmoking .wFF := by
  rsa_predict

/-! ### §8.5 Context set projection (the paper's main result, Figure 3)

The paper's headline result: after hearing "didn't stop smoking" under QUD_now,
L1 infers the speaker assumed a **+past context set** (common ground where John
smoked). This is presupposition projection: the presupposed content (past=T)
enters the listener's beliefs about the common ground, even though the utterance
literally says nothing about the past.

The mechanism: under +past context, "didn't stop" narrows L0 to exactly wTT,
giving qudAggregate = 1 and rpow(1, 6) = 1 (maximally informative). Under
-past context, L0 spreads over wFT and wFF, giving qudAggregate = 1/2 and
rpow(1/2, 6) = 1/64 (weakly informative). Since S1 rewards informativity,
the speaker is much more likely to use "didn't stop" when the +past context
holds, and L1 infers this.

Figure 3 shows that (T,T) with context set +past is the unique maximum of the
joint distribution under CG prior + QUD_now. -/

set_option maxHeartbeats 3200000 in
/-- **Context set projection**: L1 infers +past context over -past context. -/
theorem context_projection :
    cfgNow.L1_latent .notStoppedSmoking .pastTrue >
    cfgNow.L1_latent .notStoppedSmoking .pastFalse := by
  rsa_predict

set_option maxHeartbeats 3200000 in
/-- **+past beats uninformative universe** despite lower prior (9 vs 6).

    Under +past, "didn't stop" narrows to exactly wTT (rpow(1,6) = 1).
    Under universe, it spreads over 3 worlds (rpow(1/4,6) ≈ 0). The
    informativity gain overwhelms the prior advantage. -/
theorem context_projection_over_universe :
    cfgNow.L1_latent .notStoppedSmoking .pastTrue >
    cfgNow.L1_latent .notStoppedSmoking .universe := by
  rsa_predict

set_option maxHeartbeats 3200000 in
/-- **-now context is dispreferred** (p. 1114): -now already entails the QUD
    answer (John doesn't smoke now), so the speaker would be maximally
    informative even saying nothing — "didn't stop smoking" adds no value.
    L1 therefore infers the speaker did NOT assume a -now context. -/
theorem now_context_dispreferred :
    cfgNow.L1_latent .notStoppedSmoking .pastTrue >
    cfgNow.L1_latent .notStoppedSmoking .nowFalse := by
  rsa_predict

/-! ### §8.6 "Stopped smoking" projects past=T via QUD answer

"Stopped smoking" is true only at wTF (past=T, now=F). Under QUD_now,
L1 infers the QUD answer is now=F. -/

set_option maxHeartbeats 3200000 in
/-- "Stopped smoking" → L1 infers now=F (the assertion). -/
theorem stopped_qud_answer :
    cfgNow.L1_marginal .stoppedSmoking (fun w => !w.now) >
    cfgNow.L1_marginal .stoppedSmoking (·.now) := by
  rsa_predict

-- ============================================================================
-- §9. Structural Properties
-- ============================================================================

/-- "didn't stop smoking" is compatible with 3 of 4 worlds. -/
theorem notStopped_compatible_worlds :
    literalMeaning .notStoppedSmoking .wTT = true ∧
    literalMeaning .notStoppedSmoking .wTF = false ∧
    literalMeaning .notStoppedSmoking .wFT = true ∧
    literalMeaning .notStoppedSmoking .wFF = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Under context set +past, "didn't stop" is maximally informative for QUD_now:
    it narrows to exactly (T,T). -/
theorem notStopped_informative_in_pastTrue :
    (compatibleBool .pastTrue .wTT && literalMeaning .notStoppedSmoking .wTT) = true ∧
    (compatibleBool .pastTrue .wTF && literalMeaning .notStoppedSmoking .wTF) = false ∧
    (compatibleBool .pastTrue .wFT && literalMeaning .notStoppedSmoking .wFT) = false ∧
    (compatibleBool .pastTrue .wFF && literalMeaning .notStoppedSmoking .wFF) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- "stopped smoking" narrows to exactly (T,F): past=T and now=F. -/
theorem stopped_world :
    literalMeaning .stoppedSmoking .wTT = false ∧
    literalMeaning .stoppedSmoking .wTF = true ∧
    literalMeaning .stoppedSmoking .wFT = false ∧
    literalMeaning .stoppedSmoking .wFF = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- "always smoked" = {(T,T)}, maximally informative for (T,T). -/
theorem alwaysSmoked_world :
    literalMeaning .alwaysSmoked .wTT = true ∧
    literalMeaning .alwaysSmoked .wTF = false ∧
    literalMeaning .alwaysSmoked .wFT = false ∧
    literalMeaning .alwaysSmoked .wFF = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- "never smoked" = {(F,F)}, maximally informative for (F,F). -/
theorem neverSmoked_world :
    literalMeaning .neverSmoked .wTT = false ∧
    literalMeaning .neverSmoked .wTF = false ∧
    literalMeaning .neverSmoked .wFT = false ∧
    literalMeaning .neverSmoked .wFF = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Context sets that entail past=T (used for measuring projection). -/
def entailsPast : ContextSet → Bool
  | .pastTrue | .pastTrueNowTrue | .pastTrueNowFalse => true
  | _ => false

/-- 3 of 9 context sets entail past=T. -/
theorem three_entail_past :
    (Finset.univ.filter (fun cs : ContextSet => entailsPast cs)).card = 3 := by
  native_decide

-- ============================================================================
-- §10. Connection to S&T and Warstadt
-- ============================================================================

/-!
## Mathematical Equivalence with @cite{scontras-tonhauser-2025} and @cite{warstadt-2022}

All three papers implement the same RSA computation:

```
L1(w, C | u, Q) ∝ S1(u | w, C, Q) · P(w) · P(C)
```

| Paper | Latent | Interpretation | Domain |
|-------|--------|---------------|--------|
| @cite{qing-goodman-lassiter-2016} | Context set C | Common ground | CoS verbs |
| @cite{scontras-tonhauser-2025} | Assumptions A | Speaker beliefs | Factives |
| @cite{warstadt-2022} | Context set C | Common ground | Genus-species |

The RSAConfig encoding is structurally identical: `Latent` = context/belief
state, `meaning` filters by compatibility, `s1Score` uses QUD-projected rpow.
See `ScontrasTonhauser2025.lean` for the factive domain implementation.

@cite{scontras-tonhauser-2025} fn. 10: "@cite{qing-goodman-lassiter-2016} call these subsets
the 'common ground,' but we think 'private assumptions' better captures
this component of the model."

The terminological difference is interpretive, not computational.
-/

end QingGoodmanLassiter2016
