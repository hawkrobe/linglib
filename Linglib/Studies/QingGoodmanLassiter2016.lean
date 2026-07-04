import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Semantics.Aspect.ChangeOfState

/-!
# [qing-goodman-lassiter-2016]

A rational speech-act model of projective content. CogSci 2016, pp. 1110–1115.

The listener jointly infers the world state and the common ground (context set)
the speaker assumed. Under the right QUD, this derives presupposition projection
without any special semantic mechanism.

## The Model

- **L0** (eq. 5): L0(Q(w) | u, C, Q) ∝ Σ_{w'∈C∩⟦u⟧} δ_{Q(w)=Q(w')} · P(w')
- **S1** (eq. 6): S(u|w,C,Q) ∝ P(u) · L0(Q(w) | u, C, Q)^α
- **L1** (eq. 7): L(w,C | u, Q) ∝ P(w) · P(C) · S(u | w, C, Q)

Domain: 13 utterances × 4 worlds × 9 context sets. α = 6.

## Formalization

Since α = 6 is a natural power, every layer of the model is a rational
function of the priors: the scores are computed in exact ℚ (`l0Q` through
`worldScoreQ`/`ctxScoreQ`), the listeners are `PMF.normalize` of those
scores, and the two meet through `ENNReal.ofReal_sum_of_nonneg` bridges.
Every prediction is a kernel-verified rational comparison; the lone
exception is the QUD_now symmetry, which holds definitionally.

## Key Insight: QUD Projection and Context Set Inference

Under QUD_now ("Does John smoke now?"), S1 scores depend on `now(w)` only —
worlds with the same `now` value are indistinguishable (§8.1). This means
presupposition projection CANNOT be observed at the world marginal level.
Instead, projection surfaces in the **context set posterior** (`l1Ctx`):
L1 infers the speaker assumed a context set entailing `past=T` (§8.5).

Under QUD_max (identity QUD), the past-now degeneracy breaks and projection
is visible directly at the world level (§8.4).

## Context Set Simplification

The paper uses 15 non-empty context sets (all 2^4 - 1 subsets of 4 worlds) with
5% noise added to eq. (8) to ensure nonzero priors. We model only the 9 context
sets derivable from observations about past/now, since the remaining 6 (e.g.,
`change = {(T,F),(F,T)}`) receive only the noise prior (≥18× lower) and do not
affect qualitative predictions.

## Connection to [scontras-tonhauser-2025] and [warstadt-2022]

All three papers implement the same mathematical structure with different
domains (change-of-state verbs, factives, genus-species). The latent variable
is called "context set" here and "private assumptions" in S&T, but the
computation is identical. See `ScontrasTonhauser2025.lean` for the factive
domain.
-/

set_option autoImplicit false

namespace QingGoodmanLassiter2016

open BigOperators
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
    CoS theory in `Semantics.Aspect.ChangeOfState`. -/
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

open Features.ChangeOfState (priorStatePresup resultStateAssertion)

/-- "Stopped smoking" = cessation presupposition (past=T) ∧ cessation assertion (now=F).

    The CoS theory operates on a single predicate P, but the QGL world model
    separates prior state (`past`) from current state (`now`). We use `·.past`
    for the presupposition and `·.now` for the assertion. -/
theorem stopped_matches_cessation (w : WorldState) :
    literalMeaning .stoppedSmoking w = true ↔
    (priorStatePresup .cessation (fun w => w.past = true) w ∧
     resultStateAssertion .cessation (fun w => w.now = true) w) := by
  cases w <;> simp [literalMeaning, priorStatePresup, resultStateAssertion,
    WorldState.past, WorldState.now]

/-- "Started smoking" = inception presupposition (past=F) ∧ inception assertion (now=T). -/
theorem started_matches_inception (w : WorldState) :
    literalMeaning .startedSmoking w = true ↔
    (priorStatePresup .inception (fun w => w.past = true) w ∧
     resultStateAssertion .inception (fun w => w.now = true) w) := by
  cases w <;> simp [literalMeaning, priorStatePresup, resultStateAssertion,
    WorldState.past, WorldState.now]

/-- "Always smoked" = continuation presupposition (past=T) ∧ continuation assertion (now=T). -/
theorem always_matches_continuation (w : WorldState) :
    literalMeaning .alwaysSmoked w = true ↔
    (priorStatePresup .continuation (fun w => w.past = true) w ∧
     resultStateAssertion .continuation (fun w => w.now = true) w) := by
  cases w <;> simp [literalMeaning, priorStatePresup, resultStateAssertion,
    WorldState.past, WorldState.now]

-- ============================================================================
-- §4. Context Sets (Common Ground)
-- ============================================================================

/-- Context sets: subsets of worlds representing common ground.
    These are the 9 context sets derivable from observations about past and now
    (eq. 8). The paper's full model uses 15 non-empty subsets with 5% noise;
    the omitted 6 (e.g., `change = {(T,F),(F,T)}`) have negligible prior. -/
inductive ContextSet where
  | pastTrue           -- +past: CommonGround entails John smoked
  | pastFalse          -- -past: CommonGround entails John didn't smoke
  | nowTrue            -- +now: CommonGround entails John smokes
  | nowFalse           -- -now: CommonGround entails John doesn't smoke
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

/-- Context set prior (eq. 8): Pr(C) ∝ Σ_{CommonGround⊆Obs} P(CommonGround) · δ_{C=∩CommonGround}.
    Each observation enters CommonGround independently with probability 0.4.
    P(CommonGround) = 0.4^|CommonGround| × 0.6^(4-|CommonGround|).
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
-- §7b. Exact-ℚ model and PMF face (local pending the RSA API pass)
-- ============================================================================

/-! The model computed in exact rational arithmetic (the project's RSA
convention): α = 6 is a natural power, so every layer — literal listener,
QUD aggregation (eq. 5), speaker (eq. 6), listener scores (eq. 7) — is a
rational function of the priors. The PMF face below normalizes these scores;
its values bridge to the ℚ layer by `ENNReal.ofReal_sum_of_nonneg`. -/

section QModel

/-- Literal-listener mass: worlds compatible with the context set where `u`
is literally true (eq. 5's normaliser; uniform world prior cancels). -/
def l0MassQ (cs : ContextSet) (u : Utterance) : ℚ :=
  ∑ w, (if compatibleBool cs w && literalMeaning u w then (1 : ℚ) else 0)

/-- Literal listener value (division by zero yields 0 at empty extensions). -/
def l0Q (cs : ContextSet) (u : Utterance) (w : WorldState) : ℚ :=
  (if compatibleBool cs w && literalMeaning u w then (1 : ℚ) else 0) / l0MassQ cs u

/-- QUD aggregation of the literal listener (eq. 5): sum over the QUD cell. -/
def qAggQ (qud : QUD) (cs : ContextSet) (u : Utterance) : WorldState → ℚ
  | .wTT => match qud with
    | .now => l0Q cs u .wTT + l0Q cs u .wFT
    | .max => l0Q cs u .wTT
    | .past => l0Q cs u .wTT + l0Q cs u .wTF
  | .wTF => match qud with
    | .now => l0Q cs u .wTF + l0Q cs u .wFF
    | .max => l0Q cs u .wTF
    | .past => l0Q cs u .wTT + l0Q cs u .wTF
  | .wFT => match qud with
    | .now => l0Q cs u .wTT + l0Q cs u .wFT
    | .max => l0Q cs u .wFT
    | .past => l0Q cs u .wFT + l0Q cs u .wFF
  | .wFF => match qud with
    | .now => l0Q cs u .wTF + l0Q cs u .wFF
    | .max => l0Q cs u .wFF
    | .past => l0Q cs u .wFT + l0Q cs u .wFF

/-- Speaker weight (eq. 6 at α = 6): `Pr(u) · qAgg⁶`. -/
def s1WeightQ (qud : QUD) (cs : ContextSet) (w : WorldState) (u : Utterance) : ℚ :=
  utterancePrior u * (qAggQ qud cs u w) ^ 6

/-- Speaker normaliser. -/
def s1ZQ (qud : QUD) (cs : ContextSet) (w : WorldState) : ℚ :=
  ∑ u, s1WeightQ qud cs w u

/-- Normalized speaker value. -/
def s1ValQ (qud : QUD) (cs : ContextSet) (w : WorldState) (u : Utterance) : ℚ :=
  s1WeightQ qud cs w u / s1ZQ qud cs w

/-- Listener world score (eq. 7, world side): context-prior-weighted speaker
mass, before normalization. -/
def worldScoreQ (qud : QUD) (u : Utterance) (w : WorldState) : ℚ :=
  ∑ cs, contextPrior cs * s1ValQ qud cs w u

/-- Listener context score (eq. 7, context side). -/
def ctxScoreQ (qud : QUD) (u : Utterance) (cs : ContextSet) : ℚ :=
  contextPrior cs * ∑ w, s1ValQ qud cs w u

theorem l0MassQ_nonneg (cs : ContextSet) (u : Utterance) : 0 ≤ l0MassQ cs u :=
  Finset.sum_nonneg fun _ _ => by split <;> norm_num

theorem l0Q_nonneg (cs : ContextSet) (u : Utterance) (w : WorldState) :
    0 ≤ l0Q cs u w :=
  div_nonneg (by split <;> norm_num) (l0MassQ_nonneg cs u)

theorem qAggQ_nonneg (qud : QUD) (cs : ContextSet) (u : Utterance) (w : WorldState) :
    0 ≤ qAggQ qud cs u w := by
  cases w <;> cases qud <;>
    simp only [qAggQ] <;>
    first
      | exact l0Q_nonneg cs u _
      | exact add_nonneg (l0Q_nonneg cs u _) (l0Q_nonneg cs u _)

theorem s1WeightQ_nonneg (qud : QUD) (cs : ContextSet) (w : WorldState) (u : Utterance) :
    0 ≤ s1WeightQ qud cs w u :=
  mul_nonneg (utterancePrior_nonneg u) (pow_nonneg (qAggQ_nonneg qud cs u w) 6)

theorem s1ZQ_nonneg (qud : QUD) (cs : ContextSet) (w : WorldState) :
    0 ≤ s1ZQ qud cs w :=
  Finset.sum_nonneg fun u _ => s1WeightQ_nonneg qud cs w u

theorem s1ValQ_nonneg (qud : QUD) (cs : ContextSet) (w : WorldState) (u : Utterance) :
    0 ≤ s1ValQ qud cs w u :=
  div_nonneg (s1WeightQ_nonneg qud cs w u) (s1ZQ_nonneg qud cs w)

theorem worldScoreQ_nonneg (qud : QUD) (u : Utterance) (w : WorldState) :
    0 ≤ worldScoreQ qud u w :=
  Finset.sum_nonneg fun cs _ =>
    mul_nonneg (le_of_lt (contextPrior_pos cs)) (s1ValQ_nonneg qud cs w u)

theorem ctxScoreQ_nonneg (qud : QUD) (u : Utterance) (cs : ContextSet) :
    0 ≤ ctxScoreQ qud u cs :=
  mul_nonneg (le_of_lt (contextPrior_pos cs))
    (Finset.sum_nonneg fun w _ => s1ValQ_nonneg qud cs w u)

end QModel

section PMFFace

open scoped ENNReal

/-- PMF speaker (eq. 6), total via dite (pure-silence fallback at cells with
no compatible utterance). -/
noncomputable def s1PMF (qud : QUD) (cs : ContextSet) (w : WorldState) : PMF Utterance :=
  if h : (∑' u, ENNReal.ofReal ((s1WeightQ qud cs w u : ℝ))) ≠ 0 then
    PMF.normalize (fun u => ENNReal.ofReal ((s1WeightQ qud cs w u : ℝ))) h
      (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)
  else PMF.pure .silence

private theorem sumW_eq (qud : QUD) (cs : ContextSet) (w : WorldState) :
    (∑' u, ENNReal.ofReal ((s1WeightQ qud cs w u : ℝ)))
      = ENNReal.ofReal ((s1ZQ qud cs w : ℝ)) := by
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
    (fun u _ => by exact_mod_cast s1WeightQ_nonneg qud cs w u)]
  congr 1
  push_cast [s1ZQ]
  rfl

/-- The PMF speaker's values bridge exactly to the ℚ model (off `silence`,
which absorbs the degenerate fallback). -/
theorem s1PMF_apply (qud : QUD) (cs : ContextSet) (w : WorldState)
    {u : Utterance} (hu : u ≠ .silence) :
    s1PMF qud cs w u = ENNReal.ofReal ((s1ValQ qud cs w u : ℝ)) := by
  unfold s1PMF
  by_cases hZ : (0 : ℚ) < s1ZQ qud cs w
  · rw [dif_pos (by rw [sumW_eq, ENNReal.ofReal_ne_zero_iff]; exact_mod_cast hZ),
      PMF.normalize_apply, sumW_eq,
      ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hZ),
      ← ENNReal.ofReal_mul (by exact_mod_cast s1WeightQ_nonneg qud cs w u)]
    congr 1
    push_cast [s1ValQ]
    rw [div_eq_mul_inv]
  · have hZ0 : s1ZQ qud cs w = 0 := le_antisymm (not_lt.mp hZ) (s1ZQ_nonneg _ _ _)
    rw [dif_neg (by rw [sumW_eq, hZ0]; simp),
      show s1ValQ qud cs w u = 0 from by rw [s1ValQ, hZ0, div_zero]]
    simp [PMF.pure_apply, hu]

/-- World score of the pragmatic listener in PMF terms. -/
noncomputable def wScore (qud : QUD) (u : Utterance) (w : WorldState) : ℝ≥0∞ :=
  ∑' cs, ENNReal.ofReal ((contextPrior cs : ℝ)) * s1PMF qud cs w u

theorem wScore_eq (qud : QUD) {u : Utterance} (hu : u ≠ .silence) (w : WorldState) :
    wScore qud u w = ENNReal.ofReal ((worldScoreQ qud u w : ℝ)) := by
  unfold wScore
  rw [tsum_fintype,
    Finset.sum_congr rfl (fun cs _ => by
      rw [s1PMF_apply qud cs w hu,
        ← ENNReal.ofReal_mul (by exact_mod_cast le_of_lt (contextPrior_pos cs))]),
    ← ENNReal.ofReal_sum_of_nonneg (fun cs _ => by
      exact_mod_cast mul_nonneg (le_of_lt (contextPrior_pos cs))
        (s1ValQ_nonneg qud cs w u))]
  congr 1
  push_cast [worldScoreQ]
  rfl

/-- Context score of the pragmatic listener in PMF terms. -/
noncomputable def cScore (qud : QUD) (u : Utterance) (cs : ContextSet) : ℝ≥0∞ :=
  ENNReal.ofReal ((contextPrior cs : ℝ)) * ∑' w, s1PMF qud cs w u

theorem cScore_eq (qud : QUD) {u : Utterance} (hu : u ≠ .silence) (cs : ContextSet) :
    cScore qud u cs = ENNReal.ofReal ((ctxScoreQ qud u cs : ℝ)) := by
  unfold cScore
  rw [tsum_fintype,
    Finset.sum_congr rfl (fun w _ => s1PMF_apply qud cs w hu),
    ← ENNReal.ofReal_sum_of_nonneg (fun w _ => by
      exact_mod_cast s1ValQ_nonneg qud cs w u),
    ← ENNReal.ofReal_mul (by exact_mod_cast le_of_lt (contextPrior_pos cs))]
  congr 1
  push_cast [ctxScoreQ]
  rfl

/-- World-side pragmatic listener (eq. 7), dite-total. -/
noncomputable def l1World (qud : QUD) (u : Utterance) : PMF WorldState :=
  if h : (∑' w, wScore qud u w) ≠ 0 then
    PMF.normalize (wScore qud u) h
      (ENNReal.tsum_ne_top_of_fintype fun _ =>
        ENNReal.tsum_ne_top_of_fintype fun _ =>
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _))
  else PMF.uniformOfFintype WorldState

/-- Context-side pragmatic listener (eq. 7), dite-total. -/
noncomputable def l1Ctx (qud : QUD) (u : Utterance) : PMF ContextSet :=
  if h : (∑' cs, cScore qud u cs) ≠ 0 then
    PMF.normalize (cScore qud u) h
      (ENNReal.tsum_ne_top_of_fintype fun _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.tsum_ne_top_of_fintype fun _ => PMF.apply_ne_top _ _))
  else PMF.uniformOfFintype ContextSet

end PMFFace

section PMFFace

open scoped ENNReal

private theorem sumWorlds4 (f : WorldState → ℝ≥0∞) :
    ∑' w, f w = f .wTT + f .wTF + f .wFT + f .wFF := by
  rw [tsum_fintype,
    show (Finset.univ : Finset WorldState) = {.wTT, .wTF, .wFT, .wFF} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem wZ_fin (qud : QUD) (u : Utterance) :
    (∑' w, wScore qud u w) ≠ ⊤ :=
  ENNReal.tsum_ne_top_of_fintype fun _ =>
    ENNReal.tsum_ne_top_of_fintype fun _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)

private theorem wZ_pos_now_ns : (∑' w, wScore .now .notStoppedSmoking w) ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.wTT, by
    rw [wScore_eq .now (by decide) _, ENNReal.ofReal_ne_zero_iff]
    exact_mod_cast
      (by decide +kernel : (0:ℚ) < worldScoreQ .now .notStoppedSmoking .wTT)⟩

private theorem wZ_pos_max_ns : (∑' w, wScore .max .notStoppedSmoking w) ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.wTT, by
    rw [wScore_eq .max (by decide) _, ENNReal.ofReal_ne_zero_iff]
    exact_mod_cast
      (by decide +kernel : (0:ℚ) < worldScoreQ .max .notStoppedSmoking .wTT)⟩

private theorem wZ_pos_now_st : (∑' w, wScore .now .stoppedSmoking w) ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.wTF, by
    rw [wScore_eq .now (by decide) _, ENNReal.ofReal_ne_zero_iff]
    exact_mod_cast
      (by decide +kernel : (0:ℚ) < worldScoreQ .now .stoppedSmoking .wTF)⟩

private theorem cZ_pos_now_ns : (∑' cs, cScore .now .notStoppedSmoking cs) ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.pastTrue, by
    rw [cScore_eq .now (by decide) _, ENNReal.ofReal_ne_zero_iff]
    exact_mod_cast
      (by decide +kernel : (0:ℚ) < ctxScoreQ .now .notStoppedSmoking .pastTrue)⟩

/-- Score comparison under a shared normaliser: the workhorse for every
strict listener prediction below. -/
private theorem ofReal_mul_inv_lt {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) (hZt : Z ≠ ⊤)
    {a b : ℝ} (hb : 0 < b) (hab : a < b) :
    ENNReal.ofReal a * Z⁻¹ < ENNReal.ofReal b * Z⁻¹ := by
  rw [mul_comm, mul_comm (ENNReal.ofReal b)]
  exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hZt)
    (ENNReal.inv_ne_top.mpr hZ0) ((ENNReal.ofReal_lt_ofReal_iff hb).mpr hab)

/-- Listener world values in ℚ-bridged form. -/
private theorem l1World_apply (qud : QUD) {u : Utterance} (hu : u ≠ .silence)
    (hpos : (∑' w, wScore qud u w) ≠ 0) (w : WorldState) :
    l1World qud u w
      = ENNReal.ofReal ((worldScoreQ qud u w : ℝ)) * (∑' w', wScore qud u w')⁻¹ := by
  unfold l1World
  rw [dif_pos hpos, PMF.normalize_apply, wScore_eq qud hu w]

/-- Event marginal of the world-side listener. -/
noncomputable def l1WorldEvent (qud : QUD) (u : Utterance)
    (P : WorldState → Prop) [DecidablePred P] : ℝ≥0∞ :=
  ∑' w, if P w then l1World qud u w else 0

private theorem cZ_fin (qud : QUD) (u : Utterance) :
    (∑' cs, cScore qud u cs) ≠ ⊤ :=
  ENNReal.tsum_ne_top_of_fintype fun _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.tsum_ne_top_of_fintype fun _ => PMF.apply_ne_top _ _)

/-- Listener context values in ℚ-bridged form. -/
private theorem l1Ctx_apply (qud : QUD) {u : Utterance} (hu : u ≠ .silence)
    (hpos : (∑' cs, cScore qud u cs) ≠ 0) (cs : ContextSet) :
    l1Ctx qud u cs
      = ENNReal.ofReal ((ctxScoreQ qud u cs : ℝ)) * (∑' cs', cScore qud u cs')⁻¹ := by
  unfold l1Ctx
  rw [dif_pos hpos, PMF.normalize_apply, cScore_eq qud hu cs]

end PMFFace

-- ============================================================================
-- §8. L1 Predictions
-- ============================================================================

/-! ### §8.1 QUD_now symmetry

Under QUD_now, the QUD aggregation maps wTT and wFT to the same value (both
have now=T), so S1(cs, wTT, u) = S1(cs, wFT, u) for all cs. With uniform
worldPrior and w-independent latentPrior, L1(wTT) = L1(wFT). This means
presupposition projection **cannot** be measured by world marginal under
QUD_now — the past dimension is invisible to L1. -/

/-- **QUD_now symmetry**: wTT and wFT are indistinguishable.

    This is the structural reason why projection under QUD_now must be
    measured via context set inference (the `l1Ctx` side), not the world
    marginal — `qAggQ .now` is definitionally symmetric in the now-cell. -/
theorem qud_now_wTT_eq_wFT :
    l1World .now .notStoppedSmoking .wTT =
    l1World .now .notStoppedSmoking .wFT := by
  rw [l1World_apply .now (by decide) wZ_pos_now_ns,
    l1World_apply .now (by decide) wZ_pos_now_ns]
  congr 2

/-! ### §8.2 QUD answer

After hearing "didn't stop smoking" with QUD = "Does John smoke now?",
L1 correctly infers the QUD answer: John smokes (now=T). -/

/-- **QUD answer inference**: L1 infers now=T from "didn't stop smoking". -/
theorem qud_answer_now_true :
    l1WorldEvent .now .notStoppedSmoking (fun w => w.now = true) >
    l1WorldEvent .now .notStoppedSmoking (fun w => w.now = false) := by
  unfold l1WorldEvent
  rw [gt_iff_lt, sumWorlds4, sumWorlds4]
  simp +decide only [if_true, if_false, add_zero, zero_add]
  simp only [l1World_apply .now (by decide) wZ_pos_now_ns]
  rw [← add_mul, ← add_mul,
    ← ENNReal.ofReal_add (by exact_mod_cast worldScoreQ_nonneg .now .notStoppedSmoking _)
      (by exact_mod_cast worldScoreQ_nonneg .now .notStoppedSmoking _),
    ← ENNReal.ofReal_add (by exact_mod_cast worldScoreQ_nonneg .now .notStoppedSmoking _)
      (by exact_mod_cast worldScoreQ_nonneg .now .notStoppedSmoking _)]
  exact ofReal_mul_inv_lt wZ_pos_now_ns (wZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) <
      worldScoreQ .now .notStoppedSmoking .wTT + worldScoreQ .now .notStoppedSmoking .wFT))
    (by exact_mod_cast (by decide +kernel :
      worldScoreQ .now .notStoppedSmoking .wTF + worldScoreQ .now .notStoppedSmoking .wFF <
      worldScoreQ .now .notStoppedSmoking .wTT + worldScoreQ .now .notStoppedSmoking .wFT))

/-! ### §8.3 World elimination

Within worlds sharing the same past value, now=T dominates now=F.
"Didn't stop smoking" is literally false at wTF (past=T, now=F is exactly
"stopped smoking"), concentrating L1 mass on wTT. -/

/-- **Now=T dominates now=F** among past=T worlds. -/
theorem wTT_gt_wTF :
    l1World .now .notStoppedSmoking .wTT >
    l1World .now .notStoppedSmoking .wTF := by
  rw [gt_iff_lt, l1World_apply .now (by decide) wZ_pos_now_ns, l1World_apply .now (by decide) wZ_pos_now_ns]
  exact ofReal_mul_inv_lt wZ_pos_now_ns (wZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < worldScoreQ .now .notStoppedSmoking .wTT))
    (by exact_mod_cast (by decide +kernel :
      worldScoreQ .now .notStoppedSmoking .wTF < worldScoreQ .now .notStoppedSmoking .wTT))

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

/-- **Projection under QUD_max**: wTT > wFT. -/
theorem projection_under_qud_max :
    l1World .max .notStoppedSmoking .wTT >
    l1World .max .notStoppedSmoking .wFT := by
  rw [gt_iff_lt, l1World_apply .max (by decide) wZ_pos_max_ns, l1World_apply .max (by decide) wZ_pos_max_ns]
  exact ofReal_mul_inv_lt wZ_pos_max_ns (wZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < worldScoreQ .max .notStoppedSmoking .wTT))
    (by exact_mod_cast (by decide +kernel :
      worldScoreQ .max .notStoppedSmoking .wFT < worldScoreQ .max .notStoppedSmoking .wTT))

/-- **Incomplete projection under QUD_max**: wTT = wFF (Figure 1c).

    Under the identity QUD, (T,T) and (F,F) receive equal L1 probability —
    the involution swapping (past, now) ↦ (¬now, ¬past) fixes the meaning of
    "didn't stop" and permutes the context sets prior-preservingly. Projection
    is NOT captured at the world level under QUD_max. -/
theorem qud_max_incomplete_projection :
    l1World .max .notStoppedSmoking .wTT =
    l1World .max .notStoppedSmoking .wFF := by
  rw [l1World_apply .max (by decide) wZ_pos_max_ns,
    l1World_apply .max (by decide) wZ_pos_max_ns]
  congr 2
  exact_mod_cast (by decide +kernel :
    worldScoreQ .max .notStoppedSmoking .wTT
      = worldScoreQ .max .notStoppedSmoking .wFF)

/-! ### §8.5 Context set projection (the paper's main result, Figure 3)

The paper's headline result: after hearing "didn't stop smoking" under QUD_now,
L1 infers the speaker assumed a **+past context set** (common ground where John
smoked). This is presupposition projection: the presupposed content (past=T)
enters the listener's beliefs about the common ground, even though the utterance
literally says nothing about the past.

The mechanism: under +past context, "didn't stop" narrows L0 to exactly wTT,
giving aggregate 1 and `1⁶ = 1` (maximally informative). Under
-past context, L0 spreads over wFT and wFF, giving aggregate `1/2` and
`(1/2)⁶ = 1/64` (weakly informative). Since S1 rewards informativity,
the speaker is much more likely to use "didn't stop" when the +past context
holds, and L1 infers this.

Figure 3 shows that (T,T) with context set +past is the unique maximum of the
joint distribution under CommonGround prior + QUD_now. -/

/-- **Context set projection**: L1 infers +past context over -past context. -/
theorem context_projection :
    l1Ctx .now .notStoppedSmoking .pastTrue >
    l1Ctx .now .notStoppedSmoking .pastFalse := by
  rw [gt_iff_lt, l1Ctx_apply .now (by decide) cZ_pos_now_ns, l1Ctx_apply .now (by decide) cZ_pos_now_ns]
  exact ofReal_mul_inv_lt cZ_pos_now_ns (cZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < ctxScoreQ .now .notStoppedSmoking .pastTrue))
    (by exact_mod_cast (by decide +kernel :
      ctxScoreQ .now .notStoppedSmoking .pastFalse < ctxScoreQ .now .notStoppedSmoking .pastTrue))

/-- **+past beats uninformative universe** despite lower prior (9 vs 6).

    Under +past, "didn't stop" narrows to exactly wTT (`1⁶ = 1`).
    Under universe, it spreads over 3 worlds (`(1/4)⁶ ≈ 0`). The
    informativity gain overwhelms the prior advantage. -/
theorem context_projection_over_universe :
    l1Ctx .now .notStoppedSmoking .pastTrue >
    l1Ctx .now .notStoppedSmoking .universe := by
  rw [gt_iff_lt, l1Ctx_apply .now (by decide) cZ_pos_now_ns, l1Ctx_apply .now (by decide) cZ_pos_now_ns]
  exact ofReal_mul_inv_lt cZ_pos_now_ns (cZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < ctxScoreQ .now .notStoppedSmoking .pastTrue))
    (by exact_mod_cast (by decide +kernel :
      ctxScoreQ .now .notStoppedSmoking .universe < ctxScoreQ .now .notStoppedSmoking .pastTrue))

/-- **-now context is dispreferred** (p. 1114): -now already entails the QUD
    answer (John doesn't smoke now), so the speaker would be maximally
    informative even saying nothing — "didn't stop smoking" adds no value.
    L1 therefore infers the speaker did NOT assume a -now context. -/
theorem now_context_dispreferred :
    l1Ctx .now .notStoppedSmoking .pastTrue >
    l1Ctx .now .notStoppedSmoking .nowFalse := by
  rw [gt_iff_lt, l1Ctx_apply .now (by decide) cZ_pos_now_ns, l1Ctx_apply .now (by decide) cZ_pos_now_ns]
  exact ofReal_mul_inv_lt cZ_pos_now_ns (cZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < ctxScoreQ .now .notStoppedSmoking .pastTrue))
    (by exact_mod_cast (by decide +kernel :
      ctxScoreQ .now .notStoppedSmoking .nowFalse < ctxScoreQ .now .notStoppedSmoking .pastTrue))

/-! ### §8.6 "Stopped smoking" projects past=T via QUD answer

"Stopped smoking" is true only at wTF (past=T, now=F). Under QUD_now,
L1 infers the QUD answer is now=F. -/

/-- "Stopped smoking" → L1 infers now=F (the assertion). -/
theorem stopped_qud_answer :
    l1WorldEvent .now .stoppedSmoking (fun w => w.now = false) >
    l1WorldEvent .now .stoppedSmoking (fun w => w.now = true) := by
  unfold l1WorldEvent
  rw [gt_iff_lt, sumWorlds4, sumWorlds4]
  simp +decide only [if_true, if_false, add_zero, zero_add]
  simp only [l1World_apply .now (by decide) wZ_pos_now_st]
  rw [← add_mul, ← add_mul,
    ← ENNReal.ofReal_add (by exact_mod_cast worldScoreQ_nonneg .now .stoppedSmoking _)
      (by exact_mod_cast worldScoreQ_nonneg .now .stoppedSmoking _),
    ← ENNReal.ofReal_add (by exact_mod_cast worldScoreQ_nonneg .now .stoppedSmoking _)
      (by exact_mod_cast worldScoreQ_nonneg .now .stoppedSmoking _)]
  exact ofReal_mul_inv_lt wZ_pos_now_st (wZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) <
      worldScoreQ .now .stoppedSmoking .wTF + worldScoreQ .now .stoppedSmoking .wFF))
    (by exact_mod_cast (by decide +kernel :
      worldScoreQ .now .stoppedSmoking .wTT + worldScoreQ .now .stoppedSmoking .wFT <
      worldScoreQ .now .stoppedSmoking .wTF + worldScoreQ .now .stoppedSmoking .wFF))

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
  decide

-- ============================================================================
-- §10. Connection to S&T and Warstadt
-- ============================================================================

/-!
## Mathematical Equivalence with [scontras-tonhauser-2025] and [warstadt-2022]

All three papers implement the same RSA computation:

```
L1(w, C | u, Q) ∝ S1(u | w, C, Q) · P(w) · P(C)
```

| Paper | Latent | Interpretation | Domain |
|-------|--------|---------------|--------|
| [qing-goodman-lassiter-2016] | Context set C | Common ground | CoS verbs |
| [scontras-tonhauser-2025] | Assumptions A | Speaker beliefs | Factives |
| [warstadt-2022] | Context set C | Common ground | Genus-species |

The encoding is structurally identical: the latent is the context/belief
state, the literal listener filters by compatibility, and the speaker
scores the QUD-projected literal posterior. See `ScontrasTonhauser2025.lean`
for the factive domain implementation.

[scontras-tonhauser-2025] fn. 10: "[qing-goodman-lassiter-2016] call these subsets
the 'common ground,' but we think 'private assumptions' better captures
this component of the model."

The terminological difference is interpretive, not computational.
-/

end QingGoodmanLassiter2016
