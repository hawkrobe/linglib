import Linglib.Pragmatics.RSA.ScoreChain
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Semantics.Aspect.ChangeOfState

/-!
# [qing-goodman-lassiter-2016]: an RSA model of projective content

The listener jointly infers the world state and the context set the speaker
assumed (CogSci 2016, pp. 1110–1115). Under the right QUD this derives
presupposition projection with no special semantic mechanism: L0 answers the
QUD within the context set (eq. 5), S1 scores QUD-projected informativity
(eq. 6, α = 6), and L1 inverts jointly over worlds and context sets (eq. 7).
Domain: 13 utterances × 4 worlds × 9 context sets.

## Main results

* `qud_now_wTT_eq_wFT`: under QUD_now the world marginal cannot show
  projection — the now-cell aggregation is definitionally symmetric.
* `context_projection`: the paper's headline — after "didn't stop smoking",
  L1 infers a +past context set over −past (and over `universe`,
  `context_projection_over_universe`, despite its higher prior).
* `projection_under_qud_max` / `qud_max_incomplete_projection`: under the
  identity QUD projection is visible at the world level but incomplete
  (wTT = wFF, Figure 1c).
* `qud_answer_now_true` / `stopped_qud_answer`: L1 recovers the QUD answer.

## Implementation notes

α = 6 is a natural power, so the chain is exact ℚ≥0: the speaker is
`RSA.Score.s1` over the QUD-aggregated literal listener (dead cells fall
back to silence — one fallback declaration covers both faces), listeners
are `PMF.ofScores` of the prior-weighted speaker mass, and each prediction
closes by the `ofScores` comparison family with one kernel certificate.

The paper uses 15 context sets with 5% noise; we model the 9 derivable from
past/now observations — the omitted 6 carry only the noise prior (≥ 18×
lower) and do not affect the qualitative predictions.

## TODO

Prove the structural equivalence with [scontras-tonhauser-2025] (factives;
latent = "private assumptions", their fn. 10: the difference from QGL's
"common ground" is interpretive, not computational) and [warstadt-2022]
(genus-species) — all three compute `L1(w, C | u, Q) ∝ S1(u | w, C, Q) ·
P(w) · P(C)` over different domains. Blocked on `ScontrasTonhauser2025.lean`
reaching the PMF face.
-/

namespace QingGoodmanLassiter2016

open BigOperators
open scoped ENNReal NNRat
/-! ### World states -/

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

/-! ### Utterances (Table 1, negations, silence) -/

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

/-! ### Literal semantics -/

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

/-! ### Context sets -/

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

/-! ### QUD -/

/-- Questions under discussion. -/
inductive QUD where
  | now   -- "Does John smoke now?" (partitions by now)
  | max   -- Full world identification (identity QUD)
  | past  -- "Did John smoke?" (partitions by past)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### Priors -/

/-- Utterance prior (eq. 1): Pr(u) ∝ 2^{-#content-words(u)}.
    Negation and auxiliaries excluded from count.
    - 2 content words: stopped/started/always/never smoking → 1/4
    - 1 content word: smokes/smoked → 1/2
    - 0 content words: silence → 1 -/
def utterancePrior : Utterance → ℚ≥0
  | .smokes | .doesntSmoke | .smoked | .didntSmoke => 1/2
  | .alwaysSmoked | .notAlwaysSmoked
  | .stoppedSmoking | .notStoppedSmoking
  | .startedSmoking | .notStartedSmoking
  | .neverSmoked | .notNeverSmoked => 1/4
  | .silence => 1

/-- Context set prior (eq. 8):
`Pr(C) ∝ Σ_{CG ⊆ Obs} P(CG) · δ_{C = ∩CG}`.
    Each observation enters CommonGround independently with probability 0.4.
    P(CommonGround) = 0.4^|CommonGround| × 0.6^(4-|CommonGround|).
    - 0 observations (universe): 0.6^4 ∝ 9
    - 1 observation (single): 0.4 × 0.6^3 ∝ 6
    - 2 observations (pair): 0.4^2 × 0.6^2 ∝ 4 -/
def contextPrior : ContextSet → ℚ≥0
  | .universe => 9
  | .pastTrue | .pastFalse | .nowTrue | .nowFalse => 6
  | .pastTrueNowTrue | .pastTrueNowFalse
  | .pastFalseNowTrue | .pastFalseNowFalse => 4

/-! ### The score chain -/

/-- Literal listener within the context set (eq. 5; the uniform world
prior cancels, and empty extensions normalize to the zero row). -/
def l0Score (cs : ContextSet) (u : Utterance) : WorldState → ℚ≥0 :=
  PMF.normalizeScores fun w =>
    if compatibleBool cs w && literalMeaning u w then 1 else 0

/-- QUD aggregation of the literal listener (eq. 5): sum over the QUD cell. -/
def qAgg (qud : QUD) (cs : ContextSet) (u : Utterance) : WorldState → ℚ≥0
  | .wTT => match qud with
    | .now => l0Score cs u .wTT + l0Score cs u .wFT
    | .max => l0Score cs u .wTT
    | .past => l0Score cs u .wTT + l0Score cs u .wTF
  | .wTF => match qud with
    | .now => l0Score cs u .wTF + l0Score cs u .wFF
    | .max => l0Score cs u .wTF
    | .past => l0Score cs u .wTT + l0Score cs u .wTF
  | .wFT => match qud with
    | .now => l0Score cs u .wTT + l0Score cs u .wFT
    | .max => l0Score cs u .wFT
    | .past => l0Score cs u .wFT + l0Score cs u .wFF
  | .wFF => match qud with
    | .now => l0Score cs u .wTF + l0Score cs u .wFF
    | .max => l0Score cs u .wFF
    | .past => l0Score cs u .wFT + l0Score cs u .wFF

/-- Speaker (eq. 6 at α = 6): `RSA.Score.s1` over the QUD-aggregated
literal listener with the utterance prior as multiplicative cost; dead
cells fall back to silence. -/
def s1Post (qud : QUD) (cs : ContextSet) : WorldState → Utterance → ℚ≥0 :=
  RSA.Score.s1 (fun u w => qAgg qud cs u w) 6 utterancePrior (.pure .silence)

/-- Listener world score (eq. 7, world side): context-prior-weighted
speaker mass. -/
def worldScore (qud : QUD) (u : Utterance) (w : WorldState) : ℚ≥0 :=
  ∑ cs, contextPrior cs * s1Post qud cs w u

/-- Listener context score (eq. 7, context side). -/
def ctxScore (qud : QUD) (u : Utterance) (cs : ContextSet) : ℚ≥0 :=
  contextPrior cs * ∑ w, s1Post qud cs w u

/-- World-side pragmatic listener (eq. 7). -/
noncomputable def l1World (qud : QUD) (u : Utterance) : PMF WorldState :=
  .ofScores .uniform (worldScore qud u)

/-- Context-side pragmatic listener (eq. 7). -/
noncomputable def l1Ctx (qud : QUD) (u : Utterance) : PMF ContextSet :=
  .ofScores .uniform (ctxScore qud u)

/-- Event marginal of the world-side listener. -/
noncomputable def l1WorldEvent (qud : QUD) (u : Utterance)
    (P : WorldState → Bool) : ℝ≥0∞ :=
  ∑' w, if P w then l1World qud u w else 0

/-! ### Listener predictions -/

/-! ### QUD_now symmetry -/

/-- Under QUD_now, wTT and wFT are indistinguishable: `qAggQ .now` is
definitionally symmetric in the now-cell, so projection must be measured on
the context-set side (`l1Ctx`), not the world marginal. -/
theorem qud_now_wTT_eq_wFT :
    l1World .now .notStoppedSmoking .wTT =
    l1World .now .notStoppedSmoking .wFT :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-! ### QUD answer -/

/-- L1 infers the QUD answer now=T from "didn't stop smoking". -/
theorem qud_answer_now_true :
    l1WorldEvent .now .notStoppedSmoking (fun w => !w.now) <
    l1WorldEvent .now .notStoppedSmoking (·.now) :=
  PMF.ofScores_event_lt _ _ (by decide +kernel)

/-! ### World elimination

"Didn't stop smoking" is literally false at wTF, concentrating L1 on wTT. -/

/-- now=T dominates now=F among past=T worlds. -/
theorem wTT_gt_wTF :
    l1World .now .notStoppedSmoking .wTF <
    l1World .now .notStoppedSmoking .wTT :=
  PMF.ofScores_lt _ (by decide +kernel)

/-! ### Projection under QUD_max (Figure 1c)

The identity QUD breaks the QUD_now degeneracy — under +past, "didn't stop"
narrows to exactly wTT — but projection stays incomplete: wTT = wFF, so
the past marginals still coincide. -/

/-- Projection under QUD_max: wTT > wFT. -/
theorem projection_under_qud_max :
    l1World .max .notStoppedSmoking .wFT <
    l1World .max .notStoppedSmoking .wTT :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- Incomplete projection under QUD_max: wTT = wFF (Figure 1c). The
involution (past, now) ↦ (¬now, ¬past) fixes ⟦didn't stop⟧ and permutes the
context sets prior-preservingly, so world marginals cannot fully register
the presupposition. -/
theorem qud_max_incomplete_projection :
    l1World .max .notStoppedSmoking .wTT =
    l1World .max .notStoppedSmoking .wFF :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-! ### Context set projection (the paper's main result, Figure 3)

Under +past, "didn't stop" narrows L0 to wTT (aggregate 1, `1⁶ = 1`); under
−past it spreads (`(1/2)⁶ = 1/64`). S1 rewards informativity, so L1 infers
the speaker assumed a +past common ground — projection as context-set
inference, with (wTT, +past) the joint mode (Figure 3). -/

/-- The headline: L1 infers a +past context set over −past. -/
theorem context_projection :
    l1Ctx .now .notStoppedSmoking .pastFalse <
    l1Ctx .now .notStoppedSmoking .pastTrue :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- +past beats `universe` despite the prior (6 vs 9): "didn't stop" narrows
to wTT under +past (`1⁶ = 1`) but spreads over three worlds under `universe`
(`(1/4)⁶`). -/
theorem context_projection_over_universe :
    l1Ctx .now .notStoppedSmoking .universe <
    l1Ctx .now .notStoppedSmoking .pastTrue :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- −now contexts are dispreferred (p. 1114): −now already entails the QUD
answer, so "didn't stop smoking" adds nothing there. -/
theorem now_context_dispreferred :
    l1Ctx .now .notStoppedSmoking .nowFalse <
    l1Ctx .now .notStoppedSmoking .pastTrue :=
  PMF.ofScores_lt _ (by decide +kernel)

/-! ### "Stopped smoking" -/

/-- "Stopped smoking" → L1 infers now=F (the assertion). -/
theorem stopped_qud_answer :
    l1WorldEvent .now .stoppedSmoking (·.now) <
    l1WorldEvent .now .stoppedSmoking (fun w => !w.now) :=
  PMF.ofScores_event_lt _ _ (by decide +kernel)

/-! ### Structural properties -/

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

end QingGoodmanLassiter2016
