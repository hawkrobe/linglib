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

α = 6 is a natural power, so every layer is rational: scores are computed in
exact ℚ (`l0Q` … `ctxScoreQ`), listeners are `PMF.normalize` of those scores
(bridged by `ENNReal.ofReal_sum_of_nonneg`), and predictions are
kernel-verified rational comparisons (`decide +kernel`).

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
def utterancePrior : Utterance → ℚ
  | .smokes | .doesntSmoke | .smoked | .didntSmoke => 1/2
  | .alwaysSmoked | .notAlwaysSmoked
  | .stoppedSmoking | .notStoppedSmoking
  | .startedSmoking | .notStartedSmoking
  | .neverSmoked | .notNeverSmoked => 1/4
  | .silence => 1

theorem utterancePrior_nonneg (u : Utterance) : 0 ≤ utterancePrior u := by
  cases u <;> simp [utterancePrior]

/-- Context set prior (eq. 8):
`Pr(C) ∝ Σ_{CG ⊆ Obs} P(CG) · δ_{C = ∩CG}`.
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

/-! ### The exact-ℚ model and its PMF face (local pending the RSA API pass) -/

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

/-! ### Listener predictions -/

/-! ### QUD_now symmetry -/

/-- Under QUD_now, wTT and wFT are indistinguishable: `qAggQ .now` is
definitionally symmetric in the now-cell, so projection must be measured on
the context-set side (`l1Ctx`), not the world marginal. -/
theorem qud_now_wTT_eq_wFT :
    l1World .now .notStoppedSmoking .wTT =
    l1World .now .notStoppedSmoking .wFT := by
  rw [l1World_apply .now (by decide) wZ_pos_now_ns,
    l1World_apply .now (by decide) wZ_pos_now_ns]
  congr 2

/-! ### QUD answer -/

/-- L1 infers the QUD answer now=T from "didn't stop smoking". -/
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

/-! ### World elimination

"Didn't stop smoking" is literally false at wTF, concentrating L1 on wTT. -/

/-- now=T dominates now=F among past=T worlds. -/
theorem wTT_gt_wTF :
    l1World .now .notStoppedSmoking .wTT >
    l1World .now .notStoppedSmoking .wTF := by
  rw [gt_iff_lt, l1World_apply .now (by decide) wZ_pos_now_ns,
    l1World_apply .now (by decide) wZ_pos_now_ns]
  exact ofReal_mul_inv_lt wZ_pos_now_ns (wZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < worldScoreQ .now .notStoppedSmoking .wTT))
    (by exact_mod_cast (by decide +kernel :
      worldScoreQ .now .notStoppedSmoking .wTF < worldScoreQ .now .notStoppedSmoking .wTT))

/-! ### Projection under QUD_max (Figure 1c)

The identity QUD breaks the QUD_now degeneracy — under +past, "didn't stop"
narrows to exactly wTT — but projection stays incomplete: wTT = wFF, so
the past marginals still coincide. -/

/-- Projection under QUD_max: wTT > wFT. -/
theorem projection_under_qud_max :
    l1World .max .notStoppedSmoking .wTT >
    l1World .max .notStoppedSmoking .wFT := by
  rw [gt_iff_lt, l1World_apply .max (by decide) wZ_pos_max_ns,
    l1World_apply .max (by decide) wZ_pos_max_ns]
  exact ofReal_mul_inv_lt wZ_pos_max_ns (wZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < worldScoreQ .max .notStoppedSmoking .wTT))
    (by exact_mod_cast (by decide +kernel :
      worldScoreQ .max .notStoppedSmoking .wFT < worldScoreQ .max .notStoppedSmoking .wTT))

/-- Incomplete projection under QUD_max: wTT = wFF (Figure 1c). The
involution (past, now) ↦ (¬now, ¬past) fixes ⟦didn't stop⟧ and permutes the
context sets prior-preservingly, so world marginals cannot fully register
the presupposition. -/
theorem qud_max_incomplete_projection :
    l1World .max .notStoppedSmoking .wTT =
    l1World .max .notStoppedSmoking .wFF := by
  rw [l1World_apply .max (by decide) wZ_pos_max_ns,
    l1World_apply .max (by decide) wZ_pos_max_ns]
  congr 2
  exact_mod_cast (by decide +kernel :
    worldScoreQ .max .notStoppedSmoking .wTT
      = worldScoreQ .max .notStoppedSmoking .wFF)

/-! ### Context set projection (the paper's main result, Figure 3)

Under +past, "didn't stop" narrows L0 to wTT (aggregate 1, `1⁶ = 1`); under
−past it spreads (`(1/2)⁶ = 1/64`). S1 rewards informativity, so L1 infers
the speaker assumed a +past common ground — projection as context-set
inference, with (wTT, +past) the joint mode (Figure 3). -/

/-- The headline: L1 infers a +past context set over −past. -/
theorem context_projection :
    l1Ctx .now .notStoppedSmoking .pastTrue >
    l1Ctx .now .notStoppedSmoking .pastFalse := by
  rw [gt_iff_lt, l1Ctx_apply .now (by decide) cZ_pos_now_ns,
    l1Ctx_apply .now (by decide) cZ_pos_now_ns]
  exact ofReal_mul_inv_lt cZ_pos_now_ns (cZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < ctxScoreQ .now .notStoppedSmoking .pastTrue))
    (by exact_mod_cast (by decide +kernel :
      ctxScoreQ .now .notStoppedSmoking .pastFalse < ctxScoreQ .now .notStoppedSmoking .pastTrue))

/-- +past beats `universe` despite the prior (6 vs 9): "didn't stop" narrows
to wTT under +past (`1⁶ = 1`) but spreads over three worlds under `universe`
(`(1/4)⁶`). -/
theorem context_projection_over_universe :
    l1Ctx .now .notStoppedSmoking .pastTrue >
    l1Ctx .now .notStoppedSmoking .universe := by
  rw [gt_iff_lt, l1Ctx_apply .now (by decide) cZ_pos_now_ns,
    l1Ctx_apply .now (by decide) cZ_pos_now_ns]
  exact ofReal_mul_inv_lt cZ_pos_now_ns (cZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < ctxScoreQ .now .notStoppedSmoking .pastTrue))
    (by exact_mod_cast (by decide +kernel :
      ctxScoreQ .now .notStoppedSmoking .universe < ctxScoreQ .now .notStoppedSmoking .pastTrue))

/-- −now contexts are dispreferred (p. 1114): −now already entails the QUD
answer, so "didn't stop smoking" adds nothing there. -/
theorem now_context_dispreferred :
    l1Ctx .now .notStoppedSmoking .pastTrue >
    l1Ctx .now .notStoppedSmoking .nowFalse := by
  rw [gt_iff_lt, l1Ctx_apply .now (by decide) cZ_pos_now_ns,
    l1Ctx_apply .now (by decide) cZ_pos_now_ns]
  exact ofReal_mul_inv_lt cZ_pos_now_ns (cZ_fin _ _)
    (by exact_mod_cast (by decide +kernel : (0:ℚ) < ctxScoreQ .now .notStoppedSmoking .pastTrue))
    (by exact_mod_cast (by decide +kernel :
      ctxScoreQ .now .notStoppedSmoking .nowFalse < ctxScoreQ .now .notStoppedSmoking .pastTrue))

/-! ### "Stopped smoking" -/

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
