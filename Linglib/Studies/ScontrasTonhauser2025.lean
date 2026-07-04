import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.BToM
import Linglib.Semantics.Attitudes.Factivity
import Linglib.Studies.DegenTonhauser2021
import Linglib.Semantics.Presupposition.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# [scontras-tonhauser-2025]: projection without lexical presupposition

An RSA model of *know* under negation (SuB 29, pp. 1431–1448): the pragmatic
listener jointly infers the world state and the speaker's private assumptions
(eq. 7), the speaker scores QUD-projected informativity (eq. 6, α = 10, fn.
12), and the literal listener answers the QUD within the assumption set
(eq. 5). Projection of the complement C emerges with no lexically-specified
constraint on the common ground. Domain: 6 utterances × 4 worlds (BEL × C) ×
15 belief states × 2 QUDs; literal semantics from
`Semantics.Attitudes.Factivity` (know = `factivePos`, think =
`nonFactivePos`).

## Main results

* `bel_qud_marginal_eq_prior_high` / `_low`: under the BEL? QUD the world
  C-marginal *equals the prior* for every utterance — S1 depends on the
  world only through its BEL-cell, so projection is invisible there.
* `prediction_2b`: higher prior ⇒ stronger projection (C? QUD), the effect
  [degen-tonhauser-2021] documents across 20 predicates (Exp 1: β = 0.16,
  p < .001).
* `prediction_2c`: BEL? QUD ⇒ stronger projection than C? QUD (Exp 2:
  β = 0.14, p < .001).
* `c_qud_thinkNeg_higher`: under C?, negated *know* is evidence against C.
* `model_predicts_effects`: the model directions match the regressions.

## Implementation notes

α = 10 is a natural power, so the model is computed in exact ℚ (`l0Q` …
`wTotalQ`); listeners are `PMF.normalize` of those scores bridged by
`ENNReal.ofReal_sum_of_nonneg`, and every prediction is a kernel-verified
rational comparison. Degenerate cells (no compatible utterance) fall back to
`pure .cPos` on both faces, keeping the bridge total.

Utterance cost (§3.1: complex = 2 × simple) is omitted: `exp(−αC)` is
transcendental, and the omission reverses prediction (2a)'s world-marginal
direction (the paper derives know > think *with* cost, Figure 7a);
predictions (2b) and (2c) are robust to it. Prior parameters follow §3.1:
P(C) ∈ {2/3, 1/3}, P(BEL | C) = 1/2, uniform over the 15 assumption sets.

## TODO

Model the cost term (log-rational costs keep ℚ exactness) and derive
prediction (2a)'s world-marginal direction. Prove the structural equivalence
with [qing-goodman-lassiter-2016] (fn. 10: "private assumptions" vs "common
ground" is interpretive, not computational) — see the matching TODO in
`QingGoodmanLassiter2016.lean`.
-/

namespace ScontrasTonhauser2025

open BigOperators
open Semantics.Attitudes.Factivity

/-! ### Worlds and utterances -/

/-- World state: (BEL, C) where BEL = Cole believes C, C = complement is true.
    Flat inductive for tactic enumerability. -/
inductive WorldState where
  | w11  -- (BEL=1, C=1): Cole believes C and C is true
  | w10  -- (BEL=1, C=0): Cole believes C but C is false
  | w01  -- (BEL=0, C=1): Cole doesn't believe but C is true
  | w00  -- (BEL=0, C=0): Cole doesn't believe and C is false
  deriving DecidableEq, Repr, Inhabited, Fintype

def WorldState.bel : WorldState → Bool
  | .w11 | .w10 => true
  | .w01 | .w00 => false

def WorldState.c : WorldState → Bool
  | .w11 | .w01 => true
  | .w10 | .w00 => false

instance : HasComplement WorldState where c := WorldState.c
instance : HasBelief WorldState where bel := WorldState.bel

/-- Attitude verb utterances about Cole's mental state, plus bare
    complement assertions. -/
inductive Utterance where
  | knowPos     -- "Cole knows that C"
  | knowNeg     -- "Cole doesn't know that C"
  | thinkPos    -- "Cole thinks that C"
  | thinkNeg    -- "Cole doesn't think that C"
  | cPos        -- "C"
  | cNeg        -- "not C"
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := {.knowPos, .knowNeg, .thinkPos, .thinkNeg, .cPos, .cNeg}
  complete := fun x => by cases x <;> simp

/-! ### Literal truth conditions (from `Factivity`) -/

/-- Literal truth conditions derived from factive/non-factive semantics.

    "know" is factive: `factivePos` = BEL ∧ C
    "think" is non-factive: `nonFactivePos` = BEL
    "C" / "not C" are direct assertions about the complement. -/
def literalMeaning : Utterance → WorldState → Bool
  | .knowPos  => factivePos
  | .knowNeg  => factiveNeg
  | .thinkPos => nonFactivePos
  | .thinkNeg => nonFactiveNeg
  | .cPos     => HasComplement.c
  | .cNeg     => fun w => !HasComplement.c w

/-! ### Speaker belief states (the 15 non-empty subsets of W) -/

/-- Speaker's private assumptions: all 15 non-empty subsets of W.
    Section 3 follows [qing-goodman-lassiter-2016]: A ranges over all
    non-empty subsets of the world space. -/
inductive BeliefState where
  -- Singletons (4)
  | onlyW11 | onlyW10 | onlyW01 | onlyW00
  -- Aligned pairs (4)
  | belTrue | belFalse | cTrue | cFalse
  -- Cross pairs (2)
  | diagonal | antiDiagonal
  -- Triples (4)
  | notW11 | notW10 | notW01 | notW00
  -- Full (1)
  | all
  deriving DecidableEq, Repr, Inhabited

instance : Fintype BeliefState where
  elems := {.onlyW11, .onlyW10, .onlyW01, .onlyW00,
            .belTrue, .belFalse, .cTrue, .cFalse,
            .diagonal, .antiDiagonal,
            .notW11, .notW10, .notW01, .notW00,
            .all}
  complete := fun x => by cases x <;> simp

/-- Membership in belief state. Boolean operations on `WorldState` fields
    reduce cleanly under kernel evaluation. -/
def speakerCredenceBool : BeliefState → WorldState → Bool
  | .all, _ => true
  | .onlyW11, w => w.bel && w.c
  | .onlyW10, w => w.bel && !w.c
  | .onlyW01, w => !w.bel && w.c
  | .onlyW00, w => !w.bel && !w.c
  | .belTrue, w => w.bel
  | .belFalse, w => !w.bel
  | .cTrue, w => w.c
  | .cFalse, w => !w.c
  | .diagonal, w => (w.bel && w.c) || (!w.bel && !w.c)
  | .antiDiagonal, w => (!w.bel && w.c) || (w.bel && !w.c)
  | .notW11, w => !(w.bel && w.c)
  | .notW10, w => !(w.bel && !w.c)
  | .notW01, w => !(!w.bel && w.c)
  | .notW00, w => !(!w.bel && !w.c)

/-- Whether C is true in all worlds of the belief state. -/
def assumesC : BeliefState → Bool
  | .onlyW11 | .onlyW01 | .cTrue => true
  | _ => false

/-! ### Priors -/

/-- World prior parameterized by P(C).
    P(BEL, C) = P(BEL | C) · P(C), with P(BEL | C) = 1/2. -/
def worldPriorQ (pC : ℚ) : WorldState → ℚ
  | .w11 | .w01 => pC / 2
  | .w10 | .w00 => (1 - pC) / 2

theorem worldPriorQ_nonneg (pC : ℚ) (h0 : 0 ≤ pC) (h1 : pC ≤ 1)
    (w : WorldState) : 0 ≤ worldPriorQ pC w := by
  cases w <;> simp [worldPriorQ] <;> linarith

/-- World prior sums to 1 for any P(C). -/
theorem worldPriorQ_sum (pC : ℚ) :
    worldPriorQ pC .w11 + worldPriorQ pC .w10 +
    worldPriorQ pC .w01 + worldPriorQ pC .w00 = 1 := by
  simp [worldPriorQ]; ring

/-! ### The exact-ℚ model and its PMF face (local pending the RSA API pass) -/

section QModel

/-- Literal-listener mass (eq. 5's normaliser): prior mass of worlds in the
assumption set where `u` is true. -/
def l0MassQ (pC : ℚ) (bs : BeliefState) (u : Utterance) : ℚ :=
  ∑ w, (if speakerCredenceBool bs w && literalMeaning u w then worldPriorQ pC w else 0)

/-- Literal listener value (division by zero yields 0). -/
def l0Q (pC : ℚ) (bs : BeliefState) (u : Utterance) (w : WorldState) : ℚ :=
  (if speakerCredenceBool bs w && literalMeaning u w then worldPriorQ pC w else 0) /
    l0MassQ pC bs u

/-- QUD aggregation of the literal listener (eq. 5). -/
def qAggQ (qud : QUD) (pC : ℚ) (bs : BeliefState) (u : Utterance) : WorldState → ℚ
  | .w11 => match qud with
    | .bel => l0Q pC bs u .w11 + l0Q pC bs u .w10
    | .c   => l0Q pC bs u .w11 + l0Q pC bs u .w01
  | .w10 => match qud with
    | .bel => l0Q pC bs u .w11 + l0Q pC bs u .w10
    | .c   => l0Q pC bs u .w10 + l0Q pC bs u .w00
  | .w01 => match qud with
    | .bel => l0Q pC bs u .w01 + l0Q pC bs u .w00
    | .c   => l0Q pC bs u .w11 + l0Q pC bs u .w01
  | .w00 => match qud with
    | .bel => l0Q pC bs u .w01 + l0Q pC bs u .w00
    | .c   => l0Q pC bs u .w10 + l0Q pC bs u .w00

/-- Speaker weight (eq. 6 at α = 10, zero cost). -/
def s1WeightQ (qud : QUD) (pC : ℚ) (bs : BeliefState) (w : WorldState)
    (u : Utterance) : ℚ :=
  (qAggQ qud pC bs u w) ^ 10

def s1ZQ (qud : QUD) (pC : ℚ) (bs : BeliefState) (w : WorldState) : ℚ :=
  ∑ u, s1WeightQ qud pC bs w u

/-- Normalized speaker value, with the degenerate-cell fallback matching the
PMF face (`pure .cPos` where no utterance carries weight). -/
def s1ValQ (qud : QUD) (pC : ℚ) (bs : BeliefState) (w : WorldState)
    (u : Utterance) : ℚ :=
  if s1ZQ qud pC bs w = 0 then (if u = .cPos then 1 else 0)
  else s1WeightQ qud pC bs w u / s1ZQ qud pC bs w

/-- Listener world score (eq. 7; uniform assumption prior). -/
def worldScoreQ (qud : QUD) (pC : ℚ) (u : Utterance) (w : WorldState) : ℚ :=
  worldPriorQ pC w * ∑ bs, s1ValQ qud pC bs w u

/-- C-event mass and total of the listener scores. -/
def cEventQ (qud : QUD) (pC : ℚ) (u : Utterance) : ℚ :=
  ∑ w, (if w.c then worldScoreQ qud pC u w else 0)

def wTotalQ (qud : QUD) (pC : ℚ) (u : Utterance) : ℚ :=
  ∑ w, worldScoreQ qud pC u w

end QModel

section QModel

theorem worldPriorQ_nonneg' {pC : ℚ} (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (w : WorldState) :
    0 ≤ worldPriorQ pC w := worldPriorQ_nonneg pC h0 h1 w

variable {pC : ℚ}

theorem l0MassQ_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (bs : BeliefState) (u : Utterance) :
    0 ≤ l0MassQ pC bs u :=
  Finset.sum_nonneg fun w _ => by
    split
    · exact worldPriorQ_nonneg pC h0 h1 w
    · exact le_refl 0

theorem l0Q_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (bs : BeliefState) (u : Utterance)
    (w : WorldState) : 0 ≤ l0Q pC bs u w :=
  div_nonneg (by
    split
    · exact worldPriorQ_nonneg pC h0 h1 w
    · exact le_refl 0) (l0MassQ_nonneg h0 h1 bs u)

theorem qAggQ_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (bs : BeliefState)
    (u : Utterance) (w : WorldState) : 0 ≤ qAggQ qud pC bs u w := by
  cases w <;> cases qud <;>
    exact add_nonneg (l0Q_nonneg h0 h1 bs u _) (l0Q_nonneg h0 h1 bs u _)

theorem s1WeightQ_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (bs : BeliefState)
    (w : WorldState) (u : Utterance) : 0 ≤ s1WeightQ qud pC bs w u :=
  pow_nonneg (qAggQ_nonneg h0 h1 qud bs u w) 10

theorem s1ZQ_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (bs : BeliefState)
    (w : WorldState) : 0 ≤ s1ZQ qud pC bs w :=
  Finset.sum_nonneg fun u _ => s1WeightQ_nonneg h0 h1 qud bs w u

theorem s1ValQ_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (bs : BeliefState)
    (w : WorldState) (u : Utterance) : 0 ≤ s1ValQ qud pC bs w u := by
  unfold s1ValQ
  split
  · split <;> norm_num
  · exact div_nonneg (s1WeightQ_nonneg h0 h1 qud bs w u) (s1ZQ_nonneg h0 h1 qud bs w)

theorem worldScoreQ_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (u : Utterance)
    (w : WorldState) : 0 ≤ worldScoreQ qud pC u w :=
  mul_nonneg (worldPriorQ_nonneg pC h0 h1 w)
    (Finset.sum_nonneg fun bs _ => s1ValQ_nonneg h0 h1 qud bs w u)

theorem wTotalQ_nonneg (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (u : Utterance) :
    0 ≤ wTotalQ qud pC u :=
  Finset.sum_nonneg fun w _ => worldScoreQ_nonneg h0 h1 qud u w

end QModel

section PMFFace

open scoped ENNReal

private theorem sumUtts (f : Utterance → ℝ≥0∞) :
    ∑' u, f u = f .knowPos + f .knowNeg + f .thinkPos + f .thinkNeg +
      f .cPos + f .cNeg := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Utterance)
      = {.knowPos, .knowNeg, .thinkPos, .thinkNeg, .cPos, .cNeg} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem sumBS (f : BeliefState → ℝ≥0∞) :
    ∑' bs, f bs = f .onlyW11 + f .onlyW10 + f .onlyW01 + f .onlyW00 +
      f .belTrue + f .belFalse + f .cTrue + f .cFalse +
      f .diagonal + f .antiDiagonal +
      f .notW11 + f .notW10 + f .notW01 + f .notW00 + f .all := by
  rw [tsum_fintype,
    show (Finset.univ : Finset BeliefState)
      = {.onlyW11, .onlyW10, .onlyW01, .onlyW00, .belTrue, .belFalse, .cTrue,
         .cFalse, .diagonal, .antiDiagonal, .notW11, .notW10, .notW01,
         .notW00, .all} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  ring

private theorem sumWs (f : WorldState → ℝ≥0∞) :
    ∑' w, f w = f .w11 + f .w10 + f .w01 + f .w00 := by
  rw [tsum_fintype,
    show (Finset.univ : Finset WorldState) = {.w11, .w10, .w01, .w00} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

variable {pC : ℚ}

/-- PMF speaker (eq. 6 at α = 10, zero cost), dite-total. -/
noncomputable def s1PMF (qud : QUD) (pC : ℚ) (bs : BeliefState) (w : WorldState) :
    PMF Utterance :=
  if h : (∑' u, ENNReal.ofReal ((s1WeightQ qud pC bs w u : ℝ))) ≠ 0 then
    PMF.normalize (fun u => ENNReal.ofReal ((s1WeightQ qud pC bs w u : ℝ))) h
      (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)
  else PMF.pure .cPos

private theorem sumW_eq (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (bs : BeliefState)
    (w : WorldState) :
    (∑' u, ENNReal.ofReal ((s1WeightQ qud pC bs w u : ℝ)))
      = ENNReal.ofReal ((s1ZQ qud pC bs w : ℝ)) := by
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
    (fun u _ => by exact_mod_cast s1WeightQ_nonneg h0 h1 qud bs w u)]
  congr 1
  push_cast [s1ZQ]
  rfl

theorem s1PMF_apply (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (bs : BeliefState)
    (w : WorldState) (u : Utterance) :
    s1PMF qud pC bs w u = ENNReal.ofReal ((s1ValQ qud pC bs w u : ℝ)) := by
  unfold s1PMF
  by_cases hZ : (0 : ℚ) < s1ZQ qud pC bs w
  · rw [dif_pos (by rw [sumW_eq h0 h1, ENNReal.ofReal_ne_zero_iff]; exact_mod_cast hZ),
      PMF.normalize_apply, sumW_eq h0 h1,
      ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hZ),
      ← ENNReal.ofReal_mul (by exact_mod_cast s1WeightQ_nonneg h0 h1 qud bs w u),
      show s1ValQ qud pC bs w u = s1WeightQ qud pC bs w u / s1ZQ qud pC bs w from by
        rw [s1ValQ, if_neg hZ.ne']]
    congr 1
    push_cast
    rw [div_eq_mul_inv]
  · have hZ0 : s1ZQ qud pC bs w = 0 :=
      le_antisymm (not_lt.mp hZ) (s1ZQ_nonneg h0 h1 qud bs w)
    rw [dif_neg (by rw [sumW_eq h0 h1, hZ0]; simp),
      show s1ValQ qud pC bs w u = (if u = .cPos then 1 else 0) from by
        rw [s1ValQ, if_pos hZ0]]
    by_cases hu : u = .cPos <;> simp [PMF.pure_apply, hu]

/-- Listener world score (eq. 7; uniform assumption prior factors out). -/
noncomputable def wScore (qud : QUD) (pC : ℚ) (u : Utterance) (w : WorldState) :
    ℝ≥0∞ :=
  ENNReal.ofReal ((worldPriorQ pC w : ℝ)) * ∑' bs, s1PMF qud pC bs w u

theorem wScore_eq (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (u : Utterance)
    (w : WorldState) :
    wScore qud pC u w = ENNReal.ofReal ((worldScoreQ qud pC u w : ℝ)) := by
  unfold wScore
  rw [tsum_fintype,
    Finset.sum_congr rfl (fun bs _ => s1PMF_apply h0 h1 qud bs w u),
    ← ENNReal.ofReal_sum_of_nonneg (fun bs _ => by
      exact_mod_cast s1ValQ_nonneg h0 h1 qud bs w u),
    ← ENNReal.ofReal_mul (by exact_mod_cast worldPriorQ_nonneg pC h0 h1 w)]
  congr 1
  push_cast [worldScoreQ]
  rfl

private theorem sumScore_eq (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD) (u : Utterance) :
    (∑' w, wScore qud pC u w) = ENNReal.ofReal ((wTotalQ qud pC u : ℝ)) := by
  rw [tsum_fintype, Finset.sum_congr rfl (fun w _ => wScore_eq h0 h1 qud u w),
    ← ENNReal.ofReal_sum_of_nonneg (fun w _ => by
      exact_mod_cast worldScoreQ_nonneg h0 h1 qud u w)]
  congr 1
  push_cast [wTotalQ]
  rfl

/-- Pragmatic listener over worlds (eq. 7), dite-total. -/
noncomputable def l1World (qud : QUD) (pC : ℚ) (u : Utterance) : PMF WorldState :=
  if h : (∑' w, wScore qud pC u w) ≠ 0 then
    PMF.normalize (wScore qud pC u) h
      (ENNReal.tsum_ne_top_of_fintype fun _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.tsum_ne_top_of_fintype fun _ => PMF.apply_ne_top _ _))
  else PMF.uniformOfFintype WorldState

private theorem l1World_apply (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD)
    (u : Utterance) (hpos : (∑' w, wScore qud pC u w) ≠ 0)
    (w : WorldState) :
    l1World qud pC u w
      = ENNReal.ofReal ((worldScoreQ qud pC u w : ℝ)) *
        (∑' w', wScore qud pC u w')⁻¹ := by
  unfold l1World
  rw [dif_pos hpos, PMF.normalize_apply, wScore_eq h0 h1 qud u w]

/-- The listener's C-marginal. -/
noncomputable def l1CEvent (qud : QUD) (pC : ℚ) (u : Utterance) : ℝ≥0∞ :=
  ∑' w, if w.c then l1World qud pC u w else 0

private theorem cEventQ_expand (qud : QUD) (u : Utterance) :
    cEventQ qud pC u = worldScoreQ qud pC u .w11 + worldScoreQ qud pC u .w01 := by
  rw [cEventQ, show (Finset.univ : Finset WorldState) = {.w11, .w10, .w01, .w00}
      from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp +decide

private theorem l1CEvent_eq (h0 : 0 ≤ pC) (h1 : pC ≤ 1) (qud : QUD)
    (u : Utterance) (hpos : (∑' w, wScore qud pC u w) ≠ 0) :
    l1CEvent qud pC u
      = ENNReal.ofReal ((cEventQ qud pC u : ℝ)) *
        (ENNReal.ofReal ((wTotalQ qud pC u : ℝ)))⁻¹ := by
  unfold l1CEvent
  rw [sumWs]
  simp +decide only [if_true, if_false, add_zero]
  simp only [l1World_apply h0 h1 qud u hpos]
  rw [← add_mul, ← ENNReal.ofReal_add
      (by exact_mod_cast worldScoreQ_nonneg h0 h1 qud u _)
      (by exact_mod_cast worldScoreQ_nonneg h0 h1 qud u _),
    sumScore_eq h0 h1 qud u, cEventQ_expand]
  congr 2
  push_cast
  rfl

/-- Division form for the marginal identities. -/
private theorem ofReal_mul_inv_eq {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    ENNReal.ofReal (c * b) * (ENNReal.ofReal b)⁻¹ = ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul hc, mul_assoc,
    ENNReal.mul_inv_cancel (by rw [ENNReal.ofReal_ne_zero_iff]; exact hb)
      ENNReal.ofReal_ne_top, mul_one]

/-- Cross-normaliser comparison for the strict predictions. -/
private theorem ofReal_div_lt {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hc : 0 < c) (h : a * d < c * b) :
    ENNReal.ofReal a * (ENNReal.ofReal b)⁻¹ <
      ENNReal.ofReal c * (ENNReal.ofReal d)⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hb,
    ← ENNReal.ofReal_div_of_pos hd]
  exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hc hd)).mpr
    ((div_lt_div_iff₀ hb hd).mpr h)

end PMFFace

section KernelFacts

/-! The model's arithmetic content, kernel-verified over the exact-ℚ scores. -/

private theorem belHigh_pos : ∀ u, (0:ℚ) < wTotalQ .bel (2/3) u := by decide +kernel

private theorem belLow_pos : ∀ u, (0:ℚ) < wTotalQ .bel (1/3) u := by decide +kernel

private theorem cHigh_pos : ∀ u, (0:ℚ) < wTotalQ .c (2/3) u := by decide +kernel

private theorem cLow_pos : ∀ u, (0:ℚ) < wTotalQ .c (1/3) u := by decide +kernel

private theorem belHigh_id :
    ∀ u, cEventQ .bel (2/3) u = 2/3 * wTotalQ .bel (2/3) u := by decide +kernel

private theorem belLow_id :
    ∀ u, cEventQ .bel (1/3) u = 1/3 * wTotalQ .bel (1/3) u := by decide +kernel

private theorem cHigh_thinkNeg_pos : (0:ℚ) < cEventQ .c (2/3) .thinkNeg := by
  decide +kernel

private theorem cHigh_knowNeg_pos : (0:ℚ) < cEventQ .c (2/3) .knowNeg := by
  decide +kernel

private theorem belHigh_knowNeg_pos : (0:ℚ) < cEventQ .bel (2/3) .knowNeg := by
  decide +kernel

private theorem cqud_cross :
    cEventQ .c (2/3) .knowNeg * wTotalQ .c (2/3) .thinkNeg <
    cEventQ .c (2/3) .thinkNeg * wTotalQ .c (2/3) .knowNeg := by decide +kernel

private theorem prior_cross :
    cEventQ .c (1/3) .knowNeg * wTotalQ .c (2/3) .knowNeg <
    cEventQ .c (2/3) .knowNeg * wTotalQ .c (1/3) .knowNeg := by decide +kernel

private theorem qud_cross :
    cEventQ .c (2/3) .knowNeg * wTotalQ .bel (2/3) .knowNeg <
    cEventQ .bel (2/3) .knowNeg * wTotalQ .c (2/3) .knowNeg := by decide +kernel

end KernelFacts

section PMFFace

open scoped ENNReal

private theorem wZpos_belHigh (u : Utterance) :
    (∑' w, wScore .bel (2/3) u w) ≠ 0 := by
  rw [sumScore_eq (by norm_num) (by norm_num) .bel u, ENNReal.ofReal_ne_zero_iff]
  exact_mod_cast belHigh_pos u

private theorem wZpos_belLow (u : Utterance) :
    (∑' w, wScore .bel (1/3) u w) ≠ 0 := by
  rw [sumScore_eq (by norm_num) (by norm_num) .bel u, ENNReal.ofReal_ne_zero_iff]
  exact_mod_cast belLow_pos u

private theorem wZpos_cHigh (u : Utterance) :
    (∑' w, wScore .c (2/3) u w) ≠ 0 := by
  rw [sumScore_eq (by norm_num) (by norm_num) .c u, ENNReal.ofReal_ne_zero_iff]
  exact_mod_cast cHigh_pos u

private theorem wZpos_cLow (u : Utterance) :
    (∑' w, wScore .c (1/3) u w) ≠ 0 := by
  rw [sumScore_eq (by norm_num) (by norm_num) .c u, ENNReal.ofReal_ne_zero_iff]
  exact_mod_cast cLow_pos u

end PMFFace

/-! ### Listener predictions -/

open scoped ENNReal in
/-- Under the BEL? QUD the C-marginal equals the prior, for every utterance:
S1 depends on the world only through its BEL-cell, so the C-dimension washes
out of the world posterior. Projection is invisible at the world marginal. -/
theorem bel_qud_marginal_eq_prior_high (u : Utterance) :
    l1CEvent .bel (2/3) u = ENNReal.ofReal (2/3) := by
  rw [l1CEvent_eq (by norm_num) (by norm_num) .bel u (wZpos_belHigh u),
    show ((cEventQ .bel (2/3) u : ℝ)) = 2/3 * ((wTotalQ .bel (2/3) u : ℝ)) from by
      rw [belHigh_id u]; push_cast; ring]
  exact ofReal_mul_inv_eq (by exact_mod_cast belHigh_pos u) (by norm_num)

open scoped ENNReal in
/-- The low-prior analogue of `bel_qud_marginal_eq_prior_high`. -/
theorem bel_qud_marginal_eq_prior_low (u : Utterance) :
    l1CEvent .bel (1/3) u = ENNReal.ofReal (1/3) := by
  rw [l1CEvent_eq (by norm_num) (by norm_num) .bel u (wZpos_belLow u),
    show ((cEventQ .bel (1/3) u : ℝ)) = 1/3 * ((wTotalQ .bel (1/3) u : ℝ)) from by
      rw [belLow_id u]; push_cast; ring]
  exact ofReal_mul_inv_eq (by exact_mod_cast belLow_pos u) (by norm_num)

open scoped ENNReal in
/-- Under the C? QUD, knowNeg is evidence against C — ¬(BEL∧C) is compatible
with C-false worlds — so thinkNeg preserves P(C) better. -/
theorem c_qud_thinkNeg_higher :
    l1CEvent .c (2/3) .thinkNeg > l1CEvent .c (2/3) .knowNeg := by
  rw [gt_iff_lt, l1CEvent_eq (by norm_num) (by norm_num) .c _ (wZpos_cHigh _),
    l1CEvent_eq (by norm_num) (by norm_num) .c _ (wZpos_cHigh _)]
  exact ofReal_div_lt (by exact_mod_cast cHigh_pos .knowNeg)
    (by exact_mod_cast cHigh_pos .thinkNeg)
    (by exact_mod_cast cHigh_thinkNeg_pos)
    (by exact_mod_cast cqud_cross)

/-! ### Prediction 2a: utterance effect (know > think)

The paper derives 2a *with* utterance cost (Figure 7a); the cost-free model
does not — under BEL? both marginals sit at the prior, and under C? the
direction reverses (`c_qud_thinkNeg_higher`). Fn. 11's A-marginal measure
(P(A ⊧ C | u)) may capture the effect without cost; see the module TODO. -/

open scoped ENNReal in
/-- Prediction 2b (prior effect): higher prior increases projection. -/
theorem prediction_2b :
    l1CEvent .c (2/3) .knowNeg > l1CEvent .c (1/3) .knowNeg := by
  rw [gt_iff_lt, l1CEvent_eq (by norm_num) (by norm_num) .c _ (wZpos_cLow _),
    l1CEvent_eq (by norm_num) (by norm_num) .c _ (wZpos_cHigh _)]
  exact ofReal_div_lt (by exact_mod_cast cLow_pos .knowNeg)
    (by exact_mod_cast cHigh_pos .knowNeg)
    (by exact_mod_cast cHigh_knowNeg_pos)
    (by exact_mod_cast prior_cross)

open scoped ENNReal in
/-- Prediction 2c (QUD effect): under BEL? the C-marginal stays at the prior
(`bel_qud_marginal_eq_prior_high`), while under C? the literal semantics of
"doesn't know C" lowers it. -/
theorem prediction_2c :
    l1CEvent .bel (2/3) .knowNeg > l1CEvent .c (2/3) .knowNeg := by
  rw [gt_iff_lt, l1CEvent_eq (by norm_num) (by norm_num) .c _ (wZpos_cHigh _),
    l1CEvent_eq (by norm_num) (by norm_num) .bel _ (wZpos_belHigh _)]
  exact ofReal_div_lt (by exact_mod_cast cHigh_pos .knowNeg)
    (by exact_mod_cast belHigh_pos .knowNeg)
    (by exact_mod_cast belHigh_knowNeg_pos)
    (by exact_mod_cast qud_cross)

/-! ### Structural properties -/

/-- "know" entails C (from `factivePos_entails_c`). -/
theorem know_entails_c : ∀ w, literalMeaning .knowPos w = true → w.c = true :=
  factivePos_entails_c

/-- "think" does NOT entail C. -/
theorem think_not_entails_c :
    ∃ w, literalMeaning .thinkPos w = true ∧ w.c = false :=
  ⟨.w10, rfl, rfl⟩

/-- "know" entails BEL (from `factivePos_entails_bel`). -/
theorem know_entails_bel : ∀ w, literalMeaning .knowPos w = true → w.bel = true :=
  factivePos_entails_bel

/-- Know entails think (factivity is strictly stronger than belief). -/
theorem know_entails_think : ∀ w,
    literalMeaning .knowPos w = true → literalMeaning .thinkPos w = true :=
  factive_entails_nonfactive

/-- knowNeg (= ¬(BEL∧C)) is true at all worlds except w11. -/
theorem knowNeg_semantics :
    literalMeaning .knowNeg .w11 = false ∧
    literalMeaning .knowNeg .w10 = true ∧
    literalMeaning .knowNeg .w01 = true ∧
    literalMeaning .knowNeg .w00 = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- thinkNeg (= ¬BEL) is true only at worlds where Cole doesn't believe. -/
theorem thinkNeg_semantics :
    literalMeaning .thinkNeg .w11 = false ∧
    literalMeaning .thinkNeg .w10 = false ∧
    literalMeaning .thinkNeg .w01 = true ∧
    literalMeaning .thinkNeg .w00 = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- knowNeg is compatible with strictly more worlds than thinkNeg (3 vs 2),
    making it the weaker (less informative) negation. -/
theorem knowNeg_weaker_than_thinkNeg :
    (Finset.univ.filter (fun w : WorldState => literalMeaning .knowNeg w)).card >
    (Finset.univ.filter (fun w : WorldState => literalMeaning .thinkNeg w)).card := by
  decide

/-- The pattern-matched `assumesC` agrees with the generic
    `assumesComplement` from `Factivity`. -/
theorem assumesC_matches_generic : ∀ bs : BeliefState,
    assumesC bs = assumesComplement (speakerCredenceBool bs)
      [.w11, .w10, .w01, .w00] := by
  intro bs; cases bs <;> decide

/-- Exactly 3 of 15 belief states assume C: onlyW11, onlyW01, cTrue. -/
theorem three_of_fifteen_assume_c :
    (Finset.univ.filter (fun bs : BeliefState => assumesC bs)).card = 3 := by
  decide

/-! ### Experimental data -/

/-- Effect size from a linear mixed-effects model. p values are upper bounds
    (paper reports "< .001"). -/
structure UtteranceEffect where
  β : ℚ
  se : ℚ
  t : ℚ
  p : ℚ
  deriving Repr

/-- Exp 1: Utterance effect (know > think). -/
def exp1_utteranceEffect : UtteranceEffect :=
  { β := 0.35, se := 0.03, t := 12.2, p := 0.001 }

/-- Exp 1: Prior effect (higher > lower). -/
def exp1_priorEffect : UtteranceEffect :=
  { β := 0.16, se := 0.03, t := 5.5, p := 0.001 }

/-- Exp 1: QUD effect (NOT significant — manipulation too weak). -/
def exp1_qudEffect : UtteranceEffect :=
  { β := 0.009, se := 0.03, t := 0.3, p := 0.75 }

/-- Exp 2: Utterance effect (know > think). -/
def exp2_utteranceEffect : UtteranceEffect :=
  { β := 0.34, se := 0.04, t := 8.8, p := 0.001 }

/-- Exp 2: QUD effect (significant with stronger manipulation). -/
def exp2_qudEffect : UtteranceEffect :=
  { β := 0.14, se := 0.04, t := 3.6, p := 0.001 }

inductive Hypothesis where
  | utterance  -- (2a) know > think
  | prior      -- (2b) higher > lower prior
  | qud        -- (2c) BEL? > C?
  deriving DecidableEq, Repr

/-- Which experiments support each hypothesis.
    Exp 1: (2a) yes, (2b) yes, (2c) no (QUD not significant).
    Exp 2: (2a) yes, (2b) not tested, (2c) yes. -/
def supported : Hypothesis → Bool × Bool
  | .utterance => (true, true)
  | .prior     => (true, false)
  | .qud       => (false, true)

def directionCorrect : Hypothesis → Bool
  | .utterance => exp1_utteranceEffect.β > 0
  | .prior     => exp1_priorEffect.β > 0
  | .qud       => exp2_qudEffect.β > 0

/-! ### BToM bridge -/

open Core in
/-- Classification of BeliefState in BToM terms. -/
def beliefStateCategory : LatentCategory := .mental

open Core in
/-- Classification of QUD in BToM terms. -/
def qudCategory : LatentCategory := .shared

/-- Characteristic function: does the speaker assume C? -/
def assumesCIndicator : BeliefState → ℚ :=
  fun bs => if assumesC bs then 1 else 0

/-- Belief states that assume C have indicator 1. -/
theorem assumesCIndicator_pos (bs : BeliefState) (h : assumesC bs = true) :
    assumesCIndicator bs = 1 := by
  simp [assumesCIndicator, h]

/-- Belief states that don't assume C have indicator 0. -/
theorem assumesCIndicator_neg (bs : BeliefState) (h : assumesC bs = false) :
    assumesCIndicator bs = 0 := by
  simp [assumesCIndicator, h]

/-- The three C-entailing belief states have indicator 1;
    the remaining twelve have indicator 0. -/
theorem assumesCIndicator_classification :
    assumesCIndicator .onlyW11 = 1 ∧
    assumesCIndicator .onlyW01 = 1 ∧
    assumesCIndicator .cTrue = 1 ∧
    assumesCIndicator .onlyW10 = 0 ∧
    assumesCIndicator .onlyW00 = 0 ∧
    assumesCIndicator .belTrue = 0 ∧
    assumesCIndicator .belFalse = 0 ∧
    assumesCIndicator .cFalse = 0 ∧
    assumesCIndicator .diagonal = 0 ∧
    assumesCIndicator .antiDiagonal = 0 ∧
    assumesCIndicator .notW11 = 0 ∧
    assumesCIndicator .notW10 = 0 ∧
    assumesCIndicator .notW01 = 0 ∧
    assumesCIndicator .notW00 = 0 ∧
    assumesCIndicator .all = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Model–data connection -/

/-- Predictions (2b) and (2c) match experimental effect directions.
    Prediction (2a) requires cost; see the commentary above. -/
theorem model_predicts_effects :
    (l1CEvent .c (2/3) .knowNeg > l1CEvent .c (1/3) .knowNeg) ∧
    (l1CEvent .bel (2/3) .knowNeg > l1CEvent .c (2/3) .knowNeg) ∧
    directionCorrect .prior = true ∧
    directionCorrect .qud = true :=
  ⟨prediction_2b, prediction_2c,
   by simp only [directionCorrect, exp1_priorEffect, decide_eq_true_eq]; norm_num,
   by simp only [directionCorrect, exp2_qudEffect, decide_eq_true_eq]; norm_num⟩

/-! ### Connection to [degen-tonhauser-2021] -/

/-- The prior effect found by S&T 2025 (β = 0.16 > 0) replicates the positive
    prior effect of [degen-tonhauser-2021] (β = 0.14 categorical, β = 0.28
    individual): higher prior probability of the complement content leads to
    stronger projection. [degen-tonhauser-2021] makes this structural — any
    prior-sensitive (monotone) account predicts the modulation
    (`DegenTonhauser2021.sensitive_predicts_modulation`) — and the RSA model's
    `prediction_2b` provides the same explanation here. -/
theorem prior_effect_consistent_with_dt2021 :
    exp1_priorEffect.β > 0 := by norm_num [exp1_priorEffect]

/-! ### Compositional filtering vs BToM -/

/-! Compares the BToM model against compositional filtering ([heim-1983]):
presuppositions project through connectives via local context computation;
the filtering presupposition of "if A then B_p" is "A → p".

The key empirical argument: the BToM model predicts that even non-factive
"think" — which has NO presupposition to filter — exhibits projection
effects, because L1 can still infer what the speaker takes for granted.
Compositional filtering predicts a trivial presupposition for
non-presuppositional items. -/

section FilteringComparison

open Semantics.Presupposition

variable {W : Type*}

/-- The filtering prediction for "if A then know-C":
    the presupposition of the consequent (= C) is filtered by the antecedent.
    Result: conditional presupposes "A → C". -/
def filteringPrediction_know (a c : W → Prop) : PartialProp W :=
  PartialProp.impFilter (PartialProp.ofProp a) (PartialProp.condAssert c (fun _ => True))

/-- The filtering prediction for "if A then think-C":
    "think" has no presupposition, so filtering produces a trivial result. -/
def filteringPrediction_think (a : W → Prop) : PartialProp W :=
  PartialProp.impFilter (PartialProp.ofProp a) PartialProp.top

/-- **Filtering predicts non-trivial presupposition for "know"**:
    The presupposition of "if A then know-C" is ¬A ∨ C (= A → C),
    which is NOT tautological. -/
theorem filtering_know_nontrivial (a c : W → Prop)
    (h : ∃ w, a w ∧ ¬c w) :
    ∃ w, ¬(filteringPrediction_know a c).presup w := by
  obtain ⟨w, ha, hc⟩ := h
  refine ⟨w, ?_⟩
  simp only [filteringPrediction_know, PartialProp.impFilter, PartialProp.ofProp,
    PartialProp.condAssert, not_and]
  intro _
  exact fun h_imp => hc (h_imp ha)

/-- **Filtering predicts TRIVIAL presupposition for "think"**:
    The presupposition of "if A then think-C" is always true,
    regardless of A, because "think" contributes no presupposition. -/
theorem filtering_think_trivial (a : W → Prop) :
    ∀ w, (filteringPrediction_think a).presup w := by
  intro w
  simp only [filteringPrediction_think, PartialProp.impFilter, PartialProp.ofProp, PartialProp.top]
  exact ⟨trivial, fun _ => trivial⟩

/--
BToM predicts projection effects for ANY verb in conditional environments,
because projection arises from pragmatic reasoning about the speaker's
private assumptions, not from lexical presupposition.

The key mechanism: when A and C are related (correlated in the prior),
the listener infers that a speaker who utters "if A, X Vs C" likely takes
C for granted — regardless of whether V is factive.
-/
structure ProjectionPrediction where
  /-- Whether projection is predicted for factive verbs in conditionals. -/
  factive_projects : Bool
  /-- Whether projection is predicted for non-factive verbs in conditionals. -/
  nonFactive_projects : Bool
  /-- Whether relatedness modulates projection strength. -/
  relatedness_modulates : Bool

/-- BToM predictions: both factive and non-factive show conditional
    presupposition, modulated by relatedness. -/
def btomPrediction : ProjectionPrediction where
  factive_projects := true
  nonFactive_projects := true
  relatedness_modulates := true

/-- Filtering predictions: only factive shows conditional presupposition,
    with no role for relatedness (it's purely structural). -/
def filteringPrediction : ProjectionPrediction where
  factive_projects := true
  nonFactive_projects := false    -- Think has no presupposition
  relatedness_modulates := false  -- Filtering is structural, not probabilistic

/--
**Strict subsumption**: BToM predicts everything filtering predicts
(factive conditional presupposition) plus more (non-factive conditional
presupposition, relatedness modulation).
-/
theorem btom_subsumes_filtering :
    -- BToM agrees with filtering on factive projection
    btomPrediction.factive_projects = filteringPrediction.factive_projects ∧
    -- BToM predicts non-factive projection where filtering doesn't
    btomPrediction.nonFactive_projects = true ∧
    filteringPrediction.nonFactive_projects = false ∧
    -- BToM predicts relatedness modulation where filtering doesn't
    btomPrediction.relatedness_modulates = true ∧
    filteringPrediction.relatedness_modulates = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
**The critical divergence**: For non-factive "think" in conditionals,
filtering predicts trivial presupposition (no projection), while BToM
predicts non-trivial projection modulated by relatedness.

This is the [scontras-tonhauser-2025] argument: if projection were
due to compositional filtering alone, non-presuppositional items like
"think" should show no effect. But BToM predicts projection effects
even for "think", because L1 infers the speaker's private assumptions
regardless of the verb's factivity status.
-/
theorem critical_divergence_at_nonfactive :
    filteringPrediction.nonFactive_projects ≠ btomPrediction.nonFactive_projects := by
  decide

/--
**Filtering is a special case**: When relatedness is maximal (A entails C),
BToM's projection prediction converges to the filtering prediction.
Filtering captures the structural component; BToM adds the probabilistic
modulation.
-/
theorem filtering_is_limiting_case (a c : W → Prop)
    (h_entails : ∀ w, a w → c w) :
    ∀ w, (filteringPrediction_know a c).presup w := by
  intro w
  exact ⟨trivial, fun ha => h_entails w ha⟩

end FilteringComparison

end ScontrasTonhauser2025
