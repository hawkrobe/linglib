import Linglib.Fragments.German.Predicates
import Linglib.Fragments.German.Coordination
import Linglib.Fragments.German.V2
import Linglib.Fragments.German.Typology
import Linglib.Phenomena.WordOrder.Typology
import Linglib.Features.Coordination
import Linglib.Phenomena.Coordination.Studies.BrueningAlKhalaf2020
import Linglib.Features.V2

/-!
# @cite{schwarzer-2026} — Selection-Violating Coordination in German

Schwarzer, Luise. 2026. The law and order of selection-violating
coordination: German DP-CP-coordination is not sensitive to linear
or temporal order. *Glossa* 11(1). 1–19.

## Main Question

When a CP appears coordinated with a DP in a DP-selecting position
(selection-violating coordination), which conjunct must be the DP?
Three families of analyses make different predictions:

1. **Bottom-up** (@cite{sag-etal-1985}, @cite{munn-1993}): asymmetric &P
   structure; the structurally prominent (first) conjunct must be the
   selected DP. Predicts DP-first universally.

2. **Linear closeness** (@cite{bruening-alkhalaf-2020}, @cite{bruening-2025}):
   left-to-right derivation; the linearly closest conjunct to the verb
   must satisfy selection. Predicts the preferred order depends on
   whether complements precede or follow the verb.

3. **Temporal closeness** (@cite{kim-lu-2024}): processing illusion;
   the temporally closest conjunct to the verb has its features checked.
   Makes the same predictions as linear closeness.

## German as Test Case

German is OV in embedded clauses: complements precede the selecting
verb. The linear/temporal accounts predict that in OV order, the
*rightmost* (verb-adjacent) conjunct should be the DP, i.e., CP-first
order should be preferred. The bottom-up account predicts DP-first
regardless.

## Results

Two experiments show German speakers uniformly prefer DP-first order
(~77% in 2AFC) regardless of pre- or post-verbal position. This rules
out linear/temporal closeness accounts and supports bottom-up analyses.
-/

namespace Schwarzer2026

open Features.Coordination
open Core.Verbs (ComplementType VerbCore)
open Fragments.German.Predicates
open Phenomena.WordOrder.Typology
open BrueningAlKhalaf2020

-- ============================================================================
-- § 1: German Clause Type → Complement Position
-- ============================================================================

/-!
The paper's two experimental conditions correspond to different German
clause types with different verb positions:

- **Root declarative** (V2): the verb moves to C°, landing in second
  position. Complements follow the verb → postverbal.
  Paper examples (17a/b).

- **Embedded finite clause** (verb-final): only V-to-I movement, not
  full V-to-C. Combined with SOV base order, the verb stays clause-final.
  Complements precede the verb → preverbal.
  Paper examples (16a/b).

The competing analyses make different predictions for the preverbal
(= OV) condition. All agree on the postverbal (= VO) condition.
-/

/-- German has V2 in root declaratives: the finite verb moves to C°,
    placing it in second position. Complements follow the verb. -/
theorem german_root_v2 :
    Fragments.German.german.declV2 = true := rfl

/-- German has V-to-I movement in embedded finite clauses (not full
    V-to-C). Combined with the independently motivated SOV base order,
    this yields verb-final surface order in embedded clauses. -/
theorem german_embedded_v_to_i :
    Fragments.German.german.embFinV2 = true := rfl

/-- In German root declaratives, V2 places the verb before its complements.
    Coordination of complements is therefore postverbal.

    This is the VO condition in @cite{schwarzer-2026}'s Experiment 2,
    corresponding to examples (17a/b) in the paper. -/
def germanRootComplementPosition : VerbPosition := .postverbal

/-- In German embedded finite clauses, the verb remains clause-final
    (V-to-I in SOV base → verb at end of IP). Coordination of
    complements is therefore preverbal.

    This is the OV condition in @cite{schwarzer-2026}'s Experiment 2,
    corresponding to examples (16a/b) in the paper. -/
def germanEmbeddedComplementPosition : VerbPosition := .preverbal

/-- V2 root → postverbal complement position, grounded in V2Data. -/
theorem german_v2_grounds_postverbal :
    Fragments.German.german.declV2 = true ∧
    germanRootComplementPosition = .postverbal := ⟨rfl, rfl⟩

/-- Embedded V-to-I + SOV base → preverbal complement position,
    grounded in V2Data. -/
theorem german_vfinal_grounds_preverbal :
    Fragments.German.german.embFinV2 = true ∧
    germanEmbeddedComplementPosition = .preverbal := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: Selection Profile Classification
-- ============================================================================

/-! Each experimental verb is classified as CP-selecting or non-CP-selecting
    by deriving the classification from its `complementType` and
    `altComplementType` fields in the German fragment lexicon. -/

-- Non-CP-selecting verbs: DP complement only

/-- *beenden* "end" does not take a *dass*-clause complement. -/
theorem beenden_nonselecting :
    beenden.toVerbCore.canTakeClausalComplement = false := rfl

/-- *streichen* "cancel" does not take a *dass*-clause complement. -/
theorem streichen_nonselecting :
    streichen.toVerbCore.canTakeClausalComplement = false := rfl

/-- *übereilen* "rush" does not take a *dass*-clause complement. -/
theorem uebereilen_nonselecting :
    uebereilen.toVerbCore.canTakeClausalComplement = false := rfl

/-- *entwickeln* "develop" does not take a *dass*-clause complement. -/
theorem entwickeln_nonselecting :
    entwickeln.toVerbCore.canTakeClausalComplement = false := rfl

-- CP-and-DP-selecting verbs

/-- *veranlassen* "induce" takes both DP and *dass*-clause. -/
theorem veranlassen_selecting :
    veranlassen.toVerbCore.canTakeClausalComplement = true := rfl

/-- *vergessen* "forget" takes both DP and *dass*-clause. -/
theorem vergessen_selecting :
    vergessen.toVerbCore.canTakeClausalComplement = true := rfl

/-- *erwarten* "expect" takes both DP and *dass*-clause. -/
theorem erwarten_selecting :
    erwarten.toVerbCore.canTakeClausalComplement = true := rfl

/-- *beschließen* "decide" takes both DP and *dass*-clause. -/
theorem beschliessen_selecting :
    beschliessen.toVerbCore.canTakeClausalComplement = true := rfl

-- ============================================================================
-- § 3: Competing Analyses & Structural Predictions
-- ============================================================================

/-! `ConjunctOrder`, `VerbPosition`, `OVOrder.toVerbPosition`,
    `bottomUpPrediction`, and `linearClosenessPrediction` are defined
    in @cite{bruening-alkhalaf-2020} and imported via `open`. -/

/-- **Temporal closeness prediction**: the conjunct parsed closest in
    time to the verb has its features checked. Makes the same
    predictions as linear closeness.

    Analysis: @cite{kim-lu-2024}. -/
def temporalClosenessPrediction : VerbPosition → ConjunctOrder :=
  linearClosenessPrediction

/-- Under asymmetric coordination, the bottom-up prediction is
    position-invariant: the structurally prominent conjunct is always
    the first, so DP-first is predicted regardless of verb position. -/
theorem asymmetric_implies_position_invariant (pos : VerbPosition) :
    bottomUpPrediction pos = .dpFirst := rfl

/-- Linear closeness predictions *differ* by position — this is the
    key empirical distinguisher. -/
theorem linear_predictions_differ :
    linearClosenessPrediction .preverbal ≠
    linearClosenessPrediction .postverbal := by decide

/-- Temporal closeness inherits linear closeness predictions exactly. -/
theorem temporal_equals_linear (pos : VerbPosition) :
    temporalClosenessPrediction pos = linearClosenessPrediction pos := rfl

-- ============================================================================
-- § 4: Experiment 1 — Acceptability (Likert z-scores)
-- ============================================================================

/-- Complement type in Experiment 1: DP-CP coordination vs bare *dass*-clause. -/
inductive Exp1ComplementType where
  | coord  -- DP-CP coordination
  | dass   -- bare *dass*-clause
  deriving DecidableEq, Repr, BEq

/-- Descriptive statistics from Experiment 1.
    Latin square design: SELECTION (yes/no) × COMPLEMENT (dass/coord).
    50 participants on Prolific, 6 excluded; 44 per cell. -/
structure Exp1Cell where
  complement : Exp1ComplementType
  selecting : Bool      -- verb selects CP?
  nObs : Nat
  meanZ : Int           -- z-score × 1000 (milli-z) to avoid rationals
  medianZ : Int         -- z-score × 1000
  deriving Repr

def exp1_coord_nonsel : Exp1Cell :=
  { complement := .coord, selecting := false, nObs := 44,
    meanZ := -253, medianZ := -244 }

def exp1_coord_sel : Exp1Cell :=
  { complement := .coord, selecting := true, nObs := 44,
    meanZ := 369, medianZ := 495 }

def exp1_dass_nonsel : Exp1Cell :=
  { complement := .dass, selecting := false, nObs := 44,
    meanZ := -526, medianZ := -684 }

def exp1_dass_sel : Exp1Cell :=
  { complement := .dass, selecting := true, nObs := 44,
    meanZ := 891, medianZ := 1080 }

/-- Coordination is more acceptable than bare *dass*-clause in
    non-selecting contexts (the coordination "rescue" effect). -/
theorem coord_rescues_nonselected :
    exp1_coord_nonsel.meanZ > exp1_dass_nonsel.meanZ := by native_decide

/-- In selecting contexts, bare *dass*-clause is more acceptable than
    coordination (no rescue needed). -/
theorem dass_better_when_selected :
    exp1_dass_sel.meanZ > exp1_coord_sel.meanZ := by native_decide

/-- The interaction: the coordination benefit is larger in non-selecting
    contexts than in selecting ones. Difference for coord vs dass:
    non-selecting: -253 - (-526) = +273; selecting: 369 - 891 = -522. -/
theorem interaction_larger_unselected :
    (exp1_coord_nonsel.meanZ - exp1_dass_nonsel.meanZ) >
    (exp1_coord_sel.meanZ - exp1_dass_sel.meanZ) := by native_decide

-- ============================================================================
-- § 5: Experiment 2 — Order Preference (2AFC)
-- ============================================================================

/-- 2AFC experiment: participants chose between DP-first and CP-first
    order. 30 participants (48 recruited, 1 non-German excluded,
    17 excluded for selecting ungrammatical option ≥2× in control). -/
structure Exp2Data where
  position : VerbPosition
  dpFirstCount : Nat
  cpFirstCount : Nat
  deriving Repr

def exp2_preverbal : Exp2Data :=
  { position := germanEmbeddedComplementPosition, dpFirstCount := 23, cpFirstCount := 7 }

def exp2_postverbal : Exp2Data :=
  { position := germanRootComplementPosition, dpFirstCount := 23, cpFirstCount := 7 }

/-- Total responses per condition. -/
def Exp2Data.total (d : Exp2Data) : Nat := d.dpFirstCount + d.cpFirstCount

/-- The observed majority order in a 2AFC cell. -/
def Exp2Data.majorityOrder (d : Exp2Data) : ConjunctOrder :=
  if d.dpFirstCount > d.cpFirstCount then .dpFirst else .cpFirst

-- Key results

/-- Position invariance: the counts are identical in pre- and post-verbal
    position. This is the central empirical finding. -/
theorem position_invariance_dp :
    exp2_preverbal.dpFirstCount = exp2_postverbal.dpFirstCount := rfl

theorem position_invariance_cp :
    exp2_preverbal.cpFirstCount = exp2_postverbal.cpFirstCount := rfl

/-- DP-first is the observed majority in both positions. -/
theorem dp_majority_preverbal :
    exp2_preverbal.majorityOrder = .dpFirst := rfl

theorem dp_majority_postverbal :
    exp2_postverbal.majorityOrder = .dpFirst := rfl

/-- DP-first probability is 23/30 ≈ 0.767, well above chance (0.5).
    Logistic regression: logit diff to control = +0.894,
    SE = 0.327, z = 2.74, p < 0.0001. -/
theorem dp_preference_above_chance :
    exp2_preverbal.dpFirstCount * 2 > exp2_preverbal.total := by native_decide

/-- DP-first accounts for more than 3/4 of responses. -/
theorem dp_preference_supermajority :
    exp2_preverbal.dpFirstCount * 4 ≥ exp2_preverbal.total * 3 := by native_decide

-- ============================================================================
-- § 6: Theory-Data Alignment
-- ============================================================================

/-- Bottom-up predicts correctly in preverbal position. -/
theorem bottomUp_correct_preverbal :
    bottomUpPrediction .preverbal = exp2_preverbal.majorityOrder := rfl

/-- Bottom-up predicts correctly in postverbal position. -/
theorem bottomUp_correct_postverbal :
    bottomUpPrediction .postverbal = exp2_postverbal.majorityOrder := rfl

/-- Linear closeness predicts *incorrectly* in preverbal position:
    it predicts CP-first, but DP-first is observed. -/
theorem linear_wrong_preverbal :
    linearClosenessPrediction .preverbal ≠ exp2_preverbal.majorityOrder := by
  decide

/-- Temporal closeness also wrong in preverbal position. -/
theorem temporal_wrong_preverbal :
    temporalClosenessPrediction .preverbal ≠ exp2_preverbal.majorityOrder := by
  decide

/-- All three accounts agree in postverbal position (all predict DP-first,
    which is correct). The distinguishing power is preverbal only. -/
theorem all_agree_postverbal :
    bottomUpPrediction .postverbal = linearClosenessPrediction .postverbal ∧
    linearClosenessPrediction .postverbal = exp2_postverbal.majorityOrder :=
  ⟨rfl, rfl⟩

/-- The German 2AFC data falsifies linear percolation: structural
    percolation (bottom-up) matches the observed majority in both
    positions, while linear percolation fails in the preverbal
    position that distinguishes them.

    As @cite{schwarzer-2026} notes (§4), the results are "not
    straightforwardly an argument *for*" the bottom-up approach —
    there could be an independent DP-first preference — but they are
    decisive *against* linear/temporal closeness accounts. -/
theorem percolation_adjudication :
    predictOrder .structural .preverbal = exp2_preverbal.majorityOrder ∧
    predictOrder .structural .postverbal = exp2_postverbal.majorityOrder ∧
    predictOrder .linear .preverbal ≠ exp2_preverbal.majorityOrder :=
  ⟨rfl, rfl, by decide⟩

/-- Temporal closeness (@cite{kim-lu-2024}) uses the same linear
    percolation mechanism as B&AK, applied to parsing time rather
    than surface string position. -/
theorem temporal_is_linear_percolation (pos : VerbPosition) :
    temporalClosenessPrediction pos = predictOrder .linear pos := rfl

-- ============================================================================
-- § 7: Asymmetric Structure Bridge
-- ============================================================================

/-- Under asymmetric coordination structure, the bottom-up prediction
    follows: the first conjunct is structurally prominent and must
    satisfy selection. Under symmetric structure, no such prediction
    is made (both conjuncts are equally prominent). -/
def structurePrediction : CoordSymmetry → Option (VerbPosition → ConjunctOrder)
  | .asymmetric => some bottomUpPrediction
  | .symmetric  => none

/-- Asymmetric structure entails position-invariant DP-first prediction. -/
theorem asymmetric_entails_dp_first (pos : VerbPosition) :
    structurePrediction .asymmetric = some bottomUpPrediction ∧
    bottomUpPrediction pos = .dpFirst :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Cross-Linguistic Generalization
-- ============================================================================

/-- The bottom-up prediction is universal: for any language, regardless of
    its OV/VO parameter, the predicted order is always DP-first. -/
theorem bottomUp_universal (pos : VerbPosition) :
    bottomUpPrediction pos = .dpFirst := rfl

/-- For OV languages, linear closeness makes the wrong prediction
    (CP-first in preverbal position), while bottom-up is correct. -/
theorem ov_distinguishes_accounts :
    linearClosenessPrediction .preverbal = .cpFirst ∧
    bottomUpPrediction .preverbal = .dpFirst := ⟨rfl, rfl⟩

/-- The German result generalizes: if an OV language shows DP-first
    preference in preverbal position, linear/temporal closeness accounts
    are ruled out for that language. -/
theorem ov_dpfirst_rules_out_linear
    (obs : ConjunctOrder) (h : obs = .dpFirst) :
    linearClosenessPrediction .preverbal ≠ obs := by
  subst h; decide

/-- B&AK's English subject-position evidence (§3.1, examples (41a/b))
    and Schwarzer's German preverbal data both test the preverbal
    configuration. B&AK predict CP-first for both (correct for English
    subjects per B&AK's judgments, but wrong for German complements).
    German data directly contradicts the closeness prediction in the
    preverbal environment where B&AK claim their strongest evidence. -/
theorem german_contradicts_bak_subject_evidence :
    linearClosenessPrediction .preverbal = .cpFirst ∧
    exp2_preverbal.majorityOrder = .dpFirst := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Selection Profile ↔ Experiment Condition Bridge
-- ============================================================================

/-- The non-selecting verbs are exactly those used in the "not selected"
    condition of Experiment 1: they take only DP complements, so a
    *dass*-clause is unselected. -/
def nonSelectingVerbs : List GermanVerbEntry :=
  [beenden, streichen, uebereilen, entwickeln]

/-- The CP-selecting verbs are exactly those used in the "selected"
    condition of Experiment 1. -/
def selectingVerbs : List GermanVerbEntry :=
  [veranlassen, vergessen, erwarten, beschliessen]

/-- All non-selecting verbs lack clausal complement capability. -/
theorem nonSelecting_all_false :
    nonSelectingVerbs.all
      (λ v => !v.toVerbCore.canTakeClausalComplement) = true := by native_decide

/-- All selecting verbs have clausal complement capability. -/
theorem selecting_all_true :
    selectingVerbs.all
      (λ v => v.toVerbCore.canTakeClausalComplement) = true := by native_decide

/-- No verb is in both lists. -/
theorem selecting_nonselecting_disjoint :
    (nonSelectingVerbs.filter
      (λ v => selectingVerbs.any (· == v))).length = 0 := by native_decide

-- ============================================================================
-- § 10: Typological Bridges
-- ============================================================================

/-- German's WALS OV order is "no dominant" (V2 root vs SOV embedded),
    but the experimental conditions derive their verb positions from
    clause type: root V2 → postverbal, embedded verb-final → preverbal
    (§ 1). -/
theorem german_wals_vs_clausetype :
    Fragments.German.typology.wordOrder.ovOrder = .noDominant ∧
    germanRootComplementPosition = .postverbal ∧
    germanEmbeddedComplementPosition = .preverbal :=
  ⟨rfl, rfl, rfl⟩

/-- For any OV language in the typological sample, the OVOrder→VerbPosition
    bridge yields preverbal position. -/
theorem ov_languages_preverbal :
    OVOrder.toVerbPosition .ov = some VerbPosition.preverbal := rfl

/-- For any VO language in the typological sample, the OVOrder→VerbPosition
    bridge yields postverbal position. -/
theorem vo_languages_postverbal :
    OVOrder.toVerbPosition .vo = some VerbPosition.postverbal := rfl

/-- Linear closeness makes the wrong prediction for all OV languages:
    deriving VerbPosition from OVOrder and then applying linear closeness
    yields CP-first, which is refuted by German data. -/
theorem linear_wrong_for_ov_languages :
    (OVOrder.toVerbPosition .ov).map linearClosenessPrediction = some .cpFirst := rfl

/-- Bottom-up makes the correct prediction for all OV languages. -/
theorem bottomUp_correct_for_ov_languages :
    (OVOrder.toVerbPosition .ov).map bottomUpPrediction = some .dpFirst := rfl

-- ============================================================================
-- § 11: Fragment Membership & Coordination Particle
-- ============================================================================

/-- All 8 experimental verbs are in the German fragment's allVerbs list. -/
theorem experimental_verbs_in_allVerbs :
    allVerbs.any (· == beenden) = true ∧
    allVerbs.any (· == streichen) = true ∧
    allVerbs.any (· == uebereilen) = true ∧
    allVerbs.any (· == entwickeln) = true ∧
    allVerbs.any (· == veranlassen) = true ∧
    allVerbs.any (· == vergessen) = true ∧
    allVerbs.any (· == erwarten) = true ∧
    allVerbs.any (· == beschliessen) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The coordination particle used in the experiments is German *und*,
    which is the J particle in the Mitrović & Sauerland decomposition. -/
theorem experimental_conjunction_is_j :
    Fragments.German.Coordination.und.role = .j := rfl

/-- German uses J-only conjunction strategy (overt *und*, covert MU). -/
theorem german_j_only :
    Fragments.German.Coordination.conjunctionStrategy = .jOnly := rfl

end Schwarzer2026
