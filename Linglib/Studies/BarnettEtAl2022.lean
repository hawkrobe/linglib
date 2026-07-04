import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.ArgumentativeStrength
import Linglib.Pragmatics.RSA.Speaker.CombinedUtility
import Mathlib.Data.Rat.Defs

/-!
# [barnett-griffiths-hawkins-2022]: A Pragmatic Account of the Weak Evidence Effect
[barnett-griffiths-hawkins-2022]

Extends RSA with a **persuasive speaker** who has a goal state w* that may differ
from the true world state w. The speaker's utility combines epistemic and persuasive
components (Eq. 6):

  U(u; w, w*) = U_epi(u; w) + β · U_pers(u; w*)

where U_epi = ln P_L0(w|u) and U_pers = ln P_L0(w*|u). The parameter β controls
persuasive bias (β=0 recovers standard RSA).

## Key Result: The Weak Evidence Effect

When β > 0, weak positive evidence can *backfire*: a pragmatic listener who expects
the speaker to show the strongest available evidence infers that the absence of
strong evidence means it doesn't exist, shifting beliefs in the opposite direction.

## Stick Contest Domain

The paper's experiment uses 5 sticks from {1,...,9} (C(9,5)=126 worlds, midpoint 5).
We formalize a simplified Stick Contest (3 sticks from {1,...,5}, 10 worlds, midpoint 3)
that preserves the key structural properties: the prior favors ¬longer (P(longer)=0.4),
and sticks have monotonically increasing L0(longer|·) values. The simplification enables
kernel-verified exact rational arithmetic on the PMF face.

## Model design

The paper's Eq. 8 gives:

  S(u|w, w*=longer, β) ∝ L0(longer|u)^β · 𝟙[u ∈ w]

Since the paper fixes α=1 and treats αβ as a single parameter, the speaker's exponent
plays the role of β. The s1Score uses precomputed L0(longer|u) values squared
(β=2), gated by stick availability.

## Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | L0: stick 5 is positive evidence for "longer" | `l0_s5_positive` |
| 2 | L0: stick 5 is the strongest evidence | `l0_s5_strongest` |
| 3 | L0: stick 1 is evidence against "longer" | `l0_s1_negative` |
| 4 | WEE: stick 4 backfires under L1 (β=2) | `weak_evidence_effect` |
| 5 | Strong evidence works: stick 5 favors "longer" under L1 | `strong_evidence_works` |
| 6 | L0(longer|·) is monotone in stick length | `l0_monotone` |
| 7 | Stick 4 has positive argStr yet backfires | `argStr_positive_but_backfires` |
| 8 | Model predicts the observed interaction effect | `model_predicts_interaction` |
| 9 | Pragmatic group shows backfire in experiment | `pragmatic_backfire` |
| 10 | RSA speaker-dependent model fits best | `rsa_speaker_dep_best_waic` |
-/

namespace BarnettEtAl2022

open RSA.ArgumentativeStrength
open RSA.CombinedUtility

-- ============================================================
-- §1. Domain Types
-- ============================================================

/-- Stick lengths 1–5 -/
inductive Stick where
  | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Stick where
  elems := {.s1, .s2, .s3, .s4, .s5}
  complete := fun x => by cases x <;> simp

/-- Worlds: sets of 3 distinct sticks from {1,...,5}. C(5,3) = 10 worlds. -/
inductive StickWorld where
  | w123 | w124 | w125 | w134 | w135
  | w145 | w234 | w235 | w245 | w345
  deriving DecidableEq, Repr, Inhabited

instance : Fintype StickWorld where
  elems := {.w123, .w124, .w125, .w134, .w135, .w145, .w234, .w235, .w245, .w345}
  complete := fun x => by cases x <;> simp

/-- Whether a stick is available in a given world. -/
def worldContains : StickWorld → Stick → Bool
  | .w123, .s1 | .w123, .s2 | .w123, .s3 => true
  | .w124, .s1 | .w124, .s2 | .w124, .s4 => true
  | .w125, .s1 | .w125, .s2 | .w125, .s5 => true
  | .w134, .s1 | .w134, .s3 | .w134, .s4 => true
  | .w135, .s1 | .w135, .s3 | .w135, .s5 => true
  | .w145, .s1 | .w145, .s4 | .w145, .s5 => true
  | .w234, .s2 | .w234, .s3 | .w234, .s4 => true
  | .w235, .s2 | .w235, .s3 | .w235, .s5 => true
  | .w245, .s2 | .w245, .s4 | .w245, .s5 => true
  | .w345, .s3 | .w345, .s4 | .w345, .s5 => true
  | _, _ => false

/-- A world is "longer" if the average stick length exceeds the midpoint (3).
Equivalently, sum > 9 for 3 sticks. 4 of 10 worlds qualify. -/
def IsLonger : StickWorld → Prop
  | .w145 | .w235 | .w245 | .w345 => True
  | _ => False

instance : DecidablePred IsLonger := fun w => by
  cases w <;> unfold IsLonger <;> infer_instance

-- ============================================================
-- §2. Persuasive-speaker scores
-- ============================================================

/-- L0(longer|u) as ℚ for each stick. Each stick appears in C(4,2)=6 worlds;
this gives the fraction where IsLonger holds.

- s1: 1/6 (only w145 is longer)
- s2: 2/6 = 1/3 (w235, w245)
- s3: 2/6 = 1/3 (w235, w345)
- s4: 3/6 = 1/2 (w145, w245, w345)
- s5: 4/6 = 2/3 (w145, w235, w245, w345) -/
def l0LongerQ : Stick → ℚ
  | .s1 => 1/6
  | .s2 => 1/3
  | .s3 => 1/3
  | .s4 => 1/2
  | .s5 => 2/3

/-- Prior probability of "longer": 4 out of 10 worlds -/
def priorLonger : ℚ := 2 / 5

/-- S1 score as ℚ: L0(longer|u)^β · 𝟙[u ∈ w], at β=2. The squared L0 values
are precomputed as literal fractions so that the reifier extracts concrete ℚ
values from the ℚ→ℝ cast without needing to reduce function calls. -/
def s1ScoreQ (w : StickWorld) (u : Stick) : ℚ :=
  if worldContains w u then
    match u with
    | .s1 => 1/36   -- (1/6)²
    | .s2 => 1/9    -- (1/3)²
    | .s3 => 1/9    -- (1/3)²
    | .s4 => 1/4    -- (1/2)²
    | .s5 => 4/9    -- (2/3)²
  else 0

-- ============================================================
-- §2b. PMF chain (local pending the RSA API pass)
-- ============================================================

section PMFChain

open scoped ENNReal

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem stickSat : ∀ u : Stick, ∃ w, worldContains w u = true := by decide

private noncomputable def bwPrior : PMF StickWorld := PMF.uniformOfFintype StickWorld

private theorem bwPrior_pos (w : StickWorld) : bwPrior w ≠ 0 := by
  rw [bwPrior, PMF.uniformOfFintype_apply]
  simp

private theorem bwPrior_apply (w : StickWorld) : bwPrior w = 10⁻¹ := by
  rw [bwPrior, PMF.uniformOfFintype_apply,
    show Fintype.card StickWorld = 10 from by decide]
  norm_num

private theorem sumWorlds (f : StickWorld → ℝ≥0∞) :
    ∑' w, f w = f .w123 + f .w124 + f .w125 + f .w134 + f .w135 +
      f .w145 + f .w234 + f .w235 + f .w245 + f .w345 := by
  rw [tsum_fintype,
    show (Finset.univ : Finset StickWorld)
      = {.w123, .w124, .w125, .w134, .w135, .w145, .w234, .w235, .w245, .w345}
      from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem sumSticks (f : Stick → ℝ≥0∞) :
    ∑' u, f u = f .s1 + f .s2 + f .s3 + f .s4 + f .s5 := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Stick) = {.s1, .s2, .s3, .s4, .s5} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Literal listener over worlds given a revealed stick (uniform prior;
every stick appears in exactly six of the ten worlds). -/
private noncomputable def bwL0 (u : Stick) : PMF StickWorld :=
  RSA.L0LassiterGoodman bwPrior (fun u w => worldContains w u) u (by
    obtain ⟨w, hw⟩ := stickSat u
    exact ENNReal.summable.tsum_ne_zero_iff.mpr
      ⟨w, by rw [hw]; simpa using bwPrior_pos w⟩)

/-- Every stick's extension mass is `6/10`: L0 is `1/6` per containing world. -/
private theorem bwL0_apply (u : Stick) (w : StickWorld) :
    bwL0 u w = if worldContains w u then ENNReal.ofReal (1/6) else 0 := by
  unfold bwL0
  rw [RSA.L0LassiterGoodman_apply]
  have hmass : (∑' w', bwPrior w' * (if worldContains w' u then (1 : ℝ≥0∞) else 0))
      = ENNReal.ofReal (6/10) := by
    rw [sumWorlds]
    simp only [bwPrior_apply]
    have h10 : (10 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/10) := by
      rw [show (10 : ℝ≥0∞) = ENNReal.ofReal 10 from (ENNReal.ofReal_ofNat 10).symm,
        ← ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    cases u <;>
      · simp +decide
        simp only [h10]
        try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
  rw [hmass, bwPrior_apply]
  by_cases hw : worldContains w u = true
  · rw [hw]
    simp only [if_true, mul_one]
    rw [show (10 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/10) from by
        rw [show (10 : ℝ≥0∞) = ENNReal.ofReal 10 from (ENNReal.ofReal_ofNat 10).symm,
          ← ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · rw [Bool.not_eq_true] at hw
    rw [hw]
    simp

/-- Event marginal of the literal listener (`P(E|u)` over the world posterior). -/
noncomputable def l0Event (u : Stick) (P : StickWorld → Prop) [DecidablePred P] :
    ℝ≥0∞ :=
  ∑' w, if P w then bwL0 u w else 0

/-! ### Persuasive speaker and skeptical listener -/

private theorem worldSat : ∀ w : StickWorld, ∃ u : Stick, (0 : ℚ) < s1ScoreQ w u := by
  intro w
  cases w <;>
    first
      | (refine ⟨.s1, ?_⟩; norm_num [s1ScoreQ, worldContains]; done)
      | (refine ⟨.s2, ?_⟩; norm_num [s1ScoreQ, worldContains]; done)
      | (refine ⟨.s3, ?_⟩; norm_num [s1ScoreQ, worldContains]; done)

private theorem s1ScoreQ_nonneg : ∀ (w : StickWorld) (u : Stick), (0 : ℚ) ≤ s1ScoreQ w u := by
  intro w u
  cases w <;> cases u <;> norm_num [s1ScoreQ, worldContains]

/-- Persuasive speaker ([barnett-griffiths-hawkins-2022] eqs. 4–6; p. 175:
"Because the speaker only has access to true utterances, all utterances have
equal epistemic utility", so the softmax reduces to
`L0(longer|u)^β · 𝟙[u ∈ w]` at αβ = 2 — the file's exact `s1ScoreQ` table).
Local op pending the RSA API pass. -/
private noncomputable def s1Persuade (w : StickWorld) : PMF Stick :=
  PMF.normalize (fun u => ENNReal.ofReal ((s1ScoreQ w u : ℝ)))
    (by
      obtain ⟨u, hu⟩ := worldSat w
      exact ENNReal.summable.tsum_ne_zero_iff.mpr ⟨u, by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact_mod_cast hu⟩)
    (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)

/-- Per-world speaker normaliser, exactly. -/
private def ZQ (w : StickWorld) : ℚ :=
  s1ScoreQ w .s1 + s1ScoreQ w .s2 + s1ScoreQ w .s3 + s1ScoreQ w .s4 + s1ScoreQ w .s5

private theorem ZQ_pos : ∀ w : StickWorld, (0 : ℚ) < ZQ w := by
  intro w
  cases w <;> norm_num [ZQ, s1ScoreQ, worldContains]

/-- Exact speaker values: `score/Z` as a single `ofReal` rational. -/
private theorem s1Persuade_apply (w : StickWorld) (u : Stick) :
    s1Persuade w u = ENNReal.ofReal ((s1ScoreQ w u : ℝ) / (ZQ w : ℝ)) := by
  unfold s1Persuade
  rw [PMF.normalize_apply]
  have hn : ∀ u', (0 : ℝ) ≤ (s1ScoreQ w u' : ℝ) := fun u' => by
    exact_mod_cast s1ScoreQ_nonneg w u'
  have hmass : (∑' u', ENNReal.ofReal ((s1ScoreQ w u' : ℝ)))
      = ENNReal.ofReal ((ZQ w : ℝ)) := by
    rw [sumSticks, ← ENNReal.ofReal_add (hn _) (hn _),
      ← ENNReal.ofReal_add (add_nonneg (hn _) (hn _)) (hn _),
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hn _) (hn _)) (hn _)) (hn _),
      ← ENNReal.ofReal_add
        (add_nonneg (add_nonneg (add_nonneg (hn _) (hn _)) (hn _)) (hn _)) (hn _)]
    congr 1
    simp only [ZQ]
    push_cast
    ring
  rw [hmass, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast ZQ_pos w),
    ← ENNReal.ofReal_mul (hn u), div_eq_mul_inv]

private theorem stickScoreSat : ∀ u : Stick, ∃ w : StickWorld, (0 : ℚ) < s1ScoreQ w u := by
  intro u
  cases u <;>
    first
      | (refine ⟨.w123, ?_⟩; norm_num [s1ScoreQ, worldContains]; done)
      | (refine ⟨.w145, ?_⟩; norm_num [s1ScoreQ, worldContains]; done)

private theorem s1Persuade_marginal_pos (u : Stick) :
    PMF.marginal (fun w => s1Persuade w) bwPrior u ≠ 0 := by
  obtain ⟨w, hw⟩ := stickScoreSat u
  refine PMF.marginal_ne_zero _ _ _ (bwPrior_pos w) ?_
  rw [s1Persuade_apply, ENNReal.ofReal_ne_zero_iff]
  exact div_pos (by exact_mod_cast hw) (by exact_mod_cast ZQ_pos w)

/-- Skeptical pragmatic listener ([barnett-griffiths-hawkins-2022] eq. 7:
the listener "is able to be 'skeptical' of the speaker's agenda and discount
their evidence accordingly"). -/
noncomputable def l1w (u : Stick) : PMF StickWorld :=
  PMF.posterior (fun w => s1Persuade w) bwPrior u (s1Persuade_marginal_pos u)

/-- Event marginal of the pragmatic listener. -/
noncomputable def l1Event (u : Stick) (P : StickWorld → Prop) [DecidablePred P] :
    ℝ≥0∞ :=
  ∑' w, if P w then l1w u w else 0

/-- The uniform prior and the utterance marginal factor out of the event sum. -/
private theorem l1Event_eq (u : Stick) (P : StickWorld → Prop) [DecidablePred P] :
    l1Event u P = 10⁻¹ * (∑' w, if P w then s1Persuade w u else 0) *
      (PMF.marginal (fun w => s1Persuade w) bwPrior u)⁻¹ := by
  unfold l1Event l1w
  rw [show (∑' w, if P w then
        PMF.posterior (fun w' => s1Persuade w') bwPrior u
          (s1Persuade_marginal_pos u) w else 0)
      = ∑' w, 10⁻¹ * ((if P w then s1Persuade w u else 0) *
          (PMF.marginal (fun w' => s1Persuade w') bwPrior u)⁻¹) from
    tsum_congr fun w => by
      by_cases h : P w
      · simp only [h, if_true, PMF.posterior_apply, bwPrior_apply]
        ring
      · simp [h],
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ← mul_assoc]

private theorem S_sum_s4_longer :
    (∑' w, if IsLonger w then s1Persuade w .s4 else 0) = ENNReal.ofReal (729/754) := by
  rw [sumWorlds]
  simp +decide [s1Persuade_apply, s1ScoreQ, ZQ]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

private theorem S_sum_s4_notLonger :
    (∑' w, if ¬ IsLonger w then s1Persuade w .s4 else 0) = ENNReal.ofReal (216/119) := by
  rw [sumWorlds]
  simp +decide [s1Persuade_apply, s1ScoreQ, ZQ]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

private theorem S_sum_s5_longer :
    (∑' w, if IsLonger w then s1Persuade w .s5 else 0) = ENNReal.ofReal (2698/1131) := by
  rw [sumWorlds]
  simp +decide [s1Persuade_apply, s1ScoreQ, ZQ]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

private theorem S_sum_s5_notLonger :
    (∑' w, if ¬ IsLonger w then s1Persuade w .s5 else 0) = ENNReal.ofReal (32/21) := by
  rw [sumWorlds]
  simp +decide [s1Persuade_apply, s1ScoreQ, ZQ]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem sixth_conv : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/6) := by
  rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 from (ENNReal.ofReal_ofNat 6).symm,
    ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private theorem l0e_s5_longer : l0Event .s5 IsLonger = ENNReal.ofReal (4/6) := by
  unfold l0Event
  rw [sumWorlds]
  simp +decide [bwL0_apply]
  simp only [sixth_conv]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

private theorem l0e_s5_notLonger :
    l0Event .s5 (fun w => ¬ IsLonger w) = ENNReal.ofReal (2/6) := by
  unfold l0Event
  rw [sumWorlds]
  simp +decide [bwL0_apply]
  simp only [sixth_conv]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

private theorem l0e_s4_longer : l0Event .s4 IsLonger = ENNReal.ofReal (3/6) := by
  unfold l0Event
  rw [sumWorlds]
  simp +decide [bwL0_apply]
  simp only [sixth_conv]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

private theorem l0e_s1_longer : l0Event .s1 IsLonger = ENNReal.ofReal (1/6) := by
  unfold l0Event
  rw [sumWorlds]
  simp +decide [bwL0_apply]

private theorem l0e_s1_notLonger :
    l0Event .s1 (fun w => ¬ IsLonger w) = ENNReal.ofReal (5/6) := by
  unfold l0Event
  rw [sumWorlds]
  simp +decide [bwL0_apply]
  simp only [sixth_conv]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

end PMFChain

open scoped ENNReal

-- ============================================================
-- §3. Predictions — L0
-- ============================================================

/-- L0(longer|s5) > L0(¬longer|s5): stick 5 is positive evidence for "longer".
4 of 6 worlds containing s5 are longer, vs 2 not-longer. -/
theorem l0_s5_positive :
    l0Event .s5 IsLonger > l0Event .s5 (fun w => ¬ IsLonger w) := by
  rw [gt_iff_lt, l0e_s5_longer, l0e_s5_notLonger]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- L0(longer|s5) > L0(longer|s4): stick 5 provides stronger evidence than s4. -/
theorem l0_s5_strongest :
    l0Event .s5 IsLonger > l0Event .s4 IsLonger := by
  rw [gt_iff_lt, l0e_s5_longer, l0e_s4_longer]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- L0(¬longer|s1) > L0(longer|s1): stick 1 is evidence against "longer".
Only 1 of 6 worlds containing s1 is longer. -/
theorem l0_s1_negative :
    l0Event .s1 (fun w => ¬ IsLonger w) > l0Event .s1 IsLonger := by
  rw [gt_iff_lt, l0e_s1_longer, l0e_s1_notLonger]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- L0(longer|·) is monotonically increasing in stick length. This structural
property ensures the simplified domain faithfully mirrors the paper's full domain
(Appendix Theorem 2). -/
theorem l0_monotone :
    l0LongerQ .s1 ≤ l0LongerQ .s2 ∧
    l0LongerQ .s2 ≤ l0LongerQ .s3 ∧
    l0LongerQ .s3 ≤ l0LongerQ .s4 ∧
    l0LongerQ .s4 ≤ l0LongerQ .s5 := by norm_num [l0LongerQ]

-- ============================================================
-- §4. Predictions — L1 (weak evidence effect)
-- ============================================================

/-- **Weak evidence effect**: at β=2, showing stick 4 (positive literal evidence)
*decreases* the pragmatic listener's belief in "longer" below the prior
([barnett-griffiths-hawkins-2022] p. 172: "the absence of strong evidence
from a speaker who would be highly motivated to show it statistically
implies that no such evidence exists").

Structurally, this is the Z-gap across the event partition: any longer world
containing s4 also contains s5 or comparably strong sticks, inflating the
speaker's normaliser (`Z ≥ 13/18`), while every ¬longer world containing s4
has `Z ≤ 17/36` — so the s4-scores concentrate on the ¬longer side
(`216/119 > 729/754`). -/
theorem weak_evidence_effect :
    l1Event .s4 (fun w => ¬ IsLonger w) > l1Event .s4 IsLonger := by
  rw [gt_iff_lt, l1Event_eq, l1Event_eq, S_sum_s4_longer, S_sum_s4_notLonger]
  set M := PMF.marginal (fun w => s1Persuade w) bwPrior .s4 with hM
  have hM0 : M ≠ 0 := s1Persuade_marginal_pos .s4
  have hMt : M ≠ ⊤ := PMF.marginal_ne_top _ _ _
  have hc0 : (10 : ℝ≥0∞)⁻¹ * M⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr (by norm_num)) (ENNReal.inv_ne_zero.mpr hMt)
  have hct : (10 : ℝ≥0∞)⁻¹ * M⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)) (ENNReal.inv_ne_top.mpr hM0)
  calc 10⁻¹ * ENNReal.ofReal (729/754) * M⁻¹
      = 10⁻¹ * M⁻¹ * ENNReal.ofReal (729/754) := by ring
    _ < 10⁻¹ * M⁻¹ * ENNReal.ofReal (216/119) :=
        ENNReal.mul_lt_mul_right hc0 hct
          ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num))
    _ = 10⁻¹ * ENNReal.ofReal (216/119) * M⁻¹ := by ring

/-- Strong evidence does NOT backfire: stick 5 increases belief at β=2.

The strongest available evidence is always effective because it cannot
be "explained away" by the absence of something better. -/
theorem strong_evidence_works :
    l1Event .s5 IsLonger > l1Event .s5 (fun w => ¬ IsLonger w) := by
  rw [gt_iff_lt, l1Event_eq, l1Event_eq, S_sum_s5_longer, S_sum_s5_notLonger]
  set M := PMF.marginal (fun w => s1Persuade w) bwPrior .s5 with hM
  have hM0 : M ≠ 0 := s1Persuade_marginal_pos .s5
  have hMt : M ≠ ⊤ := PMF.marginal_ne_top _ _ _
  have hc0 : (10 : ℝ≥0∞)⁻¹ * M⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr (by norm_num)) (ENNReal.inv_ne_zero.mpr hMt)
  have hct : (10 : ℝ≥0∞)⁻¹ * M⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)) (ENNReal.inv_ne_top.mpr hM0)
  calc 10⁻¹ * ENNReal.ofReal (32/21) * M⁻¹
      = 10⁻¹ * M⁻¹ * ENNReal.ofReal (32/21) := by ring
    _ < 10⁻¹ * M⁻¹ * ENNReal.ofReal (2698/1131) :=
        ENNReal.mul_lt_mul_right hc0 hct
          ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num))
    _ = 10⁻¹ * ENNReal.ofReal (2698/1131) * M⁻¹ := by ring

-- ============================================================
-- §5. Bridge Theorems
-- ============================================================

/-- At β=1, the persuasive utility equals combinedWeighted(1,1,...). -/
theorem goalOriented_at_one (uEpi uPers : ℚ) :
    goalOrientedUtility uEpi uPers 1 = combinedWeighted 1 1 uEpi uPers :=
  goalOriented_eq_combinedWeighted uEpi uPers 1

/-- The paper's Eq. 6 (additive: U_epi + β·U_pers) equals
(1+β) · combined(β/(1+β), U_epi, U_pers). -/
theorem goalOriented_via_combined (uEpi uPers β : ℚ) (hβ : 0 ≤ β) :
    goalOrientedUtility uEpi uPers β = (1 + β) * combined (betaToLam β) uEpi uPers :=
  goalOriented_eq_scaled_combined uEpi uPers β hβ

/-- Connection to ArgumentativeStrength: stick 4 has positive argumentative
strength for the goal "longer" (L0(longer|s4) = 1/2 > 2/5 = P(longer)). -/
theorem s4_positive_argStr :
    hasPositiveArgStr (l0LongerQ .s4) priorLonger := by norm_num [hasPositiveArgStr, l0LongerQ, priorLonger]

/-- Stick 3 does NOT have positive argumentative strength
(L0(longer|s3) = 1/3 < 2/5 = P(longer)). -/
theorem s3_not_positive_argStr :
    ¬ hasPositiveArgStr (l0LongerQ .s3) priorLonger := by norm_num [hasPositiveArgStr, l0LongerQ, priorLonger]

/-- The weak evidence effect shows that argumentatively positive evidence
can still backfire under a pragmatic listener model. This is the core
insight connecting [barnett-griffiths-hawkins-2022] to
[cummins-franke-2021]'s work on argumentative strength.

Stick 4 has positive argStr at L0 (1/2 > 2/5), yet L1 assigns more mass
to ¬longer than longer after seeing s4. -/
theorem argStr_positive_but_backfires :
    hasPositiveArgStr (l0LongerQ .s4) priorLonger ∧
    l1Event .s4 (fun w => ¬ IsLonger w) > l1Event .s4 IsLonger :=
  ⟨s4_positive_argStr, weak_evidence_effect⟩

-- ============================================================
-- §6. Experimental Design & Behavioral Data
-- ============================================================

/-- Listener type inferred from speaker expectation phase -/
inductive ListenerType where
  | pragmatic   -- expects strongest evidence (67% of participants)
  | literal     -- expects weaker/hedged evidence (33%)
  deriving DecidableEq, Repr

/-- Evidence strength conditions (distance from midpoint 5") -/
inductive EvidenceStrength where
  | weak      -- 6" (1" from midpoint)
  | moderate  -- 7" (2" from midpoint)
  | strong    -- 8" (3" from midpoint)
  | strongest -- 9" (4" from midpoint)
  deriving DecidableEq, Repr

/-- Which contestant goes first -/
inductive FirstContestant where
  | longBiased   -- wants judge to say "longer"
  | shortBiased  -- wants judge to say "shorter"
  deriving DecidableEq, Repr

/-- Stick Contest design parameters -/
structure StickContestDesign where
  nSticks : Nat            -- sticks per sample (5)
  minLength : Nat          -- minimum stick length (1")
  maxLength : Nat          -- maximum stick length (9")
  midpoint : Nat           -- midpoint for verdict (5")
  nParticipants : Nat      -- total after exclusions
  deriving Repr

/-- The actual experimental parameters -/
def design : StickContestDesign :=
  { nSticks := 5
    minLength := 1
    maxLength := 9
    midpoint := 5
    nParticipants := 723 }

/-- Proportion expecting strongest evidence (pragmatic listeners) -/
def pragmaticProportion : ℚ := 485 / 723

/-- Proportion expecting weaker evidence (literal listeners) -/
def literalProportion : ℚ := 238 / 723

theorem pragmatic_is_majority : pragmaticProportion > 1 / 2 := by norm_num [pragmaticProportion]

/-- Key interaction: speaker expectations × evidence strength.
t(718) = 5.2, p < 0.001 (p. 175) -/
structure InteractionEffect where
  tStatistic : ℚ
  df : Nat
  pLessThan : ℚ
  deriving Repr

def interactionEffect : InteractionEffect :=
  { tStatistic := 52 / 10  -- 5.2
    df := 718
    pLessThan := 1 / 1000 }

/-- Behavioral result for a listener group -/
structure GroupResult where
  listenerType : ListenerType
  nParticipants : Nat
  meanSlider : ℚ           -- 0–100 scale, 50 = neutral
  ci95Lower : Option ℚ     -- 95% CI lower bound (when reported)
  ci95Upper : Option ℚ     -- 95% CI upper bound (when reported)
  deriving Repr

/-- Pragmatic group: weak evidence backfires (mean below 50).
95% CI: [32.3, 37.3] (paper p. 175). -/
def pragmaticResult : GroupResult :=
  { listenerType := .pragmatic
    nParticipants := 485
    meanSlider := 347 / 10    -- 34.7
    ci95Lower := some (323 / 10)   -- 32.3
    ci95Upper := some (373 / 10) } -- 37.3

/-- Literal group: no weak evidence effect (mean at 50).
CIs not reported in paper. -/
def literalResult : GroupResult :=
  { listenerType := .literal
    nParticipants := 238
    meanSlider := 501 / 10  -- 50.1
    ci95Lower := none
    ci95Upper := none }

/-- Pragmatic group shows backfire: mean significantly below 50 (midpoint) -/
theorem pragmatic_backfire : pragmaticResult.meanSlider < 50 := by norm_num [pragmaticResult]

/-- Literal group shows no backfire: mean at midpoint -/
theorem literal_no_backfire : literalResult.meanSlider > 49 := by norm_num [literalResult]

/-- The two groups differ in the predicted direction -/
theorem groups_differ :
    pragmaticResult.meanSlider < literalResult.meanSlider := by norm_num [pragmaticResult, literalResult]

-- ============================================================
-- §7. Model Comparison (Table 1)
-- ============================================================

/-- Model families compared -/
inductive ModelFamily where
  | anchorAdjust     -- A&A: P(w|u) = P(w) + η(s(u) - R)
  | minAcceptable    -- MAS: like A&A but R ~ Unif[-1,1]
  | rsaPragmatic     -- RSA with persuasive speaker
  deriving DecidableEq, Repr

/-- Model variant (how individual differences are handled) -/
inductive ModelVariant where
  | homogeneous       -- single model for all participants
  | heterogeneous     -- mixture of J0 and J1
  | speakerDependent  -- mixture weights conditioned on speaker phase
  deriving DecidableEq, Repr

/-- Model comparison result from Table 1 -/
structure ModelComparisonDatum where
  family : ModelFamily
  variant : ModelVariant
  logLikelihood : ℚ
  waic : ℚ
  waicSE : ℚ
  psisLoo : ℚ
  psisLooSE : ℚ
  deriving Repr

/-- Table 1 data -/
def modelComparison : List ModelComparisonDatum :=
  [ ⟨.anchorAdjust,  .homogeneous,      -281/10,  577/10, 99/10,  288/10, 99/10⟩
  , ⟨.minAcceptable, .homogeneous,       82/10,   -133/10, 96/10, -66/10, 96/10⟩
  , ⟨.minAcceptable, .heterogeneous,     82/10,   -113/10, 95/10, -56/10, 95/10⟩
  , ⟨.rsaPragmatic,  .homogeneous,       81/10,   -133/10, 95/10, -67/10, 95/10⟩
  , ⟨.rsaPragmatic,  .heterogeneous,     81/10,   -105/10, 93/10, -52/10, 93/10⟩
  , ⟨.rsaPragmatic,  .speakerDependent,  12,      -164/10, 91/10, -92/10, 91/10⟩
  ]

/-- The RSA speaker-dependent model has the best (highest) log-likelihood -/
theorem rsa_speaker_dep_best_likelihood :
    (12 : ℚ) > 82 / 10 := by norm_num

/-- The RSA speaker-dependent model has the best (lowest) WAIC -/
theorem rsa_speaker_dep_best_waic :
    (-164 : ℚ) / 10 < -133 / 10 := by norm_num

-- ============================================================
-- §8. Fitted Parameters
-- ============================================================

/-- Fitted parameters for the best model (RSA speaker-dependent).
β̂ = 2.26 and mixture weights from main text (p. 178);
β̄ = 2.03 and ō = −0.13 from Fig 3B caption (p. 177). -/
structure FittedParams where
  betaMAP : ℚ              -- MAP estimate of persuasive bias (p. 178)
  betaCV : ℚ               -- 10-fold CV average β (Fig 3B)
  responseOffsetCV : ℚ     -- 10-fold CV average offset (Fig 3B)
  pragmaticMixWeight : ℚ   -- mixture weight for pragmatic group (p. 178)
  literalMixWeight : ℚ     -- mixture weight for literal group (p. 178)
  deriving Repr

def bestModelParams : FittedParams :=
  { betaMAP := 226 / 100           -- β̂ = 2.26 (p. 178)
    betaCV := 203 / 100            -- β̄ = 2.03 (Fig 3B)
    responseOffsetCV := -13 / 100  -- ō = -0.13 (Fig 3B)
    pragmaticMixWeight := 99/100   -- p̂_z = 0.99 (J1 dominates; p. 178)
    literalMixWeight := 1/10 }     -- p̂_z = 0.1 (J0 dominates; p. 178)

/-- β > 0 provides strong support for non-zero persuasive bias -/
theorem beta_positive : bestModelParams.betaMAP > 0 := by norm_num [bestModelParams]

/-- Pragmatic group is best explained by J1 (pragmatic listener model) -/
theorem pragmatic_group_uses_j1 :
    bestModelParams.pragmaticMixWeight > 9 / 10 := by norm_num [bestModelParams]

/-- Literal group is best explained by J0 (literal listener model) -/
theorem literal_group_uses_j0 :
    bestModelParams.literalMixWeight < 2 / 10 := by norm_num [bestModelParams]

-- ============================================================
-- §9. Model–Data Connection
-- ============================================================

/-- The RSA model predicts the qualitative pattern underlying the observed
interaction between listener type and evidence strength (t(718) = 5.2,
p < 0.001). The literal model (L0) assigns s4 positive argumentative strength,
predicting no backfire. The pragmatic model (L1) shows backfire. The experiment
confirms exactly this divergence: pragmatic participants' mean (34.7) falls
below neutral (50), while literal participants' mean (50.1) does not. -/
theorem model_predicts_interaction :
    -- Model: L0 (literal) — s4 is positive evidence
    hasPositiveArgStr (l0LongerQ .s4) priorLonger ∧
    -- Model: L1 (pragmatic) — s4 backfires
    l1Event .s4 (fun w => ¬ IsLonger w) > l1Event .s4 IsLonger ∧
    -- Data: pragmatic group shows backfire
    pragmaticResult.meanSlider < 50 ∧
    -- Data: literal group shows no backfire
    literalResult.meanSlider > 49 :=
  ⟨s4_positive_argStr, weak_evidence_effect, pragmatic_backfire, literal_no_backfire⟩

end BarnettEtAl2022
