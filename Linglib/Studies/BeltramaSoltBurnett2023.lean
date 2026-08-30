import Linglib.Semantics.Quantification.Numerals.Roundness
import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Linglib.Semantics.Quantification.Numerals.Precision
import Linglib.Pragmatics.SocialMeaning.SCM
import Linglib.Pragmatics.SocialMeaning.EckertMontague
import Linglib.Fragments.English.NumeralModifiers
import Mathlib.Tactic.NormNum

/-!
# Context, precision, and social perception

Formalization of [beltrama-solt-burnett-2023] (Language in Society 52). Two social-perception
experiments compare three precision variants — precise "forty-nine minutes", underspecified
"fifty minutes", approximate "about fifty minutes" — across four communicative scenarios.
Ratings on ten scales reduce by PCA to Status, Solidarity, and anti-Solidarity; precise
variants are rated above approximate on Status and anti-Solidarity and below on Solidarity,
and the underspecified variant patterns with precise on Status, with approximate on
anti-Solidarity, and in between on Solidarity — precision and approximation emerge as separate
indexical loci. Scenario modulates the contrasts: the Status edge of precision is amplified
where descriptive accuracy matters and neutralized in bonding contexts, while Solidarity
contrasts sharpen where precision is pragmatically idle.

## Main definitions

* `Variant`, `classifyVariant` — the three-way contrast, derived from the substrate roundness
  score plus the presence of a tolerance modifier.
* `exp1Mean`, `exp2Mean` — the per-dimension cell means (Experiment 1: 216 recruited, 61
  excluded, within-subjects; Experiment 2: 960 recruited, 150 excluded, one-trial
  between-subjects).
* `bsbField` — the sign-valued indexical field, `0` on the underspecified variant (the
  neutral-diagnostic reading of the general discussion); `bsbGroundedField` — its
  [burnett-2019] Eckert–Montague lift.

## Main results

* `sign_alignment`, `opposite_directions` — the core sign structure: Status and
  anti-Solidarity favor precise, Solidarity reverses; precise and approximate are antipodal.
* `underspec_near_precise_on_competence`, `underspec_near_approx_on_antiSol`,
  `underspec_intermediate_on_warmth`, `diagnostic_crossover` — the underspecified diagnostic
  (pp. 827–828).
* `competence_enhanced_in_high_demand`, `warmth_enhanced_in_low_demand`, `context_crossover` —
  scenario modulation of the Status and Solidarity contrasts.
* `non_round_collapses`, `round_supports_contrast` — roundness gates the three-way contrast.
* `underspecified_indexes_nothing` — under the EM lift the underspecified variant is
  compatible with every persona.

## References

* [beltrama-solt-burnett-2023] — the paper; [beltrama-2018] — the sharp/round predecessor.
* [eckert-2008], [fiske-cuddy-glick-2007] — indexical fields and the evaluation dimensions.
* [burnett-2019] — the Eckert–Montague lift; [krifka-2007] — round-number approximation;
  [campbell-kibler-2011] — the neutral-variant diagnostic precedent.
-/

namespace BeltramaSoltBurnett2023

open SocialMeaning.IndexicalField
open SocialMeaning.SCM

/-! ### Stimuli and the three-way contrast -/

/-- The three precision variants ("The Precision manipulation"): a sharp number, a bare round
    number, and a round number under an approximator. -/
inductive Variant where
  /-- Sharp number: "forty-nine minutes". -/
  | precise
  /-- Bare round number: "fifty minutes". -/
  | underspecified
  /-- Modified round number: "about fifty minutes". -/
  | approximate
  deriving DecidableEq, Repr

/-- The precise stimulus numeral (sharp, non-round). -/
def stimPrecise : Nat := 49

/-- The round stimulus numeral (used bare or with "about"). -/
def stimRound : Nat := 50

/-- 49 has zero roundness — no imprecise reading is possible. -/
theorem stim_precise_not_round :
    Semantics.Numerals.Roundness.roundnessScore stimPrecise = 0 := by decide

/-- 50 is highly round (score 5) — imprecise readings are available. -/
theorem stim_round_is_round :
    Semantics.Numerals.Roundness.roundnessScore stimRound = 5 := by decide

open Semantics.Numerals.Precision in
/-- 49 gets the exact precision mode. -/
theorem precise_stim_is_exact :
    inferPrecisionMode stimPrecise = .exact := by decide

open Semantics.Numerals.Precision in
/-- 50 gets the approximate precision mode. -/
theorem round_stim_is_approximate :
    inferPrecisionMode stimRound = .approximate := by decide

open English.NumeralModifiers in
/-- The Fragment entry "about" is a tolerance modifier: it forces an approximate reading and
    conveys a peaked distribution shape. -/
theorem about_is_tolerance_modifier :
    about.modType = .tolerance ∧ about.conveysShape = true ∧
    about.pragFunction = .peakedSignal := ⟨rfl, rfl, rfl⟩

/-- Classify a numeral into a variant from the substrate roundness score and the presence of a
    tolerance modifier: non-round is `.precise` regardless of modifier; round is
    `.underspecified` bare and `.approximate` under a modifier. -/
def classifyVariant (n : Nat) (hasToleranceModifier : Bool) : Variant :=
  if Semantics.Numerals.Roundness.roundnessScore n < 2 then .precise
  else if hasToleranceModifier then .approximate
  else .underspecified

/-- "forty-nine minutes" is the precise variant. -/
theorem classify_49 :
    classifyVariant stimPrecise false = .precise := by decide

/-- Bare "fifty minutes" is the underspecified variant. -/
theorem classify_50_bare :
    classifyVariant stimRound false = .underspecified := by decide

/-- "about fifty minutes" is the approximate variant. -/
theorem classify_50_about :
    classifyVariant stimRound true = .approximate := by decide

/-- Non-round numerals collapse the three-way contrast to `.precise`: nothing is left for
    social perception to modulate. -/
theorem non_round_collapses (n : Nat)
    (h : Semantics.Numerals.Roundness.roundnessScore n < 2) :
    classifyVariant n true = .precise ∧ classifyVariant n false = .precise := by
  unfold classifyVariant; constructor <;> simp [if_pos h]

/-- Round numerals support the full three-way contrast: bare is underspecified, modified is
    approximate. -/
theorem round_supports_contrast (n : Nat)
    (h : Semantics.Numerals.Roundness.roundnessScore n ≥ 2) :
    classifyVariant n false = .underspecified ∧
    classifyVariant n true = .approximate := by
  have h' : ¬(Semantics.Numerals.Roundness.roundnessScore n < 2) := by omega
  unfold classifyVariant; constructor <;> simp [if_neg h']

/-! ### Cell means -/

/-- Experiment 1 cell means (216 recruited, 61 excluded; within-subjects; 7-point scales).
    PCA factors mapped onto `SocialDimension`: Status → `.competence`, Solidarity →
    `.warmth`, anti-Solidarity → `.antiSolidarity`. -/
def exp1Mean : Variant → SocialDimension → ℚ
  | .precise,       .competence      => 501/100  -- M = 5.01, SD = 0.95
  | .precise,       .warmth          => 437/100  -- M = 4.37, SD = 1.08
  | .precise,       .antiSolidarity  => 437/100  -- M = 4.37, SD = 1.22
  | .underspecified, .competence     => 496/100  -- M = 4.96, SD = 0.99
  | .underspecified, .warmth         => 449/100  -- M = 4.49, SD = 1.00
  | .underspecified, .antiSolidarity => 419/100  -- M = 4.19, SD = 1.24
  | .approximate,   .competence      => 484/100  -- M = 4.84, SD = 0.99
  | .approximate,   .warmth          => 458/100  -- M = 4.58, SD = 0.99
  | .approximate,   .antiSolidarity  => 410/100  -- M = 4.10, SD = 1.24

/-- Experiment 2 cell means (960 recruited, 150 excluded; one-trial between-subjects). -/
def exp2Mean : Variant → SocialDimension → ℚ
  | .precise,       .competence      => 516/100  -- M = 5.16, SD = 0.82
  | .precise,       .warmth          => 415/100  -- M = 4.15, SD = 0.97
  | .precise,       .antiSolidarity  => 385/100  -- M = 3.85, SD = 1.05
  | .underspecified, .competence     => 506/100  -- M = 5.06, SD = 0.73
  | .underspecified, .warmth         => 460/100  -- M = 4.60, SD = 0.90
  | .underspecified, .antiSolidarity => 359/100  -- M = 3.59, SD = 1.14
  | .approximate,   .competence      => 490/100  -- M = 4.90, SD = 0.85
  | .approximate,   .warmth          => 484/100  -- M = 4.84, SD = 0.85
  | .approximate,   .antiSolidarity  => 349/100  -- M = 3.49, SD = 1.13

/-! ### The core indexical orderings (replicated across both experiments) -/

/-- Status: precise above approximate in both experiments (5.01 > 4.84; 5.16 > 4.90). -/
theorem competence_precise_gt_approx :
    exp1Mean .precise .competence > exp1Mean .approximate .competence ∧
    exp2Mean .precise .competence > exp2Mean .approximate .competence := by
  norm_num [exp1Mean, exp2Mean]

/-- Solidarity: approximate above precise in both experiments (4.58 > 4.37; 4.84 > 4.15). -/
theorem warmth_approx_gt_precise :
    exp1Mean .approximate .warmth > exp1Mean .precise .warmth ∧
    exp2Mean .approximate .warmth > exp2Mean .precise .warmth := by
  norm_num [exp1Mean, exp2Mean]

/-- Anti-Solidarity: precise above approximate in both experiments (4.37 > 4.10;
    3.85 > 3.49). -/
theorem antiSol_precise_gt_approx :
    exp1Mean .precise .antiSolidarity > exp1Mean .approximate .antiSolidarity ∧
    exp2Mean .precise .antiSolidarity > exp2Mean .approximate .antiSolidarity := by
  norm_num [exp1Mean, exp2Mean]

/-- Sign alignment: Status and anti-Solidarity share direction (both favor precise) while
    Solidarity reverses — the core sign structure of the precision indexical field. -/
theorem sign_alignment :
    (exp1Mean .precise .competence > exp1Mean .approximate .competence ∧
     exp1Mean .precise .antiSolidarity > exp1Mean .approximate .antiSolidarity ∧
     exp1Mean .approximate .warmth > exp1Mean .precise .warmth) ∧
    (exp2Mean .precise .competence > exp2Mean .approximate .competence ∧
     exp2Mean .precise .antiSolidarity > exp2Mean .approximate .antiSolidarity ∧
     exp2Mean .approximate .warmth > exp2Mean .precise .warmth) := by
  norm_num [exp1Mean, exp2Mean]

/-! ### The three-way indexical field -/

/-- The three-way indexical field: idealized signs (±1) matching the ordering theorems above,
    with `0` on the underspecified variant. The `0` encodes the neutral-diagnostic reading of
    the general discussion (p. 828), on which the underspecified variant reveals which
    endpoint drives each contrast; the paper's alternative — round numbers carrying their own
    chameleonic indexicality — is not modeled. -/
def bsbField : IndexicalField Variant SocialDimension :=
  { association := λ v d => match v, d with
    | .precise,       .competence      =>  1
    | .precise,       .warmth          => -1
    | .precise,       .antiSolidarity  =>  1
    | .approximate,   .competence      => -1
    | .approximate,   .warmth          =>  1
    | .approximate,   .antiSolidarity  => -1
    | .underspecified, _               =>  0
  , order := .third }

/-- Precise and approximate are antipodal: algebraically opposite associations on
    every dimension. -/
theorem opposite_directions : bsbField.Antipodal .precise .approximate := by
  intro d; cases d <;> simp [bsbField]

/-! ### The underspecified diagnostic (pp. 827–828)

The underspecified variant does not sit uniformly between the endpoints: it clusters with
precise on Status (an approximation-driven downgrade), with approximate on anti-Solidarity
(a precision-driven increase), and strictly between the two on Solidarity (both forces pull).
The paper's clustering criterion is significance patterning; the mean-gap comparisons below
align with it in every cell. -/

/-- On Status the underspecified variant is closer to precise than to approximate: the
    contrast is approximation-driven (0.05 vs. 0.12 in Experiment 1; 0.10 vs. 0.16 in
    Experiment 2). -/
theorem underspec_near_precise_on_competence :
    (exp1Mean .precise .competence - exp1Mean .underspecified .competence <
     exp1Mean .underspecified .competence - exp1Mean .approximate .competence) ∧
    (exp2Mean .precise .competence - exp2Mean .underspecified .competence <
     exp2Mean .underspecified .competence - exp2Mean .approximate .competence) := by
  norm_num [exp1Mean, exp2Mean]

/-- On anti-Solidarity the underspecified variant is closer to approximate than to precise:
    the contrast is precision-driven (0.09 vs. 0.18; 0.10 vs. 0.26). -/
theorem underspec_near_approx_on_antiSol :
    (exp1Mean .underspecified .antiSolidarity - exp1Mean .approximate .antiSolidarity <
     exp1Mean .precise .antiSolidarity - exp1Mean .underspecified .antiSolidarity) ∧
    (exp2Mean .underspecified .antiSolidarity - exp2Mean .approximate .antiSolidarity <
     exp2Mean .precise .antiSolidarity - exp2Mean .underspecified .antiSolidarity) := by
  norm_num [exp1Mean, exp2Mean]

/-- On Solidarity the underspecified variant falls strictly between precise and approximate —
    significantly in both directions in Experiment 2, as a trend in Experiment 1 (p. 826):
    precision and approximation pull it in opposite directions. -/
theorem underspec_intermediate_on_warmth :
    (exp1Mean .precise .warmth < exp1Mean .underspecified .warmth ∧
     exp1Mean .underspecified .warmth < exp1Mean .approximate .warmth) ∧
    (exp2Mean .precise .warmth < exp2Mean .underspecified .warmth ∧
     exp2Mean .underspecified .warmth < exp2Mean .approximate .warmth) := by
  norm_num [exp1Mean, exp2Mean]

/-- The crossover that makes the underspecified variant diagnostic: the small gap sits on the
    precise side for Status but on the approximate side for anti-Solidarity. -/
theorem diagnostic_crossover :
    (exp1Mean .precise .competence - exp1Mean .underspecified .competence <
     exp1Mean .underspecified .competence - exp1Mean .approximate .competence) ∧
    (exp1Mean .underspecified .antiSolidarity - exp1Mean .approximate .antiSolidarity <
     exp1Mean .precise .antiSolidarity - exp1Mean .underspecified .antiSolidarity) := by
  norm_num [exp1Mean]

/-! ### Scenario modulation -/

/-- Communicative scenario ("The Scenario manipulation"). -/
inductive Scenario where
  /-- Testifying for the official record. -/
  | forTheRecord
  /-- Persuading an interlocutor to act. -/
  | persuasion
  /-- Small talk with a stranger. -/
  | stranger
  /-- Getting to know new colleagues. -/
  | bonding
  deriving DecidableEq, Repr

/-- Binary precision demand, the split the results discussion works with. -/
inductive PrecisionDemand where
  | high
  | low
  deriving DecidableEq, Repr

/-- The paper's four-point precision-need ordering: highest (For-the-record), medium
    (Persuasion), low (Stranger), lowest (Bonding). -/
def Scenario.precisionNeed : Scenario → ℕ
  | .forTheRecord => 3
  | .persuasion   => 2
  | .stranger     => 1
  | .bonding      => 0

/-- Binary demand, derived from the four-point ordering rather than stipulated per cell. -/
def Scenario.precisionDemand (s : Scenario) : PrecisionDemand :=
  if 2 ≤ s.precisionNeed then .high else .low

example :
    Scenario.forTheRecord.precisionDemand = .high ∧
      Scenario.persuasion.precisionDemand = .high ∧
        Scenario.stranger.precisionDemand = .low ∧
          Scenario.bonding.precisionDemand = .low := by decide

/-- Experiment 1 Status means for the For-the-record/Bonding × precise/approximate
    interaction cells (p. 816). Non-tabulated cells default to `0` and are cited by no
    theorem. -/
def exp1CompetenceByScenario : Scenario → Variant → ℚ
  | .forTheRecord, .precise     => 513/100  -- M = 5.13, SD = 1.02
  | .forTheRecord, .approximate => 474/100  -- M = 4.74, SD = 0.97
  | .bonding,      .precise     => 493/100  -- M = 4.93, SD = 0.96
  | .bonding,      .approximate => 495/100  -- M = 4.95, SD = 0.96
  | _, _                        => 0

/-- The Status contrast is amplified under high demand: 0.39 points in For-the-record,
    vanishing (−0.02) in Bonding (pp. 816, 829–830). -/
theorem competence_enhanced_in_high_demand :
    exp1CompetenceByScenario .forTheRecord .precise -
    exp1CompetenceByScenario .forTheRecord .approximate >
    exp1CompetenceByScenario .bonding .precise -
    exp1CompetenceByScenario .bonding .approximate := by
  norm_num [exp1CompetenceByScenario]

/-- In Bonding the Status contrast is neutralized: approximate is not below precise. -/
theorem competence_neutralized_in_bonding :
    exp1CompetenceByScenario .bonding .approximate ≥
    exp1CompetenceByScenario .bonding .precise := by
  norm_num [exp1CompetenceByScenario]

/-- Experiment 2 Solidarity means for the Stranger/For-the-record × precise/underspecified
    interaction cells — the re-leveled interaction reported in the text (p. 823).
    Non-tabulated cells default to `0` and are cited by no theorem. -/
def exp2WarmthByScenario : Scenario → Variant → ℚ
  | .stranger,     .precise        => 434/100  -- M = 4.34, SD = 1.01
  | .stranger,     .underspecified => 478/100  -- M = 4.78, SD = 0.77
  | .forTheRecord, .precise        => 388/100  -- M = 3.88, SD = 0.95
  | .forTheRecord, .underspecified => 389/100  -- M = 3.89, SD = 0.71
  | _, _                           => 0

/-- The Solidarity contrast is amplified under low demand: 0.44 points in Stranger,
    vanishing (0.01) in For-the-record (pp. 823, 826). -/
theorem warmth_enhanced_in_low_demand :
    exp2WarmthByScenario .stranger .underspecified -
    exp2WarmthByScenario .stranger .precise >
    exp2WarmthByScenario .forTheRecord .underspecified -
    exp2WarmthByScenario .forTheRecord .precise := by
  norm_num [exp2WarmthByScenario]

/-- Bidirectional modulation: high demand amplifies the Status contrast, low demand the
    Solidarity contrast — which region of the field is activated depends on the
    communicative situation. -/
theorem context_crossover :
    (exp1CompetenceByScenario .forTheRecord .precise -
     exp1CompetenceByScenario .forTheRecord .approximate >
     exp1CompetenceByScenario .bonding .precise -
     exp1CompetenceByScenario .bonding .approximate) ∧
    (exp2WarmthByScenario .stranger .underspecified -
     exp2WarmthByScenario .stranger .precise >
     exp2WarmthByScenario .forTheRecord .underspecified -
     exp2WarmthByScenario .forTheRecord .precise) := by
  norm_num [exp1CompetenceByScenario, exp2WarmthByScenario]

/-! ### The Eckert–Montague lift -/

open SocialMeaning.EckertMontague

/-- The field as a [burnett-2019] grounded field over the SCM property space. -/
def bsbGroundedField : GroundedField Variant scmSpace :=
  fromIndexicalField bsbField

/-- Precise speech indexes {competent, cold, antiSolidary}. -/
theorem precise_scmProperties :
    bsbGroundedField.indexedProperties .precise =
      {.competent, .cold, .antiSolidary} := by
  decide

/-- Approximate speech indexes the complement, {incompetent, warm, solidary}. -/
theorem approximate_scmProperties :
    bsbGroundedField.indexedProperties .approximate =
      {.incompetent, .warm, .solidary} := by
  decide

/-- The underspecified variant indexes nothing, so under the EM lift it is compatible with
    every persona — the neutral-diagnostic reading made structural. -/
theorem underspecified_indexes_nothing :
    bsbGroundedField.indexedProperties .underspecified = ∅ := by
  decide

end BeltramaSoltBurnett2023
