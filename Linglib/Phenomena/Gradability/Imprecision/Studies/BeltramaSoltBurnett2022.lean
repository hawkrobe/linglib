import Linglib.Core.Roundness
import Linglib.Core.SocialMeaning
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Fragments.English.NumeralModifiers

/-!
# Beltrama, Solt & Burnett (2022) @cite{beltrama-solt-burnett-2022}

Context, precision, and social perception: A sociopragmatic study.
*Language in Society* 52(5): 805–835. doi:10.1017/S0047404522000240

Two experiments (Exp 1: N=72 within-subjects; Exp 2: N=400 between-subjects)
examining how numeral precision affects social perception across three
PCA-derived evaluation dimensions and four communicative scenarios.

## Core contributions

1. **Three-way variant contrast**: Distinguishes precise ("forty-nine"),
   underspecified ("fifty"), and explicitly approximate ("about fifty") —
   extending prior work that only compared sharp vs. round numbers.

2. **Core indexical ordering** (robust across both experiments):
   - Competence/Status: precise ≥ underspecified > approximate
   - Warmth/Solidarity: approximate ≥ underspecified > precise
   - Anti-Solidarity: precise > underspecified ≈ approximate

3. **Underspecified as diagnostic** (§General Discussion, p. 827–828):
   bare round numbers don't uniformly pattern with either endpoint. On
   competence, underspecified hugs precise; on anti-solidarity, it hugs
   approximate; on warmth, it is genuinely intermediate. This reveals
   precision and approximation as independent indexical loci
   (Campbell-Kibler 2011).

4. **Context modulation**: high-precision-demand scenarios (For-the-record,
   Persuasion) amplify competence contrasts; low-demand scenarios (Bonding,
   Stranger) amplify warmth/solidarity contrasts.

## Fragment connections

Stimuli use numerals 49 (precise) and 50 (round), with "about" as the
tolerance modifier:
- `Core.Roundness.roundnessScore`: 49 → 0, 50 → 4
- `Semantics.Lexical.Numeral.Precision.inferPrecisionMode`: 49 → .exact,
  50 → .approximate
- `Fragments.English.NumeralModifiers.about`: tolerance modifier

## References

* Beltrama, A., Solt, S. & Burnett, H. (2022). Context, precision, and
  social perception. *Language in Society* 52(5): 805–835.
* Campbell-Kibler, K. (2011). Sociolinguistic variables and perception.
  *Language and Linguistics Compass* 5(8): 1–14.
* Fiske, S. T., Cuddy, A. J. C. & Glick, P. (2007). Universal dimensions
  of social cognition: Warmth and competence. *TICS* 11(2): 77–83.
-/

namespace Phenomena.Gradability.Imprecision.Studies.BeltramaSoltBurnett2022

open Core.SocialMeaning

-- ============================================================================
-- §1. Three-way precision variant
-- ============================================================================

/-- The three precision variants for numeral use (BSB2022 §3).

    Extends the two-way distinction (exact/approximate) in Beltrama & Schwarz
    (2024) by factoring out bare round numerals as a third, diagnostically
    crucial category. -/
inductive Variant where
  | precise        -- sharp number: "forty-nine minutes"
  | underspecified -- bare round number: "fifty minutes"
  | approximate    -- modified round number: "about fifty minutes"
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2. Stimuli and Fragment connections
-- ============================================================================

/-- The precise stimulus numeral (sharp, non-round). -/
def stimPrecise : Nat := 49

/-- The round stimulus numeral (used bare or with "about"). -/
def stimRound : Nat := 50

/-- 49 has zero roundness — no imprecise reading is possible. -/
theorem stim_precise_not_round :
    Core.Roundness.roundnessScore stimPrecise = 0 := by native_decide

/-- 50 has moderate roundness (score 4) — imprecise readings available. -/
theorem stim_round_is_round :
    Core.Roundness.roundnessScore stimRound = 4 := by native_decide

open Semantics.Lexical.Numeral.Precision in
/-- 49 → exact precision mode (roundnessScore 0 < 2). -/
theorem precise_stim_is_exact :
    inferPrecisionMode stimPrecise = .exact := by native_decide

open Semantics.Lexical.Numeral.Precision in
/-- 50 → approximate precision mode (roundnessScore 4 ≥ 2). -/
theorem round_stim_is_approximate :
    inferPrecisionMode stimRound = .approximate := by native_decide

open Fragments.English.NumeralModifiers in
/-- The Fragment entry "about" is a tolerance modifier that forces an
    approximate reading and conveys a peaked distribution shape. -/
theorem about_is_tolerance_modifier :
    about.modType = .tolerance ∧ about.conveysShape = true ∧
    about.pragFunction = .peakedSignal := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §3. Variant classification from Fragment properties
-- ============================================================================

/-- Classify a numeral into a variant based on roundness and modifier presence.

    End-to-end derivation chain:
      Fragment modifier type + Core.Roundness score → Variant.

    - Non-round (score < 2): `.precise` regardless of modifier
    - Round + no modifier: `.underspecified` (imprecision available, not forced)
    - Round + tolerance modifier: `.approximate` (imprecision forced) -/
def classifyVariant (n : Nat) (hasToleranceModifier : Bool) : Variant :=
  if Core.Roundness.roundnessScore n < 2 then .precise
  else if hasToleranceModifier then .approximate
  else .underspecified

/-- "forty-nine minutes" → precise variant. -/
theorem classify_49 :
    classifyVariant stimPrecise false = .precise := by native_decide

/-- "fifty minutes" (bare) → underspecified variant. -/
theorem classify_50_bare :
    classifyVariant stimRound false = .underspecified := by native_decide

/-- "about fifty minutes" → approximate variant. -/
theorem classify_50_about :
    classifyVariant stimRound true = .approximate := by native_decide

-- ============================================================================
-- §4. Experimental data: cell means (7-point Likert scale)
-- ============================================================================

/-- Experiment 1 (within-subjects, N=72) cell means.
    PCA factor scores mapped to `SocialDimension`:
    Status → `.competence`, Solidarity → `.warmth`,
    Anti-Solidarity → `.antiSolidarity`. -/
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

/-- Experiment 2 (between-subjects, N=400) cell means. -/
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

-- ============================================================================
-- §5. Core indexical orderings (replicated across both experiments)
-- ============================================================================

/-- **Competence: precise > approximate** (both experiments).

    Speakers using sharp numbers are perceived as more articulate, intelligent,
    confident, and trustworthy than those using explicitly approximate numbers.
    Exp 1: 5.01 > 4.84; Exp 2: 5.16 > 4.90. -/
theorem competence_precise_gt_approx :
    exp1Mean .precise .competence > exp1Mean .approximate .competence ∧
    exp2Mean .precise .competence > exp2Mean .approximate .competence := by
  constructor <;> native_decide

/-- **Warmth: approximate > precise** (both experiments).

    Speakers using "about fifty" are perceived as friendlier, cooler, more
    laid-back, and more likeable than those using "forty-nine."
    Exp 1: 4.58 > 4.37; Exp 2: 4.84 > 4.15. -/
theorem warmth_approx_gt_precise :
    exp1Mean .approximate .warmth > exp1Mean .precise .warmth ∧
    exp2Mean .approximate .warmth > exp2Mean .precise .warmth := by
  constructor <;> native_decide

/-- **Anti-Solidarity: precise > approximate** (both experiments).

    Speakers using sharp numbers are perceived as more pedantic and uptight.
    Exp 1: 4.37 > 4.10; Exp 2: 3.85 > 3.49. -/
theorem antiSol_precise_gt_approx :
    exp1Mean .precise .antiSolidarity > exp1Mean .approximate .antiSolidarity ∧
    exp2Mean .precise .antiSolidarity > exp2Mean .approximate .antiSolidarity := by
  constructor <;> native_decide

/-- **Sign alignment**: competence and anti-solidarity share sign direction
    (both favor precise), while warmth reverses (favors approximate).

    This is the core sign structure of the precision indexical field. It is
    consistent with the `precisionField` associations in Beltrama & Schwarz
    (2024), where `.exact → .competence = +1`, `.exact → .warmth = −1`,
    and `.exact → .antiSolidarity = +1`. -/
theorem sign_alignment :
    (exp1Mean .precise .competence > exp1Mean .approximate .competence ∧
     exp1Mean .precise .antiSolidarity > exp1Mean .approximate .antiSolidarity ∧
     exp1Mean .approximate .warmth > exp1Mean .precise .warmth) ∧
    (exp2Mean .precise .competence > exp2Mean .approximate .competence ∧
     exp2Mean .precise .antiSolidarity > exp2Mean .approximate .antiSolidarity ∧
     exp2Mean .approximate .warmth > exp2Mean .precise .warmth) := by
  constructor <;> refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §6. Three-way indexical field
-- ============================================================================

/-- The three-way indexical field for numeral precision (BSB2022).

    Association values are idealized signs (±1) matching the empirical ordering
    from §5. The underspecified variant gets 0 (neutral) — the diagnostic
    theorem (§7) shows its empirical position varies by dimension.

    The precise/approximate cells have the same signs as B&S 2024's
    `precisionField` on all three social dimensions. -/
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

/-- Precise and approximate have algebraically opposite associations on
    every dimension — the same anti-symmetry as B&S 2024's `opposite_directions`. -/
theorem opposite_directions (d : SocialDimension) :
    bsbField.association .precise d = - bsbField.association .approximate d := by
  cases d <;> simp [bsbField]

-- ============================================================================
-- §7. Underspecified diagnostic
-- ============================================================================

/-! **Underspecified diagnostic** (BSB2022's deepest contribution, p. 827–828).

On each dimension, the underspecified variant does not sit uniformly
between precise and approximate. Its proximity to each endpoint varies
by dimension, revealing precision and approximation as independent
indexical loci (Campbell-Kibler 2011).

The interpretation (p. 827): when underspecified clusters with precise
and away from approximate, the contrast is *approximation-driven* (it is
approximation that downgrades the trait). When underspecified clusters
with approximate and away from precise, the contrast is *precision-driven*
(it is precision that upgrades the trait). -/

/-- On competence, underspecified is closer to precise than to approximate.
    The contrast is approximation-driven: it is "about" that downgrades Status,
    not sharp numbers that upgrade it.
    Exp 1: |5.01−4.96| = 0.05 < |4.96−4.84| = 0.12.
    Exp 2: |5.16−5.06| = 0.10 < |5.06−4.90| = 0.16. -/
theorem underspec_near_precise_on_competence :
    (exp1Mean .precise .competence - exp1Mean .underspecified .competence <
     exp1Mean .underspecified .competence - exp1Mean .approximate .competence) ∧
    (exp2Mean .precise .competence - exp2Mean .underspecified .competence <
     exp2Mean .underspecified .competence - exp2Mean .approximate .competence) := by
  constructor <;> native_decide

/-- On anti-solidarity, underspecified is closer to approximate than to precise.
    The contrast is precision-driven: it is sharp numbers that make you seem
    pedantic, not "about" that makes you seem relaxed.
    Exp 1: |4.19−4.10| = 0.09 < |4.37−4.19| = 0.18.
    Exp 2: |3.59−3.49| = 0.10 < |3.85−3.59| = 0.26. -/
theorem underspec_near_approx_on_antiSol :
    (exp1Mean .underspecified .antiSolidarity - exp1Mean .approximate .antiSolidarity <
     exp1Mean .precise .antiSolidarity - exp1Mean .underspecified .antiSolidarity) ∧
    (exp2Mean .underspecified .antiSolidarity - exp2Mean .approximate .antiSolidarity <
     exp2Mean .precise .antiSolidarity - exp2Mean .underspecified .antiSolidarity) := by
  constructor <;> native_decide

/-- On warmth, underspecified is genuinely intermediate: it falls strictly
    between precise and approximate in both experiments. Both precision and
    approximation contribute independently to the Solidarity contrast,
    pulling underspecified in opposite directions. -/
theorem underspec_intermediate_on_warmth :
    (exp1Mean .precise .warmth < exp1Mean .underspecified .warmth ∧
     exp1Mean .underspecified .warmth < exp1Mean .approximate .warmth) ∧
    (exp2Mean .precise .warmth < exp2Mean .underspecified .warmth ∧
     exp2Mean .underspecified .warmth < exp2Mean .approximate .warmth) := by
  constructor <;> constructor <;> native_decide

/-- **Diagnostic asymmetry**: the dimension on which underspecified is closest
    to each endpoint differs. On competence, the cluster gap (precise to
    underspecified) is smaller than the outlier gap; on anti-solidarity, the
    reverse. This crossover is what makes underspecified diagnostic.

    Formalized as: the ratio of within-cluster to between-cluster gap
    reverses between competence and anti-solidarity. -/
theorem diagnostic_crossover :
    -- On competence: precise-to-underspec < underspec-to-approx
    (exp1Mean .precise .competence - exp1Mean .underspecified .competence <
     exp1Mean .underspecified .competence - exp1Mean .approximate .competence) ∧
    -- On anti-solidarity: approx-to-underspec < underspec-to-precise (reversed!)
    (exp1Mean .underspecified .antiSolidarity - exp1Mean .approximate .antiSolidarity <
     exp1Mean .precise .antiSolidarity - exp1Mean .underspecified .antiSolidarity) := by
  constructor <;> native_decide

-- ============================================================================
-- §8. Context modulation
-- ============================================================================

/-- Communicative scenario (BSB2022 §3.1). -/
inductive Scenario where
  | forTheRecord  -- job interview: "how long is your commute?"
  | persuasion    -- convincing friend: "it only adds X minutes"
  | stranger      -- chatting at bar: "how long have you lived here?"
  | bonding       -- new friend: "how long have you been at this job?"
  deriving DecidableEq, BEq, Repr

/-- Precision demand level of a communicative scenario. -/
inductive PrecisionDemand where
  | high  -- descriptive accuracy serves communicative goal
  | low   -- socializing; precision is irrelevant
  deriving DecidableEq, BEq, Repr

def Scenario.precisionDemand : Scenario → PrecisionDemand
  | .forTheRecord => .high
  | .persuasion   => .high
  | .stranger     => .low
  | .bonding      => .low

/-- Exp 1 scenario-specific means on competence (Status).
    For-the-record vs Bonding, precise vs approximate. -/
def exp1CompetenceByScenario : Scenario → Variant → ℚ
  | .forTheRecord, .precise   => 513/100  -- M = 5.13, SD = 1.02
  | .forTheRecord, .approximate => 474/100  -- M = 4.74, SD = 0.97
  | .bonding,      .precise   => 493/100  -- M = 4.93, SD = 0.96
  | .bonding,      .approximate => 495/100  -- M = 4.95, SD = 0.96
  | _, _                      => 0

/-- **Context amplifies competence contrast in high-demand scenarios.**

    Exp 1, Status: In For-the-record (high demand), precise is rated 0.39
    points above approximate. In Bonding (low demand), the gap vanishes
    (−0.02). The Status advantage of precision is contextually relevant
    only when descriptive accuracy matters (BSB2022 p. 830). -/
theorem competence_enhanced_in_high_demand :
    exp1CompetenceByScenario .forTheRecord .precise -
    exp1CompetenceByScenario .forTheRecord .approximate >
    exp1CompetenceByScenario .bonding .precise -
    exp1CompetenceByScenario .bonding .approximate := by
  native_decide

/-- In Bonding, the competence contrast is neutralized: approximate ≥ precise. -/
theorem competence_neutralized_in_bonding :
    exp1CompetenceByScenario .bonding .approximate ≥
    exp1CompetenceByScenario .bonding .precise := by
  native_decide

/-- Exp 2 scenario-specific means on warmth (Solidarity).
    Stranger vs For-the-record, precise vs underspecified (the significant
    interaction from Table 4 row 9 re-leveled, p. 823). -/
def exp2WarmthByScenario : Scenario → Variant → ℚ
  | .stranger,     .precise        => 434/100  -- M = 4.34, SD = 1.01
  | .stranger,     .underspecified  => 478/100  -- M = 4.78, SD = 0.77
  | .forTheRecord, .precise        => 388/100  -- M = 3.88, SD = 0.95
  | .forTheRecord, .underspecified  => 389/100  -- M = 3.89, SD = 0.71
  | _, _                           => 0

/-- **Context amplifies warmth contrast in low-demand scenarios.**

    Exp 2, Solidarity: In Stranger (low demand), underspecified is rated 0.44
    points above precise. In For-the-record (high demand), the gap vanishes
    (0.01). When precision is communicatively irrelevant, the Solidarity
    penalty of sharp numbers becomes salient (BSB2022 p. 826). -/
theorem warmth_enhanced_in_low_demand :
    exp2WarmthByScenario .stranger .underspecified -
    exp2WarmthByScenario .stranger .precise >
    exp2WarmthByScenario .forTheRecord .underspecified -
    exp2WarmthByScenario .forTheRecord .precise := by
  native_decide

/-- **Bidirectional context modulation**: high-demand contexts amplify
    competence contrasts while suppressing warmth contrasts, and vice versa.

    This crossover interaction between precision demand and social dimension
    composes `Scenario.precisionDemand` with the dimension-specific indexical
    field: which region of the field is activated depends on the communicative
    situation. -/
theorem context_crossover :
    -- High demand amplifies competence contrast
    (exp1CompetenceByScenario .forTheRecord .precise -
     exp1CompetenceByScenario .forTheRecord .approximate >
     exp1CompetenceByScenario .bonding .precise -
     exp1CompetenceByScenario .bonding .approximate) ∧
    -- Low demand amplifies warmth contrast
    (exp2WarmthByScenario .stranger .underspecified -
     exp2WarmthByScenario .stranger .precise >
     exp2WarmthByScenario .forTheRecord .underspecified -
     exp2WarmthByScenario .forTheRecord .precise) := by
  constructor <;> native_decide

-- ============================================================================
-- §9. Roundness gating
-- ============================================================================

/-- Non-round numerals collapse the three-way distinction to a single variant:
    `.precise`. There is nothing for social perception to modulate. -/
theorem non_round_collapses (n : Nat)
    (h : Core.Roundness.roundnessScore n < 2) :
    classifyVariant n true = .precise ∧ classifyVariant n false = .precise := by
  unfold classifyVariant; constructor <;> simp [if_pos h]

/-- Round numerals support the full three-way contrast: bare → underspecified,
    modified → approximate. -/
theorem round_supports_contrast (n : Nat)
    (h : Core.Roundness.roundnessScore n ≥ 2) :
    classifyVariant n false = .underspecified ∧
    classifyVariant n true = .approximate := by
  have h' : ¬(Core.Roundness.roundnessScore n < 2) := by omega
  unfold classifyVariant; constructor <;> simp [if_neg h']

end Phenomena.Gradability.Imprecision.Studies.BeltramaSoltBurnett2022
