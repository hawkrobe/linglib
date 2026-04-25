import Linglib.Features.Acceptability
import Linglib.Core.Logic.NonBivalence
import Linglib.Fragments.English.Determiners
import Linglib.Theories.Semantics.Conditionals.Counterfactual
import Linglib.Theories.Semantics.Conditionals.Counterfactual.QuantifierEmbedding
import Linglib.Theories.Semantics.Conditionals.Counterfactual.Implicature
import Mathlib.Data.Rat.Defs

/-!
# @cite{ramotowska-marty-romoli-santorio-2025} - Counterfactuals and Quantificational Force

Ramotowska, S., Marty, P., Romoli, J. & Santorio, P. (2025).
Counterfactuals and quantificational force: Experimental evidence for
selectional semantics. Semantics & Pragmatics 18, Article 6: 1–43.

## Finding

Quantifier STRENGTH determines graded truth-value judgments for
counterfactuals embedded under quantifiers, not polarity or QUD.

This supports the SELECTIONAL theory (Stalnaker + supervaluation) over:
- Homogeneity theory (von Fintel/Križ): predicts QUD × polarity interaction
- Universal theory (Lewis/Kratzer): predicts determinate true/false

## Experimental Paradigm

Two experiments using graded truth-value judgments (0–99 slider from
"completely false" to "completely true"). QUD manipulated between
subjects: E-QuD (existential: "at least one has a chance to win")
vs U-QuD (universal: "all are guaranteed to win").

- **Experiment 1** (n=87 after exclusion): Lottery scenarios where
  "only some of the tickets that have been bought win a prize."
- **Experiment 2** (n=94 after exclusion): Card game with 4 players;
  mixed scenario has 2/4 red cards (win) and 2/4 gray cards (lose).
  Also tested plural definite sentences alongside counterfactuals.

Test sentences (Experiment 2):
- "All/None/Some/Not all of the players would have won if they had
  played and finished this round."

## Key Results

- Strong quantifiers (every, no): mean ratings < 15 (Exp 1), < 4 (Exp 2)
- Weak quantifiers (some, not every): mean ratings > 84 (Exp 1), > 82 (Exp 2)
- STRENGTH: β = −77.09, p < .001 (Exp 1); β = −88.7, p < .001 (Exp 2)
- QUD: not significant for counterfactuals
  (Exp 1: β = −0.09, p = .97; Exp 2: β = −0.6, p = 0.7)
- Plural definites WERE sensitive to QUD (Exp 2: β = −12.6, p = 0.01;
  raw means E-QuD M=41.0, U-QuD M=22.8), confirming QUD manipulation effective
-/

namespace RamotowskaEtAl2025

-- ════════════════════════════════════════════════════════════════
-- Experimental Design
-- ════════════════════════════════════════════════════════════════

/-- The three theories being tested. -/
inductive Theory where
  | universal    -- Lewis/Kratzer: ∀ closest worlds
  | selectional  -- Stalnaker + supervaluation
  | homogeneity  -- Universal + homogeneity presupposition
  deriving Repr, DecidableEq

/-- Quantifiers tested in the experiment. -/
inductive Quantifier where
  | every      -- Universal affirmative (strong/positive)
  | some       -- Existential (weak/positive)
  | no         -- Universal negative (strong/negative)
  | notEvery   -- Negated universal (weak/negative)
  deriving Repr, DecidableEq

open Fragments.English.Determiners (Strength)

/-- Map local quantifiers to canonical Strength (B&C Table II). -/
def Quantifier.strength : Quantifier → Strength
  | .every => .strong | .no => .strong
  | .some => .weak   | .notEvery => .weak

/-- Quantifier strength classification, derived from canonical `Strength`. -/
def Quantifier.isStrong (q : Quantifier) : Bool := q.strength == .strong

/-- Quantifier polarity classification. -/
def Quantifier.isPositive : Quantifier → Bool
  | .every => true
  | .some => true
  | .no => false
  | .notEvery => false

/-- QUD type manipulated between subjects. -/
inductive QuDType where
  | existential  -- E-QuD: "at least one has a chance to win"
  | universal    -- U-QuD: "all are guaranteed to win"
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════════════════
-- Theoretical Predictions (Table 3 of the paper)
-- ════════════════════════════════════════════════════════════════

/-- Selectional theory predictions (Table 3): QUD-independent.
    Strong quantifiers → rejected (low ratings),
    weak quantifiers → accepted (high ratings). -/
def selectionalPredictedHigh (q : Quantifier) : Bool := !q.isStrong

/-- Homogeneity theory predictions (Table 3): QUD-dependent.
    Positive quantifiers: high under E-QuD, low under U-QuD.
    Negative quantifiers: low under E-QuD, high under U-QuD.
    The predicted interaction is between QUD and polarity, not strength. -/
def homogeneityPredictedHigh (q : Quantifier) (qud : QuDType) : Bool :=
  match q.isPositive, qud with
  | true,  .existential => true
  | true,  .universal   => false
  | false, .existential => false
  | false, .universal   => true

-- ════════════════════════════════════════════════════════════════
-- Experimental Results
-- ════════════════════════════════════════════════════════════════

/--
Experimental datum: mean slider rating (0–99 scale) for a condition.
0 = "completely false", 99 = "completely true". -/
structure ExperimentalDatum where
  quantifier : Quantifier
  qud : QuDType
  meanRating : ℚ     -- Mean slider value (0–99 scale)
  deriving Repr

/-! ### Experiment 2 Results (card game, n=94)

Experiment 2 (§6) provides per-condition mean slider ratings for
target counterfactual (TC) sentences in the mixed scenario, reported
in §6.7.3 (p. 6:34). Values verified against raw CSV data (OSF:
osf.io/3jywr); paper rounds raw means to 1 decimal place. -/

/-- Experiment 2: mean slider ratings for counterfactuals in mixed
    scenarios. Verified against raw CSV data (OSF) and paper §6.7.3.

    Strong quantifiers (every/all, none): all means < 4.
    Weak quantifiers (not all, some): all means > 82. -/
def experiment2MixedResults : List ExperimentalDatum :=
  [ -- Strong quantifiers
    { quantifier := .every, qud := .universal,    meanRating := 222/153 }  -- M = 1.45
  , { quantifier := .every, qud := .existential,  meanRating := 165/127 }  -- M = 1.30
  , { quantifier := .no,    qud := .universal,    meanRating := 510/153 }  -- M = 3.33
  , { quantifier := .no,    qud := .existential,  meanRating := 112/126 }  -- M = 0.89
    -- Weak quantifiers
  , { quantifier := .notEvery, qud := .universal,   meanRating := 12567/153 } -- M = 82.14
  , { quantifier := .notEvery, qud := .existential, meanRating := 11026/128 } -- M = 86.14
  , { quantifier := .some,     qud := .universal,   meanRating := 14652/152 } -- M = 96.39
  , { quantifier := .some,     qud := .existential, meanRating := 12197/125 } -- M = 97.58
  ]

/-! ### Experiment 1 Results (lottery, n=87)

Experiment 1 (§5) uses lottery scenarios where "only some of the tickets
that have been bought win a prize." Mean slider ratings (0–99) for
counterfactual sentences in the mixed scenario. No per-quantifier ×
per-QUD breakdown is reported; the paper reports marginal means by
STRENGTH (collapsing across QUD and polarity).

Key results from the mixed-effects model (§5.7.2):
- STRENGTH: β = −77.09, p < .001
- QUD: β = −0.09, p = .97 (not significant) -/

/-- Experiment 1: marginal means by quantifier strength in mixed
    scenarios. These are the key data points establishing the
    strength effect (strong < 15, weak > 84).
    Values verified from raw CSV data (OSF: osf.io/3jywr). -/
structure StrengthMarginal where
  isStrong : Bool
  meanRating : ℚ
  deriving Repr

def experiment1Marginals : List StrengthMarginal :=
  [ { isStrong := true,  meanRating := 1705/150 }   -- M = 11.37 (strong, n=150)
  , { isStrong := false, meanRating := 13086/146 }   -- M = 89.63 (weak, n=146)
  ]

-- The strength effect replicates across experiments: strong < 15,
-- weak > 84 in Experiment 1.
#guard experiment1Marginals.all λ d =>
  if d.isStrong then d.meanRating < 15 else d.meanRating > 84

-- ════════════════════════════════════════════════════════════════
-- Key Empirical Observations
-- ════════════════════════════════════════════════════════════════

/--
**Key empirical observation**: Strength, not polarity or QUD, determines
truth-value judgments for counterfactuals in mixed scenarios.

Strong quantifiers (every, no) have uniformly low mean ratings (< 4/99).
Weak quantifiers (some, not every) have uniformly high ratings (> 82/99).
QUD has no significant effect on counterfactual ratings. -/
def strengthEffect : Bool :=
  let strong := experiment2MixedResults.filter (·.quantifier.isStrong)
  let weak := experiment2MixedResults.filter (!·.quantifier.isStrong)
  -- All strong ratings below midpoint (50), all weak above
  strong.all (·.meanRating < 50) && weak.all (·.meanRating > 50)

#guard strengthEffect

/--
**Strength effect**: all strong quantifier ratings are below 5/99 and
all weak quantifier ratings are above 80/99 in the mixed scenario.

This extreme separation rules out chance variation and confirms that
strength is the dominant factor. -/
theorem strength_effect_verified :
    experiment2MixedResults.all (λ d =>
      if d.quantifier.isStrong then d.meanRating < 5
      else d.meanRating > 80) = true := by
  rw [List.all_eq_true]
  intro d hd
  unfold experiment2MixedResults at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Quantifier.isStrong, Quantifier.strength] <;> norm_num

/--
**QUD has no effect on counterfactuals**: within each quantifier,
E-QuD and U-QuD ratings are close (differ by < 5 points on 0–99 scale).

This is the key prediction of the selectional theory (QUD-independent)
and against the homogeneity theory (which predicts QUD × polarity). -/
def qudNoEffect : Bool :=
  let pairs := [
    (Quantifier.every, QuDType.existential, QuDType.universal),
    (Quantifier.no, QuDType.existential, QuDType.universal),
    (Quantifier.some, QuDType.existential, QuDType.universal),
    (Quantifier.notEvery, QuDType.existential, QuDType.universal)
  ]
  pairs.all λ (q, qud1, qud2) =>
    match experiment2MixedResults.find? (λ d => d.quantifier == q && d.qud == qud1),
          experiment2MixedResults.find? (λ d => d.quantifier == q && d.qud == qud2) with
    | some d1, some d2 =>
      let diff := if d1.meanRating > d2.meanRating
                  then d1.meanRating - d2.meanRating
                  else d2.meanRating - d1.meanRating
      diff < 5  -- Within 5 points on 0–99 scale
    | _, _ => false

#guard qudNoEffect

-- ════════════════════════════════════════════════════════════════
-- Theory Evaluation
-- ════════════════════════════════════════════════════════════════

/--
**Selectional theory succeeds**: predictions match data.

The selectional theory predicts that quantifier strength determines
ratings regardless of QUD. This matches the observed pattern:
strong quantifiers uniformly rejected, weak uniformly accepted,
with no QUD modulation. -/
def selectionalFits : Bool :=
  experiment2MixedResults.all λ d =>
    let predictedHigh := selectionalPredictedHigh d.quantifier
    if predictedHigh then d.meanRating > 50 else d.meanRating < 50

#guard selectionalFits

/--
**Homogeneity theory fails**: predicted QUD × polarity interaction absent.

The homogeneity theory predicts that positive quantifiers (every, some)
should be rated HIGH under E-QuD but LOW under U-QuD, and vice versa
for negative quantifiers. The data shows no such interaction:
- "every" is low under BOTH QUDs (~1.2 and ~1.5)
- "some" is high under BOTH QUDs (~97.2 and ~96.1) -/
def homogeneityFails : Bool :=
  -- Find a case where the homogeneity prediction is wrong
  experiment2MixedResults.any λ d =>
    let predictedHigh := homogeneityPredictedHigh d.quantifier d.qud
    -- Prediction says high but rating is low, or vice versa
    (predictedHigh && d.meanRating < 50) || (!predictedHigh && d.meanRating > 50)

#guard homogeneityFails

/--
The homogeneity theory makes wrong predictions for 4 of 8 conditions.

Under U-QuD, homogeneity predicts:
- every → low (✓ observed: 1.5)
- some → low (✗ observed: 96.1)
- no → high (✗ observed: 3.3)
- not every → high (✓ observed: 82.1)

Under E-QuD, homogeneity predicts:
- every → high (✗ observed: 1.2)
- some → high (✓ observed: 97.2)
- no → low (✓ observed: 0.9)
- not every → low (✗ observed: 86.1) -/
theorem homogeneity_wrong_count :
    (experiment2MixedResults.filter λ d =>
      let predictedHigh := homogeneityPredictedHigh d.quantifier d.qud
      (predictedHigh && d.meanRating < 50) || (!predictedHigh && d.meanRating > 50)
    ).length = 4 := by
  unfold experiment2MixedResults
  simp only [List.filter_cons, List.filter_nil, homogeneityPredictedHigh,
    Quantifier.isPositive, decide_eq_true_eq]
  norm_num

-- ════════════════════════════════════════════════════════════════
-- Statistical Results
-- ════════════════════════════════════════════════════════════════

/-!
### Mixed-Effects Model Results (Table 5 of paper)

Experiment 2 target counterfactual sentences, linear mixed-effects model
with POLARITY, STRENGTH, QUD and interactions as predictors:

| Effect              | β      | p      |
|---------------------|--------|--------|
| INTERCEPT           | 46.1   | < .001 |
| STRENGTH            | −88.7  | < .001 |
| QUD                 | −0.6   | 0.7    |
| POLARITY            | 5.9    | < .001 |
| QUD:POLARITY        | 0.3    | 0.9    |
| STRENGTH:QUD        | 3.9    | 0.2    |
| STRENGTH:POLARITY   | −13.2  | < .001 |
| STR:POL:QUD         | −5.3   | 0.4    |

Key findings:
- **STRENGTH** is the dominant predictor (β = −88.7)
- **QUD** has no significant main effect or interactions
- **POLARITY** has a small effect (β = 5.9): "some" rated slightly
  higher than "not every" within weak quantifiers
- **STRENGTH×POLARITY** interaction (β = −13.2): the polarity effect
  is confined to weak quantifiers
-/

-- ════════════════════════════════════════════════════════════════
-- Plural Definite Dissociation (Experiment 2)
-- ════════════════════════════════════════════════════════════════

/-!
### Plural Definites vs Counterfactuals: QUD Sensitivity

Experiment 2 also tested plural definite sentences alongside
counterfactuals. The key finding: plural definites ARE sensitive to
QUD (β = −12.6, p = 0.01), while counterfactuals are NOT (β = −0.6,
p = 0.7). This dissociation confirms:

1. The QUD manipulation was effective (plural definites detect it)
2. Counterfactuals' QUD insensitivity is a genuine semantic property
3. Both phenomena use the same DIST operator, but differ in
   architecture: plural homogeneity is LOCAL (gap before quantifier),
   while selectional counterfactuals are GLOBAL (Bool before quantifier)
-/

/-- Plural definite datum: mean slider rating under each QUD condition
    in the mixed scenario ("The players won this round"). -/
structure PluralDefiniteDatum where
  qud : QuDType
  meanRating : ℚ
  deriving Repr

/-- Experiment 2: plural definite mean ratings in mixed scenario.
    Unlike counterfactuals, these show a significant QUD effect.
    Raw means from OSF data; paper §6.7.2 reports model-estimated
    marginals (42.2 / 29.6) which differ slightly. -/
def experiment2PluralDefiniteResults : List PluralDefiniteDatum :=
  [ { qud := .existential, meanRating := 4554/111 }   -- M = 41.03
  , { qud := .universal,   meanRating := 2601/114 }    -- M = 22.82
  ]

-- QUD affects plural definites: E-QuD > U-QuD by > 10 points
#guard
  match experiment2PluralDefiniteResults.find? (·.qud == .existential),
        experiment2PluralDefiniteResults.find? (·.qud == .universal) with
  | some e, some u => e.meanRating - u.meanRating > 10
  | _, _ => false

-- ════════════════════════════════════════════════════════════════
-- Grounding: Study Predictions ↔ Formal Selectional Semantics
-- ════════════════════════════════════════════════════════════════

open Semantics.Conditionals.Counterfactual
  (embeddedSelectional noSelectional notEverySelectional QStrength
   all_four_quantifiers_mixed)
open Core.Duality (Truth3)

/-- Bridge: map study quantifiers to formal selectional predictions.
    Each quantifier maps to the corresponding projection operation
    from the theory layer (`Counterfactual.lean`). -/
def Quantifier.selectionalResult (q : Quantifier) (results : List Truth3) : Truth3 :=
  match q with
  | .every    => embeddedSelectional .strong results
  | .some     => embeddedSelectional .weak results
  | .no       => noSelectional results
  | .notEvery => notEverySelectional results

/--
**Grounding theorem**: the study-level prediction (`selectionalPredictedHigh`)
agrees with the formal selectional semantics for any mixed input.

This connects the theory layer's three-valued projection operations to the
study file's simple strength-based classification. The classification is
not stipulated — it is derived from the formal theory by construction. -/
theorem selectional_prediction_grounded (q : Quantifier) (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    (q.selectionalResult (bs.map Truth3.ofBool) == .true) = selectionalPredictedHigh q := by
  obtain ⟨h1, h2, h3, h4⟩ := all_four_quantifiers_mixed bs h_some_true h_some_false
  cases q <;>
    simp only [Quantifier.selectionalResult, selectionalPredictedHigh,
      Quantifier.isStrong, Quantifier.strength, h1, h2, h3, h4] <;>
    decide

-- ════════════════════════════════════════════════════════════════
-- Architectural Explanation: Local vs Global Trivalence
-- ════════════════════════════════════════════════════════════════

open Core.NonBivalence (TrivalenceScope local_strength_irrelevant
  global_mixed_pattern global_always_determinate)
open Core.Duality (DualityType aggregate ProjectionType)
open Semantics.Conditionals.Counterfactual (projToDuality projectTruthValues_eq_aggregate)

/-!
### Why Strength Matters: The Trivalence Scope Dichotomy

The paper's deepest insight (§2.2): whether gaps arise LOCALLY (before
the quantifier) or GLOBALLY (after the quantifier) determines whether
quantifier strength matters. This is formalized in `Core.NonBivalence`
as the dichotomy between `TrivalenceScope.local` and `.global`.

- **Homogeneity** uses local scope: each individual's counterfactual
  is `.indet` (gap). `local_strength_irrelevant` proves both ∃ and
  ∀ aggregation return `.indet` — strength is invisible.
- **Selectional** uses global scope: within each selected world,
  individual outcomes are Bool. `global_mixed_pattern` proves mixed
  Bools yield `.true` for ∃ and `.false` for ∀ — the strength effect.
-/

/-- Map each theory to its trivalence scope architecture. -/
def Theory.scope : Theory → TrivalenceScope
  | .universal   => .global   -- Lewis/Kratzer: closest worlds give Bool
  | .selectional => .global   -- Stalnaker: selection function gives Bool
  | .homogeneity => .«local»  -- Gaps arise before quantifier

/-- **Homogeneity architecture erases strength**: when gaps arise locally,
    both strong and weak quantifiers return `.indet`. The quantifier's
    projection type is invisible — it cannot "see past" gaps.

    This is why the homogeneity theory predicts no strength effect and
    must resort to QUD × polarity to distinguish conditions. -/
theorem homogeneity_erases_strength (n : Nat) (hn : n > 0) :
    ∀ proj : ProjectionType,
    embeddedSelectional proj (List.replicate n Truth3.indet) = .indet := by
  intro proj
  unfold embeddedSelectional
  rw [projectTruthValues_eq_aggregate]
  exact local_strength_irrelevant (projToDuality proj) n hn

/-- **Selectional architecture produces strength effect**: when the
    quantifier sees only Bools (global scope), mixed inputs yield
    `.true` for weak (∃/disjunctive) and `.false` for strong (∀/conjunctive).

    This connects the study's `embeddedSelectional` through the bridging
    theorem to `NonBivalence.global_mixed_pattern`. -/
theorem selectional_strength_effect (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    embeddedSelectional .weak (bs.map Truth3.ofBool) = .true ∧
    embeddedSelectional .strong (bs.map Truth3.ofBool) = .false := by
  unfold embeddedSelectional QStrength.toProjection
  constructor <;> (rw [projectTruthValues_eq_aggregate]; simp only [projToDuality])
  · exact (global_mixed_pattern bs h_some_true h_some_false).1
  · exact (global_mixed_pattern bs h_some_true h_some_false).2

/-- **Selectional counterfactuals are always determinate**: under global
    scope, aggregation over Bools never produces a gap.

    This explains why selectional semantics yields crisp true/false
    judgments (no "undefined"), matching the experimental pattern of
    extreme slider values (< 4 or > 82). -/
theorem selectional_always_determinate (proj : ProjectionType) (bs : List Bool) :
    embeddedSelectional proj (bs.map Truth3.ofBool) ≠ .indet := by
  unfold embeddedSelectional
  rw [projectTruthValues_eq_aggregate]
  exact global_always_determinate (projToDuality proj) bs

-- ════════════════════════════════════════════════════════════════
-- The Plural Definite Dissociation
-- ════════════════════════════════════════════════════════════════

/-!
### Why Plural Definites Are QUD-Sensitive But Counterfactuals Are Not

Experiment 2 tested both counterfactuals and plural definites ("The
players won this round") in the same mixed scenarios. The key finding:

- **Counterfactuals**: QUD has no effect (β = −0.6, p = 0.7)
- **Plural definites**: QUD has a significant effect (β = −12.6, p = 0.01;
  E-QuD M=41.0 vs U-QuD M=22.8)

The NonBivalence dichotomy explains this dissociation:

- **Plural definites use LOCAL trivalence**: each individual's predication
  is evaluated via supervaluation (pluralTruthValue / dist), producing
  `.indet` when some-but-not-all atoms satisfy the predicate. The
  quantifier sees these gaps. By `local_strength_irrelevant`, ALL
  quantifier types return `.indet`.

- **Counterfactuals use GLOBAL trivalence**: within each selected world,
  individual outcomes are Boolean. The quantifier sees Bools. By
  `global_always_determinate`, the result is always definite.

The consequence: when the semantic layer returns `.indet`, the only
source of variation in judgments is pragmatic resolution — and pragmatic
resolution is QUD-dependent (@cite{kriz-2016}: `sufficientlyTrue` and
`addressesIssue`). When the semantic layer returns a determinate value,
there is no gap for pragmatics to exploit — QUD has nothing to modulate.

This is why the SAME mixed scenario produces QUD-sensitivity for PDs
but not for CFs: the scope of trivalence determines whether pragmatics
gets a foothold.
-/

/-- **Plural definites are LOCAL**: in mixed scenarios, every quantifier
    returns `.indet`. Strength, polarity, and QUD are all invisible at
    the semantic level — the quantifier cannot see past the gap. -/
theorem pd_all_quantifiers_gap (n : Nat) (hn : n > 0) (d : DualityType) :
    aggregate d (List.replicate n Truth3.indet) = .indet :=
  local_strength_irrelevant d n hn

/-- **Counterfactuals are GLOBAL**: in mixed scenarios, every quantifier
    returns a determinate value. There is no gap for pragmatics to exploit. -/
theorem cf_all_quantifiers_determinate (d : DualityType) (bs : List Bool) :
    aggregate d (bs.map Truth3.ofBool) ≠ .indet :=
  global_always_determinate d bs

/-- **The dissociation**: for the same mixed input (n individuals, some
    satisfying the predicate, some not), PDs return `.indet` while CFs
    return a definite value. The gap is what makes PDs QUD-sensitive —
    pragmatic resolution via `sufficientlyTrue` (@cite{kriz-2016}) depends
    on the QUD partition. CFs have no gap to resolve.

    This is a direct corollary of NonBivalence's dichotomy: local scope
    produces gaps that pass through quantifiers; global scope produces
    Bools that quantifiers can distinguish. -/
theorem scope_determines_qud_sensitivity (n : Nat) (hn : n > 0)
    (bs : List Bool) (hlen : bs.length = n)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·))
    (d : DualityType) :
    -- PDs: gap (pragmatic resolution needed, QUD-sensitive)
    aggregate d (List.replicate n Truth3.indet) = .indet ∧
    -- CFs: determinate (no pragmatic resolution, QUD-insensitive)
    aggregate d (bs.map Truth3.ofBool) ≠ .indet :=
  ⟨local_strength_irrelevant d n hn, global_always_determinate d bs⟩

-- ════════════════════════════════════════════════════════════════
-- Connections to Other Phenomena
-- ════════════════════════════════════════════════════════════════

/-!
## Related Phenomena

1. **Local vs Global Trivalence** (`Core.NonBivalence`):
   The paper's deepest architectural insight is formalized as the
   dichotomy theorems. `homogeneity_erases_strength` derives that
   local gaps make strength invisible; `selectional_strength_effect`
   derives that global Bools produce the strength effect.

2. **Plural Definite Dissociation** (above):
   `scope_determines_qud_sensitivity` derives the CF/PD dissociation
   from the NonBivalence dichotomy. Plural definites are LOCAL (gap
   before quantifier → QUD-sensitive pragmatic resolution); counterfactuals
   are GLOBAL (Bool before quantifier → no gap to resolve).

3. **Modal Homogeneity** (@cite{agha-jeretic-2022}):
   Weak necessity modals (*should*) are to strong necessity (*must*) what
   plural definites are to `all`-sentences. `shouldEval` produces `.indet`
   in mixed domains (local), while `mustEval` produces `ofBool` (global).
   The same NonBivalence dichotomy predicts that embedded *should*-sentences
   would be strength-insensitive while embedded *must*-sentences would show
   the strength effect.

4. **Conditional Excluded Middle (CEM)**:
   Stalnaker's semantics validates CEM: (A □→ B) ∨ (A □→ ¬B).
   See `Counterfactual.lean` for the proof.
-/

end RamotowskaEtAl2025
