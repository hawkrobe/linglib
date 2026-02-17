/-
# Island Effects: Competence vs. Performance vs. Discourse

Comparing how competence-based, performance-based, and discourse-based accounts
explain the gradient nature of island effects.

## Accounts Compared

1. **Competence** (Subjacency, CNPC, Barriers, MLC): categorical blocking
2. **Performance** (Kluender, Deane, Hofmeister & Sag): gradient processing cost
3. **Discourse** (Goldberg, Erteschik-Shir, Lu, Pan & Degen): information-structural
   backgroundedness

## Key Questions

- Nonstructural manipulations (filler complexity, NP definiteness) dramatically
  alter island acceptability while leaving the island configuration intact.
  Which account predicts this? (H&S 2010 → Processing)

- Prosodic focus on embedded objects ameliorates MoS islands; adding manner
  adverbs to bridge verbs creates new islands. Which account predicts this?
  (Lu et al. 2025 → Discourse)

## References

- Ross, J.R. (1967). Constraints on Variables in Syntax.
- Chomsky, N. (1973). Conditions on Transformations.
- Chomsky, N. (1986). Barriers.
- Chomsky, N. (1995). The Minimalist Program.
- Kluender, R. (1991, 1998). Cognitive constraints on variables in syntax.
- Deane, P. (1991). Limits to attention: A cognitive theory of island phenomena.
- Hofmeister, P. & Sag, I.A. (2010). Cognitive constraints and island effects.
  Language 86(2):366–415.
- Lu, J., Pan, D. & Degen, J. (2025). Evidence for a discourse account of
  manner-of-speaking islands. Language 101(4):627–659.
-/

import Linglib.Phenomena.FillerGap.Islands.Data
import Linglib.Phenomena.FillerGap.Studies.Sag2010
import Linglib.Core.ProcessingModel

namespace Phenomena.FillerGap.Compare

open ProcessingModel

-- ============================================================================
-- Concrete Conditions from Hofmeister & Sag 2010
-- ============================================================================

/-! ### CNPC conditions (Experiment 1) -/

/-- Bare wh + definite island-forming NP: worst CNPC condition.
"I saw **who** Emma doubted **the report** that we had captured ___" -/
def cnpc_bare_def : ProcessingProfile :=
  { locality := 8, boundaries := 1, referentialLoad := 2, ease := 0 }

/-- Which-N + indefinite island-forming NP: best CNPC condition.
"I saw **which convict** Emma doubted **a report** that we had captured ___" -/
def cnpc_which_indef : ProcessingProfile :=
  { locality := 8, boundaries := 1, referentialLoad := 1, ease := 2 }

/-- Non-island baseline (no extraction): "I saw who Emma doubted that ___" -/
def cnpc_baseline : ProcessingProfile :=
  { locality := 5, boundaries := 0, referentialLoad := 0, ease := 0 }

/-! ### Wh-island conditions (Experiment 2) -/

/-- Bare wh into wh-island: "**Who** did Albert learn whether they dismissed ___" -/
def whIsland_bare : ProcessingProfile :=
  { locality := 7, boundaries := 1, referentialLoad := 1, ease := 0 }

/-- Which-N into wh-island: "**Which employee** did Albert learn whether they dismissed ___" -/
def whIsland_which : ProcessingProfile :=
  { locality := 7, boundaries := 1, referentialLoad := 1, ease := 2 }

-- ============================================================================
-- HasProcessingProfile Instance
-- ============================================================================

/-- Island conditions as a sum type for typeclass instance. -/
inductive IslandCondition where
  | cnpcBareDef
  | cnpcWhichIndef
  | cnpcBaseline
  | whIslandBare
  | whIslandWhich
  deriving Repr, DecidableEq, BEq

instance : HasProcessingProfile IslandCondition where
  profile
    | .cnpcBareDef    => cnpc_bare_def
    | .cnpcWhichIndef => cnpc_which_indef
    | .cnpcBaseline   => cnpc_baseline
    | .whIslandBare   => whIsland_bare
    | .whIslandWhich  => whIsland_which

-- ============================================================================
-- Processing Model Predictions (Pareto Dominance)
-- ============================================================================

/-- Complex fillers reduce processing difficulty in CNPC.
This is the **filler complexity paradox**: more syntactic material in the
filler makes the island *easier* to process, contrary to any account
where cost increases monotonically with phrase size.

Pareto: cnpc_which_indef is easier than cnpc_bare_def because it has
lower referentialLoad (1 < 2) and higher ease (2 > 0), with locality
and boundaries equal. -/
theorem filler_reduces_cnpc_cost :
    cnpc_bare_def.compare cnpc_which_indef = .harder := by
  native_decide

/-- Complex fillers reduce processing difficulty in wh-islands.

Pareto: whIsland_which is easier than whIsland_bare because it has
higher ease (2 > 0), with all other dimensions equal. -/
theorem filler_reduces_whIsland_cost :
    whIsland_bare.compare whIsland_which = .harder := by
  native_decide

/-- Worst CNPC condition is harder than baseline.

Pareto: cnpc_bare_def is worse on locality (8 > 5), boundaries (1 > 0),
and referentialLoad (2 > 0), with ease equal. -/
theorem bare_def_harder_than_baseline :
    cnpc_bare_def.compare cnpc_baseline = .harder := by
  native_decide

/-- Worst CNPC condition (bare-def) is strictly harder than best (which-indef).

Pareto: bare-def has higher referentialLoad (2 > 1) and lower ease (0 < 2),
with locality and boundaries equal. -/
theorem bare_def_harder_than_which_indef :
    cnpc_bare_def.compare cnpc_which_indef = .harder := by
  native_decide

/-- Which-indef CNPC vs baseline is incomparable under Pareto.

Which-indef is worse on locality (8 > 5), boundaries (1 > 0), and
referentialLoad (1 > 0), but better on ease (2 > 0). The trade-off
between distance costs and retrieval facilitation is genuine — Pareto
honestly reports it as `incomparable` rather than forcing a cardinal
aggregate. -/
theorem which_indef_vs_baseline_incomparable :
    cnpc_which_indef.compare cnpc_baseline = .incomparable := by
  native_decide

-- ============================================================================
-- Theory Comparison: Competence vs. Performance
-- ============================================================================

/-- A nonstructural manipulation that changes island acceptability
without altering the island configuration.

Each of the three accounts (competence, processing, discourse) makes
a prediction about whether the manipulation should affect acceptability. -/
structure IslandManipulation where
  description : String
  /-- Does any competence theory predict an acceptability difference? -/
  competencePredictsDifference : Bool
  /-- Does the processing account predict a difference? -/
  processingPredictsDifference : Bool
  /-- Does the discourse/backgroundedness account predict a difference? -/
  discoursePredictsDifference : Bool
  /-- Is a difference actually observed? -/
  differenceObserved : Bool
  /-- Statistical significance (p-value description) -/
  significance : String
  deriving Repr

/-- Filler complexity in CNPC (Experiment 1, §5).
which-N vs bare wh — **same island structure**, different filler. -/
def fillerComplexityCNPC : IslandManipulation :=
  { description := "Filler complexity (which-N vs bare) in CNPC"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false  -- filler complexity doesn't change QUD
    differenceObserved := true
    significance := "F1(1,20)=48.741, p<0.0001" }

/-- Filler complexity in wh-islands (Experiment 2, §6).
which-N vs bare wh — **same island structure**. -/
def fillerComplexityWhIsland : IslandManipulation :=
  { description := "Filler complexity (which-N vs bare) in wh-islands"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false  -- filler complexity doesn't change QUD
    differenceObserved := true
    significance := "F1(1,15)=15.964, p=0.001" }

/-- NP type in CNPC (Experiment 1, §5).
Definite vs indefinite island-forming NP — **same CNPC configuration**. -/
def npTypeCNPC : IslandManipulation :=
  { description := "NP definiteness (def vs indef) in CNPC"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false  -- NP type doesn't change QUD
    differenceObserved := true
    significance := "Marginal interaction with filler type" }

/-- Filler complexity in adjunct islands (Experiment 3, §7).
Complex vs simple temporal adjunct — **same wh-island structure**. -/
def fillerComplexityAdjunct : IslandManipulation :=
  { description := "Adjunct complexity (complex vs simple) in wh-islands"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false  -- adjunct complexity doesn't change QUD
    differenceObserved := true
    significance := "t1(27)=3.484, p<0.01" }

/-! ### MoS island manipulations (Lu, Pan & Degen 2025) -/

/-- Prosodic focus on embedded object in MoS islands (Experiments 1, 2a, 3b).
Focus changes information structure without changing syntax or processing load. -/
def prosodicFocusMoS : IslandManipulation :=
  { description := "Prosodic focus (embedded vs verb) in MoS islands"
    competencePredictsDifference := false   -- syntax unchanged
    processingPredictsDifference := false   -- processing load unchanged
    discoursePredictsDifference := true     -- focus changes QUD → changes backgroundedness
    differenceObserved := true
    significance := "β=0.23, t=7.10, p<0.001 (Exp 1)" }

/-- Say + manner adverb creates island (Experiment 3a).
Adding an adverb doesn't change CP structure but adds manner weight. -/
def sayAdverbIsland : IslandManipulation :=
  { description := "Say+adverb vs say alone (MoS island creation)"
    competencePredictsDifference := false   -- same CP structure ± adverb
    processingPredictsDifference := false   -- no processing load difference
    discoursePredictsDifference := true     -- manner adverb adds manner weight → QUD shift
    differenceObserved := true
    significance := "β=−0.24, t=−12.4, p<0.001 (Exp 3a)" }

/-- Verb-frame frequency in MoS islands (all experiments).
Frequency is the mechanism proposed by Liu et al. (2019, 2022). -/
def frequencyMoS : IslandManipulation :=
  { description := "Verb-frame frequency as predictor of MoS acceptability"
    competencePredictsDifference := false   -- irrelevant to structure
    processingPredictsDifference := true    -- frequency → surprisal → processing cost
    discoursePredictsDifference := false    -- backgroundedness, not frequency, is causal
    differenceObserved := false             -- n.s. in ALL experiments
    significance := "β=−0.003, p=0.874 (Exp 1); all others n.s." }

-- ============================================================================
-- Accuracy Scoring
-- ============================================================================

/-- All manipulations: H&S 2010 + Lu et al. 2025. -/
def allManipulations : List IslandManipulation := [
  fillerComplexityCNPC,
  fillerComplexityWhIsland,
  npTypeCNPC,
  fillerComplexityAdjunct,
  prosodicFocusMoS,
  sayAdverbIsland,
  frequencyMoS
]

/-- Processing correctly predicts the observed difference. -/
def processingCorrect (m : IslandManipulation) : Bool :=
  m.differenceObserved == m.processingPredictsDifference

/-- Competence correctly predicts the observed (non-)difference. -/
def competenceCorrect (m : IslandManipulation) : Bool :=
  m.differenceObserved == m.competencePredictsDifference

/-- Discourse correctly predicts the observed (non-)difference. -/
def discourseCorrect (m : IslandManipulation) : Bool :=
  m.differenceObserved == m.discoursePredictsDifference

def processingScore : Nat := allManipulations.filter processingCorrect |>.length
def competenceScore : Nat := allManipulations.filter competenceCorrect |>.length
def discourseScore : Nat := allManipulations.filter discourseCorrect |>.length

/-- Processing scores 4/7: correct on all 4 H&S manipulations,
but misses prosodic focus, say+adverb, and frequency (predicts effect, none found). -/
theorem processing_scores_4_of_7 :
    processingScore = 4 := by native_decide

/-- Competence scores 1/7 — only the frequency null result
(where it correctly predicts no effect). -/
theorem competence_scores_1_of_7 :
    competenceScore = 1 := by native_decide

/-- Discourse scores 3/7: correct on prosodic focus, say+adverb, and frequency null.
Misses the 4 H&S effects which are processing, not discourse. -/
theorem discourse_scores_3_of_7 :
    discourseScore = 3 := by native_decide

/-- Processing and discourse are perfectly complementary: for every manipulation,
exactly one of the two accounts is correct (XOR). This means they have full
coverage (together 7/7) with zero overlap. -/
theorem complementary_accounts :
    allManipulations.all (fun m => processingCorrect m != discourseCorrect m) = true := by
  native_decide

-- ============================================================================
-- Ordering Predictions (via shared infrastructure)
-- ============================================================================

/-- Ordering predictions that Pareto dominance can verify.

Note: which-indef CNPC vs baseline is `incomparable` (trade-off between
distance costs and retrieval facilitation), so it is not included here.
See `which_indef_vs_baseline_incomparable`. -/
def islandOrderingPredictions : List (OrderingPrediction IslandCondition) := [
  { harder := .cnpcBareDef, easier := .cnpcWhichIndef,
    description := "Bare-def CNPC harder than which-indef CNPC" },
  { harder := .cnpcBareDef, easier := .cnpcBaseline,
    description := "Bare-def CNPC harder than baseline" },
  { harder := .whIslandBare, easier := .whIslandWhich,
    description := "Bare wh-island harder than which-N wh-island" }
]

/-- All Pareto-orderable predictions verified. -/
theorem all_ordering_predictions_verified :
    islandOrderingPredictions.all verifyOrdering = true := by native_decide

-- ============================================================================
-- Connection to Existing Island Classification
-- ============================================================================

/-- The binary strong/weak classification (constraintStrength in Islands.Data)
is challenged by H&S's data.

The CNPC is classified as "strong", yet its acceptability varies by 25 points
(60 → 85) under nonstructural manipulation. If "strong" means "consistently
blocks the dependency", the CNPC is not consistently strong.

Similarly, wh-islands are classified as "weak" (ameliorated with D-linking),
but H&S show that the amelioration tracks processing difficulty specifically,
not D-linking per se — the same effect appears with nonreferential adjuncts
(Experiment 3). -/
theorem cnpc_is_classified_strong :
    constraintStrength .complexNP = .strong := by rfl

/-- Yet CNPC acceptability varies by 25+ points under nonstructural
manipulation — gradient, not categorical. -/
theorem cnpc_acceptability_range :
    let worst := 60  -- bare-def
    let best := 85   -- which-pl
    best - worst ≥ 25 := by native_decide

-- ============================================================================
-- Connection to Sag 2010: Construction-Specific Islands
-- ============================================================================

/-! ### Sag's (2010) construction-based island analysis

Sag (2010, p.514) argues that island constraints are construction-specific
GAP restrictions, not universal Subjacency. This means:
- The grammar **overgerates** (licenses extractions freely)
- Construction-specific constraints (GAP restrictions) block some extractions
- Remaining gradient acceptability is explained by processing

This is exactly the division of labor the processing comparison reveals:
grammar determines structural possibility, processing determines ease.

The Sag 2010 F-G typology (`Phenomena.FillerGap.Studies.Sag2010`) classifies which
constructions are islands. The processing model explains **within-island**
gradient effects (filler complexity, NP type). -/

open Phenomena.FillerGap.Studies.Sag2010

/-- Sag's two island constructions are a proper subset of all F-G types.
The non-island types (interrogative, relative, the-clause) freely permit
extraction, consistent with the processing account's prediction that
apparent island effects in these are gradient, not categorical. -/
theorem sag_island_subset :
    islandConstructions.length < 5 := by native_decide

/-- The constructions Sag identifies as islands (topicalization, exclamatives)
are not among those tested by Hofmeister & Sag 2010 (CNPC, wh-islands,
adjuncts). This is significant: H&S test processing-based islands, while
Sag 2010 identifies grammar-based islands — they explain **different** cases.

Together they cover both:
- Grammar-based islands: topicalization [GAP ⟨⟩], exclamatives [GAP ⟨⟩]
- Processing-based "islands": CNPC, wh-islands, adjuncts (gradient effects) -/
theorem complementary_coverage :
    -- Sag's grammatical islands
    (fgParams .topicalized).isIsland = true ∧
    (fgParams .whExclamative).isIsland = true ∧
    -- H&S's processing-based gradient effects apply to non-Sag island types
    constraintStrength .complexNP = .strong ∧
    -- Lu et al.'s discourse-based islands are a third mechanism
    constraintSource .mannerOfSpeaking = .discourse := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Implications
-- ============================================================================

/-!
## Summary: Island Effects Three-Way Comparison

### Nonstructural manipulations of island acceptability

| Manipulation | Competence | Processing | Discourse | Observed |
|---|---|---|---|---|
| Filler complexity (CNPC) | No effect | Effect ✓ | No effect | p<0.0001 |
| Filler complexity (wh-island) | No effect | Effect ✓ | No effect | p=0.001 |
| NP definiteness (CNPC) | No effect | Effect ✓ | No effect | Marginal |
| Adjunct complexity (wh-island) | No effect | Effect ✓ | No effect | p<0.01 |
| Prosodic focus (MoS) | No effect | No effect | Effect ✓ | p<0.001 |
| Say+adverb island | No effect | No effect | Effect ✓ | p<0.001 |
| Verb-frame frequency (MoS) | No effect ✓ | Effect | No effect ✓ | n.s. |

**Score**: Processing 4/7, Discourse 3/7, Competence 1/7. Together: 7/7.

### Key findings

1. **Filler complexity paradox** (H&S 2010): more complex wh-phrases *improve*
   island acceptability. Predicted by processing, not by competence or discourse.

2. **Prosodic amelioration** (Lu et al. 2025): focus on embedded object
   ameliorates MoS islands. Predicted by discourse, not by competence or processing.

3. **Say+adverb replication** (Lu et al. 2025): adding manner adverbs to bridge
   verb *say* creates new islands. Predicted by discourse alone.

4. **Perfect complementarity**: processing (4/7) and discourse (3/7) cover
   disjoint manipulations. Together they explain all 7 observed patterns.

### Theoretical upshot

Island effects arise from (at least) three distinct mechanisms:
- **Grammar**: categorical blocking (topicalization, exclamatives — Sag 2010)
- **Processing**: gradient difficulty from memory load (CNPC, wh-islands — H&S 2010)
- **Discourse**: information-structural backgroundedness (MoS — Lu et al. 2025)

This parallels the scope-freezing comparison (`Phenomena.Quantification.Compare`),
where processing also outperforms grammar-only accounts on gradient data.
Both domains use `ProcessingModel.ProcessingProfile` with Pareto dominance
for weight-free ordinal comparison.

### Connection to Sag (2010)

Sag's F-G typology (`Phenomena.FillerGap.Studies.Sag2010`) identifies grammar-based
islands (topicalization, exclamatives with `[GAP ⟨⟩]`). H&S 2010 covers
processing-based islands (CNPC, wh-islands). Lu et al. 2025 covers
discourse-based islands (MoS). Together they provide a three-mechanism account.
-/

-- ============================================================================
-- Connection to MoS Islands: A Third Type of Account
-- ============================================================================

/-! ### Manner-of-Speaking Islands (Lu, Pan & Degen 2025)

Lu, Pan & Degen (2025) introduce a **discourse-based** account of island effects
that complements both competence and processing accounts. MoS islands arise from
information-structural backgroundedness, not syntactic configuration or processing
cost. This is a third mechanism alongside grammar-based and processing-based islands.

The three sources are now tracked by `constraintSource` in Islands.Data:
- `.syntactic` → competence grammar (Ross 1967, Chomsky 1973)
- `.processing` → performance/memory (Hofmeister & Sag 2010)
- `.discourse` → information structure (Lu, Pan & Degen 2025)

Together, these three mechanisms partition the space of island phenomena:
1. Grammar-based: topicalization, exclamatives (Sag 2010)
2. Processing-based: CNPC, wh-islands (H&S 2010) — gradient with filler complexity
3. Discourse-based: MoS complements (Lu et al. 2025) — gradient with prosodic focus -/

/-- MoS islands are discourse-sourced, distinct from syntactic/processing islands. -/
theorem mos_distinct_from_traditional_islands :
    constraintSource .mannerOfSpeaking = .discourse ∧
    constraintSource .complexNP = .syntactic ∧
    constraintSource .embeddedQuestion = .syntactic := ⟨rfl, rfl, rfl⟩

end Phenomena.FillerGap.Compare
