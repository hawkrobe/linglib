/-!
# Generalised Surprisal and Incremental Alternative Sampling
@cite{giulianelli-etal-2026} @cite{giulianelli-opedal-cotterell-2024}

Parameterized family of processing difficulty measures that decomposes
prediction into explicit temporal and representational dimensions,
generalizing standard surprisal.

Standard surprisal treats prediction error as a single scalar
(−log P(next word)). The generalised framework disentangles this into:

1. A **warping function** f mapping expected scores to processing measures
2. A **scoring function** g measuring how well alternatives match the target
3. A **forecast horizon** h: how many future symbols are considered
4. A **representational level**: the abstraction at which alternatives are compared

Standard surprisal is the special case (negLog, indicator, 1, predictive).
Incremental information value is the family (identity, distance, h, l).

## Main definitions

- `SurprisalConfig`: Complete generalised surprisal specification
- `standardSurprisal`: The configuration corresponding to @cite{levy-2008}
- `informationValue`: The IAS configuration at a given (horizon, level)
- `PsychMeasure`: Standard psycholinguistic response types
- `ias_recovers_surprisal`: Standard surprisal is a special case of IAS

## Connection to existing infrastructure

- `Core.InformationTheory.conditionalEntropy` computes H(W|M), the expected
  surprisal under bounded memory
- `Core.Divergence.kl_pointMass_eq_neg_log`: KL with point mass = surprisal
- `Core.ProcessingModel.ProcessingProfile`: multi-dimensional processing cost,
  which IAS motivates decomposing by temporal and representational resolution
-/

set_option autoImplicit false

namespace Core.GeneralisedSurprisal

-- ============================================================================
-- §1: Warping and Scoring Functions
-- ============================================================================

/-- Warping functions mapping expected scores to processing measures.
γ(w;c) = f(E[g(a,w,c)]). -/
inductive WarpingFn where
  /-- f(x) = −log(x): standard surprisal (bits) -/
  | negLog
  /-- f(x) = x: information value (raw expected distance) -/
  | identity
  deriving DecidableEq, BEq, Repr

/-- Scoring functions measuring prediction accuracy.
g(a, w, c) evaluates alternative a against target w in context c. -/
inductive ScoringFn where
  /-- 𝟙{w ≤ a}: binary prefix match. With negLog → standard surprisal. -/
  | indicator
  /-- d_r(a, w): representational distance. With identity → information value. -/
  | distance
  /-- sim(r(a), r(w)): semantic similarity.
      @cite{meister-giulianelli-pimentel-2024} -/
  | similarity
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2: Temporal and Representational Resolution
-- ============================================================================

/-- Forecast horizon: how many future symbols each alternative spans.
h = 1 is standard surprisal's implicit horizon (next word only). -/
abbrev ForecastHorizon := Nat

/-- Representational level at which predictions are evaluated.

Different layers of a neural language model capture different levels of
linguistic processing. The key finding is that the most predictive level
varies by psycholinguistic measure: lexical identity layers best predict
explicit predictability; intermediate layers best predict reading times. -/
inductive RepLevel where
  /-- Layer 0 / embedding: decontextualized lexical identity -/
  | lexical
  /-- Early-to-intermediate layers: shallow syntactic processing -/
  | shallowSyntactic
  /-- Intermediate layers: deep syntactic, shallow semantic -/
  | syntactic
  /-- Deep layers: fully contextualized semantics -/
  | semantic
  /-- Final layer: specialized for next-token prediction -/
  | predictive
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §3: Distance Summary Statistics
-- ============================================================================

/-- How pairwise distances between alternative sets are aggregated.

Different summaries capture different notions of predictability:
`mean` is the unbiased discrepancy estimate; `min` asks whether *any*
hypothesis is close to the outcome; `max` captures worst-case error.

Key finding: under `min`, surprisal correlates most strongly with
intermediate layers and medium horizons, revealing that surprisal's
predictability is closest to a best-case (closest-hypothesis) notion
rather than average discrepancy. -/
inductive DistanceSummary where
  /-- Average pairwise distance. Equivalent to the original information
      value definition. -/
  | mean
  /-- Minimum pairwise distance. Closest pre-observation hypothesis. -/
  | min
  /-- Maximum pairwise distance. Worst-case prediction error. -/
  | max
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §4: Surprisal Configurations
-- ============================================================================

/-- A generalised surprisal model: the complete parameter set for
a specific processing measure. -/
structure SurprisalConfig where
  warp    : WarpingFn
  scoring : ScoringFn
  horizon : ForecastHorizon
  level   : RepLevel
  deriving DecidableEq, BEq, Repr

/-- Standard surprisal: −log P(next word).
@cite{levy-2008} @cite{smith-levy-2013} -/
def standardSurprisal : SurprisalConfig where
  warp    := .negLog
  scoring := .indicator
  horizon := 1
  level   := .predictive

/-- Incremental information value at temporal-representational resolution (h, l).
@cite{giulianelli-etal-2026} -/
def informationValue (h : ForecastHorizon) (l : RepLevel) : SurprisalConfig where
  warp    := .identity
  scoring := .distance
  horizon := h
  level   := l

-- ============================================================================
-- §5: Psycholinguistic Measures
-- ============================================================================

/-- Standard psycholinguistic response types that index processing effort. -/
inductive PsychMeasure where
  | predictabilityRating  -- Likert-scale (1–5) predictability judgement
  | clozeProbability      -- Proportion of cloze completions matching target
  | clozeSurprisal        -- −log(cloze probability)
  | firstFixationRT       -- First fixation duration (eye-tracking)
  | firstPassRT           -- First-pass reading time (eye-tracking)
  | rightBoundedRT        -- Right-bounded reading time (eye-tracking)
  | goPastRT              -- Go-past time including regressions (eye-tracking)
  | selfPacedRT           -- Button-press latency (self-paced reading)
  | n400                  -- N400 ERP amplitude: semantic prediction error
  | p600                  -- P600 ERP amplitude: syntactic integration
  deriving DecidableEq, BEq, Repr

/-- Explicit predictability judgements (cloze, rating) vs. implicit processing
signatures (RTs, ERPs). Best-predicting IAS configurations differ between
these classes: explicit measures peak at h = 1 with lexical-level
representations; implicit measures benefit from longer horizons and
intermediate representations. -/
def PsychMeasure.isExplicit : PsychMeasure → Bool
  | .predictabilityRating | .clozeProbability | .clozeSurprisal => true
  | _ => false

/-- Expected sign of the relationship between information value and measurement.
Positive: higher info value → larger response. Negative: inverse. -/
def PsychMeasure.expectedSign : PsychMeasure → Int
  | .predictabilityRating => -1
  | .clozeProbability     => -1
  | .clozeSurprisal       =>  1
  | .firstFixationRT      =>  1
  | .firstPassRT          =>  1
  | .rightBoundedRT       =>  1
  | .goPastRT             =>  1
  | .selfPacedRT          =>  1
  | .n400                 => -1  -- more surprising → more negative deflection
  | .p600                 =>  1

-- ============================================================================
-- §6: Key Relationships
-- ============================================================================

/-- Standard surprisal is IAS at horizon 1 with predictive-level representation
and negLog/indicator replacing identity/distance. Subsumption by construction. -/
theorem ias_recovers_surprisal :
    { informationValue 1 .predictive with
        warp := .negLog, scoring := .indicator } =
    standardSurprisal := by
  rfl

end Core.GeneralisedSurprisal
