/-!
# Generalised Surprisal Configuration
@cite{giulianelli-etal-2026}

Enum-level configuration for the generalised surprisal family. The
real-valued semantics of these enum tags lives in `IAS.lean`; this file
just enumerates the parameter axes.

A generalised surprisal model has four parameters:

1. A **warping function** f mapping expected scores to processing measures
2. A **scoring function** g measuring how well alternatives match the target
3. A **forecast horizon** h: how many future symbols are considered
4. A **representational level**: the abstraction at which alternatives are compared

Standard surprisal is the special case (negLog, indicator, 1, predictive).
Incremental information value is the family (identity, distance, h, l).

## Scope note

Per linglib's processing-library scope (CLAUDE.md): this file formalizes
the *parameter space* of a processing-theory family. It does not
formalize psycholinguistic measurement instruments (N400, P600, RT,
cloze, etc.) or empirical-fit tables — those are out of scope. Per-paper
empirical findings about which (h, l) configuration best predicts which
measure live in study-file docstring prose with citations, not as Lean
theorems.

## Main definitions

- `SurprisalConfig`: Complete generalised surprisal parameter tuple
- `standardSurprisal`: The configuration corresponding to @cite{levy-2008}
- `informationValue`: The IAS configuration at a given (horizon, level)
- `ias_recovers_surprisal`: Standard surprisal is a special case of IAS
-/

set_option autoImplicit false

namespace Theories.Processing.PredictiveUncertainty

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Temporal and Representational Resolution
-- ============================================================================

/-- Forecast horizon: how many future symbols each alternative spans.
h = 1 is standard surprisal's implicit horizon (next word only). -/
abbrev ForecastHorizon := Nat

/-- Representational level at which predictions are evaluated.

These tags name *layers of abstraction* — the kind of representational
space in which alternatives are compared. They are not claims about
specific layers of any particular neural network. -/
inductive RepLevel where
  /-- Decontextualised lexical identity (token / embedding) -/
  | lexical
  /-- Shallow syntactic structure (linear order, POS) -/
  | shallowSyntactic
  /-- Compositional syntactic structure -/
  | syntactic
  /-- Fully contextualised semantic content -/
  | semantic
  /-- Predictive distribution over next symbols -/
  | predictive
  deriving DecidableEq, Repr

-- ============================================================================
-- §3: Surprisal Configurations
-- ============================================================================

/-- A generalised surprisal model: the complete parameter set for
a specific processing measure. -/
structure SurprisalConfig where
  warp    : WarpingFn
  scoring : ScoringFn
  horizon : ForecastHorizon
  level   : RepLevel
  deriving DecidableEq, Repr

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
-- §4: Key Relationships
-- ============================================================================

/-- Standard surprisal is IAS at horizon 1 with predictive-level representation
and negLog/indicator replacing identity/distance. Subsumption by construction. -/
theorem ias_recovers_surprisal :
    { informationValue 1 .predictive with
        warp := .negLog, scoring := .indicator } =
    standardSurprisal := by
  rfl

end Theories.Processing.PredictiveUncertainty
