module

/-!
# Generalised surprisal configurations

This file enumerates the parameters of the generalised surprisal family of
[giulianelli-etal-2026]: a warping function from expected scores to processing measures, a
scoring function of an alternative against the unit, a forecast horizon, and a representational
level. Standard surprisal [levy-2008] is the configuration with the negative logarithm, the
indicator, horizon one and the predictive level; information value is the family with the
identity, a distance, and a horizon and level. The tags denote real functions in
`Processing.Expectation.InformationValue`.

## References

* [giulianelli-etal-2026]
* [levy-2008]
* [smith-levy-2013]
* [meister-giulianelli-pimentel-2024]
-/

@[expose] public section

namespace Processing.PredictiveUncertainty

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
      [meister-giulianelli-pimentel-2024] -/
  | similarity
  deriving DecidableEq, Repr

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

/-- A generalised surprisal model: the complete parameter set for
a specific processing measure. -/
structure SurprisalConfig where
  warp    : WarpingFn
  scoring : ScoringFn
  horizon : ForecastHorizon
  level   : RepLevel
  deriving DecidableEq, Repr

/-- Standard surprisal: −log P(next word).
[levy-2008] [smith-levy-2013] -/
def standardSurprisal : SurprisalConfig where
  warp    := .negLog
  scoring := .indicator
  horizon := 1
  level   := .predictive

/-- Incremental information value at temporal-representational resolution (h, l).
[giulianelli-etal-2026] -/
def informationValue (h : ForecastHorizon) (l : RepLevel) : SurprisalConfig where
  warp    := .identity
  scoring := .distance
  horizon := h
  level   := l

/-- Standard surprisal is IAS at horizon 1 with predictive-level representation
and negLog/indicator replacing identity/distance. Subsumption by construction. -/
theorem ias_recovers_surprisal :
    { informationValue 1 .predictive with
        warp := .negLog, scoring := .indicator } =
    standardSurprisal := by
  rfl

end Processing.PredictiveUncertainty
