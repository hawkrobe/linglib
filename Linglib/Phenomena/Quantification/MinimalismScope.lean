import Linglib.Theories.Syntax.Minimalism.Scope
import Linglib.Phenomena.Quantification.Data

/-!
# Bridge: Minimalist Scope Theory to Quantification Phenomena

Connects Minimalist QR/Scope Economy theory to empirical scope freezing data
in `Phenomena.Quantification.Data`.

## Main results

- `analyzeFreezingContext`: Maps freezing contexts to QR barriers
- `predictsFreezing`: Minimalist predictions for each context
- `possessor_freezes_scope`, `double_object_freezes_scope`, etc.: Verification theorems
- `configFromExample`, `predictAvailability`, `correctlyPredicts`: Per-datum predictions
-/

namespace Phenomena.Quantification.MinimalismBridge

open ScopeTheory
open Phenomena.Quantification.Data
open Minimalism.Phenomena.Scope

-- Freezing Context Analysis

/-- Analyze why a freezing context blocks inverse scope in Minimalism. -/
def analyzeFreezingContext : FreezingContext → Option QRBarrier
  | .none => none  -- No barrier
  | .possessor => some .dpPhase  -- Quantifier trapped in possessor DP
  | .doubleObject => some .superiority  -- IO c-commands DO
  | .passive => some .adjunctIsland  -- By-phrase is adjunct
  | .heavyNP => none  -- Not a grammatical barrier (processing)
  | .weakCrossover => none  -- Blocked by binding, not QR locality
  | .adjunct => some .adjunctIsland
  | .attitude => some .clauseBoundary

/-- Does Minimalism predict freezing for this context? -/
def predictsFreezing (ctx : FreezingContext) : Bool :=
  (analyzeFreezingContext ctx).isSome

-- Scope Availability in Minimalism

/-- Minimalist representation of a scope configuration. -/
structure MinimalistScopeConfig where
  /-- Higher quantifier (typically subject) -/
  q1 : PositionedQuantifier
  /-- Lower quantifier (typically object) -/
  q2 : PositionedQuantifier
  /-- Freezing context if any -/
  freezingContext : FreezingContext := .none
  deriving Repr

/-- Compute available scope readings in Minimalism -/
def availableReadings (config : MinimalistScopeConfig) : Availability :=
  let q2Barrier := qrIsBlocked config.q2
  let contextBarrier := analyzeFreezingContext config.freezingContext
  let superiorityViolation := violatesSuperiority config.q2 config.q1

  if q2Barrier.isSome || contextBarrier.isSome || superiorityViolation then
    .surfaceOnly
  else
    .ambiguous

-- HasAvailableScopes Instance

/-- Marker type for Minimalist scope theory -/
structure MinimalismScopeTheory where
  deriving Repr, Inhabited

/-- Surface reading: q1 > q2 -/
def surfaceReading (config : MinimalistScopeConfig) : ScopeReading :=
  ⟨[config.q1.quantifier, config.q2.quantifier]⟩

/-- Inverse reading: q2 > q1 -/
def inverseReading (config : MinimalistScopeConfig) : ScopeReading :=
  ⟨[config.q2.quantifier, config.q1.quantifier]⟩

instance : HasAvailableScopes MinimalismScopeTheory MinimalistScopeConfig where
  availableScopes config :=
    let avail := availableReadings config
    match avail with
    | .ambiguous => ⟨[surfaceReading config, inverseReading config], by simp⟩
    | .surfaceOnly => ⟨[surfaceReading config], by simp⟩
    | .inverseOnly => ⟨[inverseReading config], by simp⟩

-- Predictions for Phenomena

/-- Build config from a freezing example -/
def configFromExample (ex : Example) : MinimalistScopeConfig :=
  { q1 := { quantifier := ex.quant1
          , position := .specTP
          , insideDP := ex.context == .possessor
          , inDoubleObject := ex.context == .doubleObject }
  , q2 := { quantifier := ex.quant2
          , position := if ex.context == .passive then .adjunct else .specVP
          , insideDP := false
          , inDoubleObject := ex.context == .doubleObject }
  , freezingContext := ex.context }

/-- Minimalism's prediction for an example -/
def predictAvailability (ex : Example) : Availability :=
  availableReadings (configFromExample ex)

/-- Check if Minimalism correctly predicts the example -/
def correctlyPredicts (ex : Example) : Bool :=
  predictAvailability ex == ex.observed

-- Theoretical Claims as Theorems

/-- Possessor freezing follows from DP being a phase -/
theorem possessor_freezes_scope :
    predictsFreezing .possessor = true := rfl

/-- Double object freezing follows from superiority -/
theorem double_object_freezes_scope :
    predictsFreezing .doubleObject = true := rfl

/-- Passive freezing follows from adjunct island -/
theorem passive_freezes_scope :
    predictsFreezing .passive = true := rfl

/-- Heavy NP is NOT predicted to freeze (it's processing) -/
theorem heavy_np_not_grammatically_frozen :
    predictsFreezing .heavyNP = false := rfl

/-- Baseline (no context) is predicted ambiguous -/
theorem baseline_is_ambiguous :
    predictsFreezing .none = false := rfl

/-!
## Summary

### Freezing Explanations
| Context | Minimalist Explanation |
|---------|----------------------|
| Possessor | DP phase blocks QR |
| Double object | Superiority: IO c-commands DO |
| Passive | Adjunct island |
| Heavy NP | NOT grammatical (processing) |
| Attitude | Clause boundary |
-/

end Phenomena.Quantification.MinimalismBridge
