/-
# Minimalist Scope Theory: QR and Scope Economy

Formalization of quantifier scope in the Minimalist tradition.

## Core Mechanisms

1. **Quantifier Raising (QR)**: Covert A'-movement of quantifiers to adjoin to TP/CP
2. **Scope Economy (Fox 2000)**: QR only applies if it yields a distinct interpretation
3. **Locality**: QR is clause-bounded and blocked by certain structural barriers

## Scope Freezing in Minimalism

Inverse scope is unavailable when:
- **Possessor**: Quantifier inside possessor DP cannot escape (DP is a phase/barrier)
- **Double Object**: Indirect object c-commands direct object; QR would violate locality
- **Passive**: By-phrase is an adjunct; QR from adjuncts is blocked

## References

- May (1985). Logical Form.
- Fox (2000). Economy and Scope.
- Bruening (2001). QR obeys Superiority.
- Szabolcsi (2010). Quantification.
-/

import Linglib.Core.Interfaces.ScopeTheory
import Linglib.Phenomena.Quantification.ScopeFreezing

namespace Minimalism.Scope

open ScopeTheory
open Phenomena.Quantification.ScopeFreezing

-- Structural Positions

/-- Structural positions relevant for scope -/
inductive Position where
  | specTP      -- Subject position (Spec-TP)
  | specVP      -- Object position (Spec-vP or complement of V)
  | adjunct     -- Adjunct position (by-phrase, PP modifier)
  | embedded    -- Inside a DP (possessor, PP complement)
  | complement  -- Clausal complement
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A quantifier with its structural position -/
structure PositionedQuantifier where
  quantifier : String
  position : Position
  /-- Is this inside another DP? -/
  insideDP : Bool := false
  /-- Is this in a double object construction? -/
  inDoubleObject : Bool := false
  deriving Repr

-- QR Operation

/--
Quantifier Raising (QR) as covert movement.

QR adjoins a quantifier to a clausal node (TP or CP),
allowing it to take scope over material it c-commands at LF.
-/
structure QROperation where
  /-- The quantifier being raised -/
  target : PositionedQuantifier
  /-- Landing site -/
  landingSite : Position
  /-- Does this create a new scope relation? -/
  createsNewScope : Bool
  deriving Repr

-- Locality Constraints on QR

/--
Barriers to QR movement.

Following phase theory and earlier barrier theory, certain nodes
block extraction/QR.
-/
inductive QRBarrier where
  | dpPhase       -- DP is a phase; QR cannot escape
  | clauseBoundary -- QR is clause-bounded (cannot cross CP)
  | adjunctIsland -- QR from adjuncts is blocked
  | superiority   -- QR cannot cross a c-commanding quantifier (Bruening)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Check if QR is blocked for a given quantifier -/
def qrIsBlocked (q : PositionedQuantifier) : Option QRBarrier :=
  if q.insideDP then some .dpPhase
  else if q.position == .adjunct then some .adjunctIsland
  else if q.position == .embedded then some .dpPhase
  else none

/-- Check if QR over another quantifier violates superiority -/
def violatesSuperiority (lower upper : PositionedQuantifier) : Bool :=
  -- In double object, IO c-commands DO; QR of DO over IO violates superiority
  lower.inDoubleObject && upper.inDoubleObject

-- Scope Economy (Fox 2000)

/--
Scope Economy: QR is only licensed if it creates a truth-conditional difference.

"Covert scope-shifting operations are blocked if they don't have
a semantic effect (i.e., if they yield a logically equivalent interpretation)."
-/
structure ScopeEconomy where
  /-- Surface scope interpretation -/
  surfaceInterpretation : String
  /-- Would-be inverse interpretation -/
  inverseInterpretation : String
  /-- Are they truth-conditionally equivalent? -/
  equivalent : Bool
  deriving Repr

/-- QR is blocked by economy if interpretations are equivalent -/
def economyBlocksQR (e : ScopeEconomy) : Bool :=
  e.equivalent

-- Freezing Context Analysis

/--
Analyze why a freezing context blocks inverse scope in Minimalism.
-/
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

/--
Minimalist representation of a scope configuration.
-/
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
  -- Check if QR of q2 over q1 is blocked
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

-- Summary

/-!
## Summary: Minimalist Scope Theory

### Core Claims
1. **QR**: Quantifiers covertly move to take scope
2. **Economy**: QR blocked if semantically vacuous
3. **Locality**: QR blocked by phases (DP, CP) and islands (adjuncts)

### Freezing Explanations
| Context | Minimalist Explanation |
|---------|----------------------|
| Possessor | DP phase blocks QR |
| Double object | Superiority: IO c-commands DO |
| Passive | Adjunct island |
| Heavy NP | NOT grammatical (processing) |
| Attitude | Clause boundary |

### Predictions
- Freezing is **categorical** (grammatical constraint)
- Context cannot rescue frozen readings
- All freezing contexts should behave uniformly

### What This Doesn't Capture
- Gradient judgments (passive is weaker than possessor)
- Context effects on scope availability
- Processing-based freezing (heavy NP)

See `Theories/Comparisons/ScopeFreezing.lean` for comparison with CCG.
-/

end Minimalism.Scope
