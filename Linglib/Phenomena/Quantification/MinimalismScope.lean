import Linglib.Theories.Syntax.Minimalism.Scope
import Linglib.Core.ScopeTypes
import Linglib.Phenomena.Quantification.Data
import Linglib.Phenomena.ArgumentStructure.Studies.Pylkkanen2008

/-!
# Bridge: Minimalist Scope Theory to Quantification Phenomena

Connects Minimalist QR/Scope Economy theory to empirical scope freezing data
in `Phenomena.Quantification.Data`.

## Main results

- `analyzeFreezingContext`: Maps freezing contexts to QR barriers
- `predictsFreezing`: Minimalist predictions for each context
- `possessor_freezes_scope`, `double_object_freezes_scope`, etc.: Verification theorems
- `configFromExample`, `predictAvailability`, `correctlyPredicts`: Per-datum predictions

## Superiority from C-Command

Double-object scope freezing is derived from asymmetric c-command in
@cite{pylkknen-2008}'s Voice + low-Appl tree (`ditransitiveTree`),
where the goal asymmetrically c-commands the theme.
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
  /-- The tree in which q1 and q2 are positioned. When provided,
      superiority is derived from c-command rather than stipulated. -/
  tree : Option Minimalism.SyntacticObject := none
  deriving Repr

/-- Check if superiority blocks QR in this configuration.

    When a tree and SO positions are provided, superiority is DERIVED
    from asymmetric c-command. Otherwise falls back to the freezing
    context annotation. -/
def superiorityBlocked (config : MinimalistScopeConfig) : Bool :=
  match config.tree, config.q1.so, config.q2.so with
  | some t, some s1, some s2 =>
    -- DERIVED: q1 asymmetrically c-commands q2
    superiorityFromTree t s1 s2
  | _, _, _ =>
    -- FALLBACK: use the freezing context annotation
    config.freezingContext == .doubleObject

/-- Compute available scope readings in Minimalism -/
def availableReadings (config : MinimalistScopeConfig) : Availability :=
  let q2Barrier := qrIsBlocked config.q2
  let contextBarrier := analyzeFreezingContext config.freezingContext
  let superiorityViolation := superiorityBlocked config

  if q2Barrier.isSome || contextBarrier.isSome || superiorityViolation then
    .surfaceOnly
  else
    .ambiguous

-- Predictions for Phenomena

/-- Build config from a freezing example (fallback path — no tree). -/
def configFromExample (ex : Example) : MinimalistScopeConfig :=
  { q1 := { quantifier := ex.quant1
          , position := .specTP
          , insideDP := ex.context == .possessor }
  , q2 := { quantifier := ex.quant2
          , position := if ex.context == .passive then .adjunct else .specVP }
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

-- ============================================================================
-- DOC Scope Freezing (derived from c-command)
-- ============================================================================

/-! ### Superiority derived from c-command

@cite{pylkknen-2008}'s Voice + low-Appl tree (`ditransitiveTree`) produces the
DOC structure where the goal asymmetrically c-commands the theme. QR of the
theme over the goal is blocked by superiority, derived from c-command rather
than stipulated. -/

open Phenomena.ArgumentStructure.Studies.Pylkkanen2008 in

/-- DOC scope freezing config with @cite{pylkknen-2008}'s tree:
    superiority is derived from goal asymmetrically c-commanding theme
    in the Voice + low-Appl structure. -/
def docScopeConfig : MinimalistScopeConfig :=
  { q1 := { quantifier := "every worker"
           , position := .specVP
           , so := some DP_mary_t }
  , q2 := { quantifier := "a paycheck"
           , position := .specVP
           , so := some DP_letter_t }
  , freezingContext := .doubleObject
  , tree := some ditransitiveTree }

open Phenomena.ArgumentStructure.Studies.Pylkkanen2008 in

/-- Superiority in the DOC is DERIVED from c-command in @cite{pylkknen-2008}'s
    tree: goal (Mary) asymmetrically c-commands theme (a letter) via low Appl,
    so QR of theme over goal is blocked. -/
theorem doc_superiority_from_tree :
    superiorityBlocked docScopeConfig = true := by native_decide

/-!
## Summary

### Freezing Explanations
| Context | Minimalist Explanation |
|---------|----------------------|
| Possessor | DP phase blocks QR |
| Double object | Superiority: goal c-commands theme (@cite{pylkknen-2008} tree) |
| Passive | Adjunct island |
| Heavy NP | NOT grammatical (processing) |
| Attitude | Clause boundary |
-/

end Phenomena.Quantification.MinimalismBridge
