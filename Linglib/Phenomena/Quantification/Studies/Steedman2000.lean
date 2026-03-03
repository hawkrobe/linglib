import Linglib.Theories.Syntax.CCG.Scope
import Linglib.Phenomena.Quantification.Data

/-!
# CCG Scope Bridge
@cite{steedman-2000}

Connects CCG scope theory (from `Theories.Syntax.CCG.Scope`) to
empirical scope-word-order data (from `Phenomena.Quantification.Data`).

Proves that CCG derivation types correctly predict scope availability
based on verb order (verb raising vs. verb projection raising).

-/

namespace Phenomena.Quantification.CCGBridge

open CCG
open CCG.Scope
open ScopeTheory
open Phenomena.Quantification.Data

/-- Map Phenomena.Quantification.Data.VerbOrder to CCG derivation type. -/
def verbOrderToDerivationType : VerbOrder → DerivationType
  | .verbRaising => .composed           -- Object + embedded verb via composition
  | .verbProjectionRaising => .directApp -- Matrix verb first, standard application

/-- Helper to convert ScopeAvailability to BinaryScopeAvailability. -/
def ScopeAvailability.toBinaryScopeAvailability : ScopeAvailability → BinaryScopeAvailability
  | .surfaceOnly => .surfaceOnly
  | .ambiguous => .ambiguous

/-- CCG prediction matches observed scope availability. -/
theorem ccg_predicts_verb_raising_scope (vo : VerbOrder) :
    derivationTypeToAvailability (verbOrderToDerivationType vo) =
    ScopeAvailability.toBinaryScopeAvailability (wordOrderToAvailability vo) := by
  cases vo <;> rfl

end Phenomena.Quantification.CCGBridge
