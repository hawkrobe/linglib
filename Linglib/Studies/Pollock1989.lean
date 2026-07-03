import Linglib.Syntax.Minimalist.Movement.VerbMovementParameter
import Linglib.Data.Examples.Pollock1989

/-!
# Pollock's Verb Movement Diagnostics
[pollock-1989]

Connects the Minimalist verb movement parameter
(`Syntax/Minimalist/VerbMovementParameter.lean`) to Pollock's
French/English diagnostic paradigm (`Data/Examples/Pollock1989.json`).

## Main declarations

- `paramOf`, `diagOf`: adapters reading a row's language and
  `paperFeatures` into `VMovementParam` and `VDiagnostic`
- `acceptable_iff_order_predicted`: a row is acceptable iff the theory's
  predicted V/diagnostic order matches the row's attested surface order
- `all_diagnostics_converge`: all four diagnostics agree for any
  parameter setting
- `doSupport_iff_no_raising`: do-support anticorrelates with V-raising
-/

namespace Pollock1989

open Data.Examples
open Minimalist

-- ============================================================================
-- § 1  Transfer Equation over Pollock's Rows
-- ============================================================================

/-- Movement-parameter adapter: French lexical verbs raise, English
    lexical verbs stay in situ, English auxiliaries raise. -/
def paramOf (row : LinguisticExample) : Option VMovementParam :=
  match row.language, row.feature? "verb_type" with
  | "stan1290", some "lexical"   => some french
  | "stan1293", some "lexical"   => some englishLexical
  | "stan1293", some "auxiliary" => some englishAux
  | _, _ => none

/-- Diagnostic adapter: the row's `diagnostic` feature as a `VDiagnostic`. -/
def diagOf (row : LinguisticExample) : Option VDiagnostic :=
  match row.feature? "diagnostic" with
  | some "inversion" => some .inversion
  | some "adverb"    => some .adverb
  | some "negation"  => some .negation
  | some "floatingQ" => some .floatingQ
  | _ => none

/-- The theory's predicted surface order: does the verb precede the
    diagnostic element? -/
def predictedOrder (row : LinguisticExample) : Option Bool := do
  pure (verbPrecedesDiagnostic (← paramOf row) (← diagOf row))

/-- The attested surface order recorded in the row's
    `v_precedes_diagnostic` feature. -/
def surfaceOrder (row : LinguisticExample) : Option Bool :=
  (row.feature? "v_precedes_diagnostic").map (· == "true")

/-- **Transfer equation**: a Pollock row is acceptable iff the verb
    movement parameter predicts exactly the attested surface order.
    The marginal row (`ex_p12`, "John often has eaten pizza") sits on
    the not-acceptable side: the auxiliary should raise, so the
    Adv > Aux order mismatches the prediction. -/
theorem acceptable_iff_order_predicted :
    ∀ row ∈ Examples.all,
      row.judgment = .acceptable ↔ predictedOrder row = surfaceOrder row := by
  decide

-- ============================================================================
-- § 2  Diagnostic Convergence
-- ============================================================================

/-! All four diagnostics agree for any parameter setting. This is the core
of Pollock's argument: the four tests are not independent observations but
consequences of a single parameter (V-raises vs. V-in-situ). -/

/-- For any parameter setting, all four diagnostics give the same answer. -/
theorem all_diagnostics_converge (p : VMovementParam) (d₁ d₂ : VDiagnostic) :
    verbPrecedesDiagnostic p d₁ = verbPrecedesDiagnostic p d₂ :=
  diagnostics_converge p d₁ d₂

-- ============================================================================
-- § 3  Do-Support / V-Raising Anticorrelation
-- ============================================================================

/-! Do-support and verb raising are complementary: a parameter setting that
raises V never needs do-support, and a setting that keeps V in situ always
needs it. This follows from the theory: do-support exists *because* V
cannot raise. -/

/-- Do-support is needed iff V does not raise past negation. -/
theorem doSupport_iff_no_raising (p : VMovementParam) (ctx : TenseSupportContext) :
    needsDoSupport p ctx = !verbPrecedesDiagnostic p .negation :=
  doSupport_anticorrelates_raising p ctx

end Pollock1989
