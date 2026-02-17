import Linglib.Theories.Pragmatics.NeoGricean.Evaluativity
import Linglib.Phenomena.Gradability.Evaluativity

/-!
# Bridge: NeoGricean Evaluativity → Empirical Data

Connects NeoGricean evaluativity theory (Rett 2015) predictions to
empirical evaluativity judgments from Phenomena.Gradability.Evaluativity.

## Bridge Content

- `predictedStatus`: Convert derivation to Phenomena EvaluativityStatus
- `predictionMatches`: Check if derivation matches empirical datum
- Per-datum verification theorems for all construction/polarity combinations

## References

- Rett, J. (2015). The Semantics of Evaluativity. Oxford University Press.
-/

namespace Phenomena.Gradability.NeoGricean_EvaluativityBridge

open NeoGricean.Evaluativity
open Phenomena.Gradability.Evaluativity


/--
Convert our derivation's evaluativity prediction to the phenomena format.
-/
def predictedStatus (d : EvaluativityDerivation) : EvaluativityStatus :=
  if d.isEvaluative then .evaluative else .nonEvaluative

/--
Check if prediction matches empirical datum.
-/
def predictionMatches (d : EvaluativityDerivation) (datum : EvaluativityDatum) : Bool :=
  -- Handle the special cases
  match datum.status with
  | .ungrammatical => true  -- Can't check ungrammatical cases
  | .markedOnly => d.polarity == .negative && d.isEvaluative
  | .evaluative => d.isEvaluative
  | .nonEvaluative => !d.isEvaluative


/--
**Theorem: Predictions match positive_tall datum**
-/
theorem matches_positive_tall :
    predictionMatches (deriveEvaluativity .positive .positive) positive_tall = true := by
  native_decide

/--
**Theorem: Predictions match comparative_tall datum**
-/
theorem matches_comparative_tall :
    predictionMatches (deriveEvaluativity .comparative .positive) comparative_tall = true := by
  native_decide

/--
**Theorem: Predictions match equative_tall datum**
-/
theorem matches_equative_tall :
    predictionMatches (deriveEvaluativity .equative .positive) equative_tall = true := by
  native_decide

/--
**Theorem: Predictions match equative_short datum**
-/
theorem matches_equative_short :
    predictionMatches (deriveEvaluativity .equative .negative) equative_short = true := by
  native_decide

/--
**Theorem: Predictions match question_tall datum**
-/
theorem matches_question_tall :
    predictionMatches (deriveEvaluativity .degreeQuestion .positive) question_tall = true := by
  native_decide

/--
**Theorem: Predictions match question_short datum**
-/
theorem matches_question_short :
    predictionMatches (deriveEvaluativity .degreeQuestion .negative) question_short = true := by
  native_decide


end Phenomena.Gradability.NeoGricean_EvaluativityBridge
