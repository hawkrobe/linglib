import Linglib.Theories.Semantics.Events.Agentivity
import Linglib.Phenomena.Aspect.DiagnosticsBridge

/-!
# Bridge: Agentivity → Aspect Diagnostics

Connects Cruse (1973) agentivity decomposition to VendlerClass diagnostic
predictions from `Phenomena.Aspect.DiagnosticsBridge`.

The do-test prediction for each Vendler class is derived from the agentivity
theory: the do-test accepts durative dynamic classes (activity, accomplishment)
and is marginal for others.

## References

- Cruse, D. A. (1973). Some Thoughts on Agentivity. Journal of
  Linguistics 9(1), 11–23.
-/


namespace Phenomena.Aspect.AgentivityBridge

open Semantics.Lexical.Verb.Aspect
open Phenomena.Aspect.Diagnostics

-- ════════════════════════════════════════════════════
-- Diagnostic Predictions
-- ════════════════════════════════════════════════════

/-- Predict the do-test result for each Vendler class.

    - **State** → marginal: some pass (stand, sit, hold — via volitive)
      but most don't (know, love — no agentivity features)
    - **Activity** → accept: paradigmatic do-sentences ("John ran" →
      "What John did was run")
    - **Achievement** → marginal: some pass ("die in order to save…"
      — arguably volitive), most don't
    - **Accomplishment** → accept: all dynamic + extended → do-test -/
def doTestPrediction : VendlerClass → DiagnosticResult
  | .state         => .marginal
  | .activity      => .accept
  | .achievement   => .marginal
  | .accomplishment => .accept

/-- The do-test accepts exactly the durative dynamic classes
    (activity, accomplishment). -/
theorem doTest_accepts_durative_dynamic (c : VendlerClass) :
    doTestPrediction c = .accept ↔
    (c.duration = .durative ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [doTestPrediction, VendlerClass.duration, VendlerClass.dynamicity]

/-- Passing the do-test (for a whole Vendler class, not marginal)
    implies either a dynamic event or a volitive state.

    Formally: if a Vendler class fully accepts the do-test (not just
    marginally), then it must be dynamic. Statives only get marginal
    because the do-test passes only for select volitive statives. -/
theorem doTest_accept_implies_dynamic (c : VendlerClass) :
    doTestPrediction c = .accept → c.dynamicity = .dynamic := by
  cases c <;> simp [doTestPrediction, VendlerClass.dynamicity]

/-- The do-test and imperative test agree on activities and
    accomplishments (both diagnostics accept dynamic durative events).
    They diverge on states (do-test: marginal; imperative: reject)
    and achievements (do-test: marginal; imperative: marginal — but
    for different reasons). -/
theorem doTest_agrees_imperative_for_dynamic_durative (c : VendlerClass)
    (hDyn : c.dynamicity = .dynamic) (hDur : c.duration = .durative) :
    doTestPrediction c = imperativePrediction c := by
  cases c <;> simp_all [doTestPrediction, imperativePrediction,
    VendlerClass.dynamicity, VendlerClass.duration]

end Phenomena.Aspect.AgentivityBridge
