import Linglib.Core.DecisionTheory

/-!
# Decision-Theoretic Question Semantics (re-export shim)

All decision-theoretic infrastructure now lives in `Core.DecisionTheory`.
This file re-exports those names into the `Semantics.Questions` namespace so
that existing `open Semantics.Questions` sites continue to compile.

Blackwell's theorem and the G&S ↔ Van Rooy bridge live in
`Semantics.Questions.GSVanRooyBridge`.
-/

namespace Semantics.Questions

export Core.DecisionTheory (
  DecisionProblem
  expectedUtility optimalAction dpValue
  conditionalEU valueAfterLearning utilityValue cellProbability
  securityLevel maximinValue conditionalSecurityLevel
  maximinAfterLearning maximinUtilityValue
  questionUtility
  questionMaximin maximinUtilityValue_nonneg
  Question
  resolves resolvingAnswers isMentionSome isMentionAll
  epistemicDP completeInformationDP mentionSomeDP
)

end Semantics.Questions
