import Linglib.Core.DecisionTheory

/-!
# Decision-Theoretic Question Semantics (re-export shim)

All decision-theoretic infrastructure now lives in `Core.DecisionTheory`.
This file re-exports those names into the `QuestionSemantics` namespace so
that existing `open QuestionSemantics` sites continue to compile.

Blackwell's theorem and the G&S ↔ Van Rooy bridge live in
`QuestionSemantics.GSVanRooyBridge`.
-/

namespace QuestionSemantics

export Core.DecisionTheory (
  DecisionProblem
  expectedUtility optimalAction dpValue
  conditionalEU valueAfterLearning utilityValue cellProbability
  securityLevel maximinValue conditionalSecurityLevel
  maximinAfterLearning maximinUtilityValue
  questionUtility questionUtility_nonneg
  questionMaximin maximinUtilityValue_nonneg
  Question
  resolves resolvingAnswers isMentionSome isMentionAll
  epistemicDP completeInformationDP mentionSomeDP
)

end QuestionSemantics
