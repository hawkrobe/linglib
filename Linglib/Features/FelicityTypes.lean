/-!
# Felicity Types
@cite{fox-hackl-2006} @cite{katzir-singh-2015} @cite{magri-2009} @cite{spector-2014}

Theory-neutral data types for felicity/oddness predictions.
-/

namespace Interfaces

/-- Felicity status for an utterance in context. -/
inductive FelicityStatus where
  /-- The utterance is felicitous (no oddness). -/
  | felicitous
  /-- The utterance is odd (# marks in linguistics). -/
  | odd
  /-- Borderline: some conditions met, others not. -/
  | borderline
  deriving DecidableEq, Repr

/-- Source of oddness (which condition was violated). -/
inductive OddnessSource where
  /-- Question Condition: QUD trivially settled by CK. -/
  | questionCondition
  /-- Answer Condition: needlessly inferior alternative exists. -/
  | answerCondition
  /-- Both conditions violated. -/
  | both
  /-- Blind Mismatch: strengthened meaning contradicts common knowledge
      (@cite{magri-2009} Mismatch Hypothesis, §3.2.2). -/
  | blindMismatch
  /-- Blind Presuppositional Mismatch: strengthened presupposition contradicts
      common knowledge (@cite{magri-2009} MH_prs, §3.4). -/
  | blindPresupMismatch
  /-- Theory doesn't distinguish sources. -/
  | unspecified
  deriving DecidableEq, Repr

/-- Result of a felicity check: status + optional source information. -/
structure FelicityResult where
  status : FelicityStatus
  source : Option OddnessSource := none
  deriving Repr

end Interfaces
