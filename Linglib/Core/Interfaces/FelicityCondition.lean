import Linglib.Core.QUD
import Linglib.Core.Proposition

/-!
# FelicityCondition

Abstract interface for felicity/oddness predictions, following the
`ImplicatureTheory` pattern. Provides a unified type for comparing
K&S (2015), Magri (2009), Spector (2014), Fox & Hackl (2006), and
future felicity theories.

## References

- Katzir, R. & Singh, R. (2015). Economy of structure and information.
- Magri, G. (2009). Individual-level predicates and mandatory scalar implicatures.
- Spector, B. (2014). Scalar implicatures, blindness and common knowledge.
- Fox, D. & Hackl, M. (2006). The universal density of measurement.
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
  deriving DecidableEq, BEq, Repr

/-- Source of oddness (which condition was violated). -/
inductive OddnessSource where
  /-- Question Condition: QUD trivially settled by CK. -/
  | questionCondition
  /-- Answer Condition: needlessly inferior alternative exists. -/
  | answerCondition
  /-- Both conditions violated. -/
  | both
  /-- Theory doesn't distinguish sources. -/
  | unspecified
  deriving DecidableEq, BEq, Repr

/-- Result of a felicity check: status + optional source information. -/
structure FelicityResult where
  status : FelicityStatus
  source : Option OddnessSource := none
  deriving Repr

/-- A theory that makes predictions about utterance felicity/oddness. -/
class FelicityCondition (T : Type*) where
  /-- Name of the theory. -/
  name : String
  /-- Check whether an input is felicitous, odd, or borderline. -/
  check : T → FelicityResult

variable {T : Type*} [FelicityCondition T]

/-- Is the input felicitous? -/
def isFelicitous (t : T) : Bool :=
  (FelicityCondition.check t).status == .felicitous

/-- Is the input odd? -/
def isOdd (t : T) : Bool :=
  (FelicityCondition.check t).status == .odd

/-- Two felicity theories agree on an input if they give the same status. -/
def felicityAgree {α T₁ T₂ : Type*} [FelicityCondition T₁] [FelicityCondition T₂]
    (f : α → T₁) (g : α → T₂) (a : α) : Bool :=
  (FelicityCondition.check (f a)).status == (FelicityCondition.check (g a)).status

end Interfaces
