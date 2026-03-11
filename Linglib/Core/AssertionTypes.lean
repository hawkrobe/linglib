/-!
# Assertion Types

Theory-neutral data types for assertion discourse phenomena.
-/

namespace Interfaces

/-- The possible outcomes of an assertion in discourse.

    Not all theories distinguish all four outcomes:
    - Stalnaker: only `accepted` (assertion = CG update)
    - Farkas & Bruce: `accepted` vs `pending` (table model)
    - Krifka/Brandom: all four (commitment space / scorekeeping) -/
inductive AssertionOutcome where
  /-- Proposition enters the common ground -/
  | accepted
  /-- Proposition on the table, awaiting resolution -/
  | pending
  /-- Previously accepted proposition withdrawn -/
  | retracted
  /-- Assertion met with a demand for reasons -/
  | challenged
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Assertion-related phenomena that theories may handle. -/
inductive AssertionPhenomenon where
  /-- Basic assertion adds to common ground -/
  | basicAssertion
  /-- Hedging reduces commitment strength -/
  | hedging
  /-- Oath formulae increase commitment strength -/
  | oathFormulae
  /-- Rising declaratives shift commitment source -/
  | risingDeclaratives
  /-- Retraction / taking back a prior commitment -/
  | retraction
  /-- Lying: commitment without belief -/
  | lying
  /-- Challenging: demanding reasons for a commitment -/
  | challenging
  deriving DecidableEq, Repr, BEq

end Interfaces
