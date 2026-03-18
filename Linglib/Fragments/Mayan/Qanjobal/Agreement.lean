import Linglib.Theories.Syntax.Minimalism.Core.Features
import Linglib.Fragments.Mayan.Params

/-!
# Q'anjob'al Agreement and Case Fragment
@cite{imanishi-2020}

Agreement morphology and case assignment for Q'anjob'al (Q'anjob'alan,
Mayan), a **high absolutive** language with aspect-based split ergativity.

## The System

Q'anjob'al has the same Set A / Set B system as other Mayan languages.
Morpheme order: Asp-SET_B-SET_A-V (high absolutive order, like Kaqchikel).

Despite sharing high absolutive status with Kaqchikel, Q'anjob'al patterns
with Chol on the accusative side because the Restriction on Nominalization
(RON) does not hold: the nominalizing head *n* does not obligatorily select
for a vP lacking an external argument.
-/

namespace Fragments.Mayan.Qanjobal

open Minimalism

-- ============================================================================
-- § 1: Argument Positions
-- ============================================================================

/-- Argument positions in a Q'anjob'al clause. -/
inductive ArgPosition where
  | agent    -- A: transitive agent
  | patient  -- P: transitive patient
  | intranS  -- S: intransitive subject
  deriving DecidableEq, BEq, Repr

/-- Case assignment in perfective (ergative) clauses.
    Standard ergative alignment: A = ERG, S = P = ABS. -/
def ArgPosition.ergCase : ArgPosition → CaseVal
  | .agent   => .erg
  | .patient => .abs
  | .intranS => .abs

/-- Case assignment in non-perfective (accusative) clauses.
    Like Chol, the RON does not hold: the subject may appear inside the
    nominalized clause and gets GEN from D. The object receives ABS. -/
def ArgPosition.accCase : ArgPosition → CaseVal
  | .agent   => .gen
  | .patient => .abs
  | .intranS => .gen

def argPositions : List ArgPosition := [.agent, .patient, .intranS]

-- ============================================================================
-- § 2: Verification
-- ============================================================================

/-- Ergative alignment in perfective. -/
theorem erg_abs_alignment :
    ArgPosition.agent.ergCase ≠ ArgPosition.patient.ergCase ∧
    ArgPosition.patient.ergCase = ArgPosition.intranS.ergCase :=
  ⟨by decide, rfl⟩

/-- Accusative alignment in non-perfective: same as Chol type. -/
theorem acc_alignment :
    ArgPosition.agent.accCase = ArgPosition.intranS.accCase ∧
    ArgPosition.agent.accCase ≠ ArgPosition.patient.accCase :=
  ⟨rfl, by decide⟩

-- ============================================================================
-- § 3: Absolutive Position (HIGH-ABS)
-- ============================================================================

/-- Q'anjob'al's absolutive morphemes appear in high position (on the
    aspect marker, pre-stem). Observable from morpheme order:
    ASP-ABS-ERG-ROOT-SUFFIX. -/
def absPosition : Fragments.Mayan.ABSPosition := .high

end Fragments.Mayan.Qanjobal
