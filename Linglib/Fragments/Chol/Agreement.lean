import Linglib.Theories.Syntax.Minimalism.Core.Features

/-!
# Chol Agreement and Case Fragment @cite{coon-2010a} @cite{coon-2013a}
@cite{imanishi-2020}

Agreement morphology and case assignment for Chol (Cholan, Mayan), a
**low absolutive** language with aspect-based split ergativity.

## The System

Chol has two agreement paradigms:
- **Set A** (ERG/GEN): prefixes cross-referencing the transitive agent
- **Set B** (ABS): suffixes cross-referencing the absolutive argument

Morpheme order: Asp-SET_A-V-SET_B (low absolutive order, contrasting with
Kaqchikel's Asp-SET_B-SET_A-V).

## Case Licensing (@cite{coon-2013a}; @cite{imanishi-2020}, §2.4.3)

- **ERG**: inherent from transitive *v*
- **ABS** (transitive): structural from Voice (low absolutive)
- **ABS** (intransitive): structural from Infl

## Accusative Side (Non-Perfective)

In non-perfective aspect, the aspectual predicate *choñkol* embeds a
nominalized clause. The RON does NOT hold: the external argument may be
generated inside the nominalized clause. Result: S/A = GEN (from D),
O = ABS (from Voice).
-/

namespace Fragments.Chol

open Minimalism

-- ============================================================================
-- § 1: Argument Positions
-- ============================================================================

/-- Argument positions in a Chol clause. -/
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
    Since the RON does not hold, the subject appears inside the nominalized
    clause as the highest DP and receives GEN from D. The object receives
    ABS from Voice (low absolutive). -/
def ArgPosition.accCase : ArgPosition → CaseVal
  | .agent   => .gen
  | .patient => .abs
  | .intranS => .gen

def argPositions : List ArgPosition := [.agent, .patient, .intranS]

-- ============================================================================
-- § 2: Verification
-- ============================================================================

/-- Ergative alignment in perfective: A distinguished from S/P. -/
theorem erg_abs_alignment :
    ArgPosition.agent.ergCase ≠ ArgPosition.patient.ergCase ∧
    ArgPosition.patient.ergCase = ArgPosition.intranS.ergCase :=
  ⟨by decide, rfl⟩

/-- Accusative alignment in non-perfective: S = A (GEN), O distinct (ABS). -/
theorem acc_alignment :
    ArgPosition.agent.accCase = ArgPosition.intranS.accCase ∧
    ArgPosition.agent.accCase ≠ ArgPosition.patient.accCase :=
  ⟨rfl, by decide⟩

/-- Extended ergative: all subjects get GEN (= set A) in non-perfective. -/
theorem extended_ergative :
    ArgPosition.agent.accCase = .gen ∧
    ArgPosition.intranS.accCase = .gen := ⟨rfl, rfl⟩

end Fragments.Chol
