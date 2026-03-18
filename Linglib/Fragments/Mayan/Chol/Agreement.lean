import Linglib.Theories.Syntax.Minimalism.Core.Features
import Linglib.Core.ExtractionMorphology
import Linglib.Fragments.Mayan.Params

/-!
# Chol Agreement and Case Fragment @cite{coon-2013a}
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

namespace Fragments.Mayan.Chol

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

-- ============================================================================
-- § 3: Absolutive Position (LOW-ABS)
-- ============================================================================

/-- Chol's absolutive morphemes appear in low position (at the end of
    the verb stem, post-stem). Observable from morpheme order:
    ASP-ERG-ROOT-(DERIV)-SUFFIX-ABS. -/
def absPosition : Fragments.Mayan.ABSPosition := .low

-- ============================================================================
-- § 4: Extraction Data
-- ============================================================================

/-- Extraction possibilities in Chol transitive clauses. Unlike
    Q'anjob'al, Chol allows **both** A and P arguments to extract freely.
    There are no extraction asymmetries — Chol lacks syntactic ergativity.

    The resulting ambiguity (when both arguments are 3rd person) is a
    natural consequence of the absence of extraction restrictions:
    `Maxki₁ tyi y-il-ä (___₁) jiñi wiñik (___₁)?`
    'Who saw the man?' / 'Who did the man see?' -/
inductive ExtractionTarget where
  | intranS | patient | agent
  deriving DecidableEq, BEq, Repr

def ExtractionTarget.extractable : ExtractionTarget → Bool
  | .intranS => true
  | .patient => true
  | .agent   => true   -- Chol: agent extracts freely!

/-- All core arguments extract freely in Chol. -/
theorem all_extract_freely :
    ExtractionTarget.intranS.extractable = true ∧
    ExtractionTarget.patient.extractable = true ∧
    ExtractionTarget.agent.extractable = true := ⟨rfl, rfl, rfl⟩

/-- Chol's extraction profile: no special morphology for any extraction. -/
def extractionProfile : Interfaces.ExtractionProfile :=
  { language := "Chol"
  , strategy := .none
  , markedPositions := []
  , distinguishesPosition := false
  , notes := "No extraction asymmetries; all core arguments extract freely (Coon et al. 2014)" }

-- ============================================================================
-- § 5: Non-Finite Absolutive Availability
-- ============================================================================

/-- In Chol non-finite embedded clauses (aspectless), absolutive objects
    ARE available. This follows from Chol being LOW-ABS: v⁰ assigns case
    to the object without needing Infl⁰.

    `Mejl [i-k'el-oñ]` 'She can see me.' (ABS object ✓)
    `Choñkol [k-mek'-ety]` 'I am hugging you.' (ABS object ✓) -/
def absObjectInNonFinite : Bool := true

/-- Absolutive intransitive subjects are NOT available in Chol non-finite
    clauses: they must be marked with the ergative/possessive prefix instead.

    `Choñkol [k-ts'äm-el]` 'I am bathing.' (ERG prefix, not ABS)
    `*Choñkol [ts'äm-i-yoñ]` intended: 'I am bathing.' (ABS ✗) -/
def absIntranSInNonFinite : Bool := false

theorem nonfinite_abs_asymmetry :
    absObjectInNonFinite = true ∧ absIntranSInNonFinite = false := ⟨rfl, rfl⟩

end Fragments.Mayan.Chol
