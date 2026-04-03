import Linglib.Core.Number
import Linglib.Core.WALS.Features.F80A

/-!
# Verbal Number and Pluractionality
@cite{corbett-2000}

Verbal number — number marking on the verb that quantifies over events
rather than participants (@cite{corbett-2000} Ch 8). Languages like Hausa,
Chechen, and Navajo mark number directly on the verb stem, often via
suppletion (distinct stems for singular vs plural).

Key distinctions:
- **Participant agreement**: verb agrees with subject/object number
  (typical Indo-European pattern, not "verbal number" proper)
- **Event plurality / pluractionality**: the verb's own event argument
  is pluralized — repeated, distributed, or intensified action
- **Mixed**: both patterns co-exist (e.g. Georgian)

## WALS 80A Bridge

WALS Feature 80A records verbal number and suppletion across 193
languages. 159 have no verbal number; 34 have singular-plural pairs
(with or without suppletion); 7 have sg-du-pl triples.
-/

namespace Phenomena.Plurals.Studies.VerbalNumber

open Core.Number (Category)

-- ============================================================================
-- § 1: Verbal Number Types
-- ============================================================================

/-- Whether verbal number is participant agreement, event plurality, or both. -/
inductive VerbalNumberType where
  /-- Verb agrees with subject/object number (most Indo-European).
      Not "verbal number" in the strict Corbett sense. -/
  | participantAgreement
  /-- Verb's own event argument is pluralized. The verb stem changes
      to encode repeated, distributed, or intensified action. -/
  | eventPlurality
  /-- Both patterns co-exist in the language. -/
  | mixed
  deriving DecidableEq, BEq, Repr

/-- Profile for a language's verbal number system. -/
structure VerbalNumberProfile where
  name : String
  type : VerbalNumberType
  /-- Whether the language uses suppletion (distinct stems for sg/pl). -/
  hasSuppletion : Bool
  /-- Number values distinguished on the verb. -/
  verbValues : List Category
  deriving BEq

-- ============================================================================
-- § 2: Language Data
-- ============================================================================

/-- Hausa: event plurality with suppletive verb stems.
    *tàfi* 'go (sg)' / *tàka* 'go (pl)'. -/
def hausa : VerbalNumberProfile :=
  { name := "Hausa"
    type := .eventPlurality
    hasSuppletion := true
    verbValues := [.singular, .plural] }

/-- Chechen: event plurality with suppletion.
    Verb pairs encode singular vs plural action. -/
def chechen : VerbalNumberProfile :=
  { name := "Chechen"
    type := .eventPlurality
    hasSuppletion := true
    verbValues := [.singular, .plural] }

/-- Navajo: event plurality, sg-du-pl verb stems (one of the richer systems).
    Three-way suppletion: *łtsooz* 'flat object lies (sg)' / *łtsos*
    '(du)' / *łtsoos* '(pl)'. -/
def navajo : VerbalNumberProfile :=
  { name := "Navajo"
    type := .eventPlurality
    hasSuppletion := true
    verbValues := [.singular, .dual, .plural] }

/-- Georgian: mixed system — participant agreement on some verbs,
    event plurality on others. -/
def georgian : VerbalNumberProfile :=
  { name := "Georgian"
    type := .mixed
    hasSuppletion := false
    verbValues := [.singular, .plural] }

def allVerbalNumberProfiles : List VerbalNumberProfile :=
  [hausa, chechen, navajo, georgian]

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- Languages with event plurality always have at least sg and pl. -/
theorem event_plural_has_sg_pl :
    allVerbalNumberProfiles.all
      (λ p => p.type == .participantAgreement ||
              (p.verbValues.contains .singular &&
               p.verbValues.contains .plural)) = true := by
  native_decide

/-- Navajo is the only 3-value system in our sample. -/
theorem navajo_three_values :
    navajo.verbValues.length = 3 := by native_decide

/-- The implicational universal holds: dual verbal number implies
    singular and plural are also distinguished. -/
theorem verbal_dual_implies_sg_pl :
    allVerbalNumberProfiles.all
      (λ p => !(p.verbValues.contains .dual) ||
              (p.verbValues.contains .singular &&
               p.verbValues.contains .plural)) = true := by
  native_decide

-- ============================================================================
-- § 4: Bridge to WALS 80A
-- ============================================================================

open Core.WALS.F80A (VerbalNumberAndSuppletion)

/-- Map a VerbalNumberProfile to the corresponding WALS 80A category. -/
def VerbalNumberProfile.toWALS80A (p : VerbalNumberProfile) : VerbalNumberAndSuppletion :=
  match p.verbValues.length, p.hasSuppletion with
  | 0, _     => .none
  | 2, false => .singularPluralPairsNoSuppletion
  | 2, true  => .singularPluralPairsSuppletion
  | _, false => .singularDualPluralTriplesNoSuppletion
  | _, true  => .singularDualPluralTriplesSuppletion

/-- Hausa maps to singular-plural pairs with suppletion. -/
theorem hausa_wals :
    hausa.toWALS80A = .singularPluralPairsSuppletion := by native_decide

/-- Navajo maps to sg-du-pl triples with suppletion. -/
theorem navajo_wals :
    navajo.toWALS80A = .singularDualPluralTriplesSuppletion := by native_decide

/-- WALS 80A confirms that the majority of languages lack verbal number. -/
theorem wals_majority_no_verbal_number :
    (Core.WALS.F80A.allData.filter (·.value == .none)).length >
    (Core.WALS.F80A.allData.filter (·.value != .none)).length := by
  native_decide

end Phenomena.Plurals.Studies.VerbalNumber
