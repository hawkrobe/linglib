import Linglib.Theories.Syntax.Minimalism.Core.DependentCase
import Linglib.Fragments.German.Case
import Linglib.Fragments.Turkish.Case
import Linglib.Fragments.Russian.Case
import Linglib.Fragments.Czech.Case
import Linglib.Fragments.Polish.Case
import Linglib.Fragments.Ukrainian.Case
import Linglib.Fragments.Serbian.Case
import Linglib.Fragments.Slovenian.Case
import Linglib.Fragments.Greek.Case
import Linglib.Fragments.Latin.Case
import Linglib.Fragments.Finnish.Case
import Linglib.Fragments.Hungarian.Case
import Linglib.Fragments.Tamil.Case
import Linglib.Fragments.Japanese.Case
import Linglib.Fragments.Korean.Case
import Linglib.Fragments.Hindi.Case
import Linglib.Fragments.Basque.Agreement
import Linglib.Fragments.Georgian.Agreement
import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Kaqchikel.Agreement

/-!
# Dependent Case ↔ Inventory Bridge

Connects the dependent case algorithm (`assignCases`) to language-specific
case inventories from Fragment files. For each language, we prove that the
**structural** cases the algorithm can assign are members of that language's
validated case inventory.

## Structure

- **§ 1**: Language type assignments (accusative, ergative, or split)
- **§ 2**: Inventory coverage — for each language, the structural cases
  produced by `structuralCasesFor` are all in the language's `caseInventory`
- **§ 3**: Ergative language coverage (Basque, Mam, Kaqchikel)
- **§ 4**: Split-ergative coverage (Hindi, Georgian) — partial, because
  the algorithm's ABS is realized as NOM in these languages
- **§ 5**: Concrete derivation examples for representative languages

## The ABS/NOM Mismatch in Split-Ergative Languages

The dependent case algorithm assigns ABS (`CaseVal.abs`) as the unmarked
case in ergative alignment. However, Hindi and Georgian realize this
function morphologically as NOM (no overt marker), not as a distinct ABS
form. Their inventories contain ERG (the dependent case) but not ABS.
This is a well-known typological fact: many split-ergative languages have
a **syncretic** unmarked case that serves both the nominative (accusative
frames) and absolutive (ergative frames) functions.

The bridge documents this: we prove full coverage for accusative alignment
and ERG-specific coverage for ergative alignment, noting that ABS → NOM
is a morphological identity, not a gap in the theory.
-/

namespace Phenomena.Case.Studies.DependentCaseInventories

open Minimalism

-- ============================================================================
-- § 1: Language Type Assignments
-- ============================================================================

/-- German is an accusative language (NOM for S/A, ACC for P). -/
def germanLangType : CaseLanguageType := .accusative

/-- Turkish is an accusative language. -/
def turkishLangType : CaseLanguageType := .accusative

/-- Russian is an accusative language. -/
def russianLangType : CaseLanguageType := .accusative

/-- Czech is an accusative language. -/
def czechLangType : CaseLanguageType := .accusative

/-- Polish is an accusative language. -/
def polishLangType : CaseLanguageType := .accusative

/-- Ukrainian is an accusative language. -/
def ukrainianLangType : CaseLanguageType := .accusative

/-- Serbian is an accusative language. -/
def serbianLangType : CaseLanguageType := .accusative

/-- Slovenian is an accusative language. -/
def slovenianLangType : CaseLanguageType := .accusative

/-- Greek is an accusative language. -/
def greekLangType : CaseLanguageType := .accusative

/-- Latin is an accusative language. -/
def latinLangType : CaseLanguageType := .accusative

/-- Finnish is an accusative language. -/
def finnishLangType : CaseLanguageType := .accusative

/-- Hungarian is an accusative language. -/
def hungarianLangType : CaseLanguageType := .accusative

/-- Tamil is an accusative language. -/
def tamilLangType : CaseLanguageType := .accusative

/-- Japanese is an accusative language. -/
def japaneseLangType : CaseLanguageType := .accusative

/-- Korean is an accusative language. -/
def koreanLangType : CaseLanguageType := .accusative

/-- Basque is an ergative language (ERG for A, ABS for S/P). -/
def basqueLangType : CaseLanguageType := .ergative

/-- Mam (Mayan) is a tripartite language (ERG, ACC, ABS all distinct). -/
def mamLangType : CaseLanguageType := .tripartite

/-- Kaqchikel (Mayan) is an ergative language. -/
def kaqchikelLangType : CaseLanguageType := .ergative

-- ============================================================================
-- § 2: Accusative Language Coverage
-- ============================================================================

/-! For each accusative language, the structural cases [NOM, ACC] are both
    members of that language's case inventory. -/

theorem german_structural_coverage :
    (structuralCasesFor germanLangType).all
      (λ cv => Fragments.German.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem turkish_structural_coverage :
    (structuralCasesFor turkishLangType).all
      (λ cv => Fragments.Turkish.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem russian_structural_coverage :
    (structuralCasesFor russianLangType).all
      (λ cv => Fragments.Russian.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem czech_structural_coverage :
    (structuralCasesFor czechLangType).all
      (λ cv => Fragments.Czech.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem polish_structural_coverage :
    (structuralCasesFor polishLangType).all
      (λ cv => Fragments.Polish.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem ukrainian_structural_coverage :
    (structuralCasesFor ukrainianLangType).all
      (λ cv => Fragments.Ukrainian.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem serbian_structural_coverage :
    (structuralCasesFor serbianLangType).all
      (λ cv => Fragments.Serbian.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem slovenian_structural_coverage :
    (structuralCasesFor slovenianLangType).all
      (λ cv => Fragments.Slovenian.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem greek_structural_coverage :
    (structuralCasesFor greekLangType).all
      (λ cv => Fragments.Greek.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem latin_structural_coverage :
    (structuralCasesFor latinLangType).all
      (λ cv => Fragments.Latin.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem finnish_structural_coverage :
    (structuralCasesFor finnishLangType).all
      (λ cv => Fragments.Finnish.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem hungarian_structural_coverage :
    (structuralCasesFor hungarianLangType).all
      (λ cv => Fragments.Hungarian.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem tamil_structural_coverage :
    (structuralCasesFor tamilLangType).all
      (λ cv => Fragments.Tamil.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem japanese_structural_coverage :
    (structuralCasesFor japaneseLangType).all
      (λ cv => Fragments.Japanese.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem korean_structural_coverage :
    (structuralCasesFor koreanLangType).all
      (λ cv => Fragments.Korean.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

-- ============================================================================
-- § 3: Ergative Language Coverage
-- ============================================================================

/-! For ergative languages, the structural cases [ABS, ERG] are in the
    inventory. Basque and Kaqchikel are fully ergative; Mam is tripartite
    (ERG, ACC, ABS all distinct). -/

theorem basque_structural_coverage :
    (structuralCasesFor basqueLangType).all
      (λ cv => Fragments.Basque.Agreement.fullCaseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem mam_structural_coverage :
    (structuralCasesFor mamLangType).all
      (λ cv => Fragments.Mayan.Mam.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem kaqchikel_structural_coverage :
    (structuralCasesFor kaqchikelLangType).all
      (λ cv => Fragments.Mayan.Kaqchikel.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

-- ============================================================================
-- § 4: Split-Ergative Coverage
-- ============================================================================

/-! Hindi and Georgian are split-ergative: accusative alignment in some
    tense/aspect contexts, ergative alignment in others. We prove:
    (1) Full accusative structural coverage (NOM, ACC ∈ inventory)
    (2) ERG ∈ inventory (the dependent case in ergative frames)
    (3) ABS ∉ inventory — these languages realize the absolutive function
        morphologically as NOM, so the algorithm's ABS output maps to a
        case that is in the inventory under a different label. -/

-- Hindi: perfective = ergative, imperfective = accusative
theorem hindi_accusative_coverage :
    (structuralCasesFor .accusative).all
      (λ cv => Fragments.Hindi.Case.caseInventory.any (· == cv.toCase)) = true := by
  native_decide

theorem hindi_erg_in_inventory :
    Fragments.Hindi.Case.caseInventory.any (· == CaseVal.erg.toCase) = true := by
  native_decide

/-- ABS is not in Hindi's inventory: the absolutive function (unmarked S/P
    in perfective) is morphologically NOM. -/
theorem hindi_abs_not_in_inventory :
    Fragments.Hindi.Case.caseInventory.any (· == CaseVal.abs.toCase) = false := by
  native_decide

/-- But NOM IS in the inventory, documenting the ABS → NOM syncretism. -/
theorem hindi_nom_covers_abs_function :
    Fragments.Hindi.Case.caseInventory.any (· == CaseVal.nom.toCase) = true := by
  native_decide

-- Georgian: aorist = ergative, present/evidential = accusative-like
theorem georgian_erg_in_inventory :
    Fragments.Georgian.Agreement.fullCaseInventory.any
      (· == CaseVal.erg.toCase) = true := by
  native_decide

/-- ABS is not in Georgian's inventory: the absolutive function is
    morphologically NOM in both aorist (ergative) and present (accusative)
    frames. -/
theorem georgian_abs_not_in_inventory :
    Fragments.Georgian.Agreement.fullCaseInventory.any
      (· == CaseVal.abs.toCase) = false := by
  native_decide

/-- NOM covers the absolutive function in Georgian. -/
theorem georgian_nom_covers_abs_function :
    Fragments.Georgian.Agreement.fullCaseInventory.any
      (· == CaseVal.nom.toCase) = true := by
  native_decide

-- ============================================================================
-- § 5: Concrete Derivation Examples
-- ============================================================================

/-! ## German Derivations

"Der Mann sieht die Frau" (The man sees the woman)
- Transitive: subject (higher) + object (lower), both without lexical case
- Subject → NOM (unmarked), Object → ACC (dependent)

"Der Mann schläft" (The man sleeps)
- Intransitive: single NP without lexical case
- Subject → NOM (unmarked, no case competitor) -/

def germanTransitiveNPs : List NPInDomain :=
  [⟨"subject", none⟩, ⟨"object", none⟩]

def germanIntransitiveNPs : List NPInDomain :=
  [⟨"subject", none⟩]

theorem german_transitive_subject_nom :
    getCaseOf "subject" (assignCases .accusative germanTransitiveNPs) = some .nom := by
  native_decide

theorem german_transitive_object_acc :
    getCaseOf "object" (assignCases .accusative germanTransitiveNPs) = some .acc := by
  native_decide

theorem german_intransitive_subject_nom :
    getCaseOf "subject" (assignCases .accusative germanIntransitiveNPs) = some .nom := by
  native_decide

/-- All cases in the German transitive derivation are in German's inventory. -/
theorem german_transitive_in_inventory :
    (assignCases .accusative germanTransitiveNPs).all
      (λ np => Fragments.German.Case.caseInventory.any (· == np.case.toCase)) = true := by
  native_decide

/-- All cases in the German intransitive derivation are in German's inventory. -/
theorem german_intransitive_in_inventory :
    (assignCases .accusative germanIntransitiveNPs).all
      (λ np => Fragments.German.Case.caseInventory.any (· == np.case.toCase)) = true := by
  native_decide

/-! ## Turkish Derivations

"Adam kadını gördü" (The man saw the woman)
- Transitive: subject NOM (∅), object ACC (-I)

"Adam uyudu" (The man slept)
- Intransitive: subject NOM (∅) -/

def turkishTransitiveNPs : List NPInDomain :=
  [⟨"subject", none⟩, ⟨"object", none⟩]

def turkishIntransitiveNPs : List NPInDomain :=
  [⟨"subject", none⟩]

theorem turkish_transitive_cases :
    getCaseOf "subject" (assignCases .accusative turkishTransitiveNPs) = some .nom ∧
    getCaseOf "object" (assignCases .accusative turkishTransitiveNPs) = some .acc := by
  native_decide

theorem turkish_intransitive_case :
    getCaseOf "subject" (assignCases .accusative turkishIntransitiveNPs) = some .nom := by
  native_decide

theorem turkish_transitive_in_inventory :
    (assignCases .accusative turkishTransitiveNPs).all
      (λ np => Fragments.Turkish.Case.caseInventory.any (· == np.case.toCase)) = true := by
  native_decide

/-! ## Basque Derivations (Ergative)

"Gizonak mutila ikusi du" (The man-ERG boy-ABS see AUX)
- Transitive: agent (higher) → ERG (dependent), patient (lower) → ABS (unmarked)

"Mutila etorri da" (The boy-ABS come AUX)
- Intransitive: sole NP → ABS (unmarked, no case competitor) -/

def basqueTransitiveNPs : List NPInDomain :=
  [⟨"agent", none⟩, ⟨"patient", none⟩]

def basqueIntransitiveNPs : List NPInDomain :=
  [⟨"subject", none⟩]

theorem basque_transitive_agent_erg :
    getCaseOf "agent" (assignCases .ergative basqueTransitiveNPs) = some .erg := by
  native_decide

theorem basque_transitive_patient_abs :
    getCaseOf "patient" (assignCases .ergative basqueTransitiveNPs) = some .abs := by
  native_decide

theorem basque_intransitive_subject_abs :
    getCaseOf "subject" (assignCases .ergative basqueIntransitiveNPs) = some .abs := by
  native_decide

/-- All cases in the Basque transitive derivation are in Basque's inventory. -/
theorem basque_transitive_in_inventory :
    (assignCases .ergative basqueTransitiveNPs).all
      (λ np => Fragments.Basque.Agreement.fullCaseInventory.any
        (· == np.case.toCase)) = true := by
  native_decide

/-- All cases in the Basque intransitive derivation are in Basque's inventory. -/
theorem basque_intransitive_in_inventory :
    (assignCases .ergative basqueIntransitiveNPs).all
      (λ np => Fragments.Basque.Agreement.fullCaseInventory.any
        (· == np.case.toCase)) = true := by
  native_decide

/-! ## Hindi Split-Ergative Derivations

Hindi perfective transitive: "Raam-ne roTii khaayii"
(Ram-ERG bread-NOM ate) — ergative alignment

Hindi imperfective transitive: "Raam roTii khaataa hai"
(Ram-NOM bread-ACC eats AUX) — accusative alignment

The same structural configuration (agent + patient) yields different
case frames depending on the tense/aspect conditioning of the split. -/

def hindiTransitiveNPs : List NPInDomain :=
  [⟨"agent", none⟩, ⟨"patient", none⟩]

-- Imperfective: accusative alignment
theorem hindi_imperfective_agent_nom :
    getCaseOf "agent" (assignCases .accusative hindiTransitiveNPs) = some .nom := by
  native_decide

theorem hindi_imperfective_patient_acc :
    getCaseOf "patient" (assignCases .accusative hindiTransitiveNPs) = some .acc := by
  native_decide

theorem hindi_imperfective_in_inventory :
    (assignCases .accusative hindiTransitiveNPs).all
      (λ np => Fragments.Hindi.Case.caseInventory.any (· == np.case.toCase)) = true := by
  native_decide

-- Perfective: ergative alignment
theorem hindi_perfective_agent_erg :
    getCaseOf "agent" (assignCases .ergative hindiTransitiveNPs) = some .erg := by
  native_decide

theorem hindi_perfective_patient_abs :
    getCaseOf "patient" (assignCases .ergative hindiTransitiveNPs) = some .abs := by
  native_decide

/-- In the perfective (ergative alignment), ERG is in the inventory
    but ABS is not — it is realized as NOM. The agent case (ERG) is
    correctly predicted; the patient case (ABS → NOM) requires the
    morphological identity documented in § 4. -/
theorem hindi_perfective_erg_in_inventory :
    Fragments.Hindi.Case.caseInventory.any (· == CaseVal.erg.toCase) = true := by
  native_decide

/-! ## Georgian Split-Ergative Derivations

Georgian aorist transitive: "K'ac-ma bavšv-i naxa"
(Man-ERG child-NOM saw) — ergative alignment

Georgian present transitive: "K'ac-i bavšv-s xedavs"
(Man-NOM child-DAT sees) — accusative-like, with lexical DAT on object

In the present series, the patient receives lexical DAT from the verb,
not structural ACC from dependent case. -/

def georgianAoristNPs : List NPInDomain :=
  [⟨"agent", none⟩, ⟨"patient", none⟩]

def georgianPresentNPs : List NPInDomain :=
  [⟨"agent", none⟩, ⟨"patient", some .dat⟩]

-- Aorist: ergative alignment
theorem georgian_aorist_agent_erg :
    getCaseOf "agent" (assignCases .ergative georgianAoristNPs) = some .erg := by
  native_decide

theorem georgian_aorist_patient_abs :
    getCaseOf "patient" (assignCases .ergative georgianAoristNPs) = some .abs := by
  native_decide

/-- The agent ERG in the aorist is in Georgian's inventory. -/
theorem georgian_aorist_erg_in_inventory :
    Fragments.Georgian.Agreement.fullCaseInventory.any
      (· == CaseVal.erg.toCase) = true := by
  native_decide

-- Present: accusative-like alignment with lexical DAT on patient
theorem georgian_present_agent_nom :
    getCaseOf "agent" (assignCases .accusative georgianPresentNPs) = some .nom := by
  native_decide

theorem georgian_present_patient_dat :
    getCaseOf "patient" (assignCases .accusative georgianPresentNPs) = some .dat := by
  native_decide

/-- In the present series, lexical DAT on the patient bleeds dependent
    ACC: the agent gets NOM (no case competitor) and the patient gets
    DAT (lexical from V). Both are in Georgian's inventory. -/
theorem georgian_present_in_inventory :
    (assignCases .accusative georgianPresentNPs).all
      (λ np => Fragments.Georgian.Agreement.fullCaseInventory.any
        (· == np.case.toCase)) = true := by
  native_decide

end Phenomena.Case.Studies.DependentCaseInventories
