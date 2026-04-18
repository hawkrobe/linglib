import Linglib.Theories.Syntax.Case.Dependent
import Linglib.Fragments.German.Case
import Linglib.Fragments.Turkish.Case
import Linglib.Fragments.Hindi.Case
import Linglib.Fragments.Basque.Agreement
import Linglib.Fragments.Georgian.Agreement

/-!
# Baker (2015) — Case: Its Principles and Its Parameters
@cite{baker-2015} @cite{marantz-1991} @cite{baker-vinokurova-2010}

@cite{baker-2015}'s monograph takes the dependent case algorithm
originally proposed by @cite{marantz-1991} and refined by
@cite{baker-vinokurova-2010} for Sakha and develops it as a *cross-
linguistic* theory of morphological case, sweeping accusative,
ergative, and split-ergative systems under one assignment mechanism.
The algorithm:

1. **Lexical case** assigned by selecting heads (highest priority)
2. **Dependent case** assigned to one of two distinct caseless NPs in
   the same domain — ACC to the lower NP in accusative alignment,
   ERG to the higher NP in ergative alignment
3. **Unmarked case** assigned to remaining caseless NPs — NOM in
   accusative, ABS in ergative
4. **Default case** as last resort (not modeled here)

This study file runs `Theories/Syntax/Case/Dependent.lean`'s
`assignCases` over representative languages from each of Baker's
typological columns and proves the output matches the surface case
patterns documented in the Fragment inventories.

## Structure

- **§ 1**: Split-ergative syncretism (Hindi, Georgian) — the abstract
  ABS that the algorithm produces realizes morphologically as NOM in
  these languages.
- **§ 2**: Concrete derivations for accusative (German, Turkish),
  ergative (Basque), and split-ergative (Hindi, Georgian) languages.

## The ABS/NOM Mismatch in Split-Ergative Languages

The dependent case algorithm assigns ABS (`Core.Case.abs`) as the
unmarked case in ergative alignment. Hindi and Georgian, however,
realize this function morphologically as NOM (no overt marker), not
as a distinct ABS form — their inventories contain ERG (the dependent
case) but not ABS. @cite{baker-2015} treats this as the canonical
abstract-vs-morphological case distinction inherited from
@cite{marantz-1991}: many split-ergative languages have a syncretic
unmarked case serving both nominative (accusative frames) and
absolutive (ergative frames) functions.

@cite{baker-vinokurova-2010}'s Sakha analysis is the empirical
foundation of one of Baker's columns; that paper's full derivations
live in `Phenomena/Case/Studies/BakerVinokurova2010.lean` and are not
duplicated here. Marantz's original abstract-vs-morphological case
distinction and its Georgian application live in
`Phenomena/Case/Studies/Marantz1991.lean`.
-/

namespace Phenomena.Case.Studies.Baker2015

open Syntax.Case

-- ============================================================================
-- § 1: Split-Ergative Syncretism
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
    ∀ cv ∈ structuralCasesFor .accusative, cv ∈ Fragments.Hindi.Case.caseInventory := by
  decide

theorem hindi_erg_in_inventory :
    Core.Case.erg ∈ Fragments.Hindi.Case.caseInventory := by
  native_decide

/-- ABS is not in Hindi's inventory: the absolutive function (unmarked S/P
    in perfective) is morphologically NOM. -/
theorem hindi_abs_not_in_inventory :
    Core.Case.abs ∉ Fragments.Hindi.Case.caseInventory := by decide

/-- But NOM IS in the inventory, documenting the ABS → NOM syncretism. -/
theorem hindi_nom_covers_abs_function :
    Core.Case.nom ∈ Fragments.Hindi.Case.caseInventory := by decide

-- Georgian: aorist = ergative, present/evidential = accusative-like
theorem georgian_erg_in_inventory :
    Core.Case.erg ∈ Fragments.Georgian.Agreement.fullCaseInventory := by decide

/-- ABS is not in Georgian's inventory: the absolutive function is
    morphologically NOM in both aorist (ergative) and present (accusative)
    frames. -/
theorem georgian_abs_not_in_inventory :
    Core.Case.abs ∉ Fragments.Georgian.Agreement.fullCaseInventory := by decide

/-- NOM covers the absolutive function in Georgian. -/
theorem georgian_nom_covers_abs_function :
    Core.Case.nom ∈ Fragments.Georgian.Agreement.fullCaseInventory := by decide

-- ============================================================================
-- § 2: Concrete Derivation Examples
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
    ∀ np ∈ assignCases .accusative germanTransitiveNPs,
      np.case ∈ Fragments.German.Case.caseInventory := by decide

/-- All cases in the German intransitive derivation are in German's inventory. -/
theorem german_intransitive_in_inventory :
    ∀ np ∈ assignCases .accusative germanIntransitiveNPs,
      np.case ∈ Fragments.German.Case.caseInventory := by decide

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
    ∀ np ∈ assignCases .accusative turkishTransitiveNPs,
      np.case ∈ Fragments.Turkish.Case.caseInventory := by decide

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
    ∀ np ∈ assignCases .ergative basqueTransitiveNPs,
      np.case ∈ Fragments.Basque.Agreement.fullCaseInventory := by decide

/-- All cases in the Basque intransitive derivation are in Basque's inventory. -/
theorem basque_intransitive_in_inventory :
    ∀ np ∈ assignCases .ergative basqueIntransitiveNPs,
      np.case ∈ Fragments.Basque.Agreement.fullCaseInventory := by decide

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
    ∀ np ∈ assignCases .accusative hindiTransitiveNPs,
      np.case ∈ Fragments.Hindi.Case.caseInventory := by decide

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
    morphological identity documented in § 1. -/
theorem hindi_perfective_erg_in_inventory :
    Core.Case.erg ∈ Fragments.Hindi.Case.caseInventory := by
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
    Core.Case.erg ∈ Fragments.Georgian.Agreement.fullCaseInventory := by
  decide

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
    ∀ np ∈ assignCases .accusative georgianPresentNPs,
      np.case ∈ Fragments.Georgian.Agreement.fullCaseInventory := by
  decide

end Phenomena.Case.Studies.Baker2015
