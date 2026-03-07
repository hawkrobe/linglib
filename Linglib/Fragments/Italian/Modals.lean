import Linglib.Core.Logic.ModalLogic
import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# Italian Modal Auxiliaries

@cite{hacquard-2010} @cite{cinque-2004} @cite{hacquard-2006} @cite{rizzi-1978}Italian modal auxiliaries *dovere* ('must') and *potere* ('can'), with
their behavior under restructuring. These are the primary empirical
evidence for @cite{hacquard-2006}'s event-relative analysis: when
Italian modals appear in restructuring configurations (syntactically
low, below AspP), they lose epistemic readings.

## Italian Restructuring

Italian *potere* and *dovere* participate in restructuring. In restructuring contexts, the modal is syntactically
low — merged below AspP, with the lower verb's clitic climbing through
the modal. Diagnostics:

1. **Clitic climbing**: *lo posso fare* ('it I-can do') — clitic *lo*
   climbs past the modal (restructuring) vs *posso farlo* (non-restructuring).
2. **Auxiliary selection**: *è dovuto andare* (auxiliary *essere* with
   unaccusative *andare*) — auxiliary matches the lower verb (restructuring)
   vs *ha dovuto andare* (non-restructuring, default *avere*).

When restructured (low): only root readings (circumstantial, deontic).
When non-restructured (high): epistemic readings available.

-/

namespace Fragments.Italian.Modals

open Core.Modality (ModalForce ModalFlavor ForceFlavor)
open Semantics.Modality.EventRelativity (ModalPosition EventBinder)


-- ════════════════════════════════════════════════════
-- § 1. Italian Modal Entry Type
-- ════════════════════════════════════════════════════

/-- An Italian modal auxiliary entry with position-sensitive flavor. -/
structure ItalianModalEntry where
  /-- Citation form -/
  form : String
  /-- Modal force (necessity or possibility) -/
  force : ModalForce
  /-- Whether the modal can restructure (appear below AspP) -/
  canRestructure : Bool
  /-- Flavors available when non-restructured (high position) -/
  highFlavors : List ModalFlavor
  /-- Flavors available when restructured (low position) -/
  lowFlavors : List ModalFlavor
  deriving Repr, BEq


-- ════════════════════════════════════════════════════
-- § 2. Lexical Entries
-- ════════════════════════════════════════════════════

/-- *Potere* ('can'): restructuring modal.
    High: epistemic, deontic, circumstantial.
    Low (restructured): deontic, circumstantial only.

    (@cite{hacquard-2010}, (17)–(19)):
    - "Gianni può essere intelligente" (epistemic, non-restructured)
    - "Gianni lo può fare" (root, restructured — clitic climbing) -/
def potere : ItalianModalEntry where
  form := "potere"
  force := .possibility
  canRestructure := true
  highFlavors := [.epistemic, .deontic, .circumstantial]
  lowFlavors := [.deontic, .circumstantial]

/-- *Dovere* ('must'): restructuring modal.
    High: epistemic, deontic, circumstantial.
    Low (restructured): deontic, circumstantial only.

    (@cite{hacquard-2010}, (13)–(15)):
    - "Gianni deve essere a casa" (epistemic, non-restructured)
    - "Gianni deve lavorare" (deontic/circumstantial, restructured) -/
def dovere : ItalianModalEntry where
  form := "dovere"
  force := .necessity
  canRestructure := true
  highFlavors := [.epistemic, .deontic, .circumstantial]
  lowFlavors := [.deontic, .circumstantial]


-- ════════════════════════════════════════════════════
-- § 3. Restructuring Diagnostics
-- ════════════════════════════════════════════════════

/-- Restructuring diagnostics from @cite{rizzi-1978}. -/
inductive RestructuringDiagnostic where
  /-- Clitic climbing: clitic raises past the modal to the higher verb -/
  | cliticClimbing
  /-- Auxiliary change: auxiliary of the lower verb surfaces on the modal -/
  | auxiliaryChange
  deriving DecidableEq, BEq, Repr

/-- A restructuring example: sentence + diagnostic + reading. -/
structure RestructuringExample where
  /-- Italian sentence -/
  italian : String
  /-- English gloss -/
  gloss : String
  /-- Whether the modal is restructured -/
  isRestructured : Bool
  /-- Which diagnostic evidences restructuring -/
  diagnostic : Option RestructuringDiagnostic
  /-- The modal reading(s) available -/
  availableFlavors : List ModalFlavor
  deriving Repr

/-- (17): Non-restructured *potere* — epistemic.
    "Gianni può essere intelligente" = Gianni may be intelligent.
    No clitic climbing; epistemic reading available. -/
def potere_high : RestructuringExample where
  italian := "Gianni può essere intelligente."
  gloss := "Gianni can be intelligent."
  isRestructured := false
  diagnostic := none
  availableFlavors := [.epistemic]

/-- (18): Restructured *potere* — root only.
    "Lo posso fare" = I can do it (clitic climbing).
    Clitic climbing diagnoses low position; epistemic unavailable. -/
def potere_low_clitic : RestructuringExample where
  italian := "Lo posso fare."
  gloss := "It I-can do."
  isRestructured := true
  diagnostic := some .cliticClimbing
  availableFlavors := [.circumstantial]

/-- (13): Non-restructured *dovere* — epistemic.
    "Gianni deve essere a casa" = Gianni must be at home.
    Epistemic necessity. -/
def dovere_high : RestructuringExample where
  italian := "Gianni deve essere a casa."
  gloss := "Gianni must be at home."
  isRestructured := false
  diagnostic := none
  availableFlavors := [.epistemic]

/-- (14): Restructured *dovere* — deontic/root only.
    "É dovuto andare a casa" = He had to go home.
    Auxiliary change (*essere* from unaccusative *andare*). -/
def dovere_low_aux : RestructuringExample where
  italian := "È dovuto andare a casa."
  gloss := "He had-to go home."
  isRestructured := true
  diagnostic := some .auxiliaryChange
  availableFlavors := [.deontic, .circumstantial]

def allExamples : List RestructuringExample :=
  [potere_high, potere_low_clitic, dovere_high, dovere_low_aux]


-- ════════════════════════════════════════════════════
-- § 4. Per-Example Verification
-- ════════════════════════════════════════════════════

/-- Non-restructured examples have epistemic as a flavor. -/
theorem high_has_epistemic :
    potere_high.availableFlavors.elem .epistemic = true ∧
    dovere_high.availableFlavors.elem .epistemic = true := by
  constructor <;> native_decide

/-- Restructured examples lack epistemic as a flavor. -/
theorem low_lacks_epistemic :
    potere_low_clitic.availableFlavors.elem .epistemic = false ∧
    dovere_low_aux.availableFlavors.elem .epistemic = false := by
  constructor <;> native_decide

/-- The core generalization: restructured ↔ no epistemic. -/
theorem restructuring_blocks_epistemic :
    allExamples.all (λ ex =>
      if ex.isRestructured then !(ex.availableFlavors.elem .epistemic)
      else ex.availableFlavors.elem .epistemic
    ) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 5. Position → Flavor Bridge
-- ════════════════════════════════════════════════════

/-- The entry's position-sensitive flavors match EventRelativity's
content licensing predictions. -/
theorem potere_flavors_match_position :
    -- High: epistemic available (content licensing: speech act is contentful)
    (.epistemic ∈ potere.highFlavors) ∧
    -- Low: no epistemic (content licensing: VP event lacks content)
    (.epistemic ∉ potere.lowFlavors) := by
  constructor
  · decide
  · decide

theorem dovere_flavors_match_position :
    (.epistemic ∈ dovere.highFlavors) ∧
    (.epistemic ∉ dovere.lowFlavors) := by
  constructor
  · decide
  · decide


end Fragments.Italian.Modals
