import Linglib.Fragments.Italian.Modals
import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# Bridge: Italian Restructuring ↔ Event-Relative Modality

@cite{hacquard-2010} @cite{cinque-2004} @cite{rizzi-1978}Connects the Italian restructuring data (Fragments/Italian/Modals) to
@cite{hacquard-2010}'s content licensing theory (EventRelativity §8).

## The Argument

1. Italian *potere*/*dovere* can restructure (appear below AspP).
2. When restructured, these modals lose epistemic readings.
3. Content licensing explains WHY: restructured modals are bound to the
   VP event (by aspect), and VP events lack propositional content, so
   epistemic modal bases cannot be projected.
4. When non-restructured (above AspP), the modal binds to the speech
   event (or attitude event), which IS contentful → epistemic available.

This is the key empirical argument for event-relative modality: the same
lexical modal (*potere*) shows different flavor availability depending
purely on its syntactic position, explained by content licensing.

-/

namespace Phenomena.Modality.Bridge.EventRelativityRestructuring

open Fragments.Italian.Modals
open Semantics.Modality.EventRelativity
open Core.ModalLogic (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Restructuring = Low Position
-- ════════════════════════════════════════════════════

/-- Restructuring forces the modal below AspP. This maps to
`ModalPosition.belowAsp` in the EventRelativity framework. -/
def restructuredPosition : ModalPosition := .belowAsp

/-- Non-restructured modals sit above AspP. -/
def nonRestructuredPosition : ModalPosition := .aboveAsp


-- ════════════════════════════════════════════════════
-- § 2. Content Licensing Predicts the Pattern
-- ════════════════════════════════════════════════════

/-- Content licensing predicts that restructured (low) modals cannot be
epistemic: they are bound to the VP event, which lacks content.

This single theorem explains ALL the restructuring data:
- (17) potere_high: epistemic ✓ because high modal → speech act → content
- (18) potere_low_clitic: epistemic ✗ because low modal → VP event → no content
- (13) dovere_high: epistemic ✓ (same reasoning)
- (14) dovere_low_aux: epistemic ✗ (same reasoning) -/
theorem content_licensing_explains_restructuring :
    -- Restructured (low): VP event binder, no content → no epistemic
    restructuredPosition.defaultBinder = .vpEvent ∧
    restructuredPosition.defaultBinder.hasContent = false ∧
    restructuredPosition.defaultBinder.canProjectEpistemic = false ∧
    -- Non-restructured (high): speech act binder, content → epistemic
    nonRestructuredPosition.defaultBinder = .speechAct ∧
    nonRestructuredPosition.defaultBinder.hasContent = true ∧
    nonRestructuredPosition.defaultBinder.canProjectEpistemic = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 3. Data ↔ Theory Bridge
-- ════════════════════════════════════════════════════

/-- The empirical data matches the theoretical prediction for *potere*.

The high/low flavor sets in the fragment entry align with the
event binder's available flavors at each position. -/
theorem potere_data_matches_theory :
    -- High: entry says epistemic available; theory agrees
    (.epistemic ∈ potere.highFlavors) ∧
    nonRestructuredPosition.defaultBinder.canProjectEpistemic = true ∧
    -- Low: entry says no epistemic; theory agrees
    (.epistemic ∉ potere.lowFlavors) ∧
    restructuredPosition.defaultBinder.canProjectEpistemic = false := by
  refine ⟨?_, rfl, ?_, rfl⟩ <;> decide

/-- Same bridge for *dovere*. -/
theorem dovere_data_matches_theory :
    (.epistemic ∈ dovere.highFlavors) ∧
    nonRestructuredPosition.defaultBinder.canProjectEpistemic = true ∧
    (.epistemic ∉ dovere.lowFlavors) ∧
    restructuredPosition.defaultBinder.canProjectEpistemic = false := by
  refine ⟨?_, rfl, ?_, rfl⟩ <;> decide


-- ════════════════════════════════════════════════════
-- § 4. The Same Modal, Two Positions
-- ════════════════════════════════════════════════════

/-- Both *potere* and *dovere* are single lexical items: the same verb
appears high (with epistemic) and low (without epistemic). This rules
out lexical ambiguity as an explanation — the flavor restriction follows
from structural position alone.

@cite{hacquard-2010}: "Importantly, in Italian, epistemic and root
modals are the same lexical items. [...] the availability of epistemic
readings tracks the syntactic position of the modal." -/
theorem same_lexical_items :
    -- potere: same form in both positions
    potere.form = "potere" ∧
    -- but different flavor availability
    (.epistemic ∈ potere.highFlavors) ∧
    (.epistemic ∉ potere.lowFlavors) ∧
    -- dovere: same form in both positions
    dovere.form = "dovere" ∧
    -- but different flavor availability
    (.epistemic ∈ dovere.highFlavors) ∧
    (.epistemic ∉ dovere.lowFlavors) := by
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩ <;> decide


-- ════════════════════════════════════════════════════
-- § 5. Why Not Lexical Ambiguity?
-- ════════════════════════════════════════════════════

/-- If epistemic/root were lexically distinct modals (as in some
analyses of English *can*_epis vs *can*_root), we would expect no
syntactic correlation. But Italian shows that ONE lexical item
exhibits the restriction purely based on position. Content licensing
explains this without positing ambiguity.

Furthermore, the restriction is PRODUCTIVE: any restructuring modal
loses epistemic in the restructured position. The theory predicts this
for ALL restructuring modals — it's not a per-item stipulation. -/
theorem both_modals_restructure :
    potere.canRestructure = true ∧ dovere.canRestructure = true := ⟨rfl, rfl⟩


end Phenomena.Modality.Bridge.EventRelativityRestructuring
