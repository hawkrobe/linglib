import Linglib.Fragments.Italian.Modals
import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# Event-Relative Modality
@cite{hacquard-2010} @cite{kratzer-1981} @cite{cinque-2004} @cite{rizzi-1978}

## Part I: Italian Restructuring

Connects the Italian restructuring data (Fragments/Italian/Modals) to
@cite{hacquard-2010}'s content licensing theory (EventRelativity §8).

### The Argument

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

## Part II: Position-Based Flavor Availability

Derives from EventRelativity which modal flavors are available at each
structural position. A modal's fragment entry lists its FULL flavor
inventory across all positions; at any given position, content licensing
and addressee licensing act as filters.
-/

namespace Phenomena.Modality.Studies.Hacquard2010

open Semantics.Modality.EventRelativity
open Core.Modality (ModalFlavor)

-- ============================================================================
-- Part I: Italian Restructuring
-- ============================================================================

open Fragments.Italian.Modals

-- ============================================================================
-- § 1: Restructuring = Low Position
-- ============================================================================

/-- Restructuring forces the modal below AspP. This maps to
`ModalPosition.belowAsp` in the EventRelativity framework. -/
def restructuredPosition : ModalPosition := .belowAsp

/-- Non-restructured modals sit above AspP. -/
def nonRestructuredPosition : ModalPosition := .aboveAsp

-- ============================================================================
-- § 2: Content Licensing Predicts the Pattern
-- ============================================================================

/-- Content licensing predicts that restructured (low) modals cannot be
epistemic: they are bound to the VP event, which lacks content.

This single theorem explains ALL the restructuring data:
- potere_high: epistemic ✓ because high modal → speech act → content
- potere_low_clitic: epistemic ✗ because low modal → VP event → no content
- dovere_high: epistemic ✓ (same reasoning)
- dovere_low_aux: epistemic ✗ (same reasoning) -/
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

-- ============================================================================
-- § 3: Data ↔ Theory (Italian)
-- ============================================================================

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

-- ============================================================================
-- § 4: The Same Modal, Two Positions
-- ============================================================================

/-- Both *potere* and *dovere* are single lexical items: the same verb
appears high (with epistemic) and low (without epistemic). This rules
out lexical ambiguity as an explanation — the flavor restriction follows
from structural position alone.

@cite{hacquard-2010}, §1: Italian *potere* and *dovere* express both
epistemic and root modality with the same lexical item, and the
availability of epistemic readings tracks the syntactic position. -/
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

-- ============================================================================
-- § 5: Why Not Lexical Ambiguity?
-- ============================================================================

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

-- ============================================================================
-- Part II: Position-Based Flavor Availability
-- ============================================================================

-- ============================================================================
-- § 6: Union of Position-Available Flavors
-- ============================================================================

/-- The full set of modal flavors available across ALL positions and
contexts: the union of flavors from high (matrix), high (embedded),
and low positions.

This should equal the set of flavors listed in the fragment entry
for any given modal — the fragment entry is the MAXIMUM over all
structural contexts. -/
def allPositionFlavors : List ModalFlavor :=
  -- High matrix: speech act binder → epistemic, circumstantial, deontic
  ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors ++
  -- Low: VP event binder → circumstantial only
  ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors

/-- High matrix position contributes epistemic, circumstantial, and
deontic (from the speech act's addressee). -/
theorem high_matrix_flavors :
    ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors =
      [.epistemic, .circumstantial, .deontic] := rfl

/-- Low position contributes only circumstantial. -/
theorem low_flavors :
    ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors =
      [.circumstantial] := rfl

/-- The union covers all three flavors. -/
theorem union_covers_all_three :
    (.epistemic ∈ allPositionFlavors) ∧
    (.circumstantial ∈ allPositionFlavors) ∧
    (.deontic ∈ allPositionFlavors) := by
  unfold allPositionFlavors
  refine ⟨?_, ?_, ?_⟩ <;> simp [high_matrix_flavors, low_flavors]

-- ============================================================================
-- § 7: Fragment Entry Verification
-- ============================================================================

/-- A modal with all three flavors (like *must*, *can*): each flavor
is derivable from some position.

- Epistemic: high position (speech act is contentful)
- Circumstantial: any position (always available)
- Deontic: high position (speech act has addressee) -/
theorem three_flavor_modal_derivable :
    -- Epistemic: available at high position (content licensing)
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true ∧
    -- Circumstantial: available at any position
    ModalPosition.aboveAsp.defaultBinder.canProjectCircumstantial = true ∧
    ModalPosition.belowAsp.defaultBinder.canProjectCircumstantial = true ∧
    -- Deontic: available when binder has addressee (speech act)
    ModalPosition.aboveAsp.defaultBinder.hasAddressee = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A modal with only [epistemic] (like *might*): derived from
high position content licensing. Note that *might* being
epistemic-only is a LEXICAL restriction (it selects for epistemic
flavor), not a structural one — structurally, high position allows
both epistemic and circumstantial. -/
theorem epistemic_only_derivable :
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true := rfl

/-- A modal with [deontic, circumstantial] but no epistemic (like
*have to*): the modal selects for non-epistemic flavors and occupies
the low position, where content licensing independently blocks
epistemic. -/
theorem non_epistemic_modal_consistent :
    ModalPosition.belowAsp.defaultBinder.canProjectEpistemic = false ∧
    ModalPosition.belowAsp.defaultBinder.canProjectCircumstantial = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Position Restricts Fragment Readings
-- ============================================================================

/-- The key insight: a modal's fragment entry lists its FULL flavor
inventory, but at any given structural position, only a SUBSET is
available. Content licensing acts as a FILTER.

At low position: [epistemic, deontic, circumstantial] is filtered
to [circumstantial] — content licensing removes epistemic (no content)
and addressee licensing removes deontic (no addressee). -/
theorem low_position_filters :
    -- Low position: only circumstantial survives
    ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors =
      [.circumstantial] := rfl

/-- At high position: all flavors survive (speech act has both
content and addressee). -/
theorem high_position_preserves :
    ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors =
      [.epistemic, .circumstantial, .deontic] := rfl

/-- The filtering relationship: high position flavors INCLUDE all
the flavors available at low position (monotonicity). Moving a
modal higher can only ADD flavors, never remove them. -/
theorem high_subsumes_low :
    ∀ f : ModalFlavor,
      f ∈ ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors →
      f ∈ ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors := by
  intro f hf
  simp [low_position_filters] at hf
  simp [high_position_preserves, hf]

end Phenomena.Modality.Studies.Hacquard2010
