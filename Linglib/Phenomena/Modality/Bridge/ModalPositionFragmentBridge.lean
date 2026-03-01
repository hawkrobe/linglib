import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Core.Logic.ModalLogic

/-!
# Bridge: English Modal Fragment Entries ↔ Position-Based Flavor Availability

@cite{hacquard-2010} @cite{kratzer-1981}Connects the force–flavor cartesian products in `Fragments/English/FunctionWords.lean`
(the set of POSSIBLE readings for each modal auxiliary) to EventRelativity's
position-based flavor availability (WHEN each reading is available).

## The Relationship

The fragment lists all readings a modal CAN have across all structural
positions. EventRelativity explains WHICH readings are available at
EACH position. The bridge verifies consistency: the fragment's flavor
set = the union of position-available flavors.

## Example: English *must*

Fragment: `must` → necessity × [epistemic, deontic, circumstantial]
EventRelativity:
- High position: epistemic + circumstantial available
- Low position: circumstantial only
- Deontic: available when speech event has addressee

Union = {epistemic, circumstantial, deontic} ✓ matches fragment entry.

-/

namespace Phenomena.Modality.Bridge.ModalPositionFragmentBridge

open Semantics.Modality.EventRelativity
open Core.ModalLogic (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Union of Position-Available Flavors
-- ════════════════════════════════════════════════════

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
  refine ⟨?_, ?_, ?_⟩ <;> simp [high_matrix_flavors, low_flavors, List.mem_append]


-- ════════════════════════════════════════════════════
-- § 2. Fragment Entry Verification
-- ════════════════════════════════════════════════════

/-! The following theorems verify that each English modal's fragment
flavor set is a SUBSET of the position-available flavors. Every
reading listed in the fragment can be derived from some structural
position via content licensing.

We don't import FunctionWords.lean directly (to avoid circular
dependencies) but verify the STRUCTURAL claim: any modal with
flavors [epistemic, deontic, circumstantial] can derive each
from content licensing. -/

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


-- ════════════════════════════════════════════════════
-- § 3. Position Restricts Fragment Readings
-- ════════════════════════════════════════════════════

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


end Phenomena.Modality.Bridge.ModalPositionFragmentBridge
