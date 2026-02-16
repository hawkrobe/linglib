import Linglib.Theories.Semantics.Modality.Typology
import Linglib.Fragments.German.Predicates.Modal

/-!
# German Modals Bridge

Constructs a `ModalInventory` from the German modal fragment and verifies
that all German modals satisfy IFF (Independence of Force and Flavor).

This bridges the Fragment data (typed by `GermanModalEntry`) to the
cross-linguistic typology infrastructure.

Reference: Kratzer, A. (1981). The Notional Category of Modality.
-/

namespace Phenomena.Modality.GermanModalsBridge

open IntensionalSemantics.Modal.Typology (ModalInventory satisfiesIFF)
open Fragments.German.Predicates.Modal (GermanModalEntry allModals)

/-- German modal inventory, derived from the Fragment (single source of truth). -/
def german : ModalInventory :=
  .fromAuxEntries "German" "Indo-European" "Kratzer (1981)"
    allModals GermanModalEntry.form GermanModalEntry.modalMeaning

/-- All six German modals satisfy IFF. -/
theorem german_all_iff : german.allIFF = true := by native_decide

/-- German has six modal expressions. -/
theorem german_size : german.expressions.length = 6 := by native_decide

end Phenomena.Modality.GermanModalsBridge
