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

open Semantics.Modality.Typology (ModalInventory satisfiesIFF)
open Fragments.German.Predicates.Modal (GermanModalEntry allModals)

/-- German modal inventory, derived from the Fragment (single source of truth). -/
def german : ModalInventory :=
  .fromAuxEntries "German" "Indo-European" "Kratzer (1981)"
    allModals GermanModalEntry.form GermanModalEntry.modalMeaning

/-- All seven German modals satisfy IFF (including *sollte* as distinct from *sollen*). -/
theorem german_all_iff : german.allIFF = true := by native_decide

/-- German has seven modal expressions (*sollte* counted separately from *sollen*
    per morphological individuation, @cite{steinert-threlkeld-imel-guo-2023} §4.3). -/
theorem german_size : german.expressions.length = 7 := by native_decide

end Phenomena.Modality.GermanModalsBridge
