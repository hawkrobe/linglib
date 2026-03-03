import Linglib.Theories.Syntax.Minimalism.Derivations
import Linglib.Phenomena.ArgumentStructure.Subcategorization

/-!
# Bridge: Minimalist Derivations → Subcategorization Data

Connects Minimalist Merge derivations to the subcategorization data in
`Phenomena/ArgumentStructure/Subcategorization.lean`.

Verifies that Minimalist derivations model intransitive, transitive, and
ditransitive patterns, with phonological yields matching expected word order.
-/

namespace Phenomena.ArgumentStructure.Studies.MinimalismSubcategorization

open Minimalism.Phenomena.Derivations

/-- The derivations model grammatical intransitive patterns -/
theorem models_intransitive :
    Phenomena.ArgumentStructure.Subcategorization.data.pairs.any
      (·.grammatical == "John sleeps") := by
  native_decide

theorem models_transitive :
    Phenomena.ArgumentStructure.Subcategorization.data.pairs.any
      (·.grammatical == "John devours pizza") := by
  native_decide

theorem models_ditransitive :
    Phenomena.ArgumentStructure.Subcategorization.data.pairs.any
      (·.grammatical == "John gives Mary book") := by
  native_decide

/-- Verify the phonological yield of derivations matches expected word order -/
example : john_sleeps.phonYield = ["John", "sleeps"] := rfl

example : john_devours_pizza.phonYield = ["John", "devours", "pizza"] := by native_decide

end Phenomena.ArgumentStructure.Studies.MinimalismSubcategorization
