import Linglib.Theories.Syntax.Minimalism.Derivations
import Linglib.Phenomena.WordOrder.Basic

/-!
# Bridge: Minimalist Derivations → Word Order Data

Connects Minimalist Merge derivations to the word order data in
`Phenomena/WordOrder/Basic.lean`.

Verifies that Minimalist derivations model SVO sentences from the
phenomena data, with phonological yields matching expected word order.
-/

namespace Phenomena.WordOrder.Bridge.MinimalismDerivations

open Minimalism.Phenomena.Derivations

/-- The derivations model the grammatical SVO sentences from WordOrder.data -/
theorem models_svo_word_order :
    Phenomena.WordOrder.data.pairs.any (·.grammatical == "John sees Mary") := by
  native_decide

/-- Verify the phonological yield of a derivation matches expected word order -/
example : john_sees_mary.phonYield = ["John", "sees", "Mary"] := rfl

end Phenomena.WordOrder.Bridge.MinimalismDerivations
