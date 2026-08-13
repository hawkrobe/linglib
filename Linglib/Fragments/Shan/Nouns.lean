import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Shan noun parameters

Shan (Southwestern Tai, Kra-Dai) has no overt articles, so no covert
type-shift is blocked and bare nouns reach definite, kind, and existential
readings directly; in particular both ι and ι^x are unblocked, which lets
bare nouns express unique and anaphoric definiteness alike ([moroney-2021]
§4.3). Contrast `MeaningPreservation.englishBlocking`, where *the* blocks
covert ι and *a*/*some* block covert ∃.

## References

* [moroney-2021], §4.3
-/

namespace Shan.Nouns

open Semantics.Kinds.NMP (BlockingPrinciple)

/-- The Shan blocking principle blocks no type-shift, since Shan has no
    overt determiners. -/
def blocking : BlockingPrinciple :=
  { determiners := []
  , iotaBlocked := false
  , existsBlocked := false
  , downBlocked := false }

end Shan.Nouns
