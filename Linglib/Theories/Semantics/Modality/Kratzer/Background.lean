import Linglib.Core.IntensionalLogic.ConversationalBackground

/-!
# Kratzer Conversational Backgrounds — Re-Exports

@cite{kratzer-1981} @cite{kratzer-2012}

The conversational-background primitives moved to
`Core.IntensionalLogic.ConversationalBackground` (they're not Kratzer-specific).
This file re-exports them under the `Semantics.Modality.Kratzer` namespace
so the historical call style continues to work. New code should prefer the
`Core.IntensionalLogic.*` names.
-/

namespace Semantics.Modality.Kratzer

export Core.IntensionalLogic.Premise
  (propExtension propIntersection followsFrom isConsistent isCompatibleWith)

export Core.IntensionalLogic
  (ConvBackground ModalBase OrderingSource isRealistic isTotallyRealistic
   emptyBackground)

end Semantics.Modality.Kratzer
