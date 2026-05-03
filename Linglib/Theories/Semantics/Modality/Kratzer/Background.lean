import Linglib.Core.Logic.Intensional.ConversationalBackground

/-!
# Kratzer Conversational Backgrounds — Re-Exports

@cite{kratzer-1981} @cite{kratzer-2012}

The conversational-background primitives moved to
`Core.Logic.Intensional.ConversationalBackground` (they're not Kratzer-specific).
This file re-exports them under the `Semantics.Modality.Kratzer` namespace
so the historical call style continues to work. New code should prefer the
`Core.Logic.Intensional.*` names.
-/

namespace Semantics.Modality.Kratzer

export Core.Logic.Intensional.Premise
  (propExtension propIntersection followsFrom isConsistent isCompatibleWith)

export Core.Logic.Intensional
  (ConvBackground ModalBase OrderingSource isRealistic isTotallyRealistic
   emptyBackground)

end Semantics.Modality.Kratzer
