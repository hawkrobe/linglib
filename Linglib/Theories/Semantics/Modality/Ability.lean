import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Modality.Kratzer.Operators

/-!
# Ability Modals: Kratzer Bridge
@cite{hacquard-2006} @cite{kratzer-1981} @cite{nadathur-2023}

Connects the causal model of ability (`CausalFrame World` with
`actualization = .aspectual`, defined in `ComplementEntailing.lean`)
to Kratzer's modal semantics.

The core semantics of ability modals — `abilityFrame`, `sufficientAt`,
`actualityWithAspect`, and all actuality-entailment theorems — live in
`Causation/ComplementEntailing.lean`. This file provides only the bridge
to Kratzer's circumstantial possibility.

-/

namespace Semantics.Modality.Ability

open Core.Causal
open Semantics.Causation.ComplementEntailing
open Semantics.Attitudes.Intensional (World)
open Semantics.Modality.Kratzer (ModalBase)

-- ════════════════════════════════════════════════════
-- Bridge to Kratzer Modal Semantics
-- ════════════════════════════════════════════════════

/-- Convert an ability `CausalFrame` to a Kratzer circumstantial modal base.

    The modal base at each world returns propositions encoding the
    causal background. Ability IS circumstantial possibility, where the
    "circumstances" are the causal structure. -/
def toCircumstantialBase (f : CausalFrame World) : ModalBase World :=
  λ _w => [λ w' => f.sufficientAt w']

/-- Ability as Kratzer possibility: "can VP" is ◇(complement) where
    the modal base encodes circumstantial facts. -/
def abilityAsKratzerPossibility (f : CausalFrame World) (w : World) : Prop :=
  Semantics.Modality.Kratzer.simplePossibility
    (toCircumstantialBase f)
    (λ w' => f.actualizedAt w')
    w

/-- Ability = causal sufficiency. After the @cite{schulz-2011}/@cite{fitting-1985}
    unification, both `f.sufficientAt` and `causallySufficient` reduce to the
    same `normalDevelopment` query, so the bridge is definitional. -/
theorem ability_is_causal_sufficiency (f : CausalFrame World) (w : World) :
    f.sufficientAt w ↔
      causallySufficient f.dynamics (f.background w) f.trigger f.complement :=
  Iff.rfl

end Semantics.Modality.Ability
