import Linglib.Core.IntensionalLogic.Premise

/-!
# Conversational Backgrounds @cite{kratzer-1981} @cite{kratzer-2012}

Conversational backgrounds are functions from worlds to sets of propositions.
The modal base determines accessibility; the ordering source ranks accessible
worlds.

The premise-set primitives (`propExtension`, `propIntersection`, `followsFrom`,
`isConsistent`, `isCompatibleWith`) live in `Core.IntensionalLogic.Premise` and
are re-exported here so existing call sites continue to resolve them under the
`Semantics.Modality.Kratzer` namespace.

All types are polymorphic over the world type `W`. Propositions are
`W → Prop` (mathlib-native); reasoning is classical.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
- Kratzer, A. (2012). Modals and Conditionals. Oxford University Press.
-/

namespace Semantics.Modality.Kratzer

export Core.IntensionalLogic.Premise
  (propExtension propIntersection followsFrom isConsistent isCompatibleWith)

variable {W : Type*}

/--
A conversational background maps worlds to sets of propositions.

This is Kratzer's key innovation: the modal base and ordering source are both
conversational backgrounds, but play different roles.
-/
abbrev ConvBackground (W : Type*) := W → List (W → Prop)

/-- The modal base: determines which worlds are accessible. -/
abbrev ModalBase (W : Type*) := ConvBackground W

/-- The ordering source: determines how accessible worlds are ranked. -/
abbrev OrderingSource (W : Type*) := ConvBackground W

/--
A conversational background is **realistic** iff for all w: w ∈ ⋂f(w).

This means the actual world satisfies all propositions in the modal base.
Kratzer (p. 32): "For each world, there is a particular body of facts in w
that has a counterpart in each world in ⋂f(w)."
-/
def isRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, ∀ p ∈ f w, p w

/--
A conversational background is **totally realistic** iff for all w: ⋂f(w) = {w}.

This is the strongest form: only the actual world is accessible.
Kratzer (p. 33): "A totally realistic conversational background is a function f
such that for any world w, ⋂f(w) = {w}."
-/
def isTotallyRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, propIntersection (f w) = {w}

/--
The **empty** conversational background: f(w) = ∅ for all w.

Kratzer (p. 33): "The empty conversational background is the function f such
that for any w ∈ W, f(w) = ∅. Since ⋂f(w) = W if f(w) = ∅, empty
conversational backgrounds are also realistic."
-/
def emptyBackground : ConvBackground W := λ _ => []

end Semantics.Modality.Kratzer
