module

public import Linglib.Semantics.Modality.Kratzer.Premise

/-!
# Conversational backgrounds

A conversational background assigns each world a premise set, a list of propositions, and
Kratzer's two parameters of modal interpretation are both backgrounds in different roles: a
modal base, `ModalBase`, whose premises at a world fix the accessible worlds, those in its
intersection, and an ordering source, `OrderingSource`, whose premises rank the accessible
worlds by how many of them they verify ([kratzer-1981], [kratzer-2012]). A background is
realistic when every world verifies its own premises, `ConvBackground.IsRealistic`, so that the
actual world is accessible from itself, and totally realistic when its premises single out the
world, `ConvBackground.IsTotallyRealistic`; the empty background, `emptyBackground`, makes every
world accessible.

## References

* [A. Kratzer, *The notional category of modality* (1981)][kratzer-1981]
* [A. Kratzer, *Modals and conditionals* (2012)][kratzer-2012]
-/

@[expose] public section

namespace Modality

variable {W : Type*}

/-- A conversational background assigns each world a premise set. -/
abbrev ConvBackground (W : Type*) := W → List (W → Prop)

/-- A modal base, the background whose premises fix the accessible worlds. -/
abbrev ModalBase (W : Type*) := ConvBackground W

/-- An ordering source, the background whose premises rank the accessible worlds. -/
abbrev OrderingSource (W : Type*) := ConvBackground W

/-- A background is realistic when every world verifies its own premises. -/
def ConvBackground.IsRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, ∀ p ∈ f w, p w

/-- A background is totally realistic when its premises at a world single out that world. -/
def ConvBackground.IsTotallyRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, propIntersection (f w) = {w}

/-- The empty background, with no premises at any world, makes every world accessible. -/
def emptyBackground : ConvBackground W := fun _ ↦ []

end Modality
