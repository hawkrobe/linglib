/-
@cite{kratzer-1981} Conversational Backgrounds

Conversational backgrounds are functions from worlds to sets of propositions.
The modal base determines accessibility; the ordering source ranks accessible worlds.

All types are polymorphic over the world type `W`.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
- Kratzer, A. (2012). Modals and Conditionals. Oxford University Press.
-/

import Mathlib.Data.Finset.Card

namespace Semantics.Modality.Kratzer

variable {W : Type*} [DecidableEq W] [Fintype W]

/-- Convert to the set of worlds where proposition holds. -/
def propExtension (p : W → Bool) : Finset W :=
  Finset.univ.filter (fun w => p w)

/-- The intersection of a set of propositions: worlds satisfying ALL. -/
def propIntersection (props : List (W → Bool)) : Finset W :=
  Finset.univ.filter (fun w => props.all fun p => p w)

/-- A proposition p **follows from** a set A iff ∩A ⊆ p (Kratzer p. 31)

In other words: every world satisfying all of A also satisfies p. -/
def followsFrom (p : W → Bool) (A : List (W → Bool)) : Bool :=
  decide (∀ w ∈ propIntersection A, p w = true)

/-- A set of propositions is **consistent** iff ∩A ≠ ∅ (Kratzer p. 31) -/
def isConsistent (A : List (W → Bool)) : Bool :=
  !(propIntersection A == ∅)

/-- A proposition p is **compatible with** A iff A ∪ {p} is consistent (Kratzer p. 31) -/
def isCompatibleWith (p : W → Bool) (A : List (W → Bool)) : Bool :=
  isConsistent (p :: A)


/--
A conversational background maps worlds to sets of propositions.

This is Kratzer's key innovation: the modal base and ordering source are both
conversational backgrounds, but play different roles.
-/
abbrev ConvBackground (W : Type*) := W → List (W → Bool)

/-- The modal base: determines which worlds are accessible. -/
abbrev ModalBase (W : Type*) := ConvBackground W

/-- The ordering source: determines how accessible worlds are ranked. -/
abbrev OrderingSource (W : Type*) := ConvBackground W

/--
A conversational background is **realistic** iff for all w: w ∈ ∩f(w).

This means the actual world satisfies all propositions in the modal base.
Kratzer (p. 32): "For each world, there is a particular body of facts in w
that has a counterpart in each world in ∩f(w)."
-/
def isRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, (f w).all (λ p => p w) = true

/--
A conversational background is **totally realistic** iff for all w: ∩f(w) = {w}.

This is the strongest form: only the actual world is accessible.
Kratzer (p. 33): "A totally realistic conversational background is a function f
such that for any world w, ∩f(w) = {w}."
-/
def isTotallyRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, propIntersection (f w) = {w}

/--
The **empty** conversational background: f(w) = ∅ for all w.

Kratzer (p. 33): "The empty conversational background is the function f such
that for any w ∈ W, f(w) = ∅. Since ∩f(w) = W if f(w) = ∅, empty
conversational backgrounds are also realistic."
-/
def emptyBackground : ConvBackground W := λ _ => []

end Semantics.Modality.Kratzer
