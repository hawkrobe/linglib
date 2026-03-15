/-
@cite{kratzer-1981} Conversational Backgrounds

Conversational backgrounds are functions from worlds to sets of propositions.
The modal base determines accessibility; the ordering source ranks accessible worlds.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
- Kratzer, A. (2012). Modals and Conditionals. Oxford University Press.
-/

import Linglib.Theories.Semantics.Attitudes.Intensional

namespace Semantics.Modality.Kratzer

open Semantics.Attitudes.Intensional

/-- Convert to list of worlds where proposition holds. -/
def propExtension (p : BProp World) : List World :=
  allWorlds.filter p

/-- The intersection of a set of propositions: worlds satisfying ALL. -/
def propIntersection (props : List (BProp World)) : List World :=
  allWorlds.filter λ w => props.all λ p => p w

/-- A proposition p **follows from** a set A iff ∩A ⊆ p (Kratzer p. 31)

In other words: every world satisfying all of A also satisfies p. -/
def followsFrom (p : BProp World) (A : List (BProp World)) : Bool :=
  (propIntersection A).all p

/-- A set of propositions is **consistent** iff ∩A ≠ ∅ (Kratzer p. 31) -/
def isConsistent (A : List (BProp World)) : Bool :=
  !(propIntersection A).isEmpty

/-- A proposition p is **compatible with** A iff A ∪ {p} is consistent (Kratzer p. 31) -/
def isCompatibleWith (p : BProp World) (A : List (BProp World)) : Bool :=
  isConsistent (p :: A)


/--
A conversational background maps worlds to sets of propositions.

This is Kratzer's key innovation: the modal base and ordering source are both
conversational backgrounds, but play different roles.
-/
abbrev ConvBackground := World → List (BProp World)

/-- The modal base: determines which worlds are accessible. -/
abbrev ModalBase := ConvBackground

/-- The ordering source: determines how accessible worlds are ranked. -/
abbrev OrderingSource := ConvBackground

/--
A conversational background is **realistic** iff for all w: w ∈ ∩f(w).

This means the actual world satisfies all propositions in the modal base.
Kratzer (p. 32): "For each world, there is a particular body of facts in w
that has a counterpart in each world in ∩f(w)."
-/
def isRealistic (f : ConvBackground) : Prop :=
  ∀ w : World, (f w).all (λ p => p w) = true

/--
A conversational background is **totally realistic** iff for all w: ∩f(w) = {w}.

This is the strongest form: only the actual world is accessible.
Kratzer (p. 33): "A totally realistic conversational background is a function f
such that for any world w, ∩f(w) = {w}."
-/
def isTotallyRealistic (f : ConvBackground) : Prop :=
  ∀ w : World, propIntersection (f w) = [w]

/--
The **empty** conversational background: f(w) = ∅ for all w.

Kratzer (p. 33): "The empty conversational background is the function f such
that for any w ∈ W, f(w) = ∅. Since ∩f(w) = W if f(w) = ∅, empty
conversational backgrounds are also realistic."
-/
def emptyBackground : ConvBackground := λ _ => []

end Semantics.Modality.Kratzer
