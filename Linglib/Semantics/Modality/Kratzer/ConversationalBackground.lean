import Linglib.Core.Logic.Intensional.Premise

/-!
# Conversational Backgrounds

[kratzer-1981] [kratzer-2012]

A conversational background maps worlds to sets of propositions. Two roles:

- **Modal base** (`ModalBase`) determines accessibility — `R_f(w, w') ≡ w' ∈ ⋂f(w)`.
- **Ordering source** (`OrderingSource`) ranks accessible worlds by how many
  ordering propositions they satisfy.
-/

open Core.Logic.Intensional.Premise (propIntersection)

namespace Semantics.Modality.Kratzer

variable {W : Type*}

/-- A conversational background maps worlds to sets of propositions.

    Kratzer's key innovation: the modal base and ordering source are both
    conversational backgrounds, but play different roles. -/
abbrev ConvBackground (W : Type*) := W → List (W → Prop)

/-- The modal base: determines which worlds are accessible. -/
abbrev ModalBase (W : Type*) := ConvBackground W

/-- The ordering source: determines how accessible worlds are ranked. -/
abbrev OrderingSource (W : Type*) := ConvBackground W

/-- A conversational background is **realistic** iff for all w: w ∈ ⋂f(w).
    The actual world satisfies all propositions in the background.

    [kratzer-1981]: realistic conversational backgrounds make every fact
    about `w` part of `⋂f(w)`. UNVERIFIED page reference. -/
def isRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, ∀ p ∈ f w, p w

/-- A conversational background is **totally realistic** iff for all w:
    `⋂f(w) = {w}`. The strongest form: only the actual world is accessible.
    UNVERIFIED page reference. -/
def isTotallyRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, propIntersection (f w) = {w}

/-- The **empty** conversational background: `f(w) = ∅` for all w.
    `⋂f(w) = W` (vacuous intersection), so the empty background is itself
    trivially realistic. UNVERIFIED page reference. -/
def emptyBackground : ConvBackground W := λ _ => []

end Semantics.Modality.Kratzer
