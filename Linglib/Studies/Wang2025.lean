import Linglib.Semantics.Presupposition.Basic
import Linglib.Fragments.Mandarin.Particles

/-!
# Wang (2025): Presupposition, Competition, and Coherence

This file formalizes the constraint system of [wang-2025]'s dissertation on Mandarin
presupposition triggers. A presuppositional sentence competes with a non-presuppositional
alternative under three ranked pragmatic constraints: internal coherence, that the
presupposition is consistent with the assertion (`SatisfiesIC`), felicity, that the common
ground entails the presupposition (`SatisfiesFP`), and Maximize Presupposition!, which prefers
the presuppositional form where its presupposition is supported. Coherence is inviolable,
felicity outranks Maximize Presupposition!, and a common ground that supports the
presupposition only in part (`PartialFP`) is where triggers part ways: with the alternative
structure of the trigger, deletion of the trigger, replacement by another item, or no
alternative (`AltStructure`), the ranking predicts the trigger to be obligatory, optional or
blocked.

## Implementation notes

Presuppositional sentences are `PartialProp`s and the common ground a set of worlds, so felicity
is entailment of the definedness condition. The dissertation's three experiments are reported
there and not formalized.

## TODO

* The obligatoriness predictions over the alternative-structure classes, and the readings of
  the triggers under attitude verbs, await a check against the dissertation's text.

## References

* [wang-2025]
* [heim-1991]
* [katzir-2007]
-/

namespace Wang2025

open Presupposition Mandarin.Particles

variable {W : Type*}

/-! ### The constraints -/

/-- Internal coherence: the presupposition is consistent with the assertion, some world
satisfying both. Inviolable. -/
def SatisfiesIC (p : PartialProp W) : Prop := ∃ w, PartialProp.holds w p

/-- Felicity: the common ground entails the presupposition. -/
def SatisfiesFP (cg : Set W) (p : PartialProp W) : Prop := ∀ w ∈ cg, PartialProp.defined w p

/-- Partial support: the common ground is compatible with the presupposition without
entailing it. -/
def PartialFP (cg : Set W) (p : PartialProp W) : Prop :=
  (∃ w ∈ cg, PartialProp.defined w p) ∧ ¬ SatisfiesFP cg p

/-- Maximize Presupposition! prefers the presuppositional form when it is coherent and its
presupposition is supported. -/
def MPPrefers (cg : Set W) (p : PartialProp W) : Prop := SatisfiesFP cg p ∧ SatisfiesIC p

variable {cg cg' : Set W} {p : PartialProp W}

/-- Felicity is preserved by strengthening the common ground. -/
theorem SatisfiesFP.mono (h : SatisfiesFP cg p) (hcg : cg' ⊆ cg) : SatisfiesFP cg' p :=
  λ w hw => h w (hcg hw)

/-- Partial support and felicity exclude each other. -/
theorem PartialFP.not_satisfiesFP (h : PartialFP cg p) : ¬ SatisfiesFP cg p := h.2

/-- Under partial support Maximize Presupposition! does not prefer the trigger. -/
theorem PartialFP.not_mpPrefers (h : PartialFP cg p) : ¬ MPPrefers cg p := λ hm => h.2 hm.1

/-- A common ground that entails the presupposition can be strengthened to any subset without
losing the preference. -/
theorem MPPrefers.mono (h : MPPrefers cg p) (hcg : cg' ⊆ cg) : MPPrefers cg' p :=
  ⟨h.1.mono hcg, h.2⟩

/-- An incoherent sentence is never preferred, whatever the common ground. -/
theorem not_mpPrefers_of_not_satisfiesIC (h : ¬ SatisfiesIC p) (cg : Set W) : ¬ MPPrefers cg p :=
  λ hm => h hm.2

/-! ### Alternative structure -/

/-- How a trigger relates to its non-presuppositional alternative, after [katzir-2007]'s
structural alternatives: the alternative deletes the trigger, replaces it by another item, or
does not exist. -/
inductive AltStructure
  | deletion
  | replacement
  | none
  deriving DecidableEq

/-- The dissertation's classification of the Mandarin triggers. -/
def altStructureOf : MandarinTrigger → AltStructure
  | .ye => .deletion
  | .you => .deletion
  | .reng => .deletion
  | .jiu => .none
  | .zhidao => .replacement
  | .buzai => .replacement
  | .kaishi => .replacement
  | .faner => .replacement
  | .er => .replacement

end Wang2025
