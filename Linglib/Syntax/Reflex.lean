/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Basic

/-!
# Overt reflexes of a designated constituent

A grammar leaves perceptible traces of a constituent's designated status: a focus
([hartmann-zimmermann-2004] on Tangale, [hartmann-zimmermann-2007] on Hausa,
[branan-erlewine-2023]), an A′-extraction site (the Mayan fragments, whose `Extraction.realize`
records the reflexes of extracting each `RelativeClause.Position`), an intermediate landing
site of successive-cyclic movement ([mccloskey-2002], [georgi-2017]). A `Reflex` is a marking
`Reflex.Modality` at a host constituent; a marking system assigns each designated target its
finite set of reflexes. Modalities classify by `Reflex.Channel`, the phonological vs
morphological vs syntactic cut. Like
`Data.Examples.Judgment` for acceptability, this is a prediction-target vocabulary: studies
translate theory-native predictions into it, and no theory consumes it as machinery.

## Main declarations

* `Reflex.PiedPipes`, `Reflex.AntiPiedPipes`, `Reflex.ExactlyTargets`:
  [branan-erlewine-2023]'s three host–target configurations in the containment order.
* `Reflex.EveryTargetOvert`: the universalist claim that every designated target is overtly
  marked, which Tangale and Hausa focus refute.

## Implementation notes

Only perceptible alternants are reflexes. A string-vacuous operation (Hausa subject fronting)
contributes none; a default exponent surfacing regardless of the designation (Wolof expletive
*l-*, [georgi-2017]) is not a reflex, since reflexes covary with the target; and zero is never
a reflex, covert marking being exponence-side competition rather than a marking modality.
Deletion of otherwise-expected material (Malay voice-marker deletion) is a reflex. Semantic
reflexes of movement (intermediate scope, reconstruction) are interpretation facts formalized
in their studies.

With constituents ordered by containment, a host is the target itself, properly contains it
(pied-piping), is properly contained in it (anti-pied-piping), or is incomparable to it
(`IncompRel (· ≤ ·)`: external hosting, such as the verb-hosted extraction morphology of the
Mayan Agent Focus configuration). The predicates are stated in the order vocabulary directly
rather than through a four-way classification, over a reflex set and an explicit target, so a
study asserts the target in the claim rather than storing it beside the data. Overt marking of
a target is `Finset.Nonempty` of its reflex set.

## TODO

* The overlap-weakening of [hartmann-zimmermann-2007]'s Ex-Situ Generalisation, which needs a
  structured-meaning overlap predicate.

## References

* [branan-erlewine-2023]
* [georgi-2017]
* [hartmann-zimmermann-2004]
* [hartmann-zimmermann-2007]
* [mccloskey-2002]
-/

/-- The channel of a reflex: the literature's phonological vs morphological vs syntactic
reflex cut, individuating the reflexes of one process by the module whose output carries the
trace. -/
inductive Reflex.Channel where
  | phonological | morphological | syntactic
  deriving DecidableEq, Repr

/-- A marking modality: the kind of perceptible perturbation. The two prosodic cases keep the
demarcative vs culminative cut visible. -/
inductive Reflex.Modality where
  /-- Syntactic: an exponent constituent surfaces displaced from its base position. -/
  | displacement
  /-- Morphological: a dedicated morpheme (affix, particle, or form alternation) at a host. -/
  | morpheme
  /-- Phonological, demarcative: a phrase edge at a host (the Tangale/Chadic pattern). -/
  | boundary
  /-- Phonological, culminative: metrical prominence on a host (the English pattern). -/
  | prominence
  deriving DecidableEq, Repr

/-- A single overt reflex: a marking modality at a host constituent. -/
structure Reflex (C : Type*) where
  modality : Reflex.Modality
  host : C
  deriving DecidableEq, Repr

namespace Reflex

variable {C : Type*}

/-- The channel a modality marks in. -/
def Modality.channel : Modality → Channel
  | .displacement => .syntactic
  | .morpheme => .morphological
  | .boundary => .phonological
  | .prominence => .phonological

/-- An exponent constituent surfaces displaced from its base position. -/
def displacement (exponent : C) : Reflex C := ⟨.displacement, exponent⟩

/-- A dedicated morpheme at a host constituent. -/
def morpheme (host : C) : Reflex C := ⟨.morpheme, host⟩

/-- A phrase edge at a host constituent. -/
def boundary (edge : C) : Reflex C := ⟨.boundary, edge⟩

/-- Metrical prominence on a host constituent. -/
def prominence (host : C) : Reflex C := ⟨.prominence, host⟩

/-! ### Host–target containment

With constituents ordered by containment, [branan-erlewine-2023] distinguish exact targeting,
pied-piping (a host properly contains the target) and anti-pied-piping (a host is properly
contained in the target, attested in over sixty languages). -/

section Containment

variable [Preorder C] (s : Finset (Reflex C)) (target : C)

/-- Some reflex is hosted by a constituent properly containing the target: Ross's pied-piping,
generalized from movement to all marking morphosyntax by [branan-erlewine-2023]. -/
def PiedPipes : Prop := ∃ ρ ∈ s, target < ρ.host

/-- Some reflex is hosted by a proper subconstituent of the target:
[branan-erlewine-2023]'s anti-pied-piping. -/
def AntiPiedPipes : Prop := ∃ ρ ∈ s, ρ.host < target

/-- Every reflex is hosted by the designated constituent itself. -/
def ExactlyTargets : Prop := ∀ ρ ∈ s, ρ.host = target

variable {s target}

/-- A pied-piping reflex set does not exactly target its designee. -/
theorem PiedPipes.not_exactlyTargets (h : PiedPipes s target) : ¬ ExactlyTargets s target :=
  fun he ↦ let ⟨ρ, hρ, hlt⟩ := h; (he ρ hρ ▸ hlt).false

/-- An anti-pied-piping reflex set does not exactly target its designee. -/
theorem AntiPiedPipes.not_exactlyTargets (h : AntiPiedPipes s target) :
    ¬ ExactlyTargets s target :=
  fun he ↦ let ⟨ρ, hρ, hlt⟩ := h; (he ρ hρ ▸ hlt).false

variable (s target) [DecidableLT C] [DecidableEq C]

instance : Decidable (PiedPipes s target) := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable (AntiPiedPipes s target) := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable (ExactlyTargets s target) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

end Containment

/-- The universalist claim over a marking system `realize`: every designated target receives an
overt reflex. Tangale and Hausa focus each refute their instance ([hartmann-zimmermann-2004],
[hartmann-zimmermann-2007]). -/
def EveryTargetOvert {I : Type*} (realize : I → Finset (Reflex C)) : Prop :=
  ∀ i, (realize i).Nonempty

end Reflex
