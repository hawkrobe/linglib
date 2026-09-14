/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Overt reflexes of a designated constituent

Observation vocabulary for the perceptible traces a grammar produces
because a constituent bears a designated status — a focus
([hartmann-zimmermann-2004] Tangale, [hartmann-zimmermann-2007] Hausa,
[branan-erlewine-2023]), an A′-extraction site (`Syntax/Extraction.lean`,
the Mayan fragments), an intermediate landing site of successive-cyclic
movement ([mccloskey-2002], [georgi-2017]). A `Marking` pairs the target
with its list of `Reflex`es, each a marking `Modality` at a host
constituent; the modalities classify by `Channel` — the literature's
phonological vs morphological vs syntactic reflex cut — with the process
supplying the unity. Like `Features.Judgment` for acceptability, this is
a prediction-target vocabulary: theories never consume it as machinery;
studies translate theory-native predictions into it.

Scope: perceptible traces only. Semantic reflexes of movement
(intermediate scope/reconstruction effects) share the site indexing but
are interpretation facts, formalized in their studies. A default
exponent that surfaces regardless of the designation (Wolof expletive
*l-*, [georgi-2017]) is not a reflex — reflexes covary with the target —
and zero is never a reflex: covert marking is exponence-side competition
(blocking), not a marking modality.

## Implementation notes

String-vacuous operations (Hausa subject fronting) contribute no
reflex: the reflex list carries only perceptible alternants — including
paradigmatic ones such as deletion of otherwise-expected material
(Malay voice-marker deletion) — which is what makes `IsOvert` honest.
With constituents ordered by containment, each reflex host stands in
exactly one `HostRelation` to the target; `ExactlyTargets`, `PiedPipes`,
and [branan-erlewine-2023]'s `AntiPiedPipes` are derived from that
classification. The overlap-weakening of [hartmann-zimmermann-2007]'s
Ex-Situ Generalisation remains deferred; note `Mereology.Overlap` is
vacuous over orders with a bottom, so that member must use `¬ Disjoint`
or bot-free carriers.
-/

namespace Features

variable {C : Type*}

/-- The channel of a reflex: the literature's phonological vs
morphological vs syntactic reflex cut (reflexes of one process are
individuated by the module whose output carries the trace). -/
inductive Channel where
  | phonological | morphological | syntactic
  deriving DecidableEq, Repr, Fintype

/-- A marking modality: the kind of perceptible perturbation. The two
prosodic cases keep the demarcative vs culminative cut visible. -/
inductive Modality where
  /-- Syntactic: an exponent constituent surfaces displaced from its
  base position (movement that is not string-vacuous). -/
  | displacement
  /-- Morphological: a dedicated morpheme — affix, particle, or form
  alternation — at a host constituent. -/
  | morpheme
  /-- Phonological, demarcative: a phrase-edge at a host constituent
  (the Tangale/Chadic pattern). -/
  | boundary
  /-- Phonological, culminative: metrical prominence on a host (the
  English pattern). -/
  | prominence
  deriving DecidableEq, Repr, Fintype

/-- The channel a modality marks in. -/
def Modality.channel : Modality → Channel
  | .displacement => .syntactic
  | .morpheme     => .morphological
  | .boundary     => .phonological
  | .prominence   => .phonological

/-- A single overt reflex: a marking modality at a host constituent. -/
structure Reflex (C : Type*) where
  modality : Modality
  host     : C
  deriving DecidableEq, Repr

namespace Reflex

/-- An exponent constituent surfaces displaced from its base position. -/
def displacement (exponent : C) : Reflex C := ⟨.displacement, exponent⟩

/-- A dedicated morpheme at a host constituent. -/
def morpheme (host : C) : Reflex C := ⟨.morpheme, host⟩

/-- A demarcative prosodic event: a phrase-edge at a host constituent. -/
def boundary (edge : C) : Reflex C := ⟨.boundary, edge⟩

/-- A culminative prosodic event: metrical prominence on a host. -/
def prominence (host : C) : Reflex C := ⟨.prominence, host⟩

/-- Some reflex surfaces: the list carries perceptible material. -/
def Overt (rs : List (Reflex C)) : Prop := rs ≠ []

instance (rs : List (Reflex C)) : Decidable (Overt rs) :=
  decidable_of_iff (¬ rs.isEmpty) (by simp [Overt])

end Reflex

/-- A marking: the designated target constituent and the grammatical
reflexes marking it. -/
structure Marking (C : Type*) where
  target   : C
  reflexes : List (Reflex C)
  deriving Repr

/-- Overt marking, derived: some reflex surfaces. -/
def Marking.IsOvert (m : Marking C) : Prop := Reflex.Overt m.reflexes

instance (m : Marking C) : Decidable m.IsOvert :=
  inferInstanceAs (Decidable (Reflex.Overt _))

/-! ### Host–target containment

With constituents ordered by containment, each reflex host stands in
exactly one relation to the target: exact targeting, pied-piping (host
properly contains the target), [branan-erlewine-2023]'s anti-pied-piping
(host properly contained in the target, attested in over sixty
languages), or external hosting (host incomparable to the target — e.g.
verb-hosted extraction morphology marking an extracted argument, the
Mayan Agent Focus configuration). -/

/-- Where a reflex host sits relative to the target in the containment
order. -/
inductive HostRelation where
  | exact | piedPiping | antiPiedPiping | external
  deriving DecidableEq, Repr, Fintype

section Containment

variable [PartialOrder C] [DecidableEq C] [DecidableLT C] {m : Marking C}

/-- Classify a reflex host's position relative to a target. Total by
construction: the four `HostRelation` cells partition the possibilities. -/
def Reflex.relationTo (ρ : Reflex C) (t : C) : HostRelation :=
  if ρ.host = t then .exact
  else if t < ρ.host then .piedPiping
  else if ρ.host < t then .antiPiedPiping
  else .external

/-- Some reflex targets a constituent properly containing the target —
Ross's pied-piping, generalized from movement to all marking
morphosyntax by [branan-erlewine-2023]. -/
def Marking.PiedPipes (m : Marking C) : Prop :=
  ∃ ρ ∈ m.reflexes, ρ.relationTo m.target = .piedPiping

/-- Some reflex targets a proper subconstituent of the target —
[branan-erlewine-2023]'s anti-pied-piping. -/
def Marking.AntiPiedPipes (m : Marking C) : Prop :=
  ∃ ρ ∈ m.reflexes, ρ.relationTo m.target = .antiPiedPiping

/-- Every reflex targets the designated constituent itself. -/
def Marking.ExactlyTargets (m : Marking C) : Prop :=
  ∀ ρ ∈ m.reflexes, ρ.relationTo m.target = .exact

instance (m : Marking C) : Decidable m.PiedPipes :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (m : Marking C) : Decidable m.AntiPiedPipes :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (m : Marking C) : Decidable m.ExactlyTargets :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A pied-piping marking does not exactly target its designee. -/
theorem Marking.PiedPipes.not_exactlyTargets (h : m.PiedPipes) :
    ¬ m.ExactlyTargets := fun he =>
  let ⟨ρ, hm, hrel⟩ := h
  by rw [he ρ hm] at hrel; exact absurd hrel (by decide)

/-- An anti-pied-piping marking does not exactly target its designee. -/
theorem Marking.AntiPiedPipes.not_exactlyTargets (h : m.AntiPiedPipes) :
    ¬ m.ExactlyTargets := fun he =>
  let ⟨ρ, hm, hrel⟩ := h
  by rw [he ρ hm] at hrel; exact absurd hrel (by decide)

end Containment

/-- The universalist claim over a marking system `realize`: every
designated target receives an overt reflex. Refutation target: Hausa
and Tangale focus each refute their instance ([hartmann-zimmermann-2004],
[hartmann-zimmermann-2007]). -/
def EveryTargetOvert {I : Type*} (realize : I → Marking C) : Prop :=
  ∀ i, (realize i).IsOvert

end Features
