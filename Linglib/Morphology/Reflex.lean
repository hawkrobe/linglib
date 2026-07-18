/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Overt reflexes of a designated constituent

What a grammar overtly does to mark a designated constituent: a
`Marking` pairs the target with the list of grammatical `Reflex`es
marking it — a displaced exponent, a dedicated morpheme, a phrase-edge,
or a metrical prominence — the demarcative vs culminative cut kept
visible in the type. Nothing here fixes *why* the target is designated:
consumers instantiate the target as a focus ([hartmann-zimmermann-2004]
Tangale, [hartmann-zimmermann-2007] Hausa, [branan-erlewine-2023]), an
extraction site (`Syntax/Extraction.lean`, the Mayan fragments), or any
other marked dependency.
Overtness is derived (`IsOvert`: the reflex list is nonempty), not
flagged; strategy labels are shape classifications over reflexes; and
multi-channel marking (Hausa ex-situ focus: displacement + Relative
morphology + stabilizer) is a multi-element list.

## Implementation notes

String-vacuous operations (Hausa subject fronting) contribute no
reflex: the reflex list carries only perceptible material, which is
what makes `IsOvert` honest. With constituents ordered by containment,
a reflex host and the target stand in the exact / pied-piping /
anti-pied-piping relations of [branan-erlewine-2023] (`ExactlyTargets`,
`PiedPipes`, `AntiPiedPipes`). The overlap-weakening of
[hartmann-zimmermann-2007]'s Ex-Situ Generalisation remains deferred;
note `Mereology.Overlap` is vacuous over orders with a bottom, so that
member must use `¬ Disjoint` or bot-free carriers.
-/

namespace Morphology

variable {C : Type*}

/-- A single overt reflex marking a designated constituent. -/
inductive Reflex (C : Type*) where
  /-- An exponent constituent surfaces displaced from its base position
  (movement that is not string-vacuous). -/
  | displacement (exponent : C)
  /-- A dedicated morpheme — affix, particle, or form alternation — at
  a host constituent. -/
  | morpheme (host : C)
  /-- A demarcative prosodic event: a phrase-edge at a host constituent
  (the Tangale/Chadic pattern). -/
  | boundary (edge : C)
  /-- A culminative prosodic event: metrical prominence on a host (the
  English pattern). -/
  | prominence (host : C)
  deriving DecidableEq, Repr

/-- The constituent a reflex marks: the displaced exponent, or the host
of a morpheme, boundary, or prominence. -/
def Reflex.host : Reflex C → C
  | .displacement exponent => exponent
  | .morpheme host => host
  | .boundary edge => edge
  | .prominence host => host

/-- Some reflex surfaces: the list carries perceptible material. -/
def Reflex.Overt (rs : List (Reflex C)) : Prop := rs ≠ []

instance (rs : List (Reflex C)) : Decidable (Reflex.Overt rs) :=
  decidable_of_iff (¬ rs.isEmpty) (by simp [Reflex.Overt])

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

With constituents ordered by containment, a reflex host stands in one of
three relations to the target: exact targeting, pied-piping (host properly
contains the target), or [branan-erlewine-2023]'s anti-pied-piping (host
properly contained in the target, attested in over sixty languages). -/

section Containment

variable [PartialOrder C] {m : Marking C}

/-- Some reflex targets a constituent properly containing the target —
Ross's pied-piping, generalized from movement to all marking
morphosyntax by [branan-erlewine-2023]. -/
def Marking.PiedPipes (m : Marking C) : Prop :=
  ∃ ρ ∈ m.reflexes, m.target < ρ.host

/-- Some reflex targets a proper subconstituent of the target —
[branan-erlewine-2023]'s anti-pied-piping. -/
def Marking.AntiPiedPipes (m : Marking C) : Prop :=
  ∃ ρ ∈ m.reflexes, ρ.host < m.target

/-- Every reflex targets the designated constituent itself. -/
def Marking.ExactlyTargets (m : Marking C) : Prop :=
  ∀ ρ ∈ m.reflexes, ρ.host = m.target

instance [DecidableLT C] (m : Marking C) : Decidable m.PiedPipes :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance [DecidableLT C] (m : Marking C) : Decidable m.AntiPiedPipes :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance [DecidableEq C] (m : Marking C) : Decidable m.ExactlyTargets :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A pied-piping marking does not exactly target its designee. -/
theorem Marking.PiedPipes.not_exactlyTargets (h : m.PiedPipes) :
    ¬ m.ExactlyTargets :=
  fun he => let ⟨ρ, hm, hlt⟩ := h; absurd (he ρ hm).symm (ne_of_lt hlt)

/-- An anti-pied-piping marking does not exactly target its designee. -/
theorem Marking.AntiPiedPipes.not_exactlyTargets (h : m.AntiPiedPipes) :
    ¬ m.ExactlyTargets :=
  fun he => let ⟨ρ, hm, hlt⟩ := h; absurd (he ρ hm) (ne_of_lt hlt)

end Containment

/-- The universalist claim over a marking system `realize`: every
designated target receives an overt reflex. Refutation target: Hausa
and Tangale focus each refute their instance ([hartmann-zimmermann-2004],
[hartmann-zimmermann-2007]). -/
def EveryTargetOvert {I : Type*} (realize : I → Marking C) : Prop :=
  ∀ i, (realize i).IsOvert

end Morphology
