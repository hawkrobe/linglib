/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Focus realization

What a grammar overtly does to mark a focus: a `Realization` pairs the
focus constituent with the list of grammatical `Reflex`es marking it —
a displaced exponent, a dedicated morpheme, a phrase-edge, or a
metrical prominence — the demarcative vs culminative cut kept visible
in the type.
Overtness is derived (`IsOvert`: the reflex list is nonempty), not
flagged; strategy labels are shape classifications over reflexes; and
multi-channel marking (Hausa ex-situ focus: displacement + Relative
morphology + stabilizer) is a multi-element list. Consumed by
[hartmann-zimmermann-2007] (Hausa) and [hartmann-zimmermann-2004]
(Tangale), whose systems each refute `EveryFocusPerceptible` — the
universalist claim that every focus receives an overt reflex.

## Implementation notes

String-vacuous operations (Hausa subject fronting) contribute no
reflex: the reflex list carries only perceptible material, which is
what makes `IsOvert` honest. With constituents ordered by containment,
a reflex host and the focus stand in the exact / pied-piping /
anti-pied-piping relations of [branan-erlewine-2023] (`ExactlyTargets`,
`PiedPipes`, `AntiPiedPipes`). The overlap-weakening of
[hartmann-zimmermann-2007]'s Ex-Situ Generalisation remains deferred;
note `Mereology.Overlap` is vacuous over orders with a bottom, so that
member must use `¬ Disjoint` or bot-free carriers.
-/

namespace Morphology.Focus

variable {C : Type*}

/-- A single overt reflex of focus marking. -/
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

/-- A focus realization: the focus constituent and the grammatical
reflexes marking it. -/
structure Realization (C : Type*) where
  focus    : C
  reflexes : List (Reflex C)
  deriving Repr

/-- Overt marking, derived: some reflex surfaces. -/
def Realization.IsOvert (r : Realization C) : Prop := r.reflexes ≠ []

instance (r : Realization C) : Decidable r.IsOvert :=
  match h : r.reflexes with
  | []     => isFalse fun hne => hne h
  | _ :: _ => isTrue (by simp [Realization.IsOvert, h])

/-! ### Host–focus containment

With constituents ordered by containment, a reflex host stands in one of
three relations to the focus: exact targeting, pied-piping (host properly
contains the focus), or [branan-erlewine-2023]'s anti-pied-piping (host
properly contained in the focus, attested in over sixty languages). -/

section Containment

variable [PartialOrder C] {r : Realization C}

/-- Some reflex targets a constituent properly containing the focus —
Ross's pied-piping, generalized from movement to all focus morphosyntax
by [branan-erlewine-2023]. -/
def Realization.PiedPipes (r : Realization C) : Prop :=
  ∃ ρ ∈ r.reflexes, r.focus < ρ.host

/-- Some reflex targets a proper subconstituent of the focus —
[branan-erlewine-2023]'s anti-pied-piping. -/
def Realization.AntiPiedPipes (r : Realization C) : Prop :=
  ∃ ρ ∈ r.reflexes, ρ.host < r.focus

/-- Every reflex targets the focus itself. -/
def Realization.ExactlyTargets (r : Realization C) : Prop :=
  ∀ ρ ∈ r.reflexes, ρ.host = r.focus

instance [DecidableLT C] (r : Realization C) : Decidable r.PiedPipes :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance [DecidableLT C] (r : Realization C) : Decidable r.AntiPiedPipes :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance [DecidableEq C] (r : Realization C) : Decidable r.ExactlyTargets :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A pied-piping realization does not exactly target its focus. -/
theorem Realization.PiedPipes.not_exactlyTargets (h : r.PiedPipes) :
    ¬ r.ExactlyTargets :=
  fun he => let ⟨ρ, hm, hlt⟩ := h; absurd (he ρ hm).symm (ne_of_lt hlt)

/-- An anti-pied-piping realization does not exactly target its focus. -/
theorem Realization.AntiPiedPipes.not_exactlyTargets (h : r.AntiPiedPipes) :
    ¬ r.ExactlyTargets :=
  fun he => let ⟨ρ, hm, hlt⟩ := h; absurd (he ρ hm) (ne_of_lt hlt)

end Containment

/-- The universalist claim over a marking system `realize`: every focus
receives an overt reflex. Hausa and Tangale each refute their
instance. -/
def EveryFocusPerceptible {I : Type*} (realize : I → Realization C) : Prop :=
  ∀ i, (realize i).IsOvert


end Morphology.Focus
