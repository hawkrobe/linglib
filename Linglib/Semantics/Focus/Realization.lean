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
what makes `IsOvert` honest. Host-vs-focus tightness relations
(and the overlap-weakening of [hartmann-zimmermann-2007]'s Ex-Situ
Generalisation) are deferred until pied-piping data land; note
`Mereology.Overlap` is vacuous over orders with a bottom, so that
member must use `¬ Disjoint` or bot-free carriers.
-/

namespace Semantics.Focus

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

/-- The universalist claim over a marking system `realize`: every focus
receives an overt reflex. Hausa and Tangale each refute their
instance. -/
def EveryFocusPerceptible {I : Type*} (realize : I → Realization C) : Prop :=
  ∀ i, (realize i).IsOvert


end Semantics.Focus
