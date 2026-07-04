/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Linglib.Semantics.Alternatives.AltMeaning

/-!
# Unalternative Semantics

Focus marking without [F]-features ([buring-2015],
[assmann-etal-2023]): constructions directly constrain the focal
targets they can realize. Two constructor families:

* **Morphosyntactic** ([assmann-etal-2023] §2): a construction focally
  marks exactly one constituent (`Marking`); No Projection makes it
  realize any focus within that constituent (`Realizes`), and
  `Blocked`/`Usable` implement preemption by strictly more specific
  markings. Syncretism is containment minus blocking.
* **Prosodic** ([buring-2015]): a branching node's metrical pattern
  restricts targets pointwise. Under default weak–strong prosody the
  banned targets vary the weak daughter over its alternative domain
  while the strong daughter stays at its ordinary value
  (`weakBanned`, his Weak Restriction); under prosodic reversal only
  targets varying the accented daughter non-trivially are allowed
  (`strongAllowed`, his Strong Restriction).

`strongAllowed_subset_weakBanned` connects the two rules: reversal
allows only targets that the default bans — prosodic shift is the
complement operation on focal targets, minus the trivial one.
-/

namespace Semantics.Focus

/-! ### Morphosyntactic focal marking -/

section Marking

variable {C : Type*} [PartialOrder C]

/-- A focal marking: a construction focally marking exactly one
constituent ([assmann-etal-2023] §2.2). -/
structure Marking (C : Type*) where
  marked : C
  deriving DecidableEq, Repr

/-- No Projection ([assmann-etal-2023] §2.2): a marking realizes focus
`f` iff `f` lies within its focally marked constituent — broad foci
are marked directly, narrower foci realized syncretically. -/
def Marking.Realizes (m : Marking C) (f : C) : Prop := f ≤ m.marked

instance [DecidableLE C] (m : Marking C) (f : C) :
    Decidable (m.Realizes f) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Blocking ([assmann-etal-2023] §2.3): `m` is blocked for `f` when
the inventory has a strictly more specific marking that also realizes
`f`. -/
def Marking.Blocked (inv : List (Marking C)) (m : Marking C) (f : C) :
    Prop :=
  ∃ m' ∈ inv, m'.Realizes f ∧ m'.marked ≤ m.marked ∧ m'.marked ≠ m.marked

/-- A marking is usable for a focus: in the inventory, realizes it,
and not blocked. -/
def Marking.Usable (inv : List (Marking C)) (m : Marking C) (f : C) :
    Prop :=
  m ∈ inv ∧ m.Realizes f ∧ ¬ Marking.Blocked inv m f

instance [DecidableLE C] [DecidableEq C] (inv : List (Marking C))
    (m : Marking C) (f : C) : Decidable (Marking.Blocked inv m f) :=
  List.decidableBEx _ inv

instance [DecidableLE C] [DecidableEq C] (inv : List (Marking C))
    (m : Marking C) (f : C) : Decidable (Marking.Usable inv m f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- No Projection makes realizability downward-closed: whatever
realizes a focus realizes anything within it. -/
theorem Marking.Realizes.mono {m : Marking C} {f f' : C}
    (h : m.Realizes f) (hle : f' ≤ f) : m.Realizes f' :=
  hle.trans h

end Marking

/-! ### Prosodic focal restrictions -/

section Prosodic

open Alternatives

variable {α β : Type*}

/-- Pointwise combination of alternative sets ([buring-2015]'s ⊗). -/
def otimes (F : Set (α → β)) (A : Set α) : Set β :=
  {b | ∃ f ∈ F, ∃ a ∈ A, f a = b}

/-- Weak Restriction ([buring-2015] (1)): under the default
weak–strong pattern, the banned focal targets vary the weak
(function) daughter over its alternative domain while the strong
daughter stays at its ordinary value. -/
def weakBanned (dw : AltMeaning (α → β)) (ds : AltMeaning α) : Set β :=
  otimes dw.aSet {ds.oValue}

/-- Strong Restriction ([buring-2015] (9)): under prosodic reversal,
the allowed focal targets vary the accented (function) daughter
non-trivially while the deaccented daughter stays at its ordinary
value. -/
def strongAllowed (dm : AltMeaning (α → β)) (ds : AltMeaning α) :
    Set β :=
  otimes (dm.aSet \ {dm.oValue}) {ds.oValue}

/-- Reversal allows only targets that the default bans: prosodic
shift complements the default's focal-target restriction. -/
theorem strongAllowed_subset_weakBanned (dm : AltMeaning (α → β))
    (ds : AltMeaning α) : strongAllowed dm ds ⊆ weakBanned dm ds :=
  fun _ ⟨f, hf, a, ha, h⟩ => ⟨f, hf.1, a, ha, h⟩

end Prosodic

end Semantics.Focus
