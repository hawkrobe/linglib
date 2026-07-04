/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Focus.Unalternatives
import Linglib.Studies.HartmannZimmermann2004

/-!
# Unalternative morphosyntactic focus marking

Formalises [assmann-etal-2023]: focus marking without [F]-features.
Each construction focally marks exactly one constituent; **No
Projection** (§2.2) lets it realize any focus within that constituent
(the marked constituent and the pragmatic focus need not coincide);
**Blocking** (§2.3) preempts a marking wherever a strictly more
specific one would do. Syncretism is containment minus blocking:
disjoint-constituent syncretisms (V with Obj, §4.2.1) — which
"directly contradict Uniform Marking" — fall out by focally marking
the common mother (§4.2.3).

Case studies: Gùrùntùm (§2), where the clausal marking is blocked
for every smaller focus, and Hausa (§3.2), where the relative form
focally marks the subject and the absolute form is a default marking
the clause. Their fn. 13 extends the Hausa pattern to the Tangale
progressive and fn. 18 treats the Tangale perfective triple as the
V/VP/O syncretism, so `ua_agrees_with_hz_on_overtness` proves
cell-by-cell agreement with [hartmann-zimmermann-2004]'s reflex
analysis (`HartmannZimmermann2004.realize`) while the two accounts
disagree about what "marking the focus" means: what the reflex
analysis states as focus without overt reflex is, here, a default
marking whose focally marked constituent properly contains the
focus. Their fn. 17 hedges on the placement of the Tangale markers;
the marking-to-constituent assignment below follows their fn. 13 and
fn. 18.
-/

namespace AssmannEtAl2023

open Semantics.Focus (Marking)


/-! ## The constituent skeleton of the case studies -/

/-- Clause skeleton: subject and VP within S; verb and object within
VP. -/
inductive Node where
  | s | sbj | vp | v | obj
  deriving DecidableEq, Repr, Fintype

/-- Constituent containment. -/
def nle : Node → Node → Bool
  | _, .s => true
  | .v, .vp | .obj, .vp | .vp, .vp => true
  | .sbj, .sbj | .v, .v | .obj, .obj => true
  | _, _ => false

instance : PartialOrder Node where
  le a b := nle a b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Node := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-! ## Case study I: Gùrùntùm (§2) -/

/-- The Gùrùntùm inventory: *a* before the subject, *a* before the
object marking VP, clausal *á* ((4a–c)). -/
def guruntumInv : List (Marking Node) := [⟨.sbj⟩, ⟨.vp⟩, ⟨.s⟩]

/-- (4b): focally marking VP is syncretic for V, VP and Obj focus —
No Projection in action. -/
theorem guruntum_vp_syncretism :
    Marking.Usable guruntumInv ⟨.vp⟩ .v ∧ Marking.Usable guruntumInv ⟨.vp⟩ .vp ∧
    Marking.Usable guruntumInv ⟨.vp⟩ .obj := by decide

/-- (4c)/(5): the clausal marking realizes only clausal focus — every
smaller focus is blocked by a specialized marking. -/
theorem guruntum_clausal_blocked :
    Marking.Usable guruntumInv ⟨.s⟩ .s ∧ ¬ Marking.Usable guruntumInv ⟨.s⟩ .sbj ∧
    ¬ Marking.Usable guruntumInv ⟨.s⟩ .vp ∧ ¬ Marking.Usable guruntumInv ⟨.s⟩ .obj := by
  decide

/-! ## Case study: Hausa (§3.2) -/

/-- The Hausa canonical-order inventory: the relative form of the PAC
focally marks the subject ((10)); the absolute form is the default,
"the absence of a specific marking", focally marking the clause. -/
def hausaInv : List (Marking Node) := [⟨.sbj⟩, ⟨.s⟩]

/-- (11): the absolute form answers any non-subject constituent
question and all-new contexts — one default, syncretic for V, VP,
Obj and clausal focus. -/
theorem hausa_default_syncretism :
    Marking.Usable hausaInv ⟨.s⟩ .v ∧ Marking.Usable hausaInv ⟨.s⟩ .vp ∧
    Marking.Usable hausaInv ⟨.s⟩ .obj ∧ Marking.Usable hausaInv ⟨.s⟩ .s := by decide

/-- Only subject focus has to be marked (their fn. 13): the default
is blocked for subject focus by the relative form. -/
theorem hausa_subject_needs_relative :
    ¬ Marking.Usable hausaInv ⟨.s⟩ .sbj ∧ Marking.Usable hausaInv ⟨.sbj⟩ .sbj := by
  decide

/-! ## The Tangale rivalry (their fn. 13, 17, 18)

Their fn. 13 extends the Hausa pattern to the Tangale progressive;
fn. 18 treats the Tangale perfective V/VP/O triple as the
disjoint-constituent syncretism, focally marking VP (§4.2.3). The
resulting marking assignment agrees with
[hartmann-zimmermann-2004]'s reflex analysis on every cell of the
paradigm — the accounts differ not on the data but on what "marking
the focus" means. -/

open HartmannZimmermann2004 in
/-- The UA marking of each Tangale configuration: subjects take the
specific subject marking (postposing); perfective non-subject foci
the VP-marking (the prosodic boundary, fn. 18); progressive
non-subject foci the default clause marking (fn. 13). -/
def uaTangale : Config → Marking Node
  | ⟨.subject, _, _⟩        => ⟨.sbj⟩
  | ⟨_, .perfective, _⟩     => ⟨.vp⟩
  | ⟨_, .progressive, _⟩    => ⟨.s⟩

open HartmannZimmermann2004 in
/-- Cell-by-cell agreement with the reflex analysis: a configuration
has an overt reflex iff its UA marking is not the default. What
`focus_marking_not_obligatory` states as focus without reflex is,
for UA, the default marking whose focally marked constituent
properly contains the focus. -/
theorem ua_agrees_with_hz_on_overtness (c : Config) :
    (realize c).IsOvert ↔ uaTangale c ≠ ⟨Node.s⟩ := by
  obtain ⟨f, a, t⟩ := c
  cases f <;> cases a <;> cases t <;> decide

end AssmannEtAl2023
