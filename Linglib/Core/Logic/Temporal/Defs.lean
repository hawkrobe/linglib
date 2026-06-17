/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Linglib.Core.Logic.Modal.Defs

/-!
# T × W tense-modal logic: frames, language, and satisfaction

The object language and Kripke semantics of **T × W logic** ([thomason-1984], [von-kutschera-1997]):
linear tense (`G`/`H`) with historical modality (`N` over historical alternatives `∼ₜ`, `box` over all
worlds) on worlds sharing one time order. A `Core` restatement of the
`Semantics.Modality.HistoricalAlternatives` substrate, kept Semantics-free for the metatheory
(soundness; [dimaio-zanardo-1994] definability).

## Main definitions
* `TWFrame` — a T × W frame (linear time + per-time, backward-closed historical equivalence).
* `OForm` — the object language `L`.
* `TWFrame.sat` — the satisfaction relation.
* `OForm.M` — historical possibility `¬N¬` (the Ockhamist `◇`).
-/

namespace Core.Logic.Temporal

universe u v

/-- A **T × W frame** ([thomason-1984], [von-kutschera-1997]): linear time, worlds, and a per-time
    historical-equivalence `sim` that is an equivalence and backward-closed. -/
structure TWFrame (Time : Type u) (World : Type v) [LinearOrder Time] where
  /-- Historical equivalence `∼ₜ`: `sim t w w'` holds iff `w`, `w'` share their history up to `t`. -/
  sim : Time → World → World → Prop
  /-- Each `∼ₜ` is an equivalence relation. -/
  sim_equiv : ∀ t, Equivalence (sim t)
  /-- **Backward closure**: agreement up to `t` implies agreement up to any earlier `t'`. -/
  sim_backward : ∀ {t t' : Time} (w w' : World), t' ≤ t → sim t w w' → sim t' w w'

/-- The object language `L` of T × W logic ([von-kutschera-1997] §1). -/
inductive OForm (Atom : Type*) where
  /-- A sentential constant. -/
  | atom : Atom → OForm Atom
  /-- Negation. -/
  | neg : OForm Atom → OForm Atom
  /-- Conjunction. -/
  | and : OForm Atom → OForm Atom → OForm Atom
  /-- `G` — "it will always be that" (∀ later times, same world). -/
  | G : OForm Atom → OForm Atom
  /-- `H` — "it has always been that" (∀ earlier times, same world). -/
  | H : OForm Atom → OForm Atom
  /-- `N` — historical necessity (∀ `∼ₜ`-alternatives, same time). -/
  | N : OForm Atom → OForm Atom
  /-- `box` — truth in all worlds (von Kutschera's `N₄`). -/
  | box : OForm Atom → OForm Atom
  deriving DecidableEq

namespace TWFrame

variable {Time : Type u} {World : Type v} {Atom : Type*} [LinearOrder Time]

open Core.Logic.Modal (box universalR) in
/-- Satisfaction `V_{t,w}(A)` ([von-kutschera-1997]) relative to an atomic valuation `V`.
    `G`/`H`/`N`/`box` are `Core.Logic.Modal.box` Kripke modalities over, respectively, future
    precedence `<`, past precedence `>`, historical equivalence `sim t`, and the universal
    relation — making the object logic a multimodal Kripke logic by construction. -/
def sat (F : TWFrame Time World) (V : Atom → Time → World → Prop) :
    OForm Atom → Time → World → Prop
  | .atom p,  t, w => V p t w
  | .neg a,   t, w => ¬ F.sat V a t w
  | .and a b, t, w => F.sat V a t w ∧ F.sat V b t w
  | .G a,     t, w => box (· < ·) (fun t' => F.sat V a t' w) t
  | .H a,     t, w => box (· > ·) (fun t' => F.sat V a t' w) t
  | .N a,     t, w => box (F.sim t) (fun w' => F.sat V a t w') w
  | .box a,   t, w => box universalR (fun w' => F.sat V a t w') w

/-- Local entailment in a model: `a` entails `b` iff `b` holds wherever `a` does. -/
def entails (F : TWFrame Time World) (V : Atom → Time → World → Prop) (a b : OForm Atom) : Prop :=
  ∀ t w, F.sat V a t w → F.sat V b t w

end TWFrame

/-! ### Derived (dual) operators -/

variable {Atom : Type*}

/-- Historical possibility `M = ¬N¬` (the Ockhamist `◇`). -/
def OForm.M (a : OForm Atom) : OForm Atom := .neg (.N (.neg a))

/-- Tense `F` — "it will at some point be that" (`¬G¬`). -/
def OForm.Fut (a : OForm Atom) : OForm Atom := .neg (.G (.neg a))

/-- Tense `P` — "it was at some point that" (`¬H¬`). -/
def OForm.Pst (a : OForm Atom) : OForm Atom := .neg (.H (.neg a))

/-- Possibility in all worlds `◇ = ¬□¬`. -/
def OForm.dia (a : OForm Atom) : OForm Atom := .neg (.box (.neg a))

end Core.Logic.Temporal
