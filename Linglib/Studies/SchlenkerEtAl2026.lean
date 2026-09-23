module

public import Linglib.Semantics.Iconicity
public import Linglib.Semantics.Reference.Context.Shifts
public import Linglib.Data.Examples.SchlenkerEtAl2026

/-!
# Schlenker, Lamberton & Lamberton (2026): Traveling Shots in Language

This file formalizes the paper's extension of Iconological Semantics to dynamic viewpoints. In
[schlenker-lamberton-2024] a classifier predicate has an iconic component evaluated by projecting
its argument onto signing space from the viewpoint a variable denotes, and a dynamic classifier,
one that moves in signing space, is projected moment by moment along its movement (27). The
paper's problem is relative motion: in ASL a classifier for a static object, a tree or a pole, can
move past the signer to show the object passing a moving character, the traveling shot of film.
With projection from static viewpoints a still object projects to a still classifier, so such
readings are unavailable (`dynProj_static_eq`); once a viewpoint is a function from times and
worlds to static viewpoints (29), the movement of the classifier is information about the movement
of the viewpoint (`viewpoint_moves_of_dynProj`), the character's path in the elicited paradigms of
`Data/Examples/SchlenkerEtAl2026`.

The paper leaves two analyses open. On Analysis I any viewpoint variable may denote a dynamic
viewpoint. On Analysis II only the context-bound variable `π*`, which denotes the dynamic
viewpoint of the context's agent (33), may, and Role Shift, analyzed as overt context shift (34),
abstracts over the agent, time and world of the context (`roleShift`), so that a role-shifted
classifier is projected from the character's moving viewpoint (`roleShift_dynProj_iff`). Under the
restrictive theory that free variables are static, a traveling shot therefore needs Role Shift
(`restrictive_dynProj_eq`), and under Role Shift the classifier's movement is the character's
(`roleShift_viewpoint_moves`).

## Implementation notes

* The scaling of classifier time to evaluation time in (27) is an arbitrary clock from the
  moments of the movement to times, and projection is any function from an object, a static
  viewpoint, a time and a world to a position in signing space, so the geometry of projection is
  not modeled. An object is still when its projection from any fixed viewpoint does not change
  over time.
* Role Shift (34) is composed from the substrate's attitude and temporal shifts of the context,
  which the paper's context triple identifies with the agent, world and time coordinates.
* The elicited paradigms are recorded as rows with the mean judgment on the seven-point scale;
  the paper's inferences about the character's path from the side on which the classifier passes
  are not modeled, since they require the geometry.

## References

* [schlenker-lamberton-lamberton-2026]
* [schlenker-lamberton-2024]
* [davidson-2015]
-/

@[expose] public section

namespace SchlenkerEtAl2026

open Semantics.Iconic Reference

variable {W E P T S ι : Type*}

/-! ### Projection from dynamic viewpoints (§7) -/

/-- (29): projection from a viewpoint that may move. `proj d v t w` is the position in signing
space to which the object `d` projects from the static viewpoint `v` at `t` in `w`; from a dynamic
viewpoint, `d` projects at `t` in `w` from the viewpoint's value there. -/
def projAt (proj : E → StaticViewpoint P → T → W → S) (d : E) (vp : DynamicViewpoint W T P)
    (t : T) (w : W) : S :=
  proj d (vp w t) t w

/-- (27), (32): an object projects to a dynamic classifier, a function `cl` from the moments of
its movement to positions in signing space, when at each moment, sent to a time of evaluation by
the classifier's clock, the object projects to the classifier's position there. -/
def DynProj (proj : E → StaticViewpoint P → T → W → S) (d : E) (vp : DynamicViewpoint W T P)
    (w : W) (clock : ι → T) (cl : ι → S) : Prop :=
  ∀ i, projAt proj d vp (clock i) w = cl i

/-- An object is still in `w` when its projection from any fixed viewpoint does not change over
time. -/
def IsStill (proj : E → StaticViewpoint P → T → W → S) (d : E) (w : W) : Prop :=
  ∀ (v : StaticViewpoint P) (t t' : T), proj d v t w = proj d v t' w

variable {proj : E → StaticViewpoint P → T → W → S} {d : E} {w : W} {clock : ι → T} {cl : ι → S}

/-- From a static viewpoint a still object projects to a classifier that does not move: the
traveling shot is unavailable in [schlenker-lamberton-2024]. -/
theorem dynProj_static_eq (hd : IsStill proj d w) {v : StaticViewpoint P}
    (h : DynProj proj d (DynamicViewpoint.static v) w clock cl) (i j : ι) : cl i = cl j := by
  rw [← h i, ← h j]
  exact hd v _ _

/-- The traveling shot: when a still object projects to a classifier that moves, the viewpoint
has moved between the two moments. -/
theorem viewpoint_moves_of_dynProj (hd : IsStill proj d w) {vp : DynamicViewpoint W T P}
    (h : DynProj proj d vp w clock cl) {i j : ι} (hij : cl i ≠ cl j) :
    vp w (clock i) ≠ vp w (clock j) := λ heq =>
  hij (by rw [← h i, ← h j, projAt, projAt, heq]; exact hd _ _ _)

/-! ### Viewpoint variables and Role Shift (§8) -/

/-- (33): a free viewpoint variable denotes its value under the assignment `s`; the context-bound
variable `π*` denotes the dynamic viewpoint of the context's agent. -/
def ViewpointVar.denote (s : ℕ → DynamicViewpoint W T P) (agentVP : E → DynamicViewpoint W T P)
    (c : Context W E P T) : ViewpointVar → DynamicViewpoint W T P
  | .free i => s i
  | .contextBound => agentVP c.agent

/-- The restrictive theory of §8: every free viewpoint variable denotes a static viewpoint. -/
def Restrictive (s : ℕ → DynamicViewpoint W T P) : Prop := ∀ i, (s i).isStatic

/-- (34): Role Shift abstracts over the agent, time and world of the context, evaluating its
clause at the shifted context and at that time and world. -/
def roleShift (IP : Context W E P T → T → W → Prop) (c : Context W E P T) (x : E) (t : T)
    (w : W) : Prop :=
  IP (temporalShift t (attitudeShift x w c)) t w

/-- (31), (36): the iconic component of a dynamic classifier with viewpoint variable `π`: its
argument projects to the classifier from the viewpoint `π` denotes, along the clock started at
the time of evaluation. -/
def classifierIcon (s : ℕ → DynamicViewpoint W T P) (agentVP : E → DynamicViewpoint W T P)
    (π : ViewpointVar) (proj : E → StaticViewpoint P → T → W → S) (d : E) (clock : T → ι → T)
    (cl : ι → S) (c : Context W E P T) (t : T) (w : W) : Prop :=
  DynProj proj d (ViewpointVar.denote s agentVP c π) w (clock t) cl

variable {s : ℕ → DynamicViewpoint W T P} {agentVP : E → DynamicViewpoint W T P}
  {clock' : T → ι → T}

/-- (37c): under Role Shift a classifier with the context-bound variable is projected from the
character's dynamic viewpoint at the shifted time and world. -/
theorem roleShift_dynProj_iff (c : Context W E P T) (x : E) (t : T) (w : W) :
    roleShift (classifierIcon s agentVP .contextBound proj d clock' cl) c x t w ↔
      DynProj proj d (agentVP x) w (clock' t) cl := by
  simp [roleShift, classifierIcon, ViewpointVar.denote]

/-- Under the restrictive theory a classifier with a free viewpoint variable cannot show a
still object moving: a traveling shot needs Role Shift. -/
theorem restrictive_dynProj_eq (hs : Restrictive s) (hd : IsStill proj d w)
    (c : Context W E P T) {i : ℕ}
    (h : DynProj proj d (ViewpointVar.denote s agentVP c (.free i)) w clock cl) (j k : ι) :
    cl j = cl k := by
  rw [← h j, ← h k]
  simp only [projAt, ViewpointVar.denote]
  rw [hs i w w (clock j) (clock k)]
  exact hd _ _ _

/-- Under Role Shift the movement of a classifier for a still object is the character's own
movement between the two moments. -/
theorem roleShift_viewpoint_moves (c : Context W E P T) (x : E) (t : T) (hd : IsStill proj d w)
    (h : roleShift (classifierIcon s agentVP .contextBound proj d clock' cl) c x t w) {i j : ι}
    (hij : cl i ≠ cl j) : agentVP x w (clock' t i) ≠ agentVP x w (clock' t j) :=
  viewpoint_moves_of_dynProj hd ((roleShift_dynProj_iff c x t w).1 h) hij

end SchlenkerEtAl2026
