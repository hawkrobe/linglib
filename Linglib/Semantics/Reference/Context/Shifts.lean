/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Reference.Context.Tower

/-!
# Standard context shifts

The shifts of `Context` that embedding operators push: an attitude verb makes the holder the
agent and an accessible world the world (`attitudeShift`, [schlenker-2003]), and a
sequence-of-tense embedding moves the time to the matrix event time (`temporalShift`,
[von-stechow-2009]); a Kaplan-compliant English attitude verb pushes the identity `1`. The
lemmas record which coordinates each shift changes and which it preserves.

## References

* [schlenker-2003]
* [von-stechow-2009]
-/

namespace Reference

variable {W E P T : Type*} (c : Context W E P T)

/-- The attitude shift: the holder becomes the agent and the attitude world the world;
addressee, time and position are preserved. -/
def attitudeShift (holder : E) (attWorld : W) : Function.End (Context W E P T) :=
  λ c => { c with agent := holder, world := attWorld }

/-- The temporal shift: the time moves to `newTime`; every other coordinate is preserved. -/
def temporalShift (newTime : T) : Function.End (Context W E P T) :=
  λ c => { c with time := newTime }

section attitudeShift

variable (holder : E) (attWorld : W)

@[simp] theorem attitudeShift_agent :
    (attitudeShift (P := P) (T := T) holder attWorld c).agent = holder := rfl
@[simp] theorem attitudeShift_world :
    (attitudeShift (P := P) (T := T) holder attWorld c).world = attWorld := rfl
@[simp] theorem attitudeShift_addressee :
    (attitudeShift (P := P) (T := T) holder attWorld c).addressee = c.addressee := rfl
@[simp] theorem attitudeShift_time :
    (attitudeShift (P := P) (T := T) holder attWorld c).time = c.time := rfl
@[simp] theorem attitudeShift_position :
    (attitudeShift (P := P) (T := T) holder attWorld c).position = c.position := rfl

end attitudeShift

section temporalShift

variable (newTime : T)

@[simp] theorem temporalShift_time :
    (temporalShift (W := W) (E := E) (P := P) newTime c).time = newTime := rfl
@[simp] theorem temporalShift_agent :
    (temporalShift (W := W) (E := E) (P := P) newTime c).agent = c.agent := rfl
@[simp] theorem temporalShift_world :
    (temporalShift (W := W) (E := E) (P := P) newTime c).world = c.world := rfl
@[simp] theorem temporalShift_addressee :
    (temporalShift (W := W) (E := E) (P := P) newTime c).addressee = c.addressee := rfl
@[simp] theorem temporalShift_position :
    (temporalShift (W := W) (E := E) (P := P) newTime c).position = c.position := rfl

end temporalShift

end Reference
