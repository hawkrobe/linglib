import Linglib.Core.Context.Tower

/-!
# Standard Context Shifts

Shift constructors for `KContext` that correspond to specific linguistic operations:
attitude embedding, temporal shift, full perspective shift, and the identity (no-op)
shift. Each preserves or changes specific coordinates, with theorems documenting
the preservation pattern.

These are the building blocks for tower-based composition. An attitude verb pushes
`attitudeShift`, a sequence-of-tense embedding pushes `temporalShift`, FID pushes
`perspectiveShift`, and Kaplan-compliant English attitude verbs push `identityShift`.
-/

namespace Core.Context

open Core.Context (KContext)

section KContextShifts

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- Attitude shift: changes agent (to the attitude holder) and world
    (to an attitude-accessible world). Addressee, time, and position
    are preserved.

    Schlenker (2003): "John said that I am happy" — under the monster
    analysis, the attitude verb shifts agent to John. Under Kaplan's
    thesis, English uses `identityShift` instead. -/
def attitudeShift (holder : E) (attWorld : W) : ContextShift (KContext W E P T) where
  apply := λ c => { c with agent := holder, world := attWorld }
  label := .attitude

/-- Temporal shift: changes time only. Used for sequence of tense,
    where embedded tense is evaluated relative to the matrix event time.

    Von Stechow (2009): the attitude verb transmits its event time to
    the embedded clause's perspective time. -/
def temporalShift (newTime : T) : ContextShift (KContext W E P T) where
  apply := λ c => { c with time := newTime }
  label := .temporal

/-- Perspective shift: changes agent, time, and world simultaneously.
    This is the shift for Free Indirect Discourse (FID), where the
    narrative adopts the character's perspective across all coordinates. -/
def perspectiveShift (newAgent : E) (newTime : T) (newWorld : W) :
    ContextShift (KContext W E P T) where
  apply := λ c => { c with agent := newAgent, time := newTime, world := newWorld }
  label := .attitude

/-- Identity shift: no change to the context. Kaplan's thesis for English
    says attitude verbs push identity shifts — embedding happens without
    shifting the context of utterance. -/
def identityShift : ContextShift (KContext W E P T) where
  apply := id
  label := .generic

-- ════════════════════════════════════════════════════════════════
-- § Attitude Shift Preservation
-- ════════════════════════════════════════════════════════════════

@[simp] theorem attitudeShift_preserves_addressee (holder : E) (attWorld : W)
    (c : KContext W E P T) :
    ((attitudeShift holder attWorld).apply c).addressee = c.addressee := rfl

@[simp] theorem attitudeShift_preserves_time (holder : E) (attWorld : W)
    (c : KContext W E P T) :
    ((attitudeShift holder attWorld).apply c).time = c.time := rfl

@[simp] theorem attitudeShift_preserves_position (holder : E) (attWorld : W)
    (c : KContext W E P T) :
    ((attitudeShift holder attWorld).apply c).position = c.position := rfl

@[simp] theorem attitudeShift_changes_agent (holder : E) (attWorld : W)
    (c : KContext W E P T) :
    ((attitudeShift holder attWorld).apply c).agent = holder := rfl

@[simp] theorem attitudeShift_changes_world (holder : E) (attWorld : W)
    (c : KContext W E P T) :
    ((attitudeShift holder attWorld).apply c).world = attWorld := rfl

-- ════════════════════════════════════════════════════════════════
-- § Temporal Shift Preservation
-- ════════════════════════════════════════════════════════════════

@[simp] theorem temporalShift_preserves_agent (newTime : T) (c : KContext W E P T) :
    ((temporalShift newTime).apply c).agent = c.agent := rfl

@[simp] theorem temporalShift_preserves_world (newTime : T) (c : KContext W E P T) :
    ((temporalShift newTime).apply c).world = c.world := rfl

@[simp] theorem temporalShift_preserves_addressee (newTime : T) (c : KContext W E P T) :
    ((temporalShift newTime).apply c).addressee = c.addressee := rfl

@[simp] theorem temporalShift_changes_time (newTime : T) (c : KContext W E P T) :
    ((temporalShift newTime).apply c).time = newTime := rfl

-- ════════════════════════════════════════════════════════════════
-- § Identity Shift
-- ════════════════════════════════════════════════════════════════

@[simp] theorem identityShift_apply (c : KContext W E P T) :
    (identityShift (W := W) (E := E) (P := P) (T := T)).apply c = c := rfl

/-- Pushing an identity shift doesn't change the innermost context. -/
theorem push_identityShift_innermost (t : ContextTower (KContext W E P T)) :
    (t.push identityShift).innermost = t.innermost := by
  rw [ContextTower.push_innermost, identityShift_apply]

-- ════════════════════════════════════════════════════════════════
-- § Perspective Shift Properties
-- ════════════════════════════════════════════════════════════════

@[simp] theorem perspectiveShift_changes_agent (a : E) (t : T) (w : W)
    (c : KContext W E P T) :
    ((perspectiveShift a t w).apply c).agent = a := rfl

@[simp] theorem perspectiveShift_changes_time (a : E) (t : T) (w : W)
    (c : KContext W E P T) :
    ((perspectiveShift a t w).apply c).time = t := rfl

@[simp] theorem perspectiveShift_changes_world (a : E) (t : T) (w : W)
    (c : KContext W E P T) :
    ((perspectiveShift a t w).apply c).world = w := rfl

@[simp] theorem perspectiveShift_preserves_addressee (a : E) (t : T) (w : W)
    (c : KContext W E P T) :
    ((perspectiveShift a t w).apply c).addressee = c.addressee := rfl

@[simp] theorem perspectiveShift_preserves_position (a : E) (t : T) (w : W)
    (c : KContext W E P T) :
    ((perspectiveShift a t w).apply c).position = c.position := rfl

end KContextShifts

end Core.Context
