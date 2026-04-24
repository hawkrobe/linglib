import Linglib.Phenomena.TenseAspect.Studies.HeimKratzer1998Data
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Tense: ContextTower
@cite{abusch-1997} @cite{schlenker-2003} @cite{von-stechow-2009}

End-to-end derivation chain connecting the ContextTower infrastructure
to concrete tense phenomena. The core insight: embedded tense is modeled
as a `temporalShift` on the tower, and the embedded clause's perspective
time is read from the shifted (innermost) context.

## Derivation Chain

```
Core.Context.Tower (ContextTower, push, innermost, origin)
    ↓
Core.Context.Shifts (temporalShift: changes time, preserves agent/world)
    ↓
This file: tower operations produce the Reichenbach frames in HeimKratzer1998Data.lean
    ↓
Phenomena.TenseAspect (matrixSaid, embeddedSickSimultaneous, etc.; data lives in Studies/HeimKratzer1998Data.lean)
```

## Key Results

1. **Root clause = root tower**: `contextAt 0 = origin`, so P = S (speech time)
2. **SOT embedding = temporal shift**: `temporalShift(matrixEventTime)` produces
   the embedded perspective time P' = E_matrix
3. **Double access = origin reading**: present-under-past reads time from `.origin`
   (speech time), not `.local` (matrix event time)
4. **Tower depth = embedding depth**: one attitude verb = depth 1; nested
   attitudes = depth 2+

-/

namespace Abusch1997

open Core.Context
open Phenomena.TenseAspect

-- ============================================================================
-- § Tower-Based Tense Model
-- ============================================================================

/-- A minimal tense context: world, agent, position, and time (as ℤ). -/
abbrev TenseCtx := KContext Unit Unit Unit ℤ

/-- The speech-act context: time = 0 (speech time). -/
def speechCtx : TenseCtx :=
  { world := (), agent := (), addressee := (), time := 0, position := () }

-- ============================================================================
-- § Root Clause = Root Tower
-- ============================================================================

/-- A root clause is a tower with no shifts: depth 0. -/
def rootTower : ContextTower TenseCtx := ContextTower.root speechCtx

/-- In a root tower, the innermost context IS the origin.
    Therefore P = S (perspective time = speech time), which is the
    defining property of root clauses in the Reichenbach framework. -/
theorem root_perspective_eq_speech :
    rootTower.innermost.time = rootTower.origin.time := rfl

/-- Root tower has depth 0. -/
theorem root_depth_zero : rootTower.depth = 0 := rfl

-- ============================================================================
-- § SOT Embedding = Temporal Shift
-- ============================================================================

/-- "John said..." pushes a temporal shift: the matrix event time (-2)
    becomes the embedded clause's perspective time.

    This models @cite{von-stechow-2009}: the attitude verb transmits its event
    time to the embedded clause. -/
def sotTower : ContextTower TenseCtx :=
  rootTower.push (temporalShift (-2))

/-- After the temporal shift, the embedded perspective time is the matrix
    event time (-2), not the speech time (0). This is the SOT mechanism:
    embedded tense is evaluated relative to the matrix event time. -/
theorem sot_perspective_shifted :
    sotTower.innermost.time = -2 := rfl

/-- The temporal shift doesn't change the origin — speech time is still 0.
    This is Kaplan's thesis: the speech-act context is invariant under
    embedding. -/
theorem sot_origin_preserved :
    sotTower.origin.time = 0 := rfl

/-- SOT tower has depth 1 (one embedding). -/
theorem sot_depth_one : sotTower.depth = 1 := rfl

/-- The embedded perspective time (-2) equals the matrix event time in
    `matrixSaid`. This is the end-to-end bridge: tower operation →
    Reichenbach frame. -/
theorem sot_perspective_matches_matrix_event :
    sotTower.innermost.time = matrixSaid.eventTime := rfl

/-- The simultaneous reading: embedded R' = embedded P = matrix E = -2.
    This matches `embeddedSickSimultaneous.perspectiveTime`. -/
theorem simultaneous_perspective_match :
    sotTower.innermost.time = embeddedSickSimultaneous.perspectiveTime := rfl

-- ============================================================================
-- § Double Access = Origin Reading
-- ============================================================================

/-- "John said Mary IS sick" (present-under-past): the present tense in the
    embedded clause reads from the ORIGIN (speech time), not from the shifted
    context. This is the double-access reading: the embedded present anchors
    to speech time despite being under a past matrix verb.

    Tower model: the embedded present uses `DepthSpec.origin` for its
    temporal coordinate, reading time = 0 from the origin. -/
def presentAccess : AccessPattern TenseCtx ℤ :=
  { depth := .origin, project := KContext.time }

/-- Present-under-past reads speech time (0), not matrix event time (-2). -/
theorem double_access_reads_speech_time :
    presentAccess.resolve sotTower = 0 := rfl

/-- The embedded present's time (0) matches the speech time in
    `embeddedSickPresent`. End-to-end: tower origin access → Reichenbach
    frame perspective time. -/
theorem double_access_matches_data :
    presentAccess.resolve sotTower = embeddedSickPresent.speechTime := rfl

-- ============================================================================
-- § Shifted Reading = Local Reading
-- ============================================================================

/-- The shifted reading ("Mary WAS sick before John said so") reads from
    the LOCAL (innermost) context. The embedded past tense evaluates its
    reference time relative to the shifted perspective time. -/
def shiftedAccess : AccessPattern TenseCtx ℤ :=
  { depth := .local, project := KContext.time }

/-- Shifted reading reads matrix event time (-2) from the innermost context. -/
theorem shifted_reads_matrix_time :
    shiftedAccess.resolve sotTower = -2 := rfl

/-- The shifted reading's perspective time matches the embedded frame. -/
theorem shifted_matches_data :
    shiftedAccess.resolve sotTower = embeddedSickShifted.perspectiveTime := rfl

-- ============================================================================
-- § Kaplan's Thesis: Origin Stability
-- ============================================================================

/-- Kaplan's thesis formalized: an origin-accessing expression yields the
    same value regardless of how many shifts are pushed. The speech time
    is invariant under SOT embedding. -/
theorem kaplan_thesis_for_tense :
    presentAccess.resolve sotTower = presentAccess.resolve rootTower := by
  exact presentAccess.origin_stable rfl rootTower (temporalShift (-2))

-- ============================================================================
-- § Nested Embedding = Multiple Shifts
-- ============================================================================

/-- "John said that Mary believed that Bill was sick" — double embedding.
    Two temporal shifts: first to John's saying time (-2), then to Mary's
    believing time (-4). -/
def nestedTower : ContextTower TenseCtx :=
  sotTower.push (temporalShift (-4))

/-- Double embedding has depth 2. -/
theorem nested_depth_two : nestedTower.depth = 2 := rfl

/-- The innermost context in a doubly-embedded clause reads the most deeply
    shifted time (-4). -/
theorem nested_innermost :
    nestedTower.innermost.time = -4 := rfl

/-- Even under double embedding, the origin (speech time) is preserved. -/
theorem nested_origin_preserved :
    nestedTower.origin.time = 0 := rfl

/-- Double access still works at depth 2: present-under-past-under-past
    reads from the origin. -/
theorem nested_double_access :
    presentAccess.resolve nestedTower = 0 := by
  exact presentAccess.origin_stable rfl sotTower (temporalShift (-4))

end Abusch1997
