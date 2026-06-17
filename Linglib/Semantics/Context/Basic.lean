import Linglib.Semantics.Intensional.WorldTimeIndex
import Linglib.Semantics.Tense.Reichenbach

/-!
# Kaplanian Context of Utterance
[kaplan-1989] [speas-tenny-2003]

The full context tuple ⟨agent, world, time, position⟩ from [kaplan-1989]
"Demonstratives" §XVIII. Framework-agnostic infrastructure used by reference
theory, tense semantics, mood, and RSA.

The simple `Context W E` (agent + world) in `Reference/Basic.lean` is a
projection; `KContext` is the full Kaplanian structure.

-/

open Time

namespace Semantics.Context

open Intensional (WorldTimeIndex)

/-- Full Kaplanian context of utterance: ⟨agent, world, time, position⟩.

[kaplan-1989] §XVIII: "A context is a tuple ⟨cₐ, cw, ct, cp⟩ where cₐ is
the agent, cw the world, ct the time, and cp the position." -/
structure KContext (W : Type*) (E : Type*) (P : Type*) (T : Type*) where
  /-- The agent (speaker) of the context -/
  agent : E
  /-- The addressee (hearer) of the context -/
  addressee : E
  /-- The world of the context -/
  world : W
  /-- The time of the context -/
  time : T
  /-- The position (location) of the context -/
  position : P

/-- Proper context: the agent exists at the context's world.

[kaplan-1989] §XVIII Remark 3: contexts are proper only if the agent exists
at the world of the context. This validates ⊨ Exist I. -/
def ProperContext {W E P T : Type*} (c : KContext W E P T)
    (exists_ : E → W → Prop) : Prop :=
  exists_ c.agent c.world

/-- Located context: the agent is at the context's position at the context's
time in the context's world.

Validates ⊨ N(Located(I, Here)). -/
def LocatedContext {W E P T : Type*} (c : KContext W E P T)
    (located : E → P → T → W → Prop) : Prop :=
  located c.agent c.position c.time c.world

/-- Project a KContext to a `WorldTimeIndex` (world + time pair). -/
def KContext.toSituation {W E P T : Type*} (c : KContext W E P T) :
    WorldTimeIndex W T :=
  ⟨c.world, c.time⟩

/-- Replace the world and time of a KContext with those of a `WorldTimeIndex`,
    preserving agent / addressee / position. The natural "shift to alternative
    situation" operation: an agent at an evaluation context can hold the same
    centered identity (`agent`) while considering an alternative ⟨world, time⟩.
    Used by centered-world de re semantics to quantify the time-concept across
    a believer's doxastic or metaphysical alternative situations. -/
def KContext.shiftWorldTime {W E P T : Type*} (c : KContext W E P T)
    (s : WorldTimeIndex W T) : KContext W E P T :=
  { c with world := s.world, time := s.time }

@[simp] theorem KContext.shiftWorldTime_world {W E P T : Type*}
    (c : KContext W E P T) (s : WorldTimeIndex W T) :
    (c.shiftWorldTime s).world = s.world := rfl

@[simp] theorem KContext.shiftWorldTime_time {W E P T : Type*}
    (c : KContext W E P T) (s : WorldTimeIndex W T) :
    (c.shiftWorldTime s).time = s.time := rfl

@[simp] theorem KContext.shiftWorldTime_agent {W E P T : Type*}
    (c : KContext W E P T) (s : WorldTimeIndex W T) :
    (c.shiftWorldTime s).agent = c.agent := rfl

@[simp] theorem KContext.shiftWorldTime_toSituation {W E P T : Type*}
    (c : KContext W E P T) (s : WorldTimeIndex W T) :
    (c.shiftWorldTime s).toSituation = s := rfl

/-- Project a KContext into a root-clause ReichenbachFrame.
    Speech time S = context time; perspective time P = S (root clause
    default, [kiparsky-2002]); R and E are supplied per clause. -/
def KContext.toReichenbachFrame {W E P T : Type*}
    (c : KContext W E P T) (R Ev : T) :
    ReichenbachFrame T where
  speechTime := c.time
  perspectiveTime := c.time  -- root clause default: P = S
  referenceTime := R
  eventTime := Ev

end Semantics.Context
