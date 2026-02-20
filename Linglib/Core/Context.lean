/-
# Kaplanian Context of Utterance

The full context tuple ⟨agent, world, time, position⟩ from Kaplan (1989)
"Demonstratives" §XVIII. Framework-agnostic infrastructure used by reference
theory, tense semantics, mood, and RSA.

The simple `Context W E` (agent + world) in `Reference/Basic.lean` is a
projection; `KContext` is the full Kaplanian structure.

## References

- Kaplan, D. (1989). Demonstratives. In Almog, Perry & Wettstein (eds.),
  Themes from Kaplan. Oxford University Press, §XVIII.
-/

import Linglib.Core.Time
import Linglib.Core.Reichenbach

namespace Core.Context

open Core.Time (Situation)

/-- Full Kaplanian context of utterance: ⟨agent, world, time, position⟩.

Kaplan (1989) §XVIII: "A context is a tuple ⟨cₐ, cw, ct, cp⟩ where cₐ is
the agent, cw the world, ct the time, and cp the position." -/
structure KContext (W : Type*) (E : Type*) (P : Type*) (T : Type*) where
  /-- The agent (speaker) of the context -/
  agent : E
  /-- The addressee (hearer) of the context (Speas & Tenny 2003) -/
  addressee : E
  /-- The world of the context -/
  world : W
  /-- The time of the context -/
  time : T
  /-- The position (location) of the context -/
  position : P

/-- Proper context: the agent exists at the context's world.

Kaplan (1989) §XVIII Remark 3: contexts are proper only if the agent exists
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

/-- Project a KContext to a Situation (world + time pair). -/
def KContext.toSituation {W E P T : Type*} (c : KContext W E P T) :
    Situation W T :=
  ⟨c.world, c.time⟩

/-- Project a KContext into a root-clause ReichenbachFrame.
    Speech time S = context time; perspective time P = S (root clause
    default, Kiparsky 2002); R and E are supplied per clause. -/
def KContext.toReichenbachFrame {W E P T : Type*}
    (c : KContext W E P T) (R Ev : T) :
    Core.Reichenbach.ReichenbachFrame T where
  speechTime := c.time
  perspectiveTime := c.time  -- root clause default: P = S
  referenceTime := R
  eventTime := Ev

end Core.Context
