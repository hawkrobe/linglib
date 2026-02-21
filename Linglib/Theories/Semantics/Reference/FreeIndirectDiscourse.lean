import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Free Indirect Discourse (FID) as Mixed Perspective

Free Indirect Discourse is a narrative mode where the narrator's voice and
the character's perspective blend. The hallmark of FID is that different
context coordinates come from different sources:

- **Agent**: narrator (origin) — the narrator is "telling"
- **Time/World/Position**: character (local) — evaluated from the
  character's temporal and spatial perspective

This module formalizes FID as an `FIDProfile`: a per-coordinate depth
specification over the context tower. Classic FID, direct speech, and
indirect speech are all instances of this type, differing only in which
coordinates read from origin vs local.

## Key Definitions

- `FIDProfile`: Per-coordinate depth specification
- `classicFID`: Agent from origin, time/world/position from local
- `directSpeech`: All coordinates from local (full perspective shift)
- `indirectSpeech`: All coordinates from origin (no perspective shift)
- `fid_is_mixed`: FID is neither pure origin nor pure local access

## References

- Banfield, A. (1982). Unspeakable Sentences. Routledge.
- Schlenker, P. (2004). Context of Thought and Context of Utterance.
  *Linguistics & Philosophy*.
- Eckardt, R. (2015). The Semantics of Free Indirect Discourse.
  Brill.
-/

namespace Semantics.Reference.FreeIndirectDiscourse

open Core.Context

-- ════════════════════════════════════════════════════════════════
-- § FID Profile
-- ════════════════════════════════════════════════════════════════

/-- Per-coordinate depth specification for mixed-perspective phenomena.

    Each coordinate of the context (agent, time, world, position) gets
    its own `DepthSpec`, allowing fine-grained control over which tower
    layer each coordinate reads from. -/
structure FIDProfile where
  /-- Which depth to read the agent from -/
  agentDepth : DepthSpec
  /-- Which depth to read the time from -/
  timeDepth : DepthSpec
  /-- Which depth to read the world from -/
  worldDepth : DepthSpec
  /-- Which depth to read the position from -/
  positionDepth : DepthSpec
  deriving DecidableEq, Repr, BEq

namespace FIDProfile

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- Resolve the agent coordinate from the tower according to this profile. -/
def resolveAgent (p : FIDProfile) (t : ContextTower (KContext W E P T)) : E :=
  (t.contextAt (p.agentDepth.resolve t.depth)).agent

/-- Resolve the time coordinate from the tower according to this profile. -/
def resolveTime (p : FIDProfile) (t : ContextTower (KContext W E P T)) : T :=
  (t.contextAt (p.timeDepth.resolve t.depth)).time

/-- Resolve the world coordinate from the tower according to this profile. -/
def resolveWorld (p : FIDProfile) (t : ContextTower (KContext W E P T)) : W :=
  (t.contextAt (p.worldDepth.resolve t.depth)).world

/-- Resolve the position coordinate from the tower according to this profile. -/
def resolvePosition (p : FIDProfile) (t : ContextTower (KContext W E P T)) : P :=
  (t.contextAt (p.positionDepth.resolve t.depth)).position

/-- Resolve all coordinates into a full KContext. -/
def resolve (p : FIDProfile) (t : ContextTower (KContext W E P T)) :
    KContext W E P T :=
  { agent := p.resolveAgent t
  , addressee := (t.contextAt (p.agentDepth.resolve t.depth)).addressee
  , world := p.resolveWorld t
  , time := p.resolveTime t
  , position := p.resolvePosition t }

/-- A profile is uniform iff all coordinates read from the same depth. -/
def isUniform (p : FIDProfile) : Bool :=
  p.agentDepth == p.timeDepth &&
  p.timeDepth == p.worldDepth &&
  p.worldDepth == p.positionDepth

end FIDProfile

-- ════════════════════════════════════════════════════════════════
-- § Standard Profiles
-- ════════════════════════════════════════════════════════════════

/-- Classic FID: narrator's voice (agent from origin) combined with
    character's perspective (time, world, position from local).

    "She was happy now. Tomorrow she would leave."
    - "she" = narrator's third-person reference (agent from origin)
    - "now", "tomorrow" = character's temporal perspective (time from local)
    - The world is the character's belief/experience world -/
def classicFID : FIDProfile :=
  { agentDepth := .origin
  , timeDepth := .local
  , worldDepth := .local
  , positionDepth := .local }

/-- Direct speech: all coordinates from the local (shifted) context.
    The embedded clause is fully evaluated from the reported speaker's
    perspective.

    "John said: 'I am happy here now.'"
    - "I" = John, "here" = John's location, "now" = John's time -/
def directSpeech : FIDProfile :=
  { agentDepth := .local
  , timeDepth := .local
  , worldDepth := .local
  , positionDepth := .local }

/-- Indirect speech: all coordinates from the origin (speech-act context).
    Standard Kaplanian interpretation — no perspective shift.

    "John said that I am happy here now."
    - "I" = actual speaker, "here" = actual location, "now" = actual time -/
def indirectSpeech : FIDProfile :=
  { agentDepth := .origin
  , timeDepth := .origin
  , worldDepth := .origin
  , positionDepth := .origin }

-- ════════════════════════════════════════════════════════════════
-- § Properties
-- ════════════════════════════════════════════════════════════════

/-- Direct speech is uniform: all coordinates read from the same depth. -/
theorem directSpeech_uniform : directSpeech.isUniform = true := rfl

/-- Indirect speech is uniform: all coordinates read from the same depth. -/
theorem indirectSpeech_uniform : indirectSpeech.isUniform = true := rfl

/-- FID is NOT uniform: agent reads from a different depth than time. -/
theorem classicFID_not_uniform : classicFID.isUniform = false := rfl

/-- FID is mixed: it is neither pure origin-access nor pure local-access.
    The agent comes from origin but time comes from local. -/
theorem fid_is_mixed :
    classicFID ≠ directSpeech ∧ classicFID ≠ indirectSpeech := by
  constructor
  · intro h
    have : classicFID.agentDepth = directSpeech.agentDepth := by rw [h]
    simp only [classicFID, directSpeech] at this
    exact absurd this nofun
  · intro h
    have : classicFID.timeDepth = indirectSpeech.timeDepth := by rw [h]
    simp only [classicFID, indirectSpeech] at this
    exact absurd this nofun

/-- In a root tower (no embedding), all three profiles agree: they all
    resolve to the same context. -/
theorem root_all_agree {W E P T : Type*} (c : KContext W E P T) :
    classicFID.resolveAgent (ContextTower.root c) =
    indirectSpeech.resolveAgent (ContextTower.root c) ∧
    classicFID.resolveAgent (ContextTower.root c) =
    directSpeech.resolveAgent (ContextTower.root c) := by
  exact ⟨rfl, rfl⟩

/-- Under a perspective shift, FID's agent differs from direct speech's agent:
    FID reads the narrator (origin), direct speech reads the character (local). -/
theorem fid_vs_direct_agent {W E P T : Type*}
    (c : KContext W E P T) (character : E) (charTime : T) (charWorld : W)
    (hDiff : c.agent ≠ character) :
    let t := (ContextTower.root c).push (perspectiveShift character charTime charWorld)
    classicFID.resolveAgent t ≠ directSpeech.resolveAgent t := by
  simp only [FIDProfile.resolveAgent, classicFID, directSpeech,
    DepthSpec.resolve, ContextTower.push, ContextTower.root,
    ContextTower.contextAt, ContextTower.depth,
    List.take, List.foldl, perspectiveShift]
  exact hDiff

end Semantics.Reference.FreeIndirectDiscourse
