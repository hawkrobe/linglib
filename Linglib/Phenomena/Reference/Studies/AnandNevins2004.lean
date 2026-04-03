import Linglib.Phenomena.Reference.DirectReference
import Linglib.Theories.Semantics.Reference.FreeIndirectDiscourse
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Reference: ContextTower
@cite{anand-nevins-2004} @cite{banfield-1982} @cite{kaplan-1989} @cite{schlenker-2003}

End-to-end derivation chain connecting the ContextTower infrastructure
to the direct reference and indexical shift data in
`Phenomena.Reference.DirectReference`.

## Derivation Chain

```
Core.Context.Tower (ContextTower, push, origin, innermost)
    ↓
Core.Context.Shifts (attitudeShift, perspectiveShift, identityShift)
    ↓
Theories.Semantics.Reference.FreeIndirectDiscourse (FIDProfile)
    ↓
This file: tower operations model Kaplan's thesis and its violations
    ↓
Phenomena.Reference.DirectReference (MonsterThesis, shift languages)
```

## Key Results

1. **Kaplan's thesis = identityShift**: English attitude verbs push identity
   shifts, so embedded indexicals read from origin (speaker's context)
2. **Indexical shift = perspectiveShift**: shift languages (Amharic, Zazaki)
   push perspective shifts, so embedded "I" reads from local (attitude
   holder's context)
3. **FID = mixed access**: Classic FID reads agent from origin (narrator)
   but time/world from local (character) — the hallmark mixed perspective
4. **Direct speech = full local access**: All coordinates from the embedded
   context (full perspective shift)

-/

namespace Phenomena.Reference.Studies.AnandNevins2004

open Core.Context
open Semantics.Reference.FreeIndirectDiscourse

-- ============================================================================
-- § Concrete Context Type
-- ============================================================================

/-- A context with distinguishable agents (for testing identity). -/
inductive Agent where | narrator | character
  deriving DecidableEq, Repr

abbrev RefCtx := KContext Unit Agent Unit ℤ

/-- Speech-act context: narrator speaking at time 0. -/
def speechCtx : RefCtx :=
  { world := (), agent := .narrator, addressee := .character, time := 0, position := () }

/-- Root tower at the speech-act context. -/
def rootTower : ContextTower RefCtx := ContextTower.root speechCtx

-- ============================================================================
-- § Kaplan's Thesis: English = Identity Shift
-- ============================================================================

/-- English attitude verbs push identity shifts (Kaplan's thesis).
    "John said that I am here now" — "I", "here", "now" all refer to
    the speaker, not to John. -/
def englishAttitudeTower : ContextTower RefCtx :=
  rootTower.push identityShift

/-- Under an identity shift, the embedded agent is still the narrator.
    This is Kaplan's thesis: English indexicals are not shifted. -/
theorem english_I_is_narrator :
    englishAttitudeTower.innermost.agent = .narrator := rfl

/-- Under an identity shift, the embedded time is still 0.
    "Now" refers to the speech time, not the attitude time. -/
theorem english_now_is_speech_time :
    englishAttitudeTower.innermost.time = 0 := rfl

/-- Kaplan's thesis holds for English — consistent with `monsterThesis.holdsForEnglish`. -/
theorem kaplan_holds_english :
    DirectReference.monsterThesis.holdsForEnglish = true := rfl

-- ============================================================================
-- § Shift Languages: perspectiveShift
-- ============================================================================

/-- Shift languages (Amharic, Zazaki, etc.) push perspective shifts.
    The attitude verb shifts the agent to the attitude holder and the
    time to the attitude time. -/
def shiftLanguageTower : ContextTower RefCtx :=
  rootTower.push (perspectiveShift .character (-3) ())

/-- Under a perspective shift, the embedded agent is the character.
    "I" in Amharic under an attitude verb refers to the attitude holder. -/
theorem shifted_I_is_character :
    shiftLanguageTower.innermost.agent = .character := rfl

/-- Under a perspective shift, the embedded time is the attitude time.
    "Now" in a shifted language refers to the attitude time, not speech time. -/
theorem shifted_now_is_attitude_time :
    shiftLanguageTower.innermost.time = -3 := rfl

/-- The monster thesis IS challenged cross-linguistically — consistent with
    `monsterThesis.challengedCrossLinguistically`. -/
theorem monsters_exist :
    DirectReference.monsterThesis.challengedCrossLinguistically = true := rfl

-- ============================================================================
-- § FID: Mixed Access (Narrator Agent + Character Time/World)
-- ============================================================================

/-- Classic FID pushes a perspective shift (character's time/world) but
    reads the agent from origin (narrator). The FIDProfile encodes this
    per-coordinate depth specification. -/
def fidTower : ContextTower RefCtx :=
  rootTower.push (perspectiveShift .character (-5) ())

/-- Classic FID profile: agent from origin, everything else from local. -/
def classicFIDProfile : FIDProfile := classicFID

/-- In FID, the agent is the narrator (read from origin). -/
theorem fid_agent_is_narrator :
    classicFIDProfile.resolveAgent fidTower = .narrator := rfl

/-- In FID, the time is the character's (read from local). -/
theorem fid_time_is_character :
    classicFIDProfile.resolveTime fidTower = -5 := rfl

/-- FID is genuinely mixed: agent ≠ what perspectiveShift gives. -/
theorem fid_is_mixed_perspective :
    classicFIDProfile.resolveAgent fidTower ≠
    fidTower.innermost.agent := by decide

-- ============================================================================
-- § Direct vs Indirect Speech Comparison
-- ============================================================================

/-- Indirect speech: all coordinates from origin (Kaplan-compliant). -/
def indirectProfile : FIDProfile := indirectSpeech

/-- Direct speech: all coordinates from local (full shift). -/
def directProfile : FIDProfile := directSpeech

/-- In indirect speech, agent is narrator (from origin). -/
theorem indirect_agent_narrator :
    indirectProfile.resolveAgent fidTower = .narrator := rfl

/-- In direct speech, agent is character (from local). -/
theorem direct_agent_character :
    directProfile.resolveAgent fidTower = .character := rfl

/-- FID agent agrees with indirect speech (both from origin). -/
theorem fid_agent_eq_indirect :
    classicFIDProfile.resolveAgent fidTower =
    indirectProfile.resolveAgent fidTower := rfl

/-- FID time agrees with direct speech (both from local). -/
theorem fid_time_eq_direct :
    classicFIDProfile.resolveTime fidTower =
    directProfile.resolveTime fidTower := rfl

end Phenomena.Reference.Studies.AnandNevins2004
