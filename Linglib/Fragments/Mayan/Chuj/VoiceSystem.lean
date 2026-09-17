import Linglib.Syntax.Voice.Basic

/-!
# Chuj voice

Chuj (Q'anjob'alan Mayan) forms transitive stems from transitive roots with a null suffix and
intransitive stems from them with three consonantal suffixes ([coon-2019]'s table (58)):
*-ch*, the passive, whose implicit agent may be expressed in an oblique *-uj*-phrase and
licenses agent-oriented adverbs and purpose clauses; *-j*, the agentless passive, with no
thematic agent, an *-uj*-phrase naming a cause of the event; and *-w*, the incorporation
antipassive, whose internal argument is a bare NP that is not a true argument, and which also
forms agentive intransitives from nominal and positional roots. Each stem is built directly
from the root and the suffix rather than derived from another stem, so the alternations are
read from the transitive construction. The decomposition of the attested *-chaj* and *-waj*
into these suffixes and *-aj* is the study's.

## Main definitions

* `Chuj.VoiceSuffix`, `VoiceSuffix.toVoice`: the four suffixes and the voice each forms.

## Main results

* `Chuj.VoiceSuffix.agentFate`: the agent is kept by *-w*, demoted but present under *-ch*,
  and absent under *-j*.

## Implementation notes

The incorporated bare NP of a *-w* stem is entered as an implicit position, the frame
vocabulary having no expressed non-argument.

## References

* [coon-2019]
-/

open Voice

namespace Chuj

/-- The four voice suffixes ([coon-2019]'s table (58)). -/
inductive VoiceSuffix where
  /-- Ø: the transitive stem. -/
  | null
  /-- *-ch*: the passive, with an implicit agent. -/
  | ch
  /-- *-j*: the agentless passive, with no thematic agent. -/
  | j
  /-- *-w*: the incorporation antipassive, and the agentive intransitive of a nominal or
      positional root. -/
  | w
  deriving DecidableEq, Repr

/-- The voice each suffix forms from the transitive construction: Ø the active; *-ch* the
passive, the agent implicit; *-j* the anticausative, the agent suppressed; *-w* the
denucleativization of the object to an incorporated bare NP. All synthetically coded. -/
def VoiceSuffix.toVoice : VoiceSuffix → Voice
  | .null => .active
  | .ch => passive.synthetic
  | .j => anticausative.synthetic
  | .w => { source := .np, target := .objectDrop, coding := .synthetic,
            correspondence := [(.external, .external), (.complement 0, .complement 0)] }

/-- The three intransitivizing suffixes differ in the fate of the agent: kept by *-w*,
demoted but present under *-ch*, absent under *-j* ([coon-2019] §3.2, §4.1). -/
theorem VoiceSuffix.agentFate :
    (toVoice .w).fateOfRole .A = .maintained ∧
      (toVoice .ch).fateOfRole .A = .denucleativized ∧
      (toVoice .j).fateOfRole .A = .suppressed := by
  decide

end Chuj
