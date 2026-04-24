import Linglib.Theories.Semantics.Verb.VerbEntry
import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Theories.Syntax.Minimalism.Movement.Smuggling

/-!
# Verb ↔ Smuggling Interface
@cite{collins-2005} @cite{storment-2026} @cite{kratzer-1996}

Promotes the bridge from `VerbCore`'s lexical fields to the smuggling
operators in `Theories/Syntax/Minimalism/Movement/Smuggling.lean`. These
are general operations on `VerbCore` reused across argument-structure
studies (QI, locative inversion, passives), not study-local helpers.

## Composition

```
VerbCore.derivedUnaccusative  →  VerbCore.voiceFor : VoiceHead
VerbCore.complementType       →  VerbCore.hasComplement : Bool
                                       ↓
                         VerbCore.derivedQI = licensesQI ∘ voiceFor ∘ hasComplement
```

`voiceFor` consults `VerbCore.derivedUnaccusative` (which itself reads
`voiceType.assignsTheta` when present), keeping the chain rooted in the
deeper Voice-as-not-introducing-external-argument characterization rather
than the surface `unaccusative : Bool` annotation.
-/

namespace Core.Verbs

open Minimalism

/-- A verb has a syntactic complement iff its `complementType` is anything
    other than `.none`. Used by smuggling derivations to check that there
    is something to smuggle. -/
def VerbCore.hasComplement (v : VerbCore) : Bool := v.complementType != .none

/-- The Voice head determined by a verb's derived unaccusativity:
    non-thematic (anticausative) for unaccusatives, agentive for unergatives.
    Reads `derivedUnaccusative`, which consults `voiceType.assignsTheta`
    when present, so the bridge is grounded in the Voice-as-not-introducing-
    external-argument characterization (@cite{kratzer-1996}). -/
def VerbCore.voiceFor (v : VerbCore) : VoiceHead :=
  if v.derivedUnaccusative then voiceAnticausative else voiceAgent

/-- Derived prediction: does the verb license quotative inversion?
    Composes `voiceFor` and `hasComplement` through `licensesQI`
    (@cite{storment-2026}, §4: smuggling requires non-phase Voice + a
    complement to smuggle). -/
def VerbCore.derivedQI (v : VerbCore) : Bool :=
  licensesQI v.voiceFor v.hasComplement

/-- A verb licenses QI iff its derived Voice permits smuggling and it
    has a complement to smuggle. Direct unfolding from `licensesQI`'s
    definition. -/
theorem VerbCore.derivedQI_iff (v : VerbCore) :
    v.derivedQI = true ↔ v.voiceFor.permitsSmuggling = true ∧ v.hasComplement = true := by
  unfold VerbCore.derivedQI licensesQI
  simp only [Bool.and_eq_true]

/-- Unaccusative verbs project non-thematic (anticausative) Voice. -/
theorem VerbCore.voiceFor_of_unaccusative (v : VerbCore)
    (h : v.derivedUnaccusative = true) : v.voiceFor = voiceAnticausative := by
  unfold VerbCore.voiceFor; simp [h]

/-- Unergative verbs project agentive Voice. -/
theorem VerbCore.voiceFor_of_unergative (v : VerbCore)
    (h : v.derivedUnaccusative = false) : v.voiceFor = voiceAgent := by
  unfold VerbCore.voiceFor; simp [h]

/-- An unaccusative verb with a complement licenses QI. The two
    independent properties — non-phase Voice and complement availability —
    suffice. -/
theorem VerbCore.derivedQI_of_unaccusative_with_complement (v : VerbCore)
    (hu : v.derivedUnaccusative = true) (hc : v.hasComplement = true) :
    v.derivedQI = true := by
  rw [VerbCore.derivedQI_iff, VerbCore.voiceFor_of_unaccusative v hu]
  exact ⟨nonthematic_permits_smuggling, hc⟩

/-- An unergative verb cannot license QI (regardless of complement),
    because agentive Voice blocks smuggling. -/
theorem VerbCore.derivedQI_blocked_when_unergative (v : VerbCore)
    (hu : v.derivedUnaccusative = false) : v.derivedQI = false := by
  unfold VerbCore.derivedQI
  rw [VerbCore.voiceFor_of_unergative v hu]
  exact agentive_blocks_qi _

end Core.Verbs
