import Linglib.Semantics.ArgumentStructure.ArgumentIntroduction
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm
import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Kratzer (1996): Severing the External Argument from its Verb

This file formalizes the paper's proposal that the external argument is not an argument of
the verb. A transitive verb denotes a relation between its internal argument and an event,
and the external argument is introduced by a separate functional head, Voice, whose
denotation is a thematic relation such as Agent. Voice and the verb phrase combine by Event
Identification, which conjoins the two at the event and leaves the introduced participant
open, so that the sentence *Mittie fed the dog* denotes the events that are feedings of the
dog and of which Mittie is the agent. Syntactically the external argument is the specifier of
VoiceP, above the verb phrase that contains the verb and its internal argument.

## Implementation notes

Event Identification and the Voice denotation are the library's `eventIdentification` and
`applToEvent`, and the agentive Voice head is `Voice.agentive`; the derivation is stated for an
arbitrary agent relation and verb. The tree is built from planar leaf tokens, and the paper's
structural claim is its c-command relations.

## References

* [kratzer-1996]
* [marantz-1984] — the asymmetry between internal and external arguments the paper builds on
-/

namespace Kratzer1996

open ArgumentStructure

section Semantics

variable {Entity T : Type*} [LinearOrder T]

/-- The denotation of *Mittie fed the dog*: Voice, denoting the agent relation, combines with
the verb phrase by Event Identification, so the agent enters above the verb. -/
def mittieFedTheDog (agent feed : ThematicRel Entity T) (mittie dog : Entity) :
    Event T → Prop :=
  applToEvent agent (feed dog) mittie

/-- The sentence holds of an event iff Mittie is its agent and it is a feeding of the dog;
the verb contributes no agent. -/
theorem mittieFedTheDog_iff (agent feed : ThematicRel Entity T) (mittie dog : Entity)
    (e : Event T) : mittieFedTheDog agent feed mittie dog e ↔ agent mittie e ∧ feed dog e :=
  Iff.rfl

/-- Severing: two verb phrases with the same events are indistinguishable once Voice adds
the external argument, whatever the agent relation. -/
theorem mittieFedTheDog_congr (agent feed feed' : ThematicRel Entity T) (mittie dog : Entity)
    (h : ∀ e, feed dog e ↔ feed' dog e) (e : Event T) :
    mittieFedTheDog agent feed mittie dog e ↔ mittieFedTheDog agent feed' mittie dog e :=
  and_congr_right λ _ => h e

end Semantics

section Syntax

open Minimalist SyntacticObject

/-- Agentive Voice, subcategorizing for the verb phrase. -/
def voice : LIToken := ⟨.simple .Voice [.v] "Voice", 200⟩

/-- The verbalizer. -/
def little_v : LIToken := ⟨.simple .v [.V] "v", 201⟩

/-- The verb *fed*, subcategorizing for its internal argument. -/
def fed : LIToken := ⟨.simple .V [.D] "fed", 202⟩

/-- The external argument. -/
def mittie : LIToken := ⟨.simple .D [] "Mittie", 203⟩

/-- The internal argument. -/
def theDog : LIToken := ⟨.simple .D [] "the dog", 204⟩

/-- `[VoiceP Mittie [Voice' Voice [vP v [VP fed [DP the dog]]]]]`. -/
def tree : PlanarSyntacticObject := mittie * (voice * (little_v * (fed * theDog)))

/-- The external argument c-commands the internal argument, and not conversely. -/
theorem mittie_cCommands_theDog :
    cCommandsIn tree (leaf mittie) (leaf theDog) ∧
      ¬ cCommandsIn tree (leaf theDog) (leaf mittie) := by
  constructor <;> decide

/-- Voice c-commands the verb phrase, and the external argument c-commands Voice: the
external argument sits above the head that introduces it. -/
theorem voice_between :
    cCommandsIn tree (leaf voice) (leaf fed) ∧ cCommandsIn tree (leaf mittie) (leaf voice) := by
  constructor <;> decide

/-- Agentive Voice assigns the external θ-role. -/
theorem agentive_assignsTheta : Voice.agentive.AssignsTheta := by decide

end Syntax

end Kratzer1996
