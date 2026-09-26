module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English communication verbs

This file defines the English verbs of communication, *say*, *tell* and *claim*, and Levin's
manner-of-speaking class, *whisper*, *shout*, *mumble* and the rest, with *speak* and *talk*.

## References

* [bruening-2021]
* [storment-2026]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Communication -/

/-- "say" — communication verb, not factive -/
def say : Verb where
  form := "say"
  form3sg := "says"
  formPast := "said"
  formPastPart := "said"
  formPresPart := "saying"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClasses := {LevinClass.say}

/-- "tell" — communication verb with recipient.
    Also ditransitive ("tell me a story"). Implicit second obj is definite
    ([bruening-2021]: recoverable). Implicit goal (PP) is indefinite. -/
def tell : Verb where
  form := "tell"
  form3sg := "tells"
  formPast := "told"
  formPastPart := "told"
  formPresPart := "telling"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.np_np,
    ⟨some .nominal, [.implicit (some .def), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClasses := {LevinClass.tell, .transferOfMessage}

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : Verb := .mkRegular {
  form := "claim"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClasses := {LevinClass.say} }

/-! ### Manner of Speaking (Levin 37.3) -/

/-! Manner-of-speaking (MoS) verbs specify *how* something is said.
    [storment-2026] shows these divide into two classes:
    - **QI-permitting** (unaccusative): whisper, murmur, mumble, mutter, shout,
      cry, scream, shriek, yell, groan, grumble, hiss, sigh, whimper, snap
    - **Non-QI** (unergative): speak, talk -/

/-- "whisper" — Levin 37.3 Manner of Speaking verbs. -/
def whisper : Verb := .mkRegular {
  form := "whisper"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "murmur" — Levin 37.3 Manner of Speaking verbs. -/
def murmur : Verb := .mkRegular {
  form := "murmur"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission} }

/-- "shout" — Levin 37.3 Manner of Speaking verbs. -/
def shout : Verb := .mkRegular {
  form := "shout"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "cry" — Levin 37.3 Manner of Speaking verbs. -/
def cry : Verb := .mkRegular {
  form := "cry"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .mannerOfSpeaking, .marvel, .nonverbalExpression,
    .soundEmission} }

/-- "scream" — Levin 37.3 Manner of Speaking verbs. -/
def scream : Verb := .mkRegular {
  form := "scream"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking, .soundEmission} }

/-- "mumble" — Levin 37.3 Manner of Speaking verbs. -/
def mumble : Verb := .mkRegular {
  form := "mumble"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "mutter" — Levin 37.3 Manner of Speaking verbs. -/
def mutter : Verb := .mkRegular {
  form := "mutter"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "shriek" — Levin 37.3 Manner of Speaking verbs. -/
def shriek : Verb := .mkRegular {
  form := "shriek"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission} }

/-- "yell" — Levin 37.3 Manner of Speaking verbs. -/
def yell : Verb := .mkRegular {
  form := "yell"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking} }

/-- "groan" — Levin 37.3 Manner of Speaking verbs. -/
def groan : Verb := .mkRegular {
  form := "groan"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .nonverbalExpression, .soundEmission} }

/-- "grumble" — Levin 37.3 Manner of Speaking verbs. -/
def grumble : Verb := .mkRegular {
  form := "grumble"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.complain, .mannerOfSpeaking} }

/-- "hiss" — Levin 37.3 Manner of Speaking verbs. -/
def hiss : Verb := .mkRegular {
  form := "hiss"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking, .soundEmission} }

/-- "sigh" — Levin 40.2 Nonverbal Expression verbs. -/
def sigh : Verb := .mkRegular {
  form := "sigh"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonverbalExpression} }

/-- "whimper" — Levin 37.3 Manner of Speaking verbs. -/
def whimper : Verb := .mkRegular {
  form := "whimper"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking} }

/-- "snap" — Levin 37.3 Manner of Speaking verbs. -/
def snap : Verb := .mkRegular {
  form := "snap"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .break_, .crane, .mannerOfSpeaking, .soundEmission} }

/-- "speak" — agentive communication verb, blocks quotative inversion (unergative)
    Levin 37.5 Talk verbs. -/
def speak : Verb where
  form := "speak"
  form3sg := "speaks"
  formPast := "spoke"
  formPastPart := "spoken"
  formPresPart := "speaking"
  speechActVerb := true
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.talk}

/-- "talk" — agentive communication verb, blocks quotative inversion (unergative)
    Levin 37.5 Talk verbs. -/
def talk : Verb := .mkRegular {
  form := "talk"
  speechActVerb := true
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.talk} }

end English.Verbs
