import Linglib.Syntax.Voice.System
import Linglib.Syntax.Person.Basic

/-!
# Indonesian voice

Indonesian has three voices projecting transitive clauses. In the subject voice the verb takes
the prefix *meN-*, whose nasal assimilates to the stem, and the agent is the subject, as in
*Tono membeli buku* 'Tono bought a book'. In the object voice the verb is bare, the patient is
the subject and the agent stands immediately before the verb, after negation and the
auxiliaries, as in *Topi ini sudah saya beli* 'I have bought this hat'; the agent is
obligatory and pronominal, *aku* and *kamu* appearing as the bound *ku-* and *kau-*. In the
*di-* voice the patient is the subject and the agent follows the verb, bare or with *oleh*
'by', and may be omitted, as in *Kue ini dimakan (oleh) Arna* 'This cake was eaten by Arna';
its agent is third person, *dia*, *mereka* or a noun, so that the third-person pronouns alone
take both patient-subject voices. The middle *ber-* selects no pivot and is the matter of
`Verbs.lean` and `Studies/BeaversUdayana2022.lean`. Sneddon, Cole, Hermon and Yanti, and
Erlewine, Levin and van Urk describe the three voices, and Creissels reads *di-* two ways: as
a patient voice whose bare postverbal agent remains a core term, which makes the system a
binary symmetrical one, or as a passive whose agent is demoted to the *oleh*-phrase.

## Main definitions

* `Indonesian.subjectVoice`, `objectVoice`, `di` — the three voices, *di-* under a reading
* `Indonesian.DiReading` — Creissels's two readings of *di-*
* `Indonesian.voices` — the inventory under a reading
* `Indonesian.Agent`, `objectVoiceAgents`, `diAgents` — the forms of the agent each
  patient-subject voice takes

## Main results

* `Indonesian.symmetrical_iff` — the system is symmetrical exactly under the patient-voice
  reading of *di-*
* `Indonesian.objectVoiceAgents_inter_diAgents` — the third-person pronouns alone take
  both patient-subject voices
* `Indonesian.objectVoiceAgents_union_diAgents` — every agent has a patient-subject voice

## References

* [cole-hermon-yanti-2008]
* [creissels-2024]
* [erlewine-levin-van-urk-2017]
* [sneddon-1996]
-/

namespace Indonesian

/-- The subject voice *meN-*: the agent is the pivot. -/
def subjectVoice : Voice := Voice.agentVoice.marked [.pref "meN"]

/-- The object voice, the bare verb: the patient is the pivot, the agent a preverbal
pronoun. -/
def objectVoice : Voice := Voice.patientVoice

/-- The two readings of *di-* ([creissels-2024]): a patient voice whose bare postverbal
agent remains a core term, or a passive whose agent is demoted to the *oleh*-phrase. -/
inductive DiReading where
  | patientVoice
  | passive
  deriving DecidableEq, Repr, Fintype

/-- The *di-* voice under a reading: the patient voice or the passive, marked by *di-*. -/
def di : DiReading → Voice
  | .patientVoice => Voice.patientVoice.marked [.pref "di"]
  | .passive => Voice.passive.marked [.pref "di"]

/-- The three voices under a reading of *di-*. -/
def voices (r : DiReading) : Finset Voice := {subjectVoice, objectVoice, di r}

/-- Read as a patient voice, *di-* makes Indonesian a binary symmetrical system; read as a
passive it does not ([creissels-2024]). -/
theorem symmetrical_iff (r : DiReading) : Voice.Symmetrical (voices r) ↔ r = .patientVoice := by
  cases r <;> decide

/-! ### The agent of the patient-subject voices -/

/-- The form of the agent of a transitive clause: a pronoun of a person, a noun, or none. -/
inductive Agent where
  | pronoun (person : Person)
  | noun
  | absent
  deriving DecidableEq, Repr, Fintype

/-- The agent is a pronoun. -/
def Agent.IsPronoun : Agent → Prop
  | .pronoun _ => True
  | _ => False

instance : DecidablePred Agent.IsPronoun := fun a ↦ by
  cases a <;> unfold Agent.IsPronoun <;> infer_instance

/-- The agents the object voice takes: a pronoun of any person, obligatorily. -/
def objectVoiceAgents : Finset Agent := Finset.univ.filter Agent.IsPronoun

/-- The agents the *di-* voice takes: a third-person pronoun, a noun, or none. -/
def diAgents : Finset Agent := {.pronoun .third, .noun, .absent}

/-- The third-person pronouns *dia* and *mereka* alone take both patient-subject voices
([sneddon-1996]). -/
theorem objectVoiceAgents_inter_diAgents :
    objectVoiceAgents ∩ diAgents = {.pronoun .third} := by
  decide

/-- Every agent, expressed or not, has a patient-subject voice. -/
theorem objectVoiceAgents_union_diAgents : objectVoiceAgents ∪ diAgents = Finset.univ := by
  decide

end Indonesian
