module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# French verbs

This file defines the French verb entries: the causatives *faire* and *laisser*, the
anticausatives of the causative alternation whose *se* is optional, and the transitive verbs
whose passive agent is marked by *par* or *de*. An entry is a `Verb` with its argument frames
and the proto-role entailments of its arguments in the sense of Dowty. Martin, Schäfer and
Kastner sort the anticausatives by whether a human undergoer typically controls the change,
and Staps and Rooryck group the transitive verbs by the agent preposition they take; both
classifications are the papers' and live in their studies, while the entries here carry the
frames and entailments the classifications are read from. A polysemous verb has one entry per
sense, told apart by its `SenseTag`.

## Main definitions

* `undergoer`, `movingUndergoer`: the entailments of an anticausative's sole argument, without
  and with movement.
* `independentParticipant`, `companionSubject`, `neglectSubject`: the entailments of the
  arguments the transitive entries do not share with a template.
* `allVerbs`: the entries.

## Implementation notes

The citation frame of an anticausative is `ArgumentFrame.unaccusative`, so its sole argument
is the object slot and its entailments are the entry's `objectEntailments`; the transitive
frame of the alternation is the second frame. The entries record no inflectional forms.

## References

* [dowty-1991]
* [martin-schaefer-kastner-2025]
* [staps-rooryck-2024]
* [authier-revuz-1972]
-/

@[expose] public section

namespace French.Verbs

open ArgumentStructure

/-! ### Causatives -/

/-- *faire* 'make', the causative that forms one predicate with its infinitive, as in *faire
lire* 'make read'. -/
def faire : Verb where
  form := "faire"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  causative := some .make

/-- *laisser* 'let', the permissive causative. -/
def laisser : Verb where
  form := "laisser"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  causative := some .enable

/-! ### Anticausatives

The anticausatives with an optional *se* that Martin, Schäfer and Kastner test: the verbs of
their experiment 1a, whose change a human undergoer typically does not control, and the verbs
of their experiment 1b, whose change the undergoer typically controls. -/

/-- The sole argument of an anticausative undergoes the change, is causally affected and
exists independently of the event. It is not entailed to be sentient, as *le mur rougit* 'the
wall reddened' shows, nor to be stationary, which is relative to another participant. -/
def undergoer : EntailmentProfile :=
  { independentExistence := true, changeOfState := true, causallyAffected := true }

/-- The sole argument of an anticausative of motion or posture is an `undergoer` that also
moves. -/
def movingUndergoer : EntailmentProfile := { undergoer with movement := true }

/-- The entry of an anticausative with an optional *se* has the unaccusative frame as its
citation frame and the transitive frame of the alternation after it. -/
def anticausative (form : String) (arg : EntailmentProfile := undergoer) : Verb :=
  { form, frames := [ArgumentFrame.unaccusative, ArgumentFrame.np], objectEntailments := some arg }

/-- *brunir* 'turn brown(er)' ([martin-schaefer-kastner-2025] (31)). -/
def brunir : Verb := anticausative "brunir"

/-- *noircir* 'blacken' ([martin-schaefer-kastner-2025] (31)). -/
def noircir : Verb := anticausative "noircir"

/-- *pâlir* 'get pale' ([martin-schaefer-kastner-2025] (31)). -/
def palir : Verb := anticausative "pâlir"

/-- *rajeunir* 'get young(er)' ([martin-schaefer-kastner-2025] (31)). -/
def rajeunir : Verb := anticausative "rajeunir"

/-- *rougir* 'redden, blush' ([martin-schaefer-kastner-2025] (31)). -/
def rougir : Verb := anticausative "rougir"

/-- *approcher (de)* 'get close(r) to', whose undergoer moves
([martin-schaefer-kastner-2025] (40)). -/
def approcher : Verb := anticausative "approcher" movingUndergoer

/-- *durcir* 'harden' ([martin-schaefer-kastner-2025] (40)). -/
def durcir : Verb := anticausative "durcir"

/-- *plier* 'bend', whose undergoer changes posture ([martin-schaefer-kastner-2025] (40)). -/
def plier : Verb := anticausative "plier" movingUndergoer

/-- *radoucir* 'get soft(er)' ([martin-schaefer-kastner-2025] (40)). -/
def radoucir : Verb := anticausative "radoucir"

/-- *refroidir* 'get cold(er)' ([martin-schaefer-kastner-2025] (40)). -/
def refroidir : Verb := anticausative "refroidir"

/-! ### Transitive verbs

The verbs of Staps and Rooryck's Table 1 and of the sections that follow it, with the
proto-role entailments of their subject and object. The prototypically transitive verbs have
the accomplishment template's profiles, the psych verbs an experiencer subject, and the verbs
of following and accompaniment an object that merely exists independently of the event. -/

/-- An argument entailed only to exist independently of the event, neither agentive nor
affected: the object of a psych verb or of a verb of accompaniment, and the subject of a
stative positional verb. -/
def independentParticipant : EntailmentProfile := { independentExistence := true }

/-- The subject of *accompagner* is sentient and moves but is not entailed to be volitional,
since the accompanying party may merely watch ([staps-rooryck-2024] §3.2). -/
def companionSubject : EntailmentProfile :=
  { sentience := true, movement := true, independentExistence := true }

/-- The subject of the neglect reading of *abandonner* and *délaisser* is volitional and
sentient but brings about no change. -/
def neglectSubject : EntailmentProfile :=
  { volition := true, sentience := true, independentExistence := true }

/-- The entry of a transitive verb with the given subject and object entailments, Vendler
class and sense. -/
def transitive (form : String) (subj obj : EntailmentProfile) (cls : Aspect.VendlerClass)
    (tag : SenseTag := .default) : Verb :=
  { form, frames := [ArgumentFrame.np], subjectEntailments := some subj,
    objectEntailments := some obj, vendlerClass := some cls, senseTag := tag }

/-- *laver* 'wash' ([staps-rooryck-2024] Table 1). -/
def laver : Verb :=
  transitive "laver" accomplishmentSubjectProfile accomplishmentObjectProfile .accomplishment

/-- *briser* 'break' ([staps-rooryck-2024] Table 1). -/
def briser : Verb :=
  transitive "briser" accomplishmentSubjectProfile accomplishmentObjectProfile .achievement

/-- *écrire* 'write', a verb of creation ([staps-rooryck-2024] Table 1). -/
def ecrire : Verb :=
  transitive "écrire" accomplishmentSubjectProfile creationObject .accomplishment

/-- *construire* 'build', a verb of creation ([staps-rooryck-2024] Table 1). -/
def construire : Verb :=
  transitive "construire" accomplishmentSubjectProfile creationObject .accomplishment

/-- *tuer* 'kill', whose object does not survive the event ([staps-rooryck-2024] Table 1). -/
def tuer : Verb :=
  transitive "tuer" accomplishmentSubjectProfile
    { accomplishmentObjectProfile with dependentExistence := true } .achievement

/-- *aimer* 'love', a stative psych verb ([staps-rooryck-2024] Table 1). -/
def aimer : Verb := transitive "aimer" experiencerProfile independentParticipant .state

/-- *adorer* 'adore, worship', a stative psych verb ([staps-rooryck-2024] §3.2). -/
def adorer : Verb := transitive "adorer" experiencerProfile independentParticipant .state

/-- *respecter* 'respect', a stative psych verb ([staps-rooryck-2024] Table 1). -/
def respecter : Verb := transitive "respecter" experiencerProfile independentParticipant .state

/-- *accompagner* 'accompany' ([staps-rooryck-2024] §3.2). -/
def accompagner : Verb :=
  transitive "accompagner" companionSubject independentParticipant .activity

/-- *suivre* 'follow' in its goal-directed sense, with a volitional subject
([staps-rooryck-2024] §3.3). -/
def suivreDyn : Verb :=
  transitive "suivre" activitySubjectProfile independentParticipant .activity

/-- *suivre* 'follow' in its stative positional sense, a purely spatial relation
([staps-rooryck-2024] §3.3). -/
def suivreStat : Verb :=
  transitive "suivre" independentParticipant independentParticipant .state .stative

/-- *précéder* 'precede' in its stative positional sense ([staps-rooryck-2024] §3.3). -/
def preceder : Verb :=
  transitive "précéder" independentParticipant independentParticipant .state

/-- *abandonner* 'abandon' in its telic sense, an event of leaving behind
([staps-rooryck-2024] §3.4, with examples from [authier-revuz-1972]). -/
def abandonner : Verb :=
  transitive "abandonner" accomplishmentSubjectProfile accomplishmentObjectProfile
    .accomplishment

/-- *abandonner* 'neglect' in its atelic stative sense ([staps-rooryck-2024] §3.4, with
examples from [authier-revuz-1972]). -/
def abandonnerStat : Verb :=
  transitive "abandonner" neglectSubject independentParticipant .state .stative

/-- *délaisser* 'leave behind' in its telic sense ([staps-rooryck-2024] §3.4). -/
def delaisser : Verb :=
  transitive "délaisser" accomplishmentSubjectProfile accomplishmentObjectProfile
    .accomplishment

/-- *délaisser* 'neglect' in its atelic stative sense ([staps-rooryck-2024] §3.4). -/
def delaisserStat : Verb :=
  transitive "délaisser" neglectSubject independentParticipant .state .stative

/-- `allVerbs` lists the entries. -/
def allVerbs : List Verb :=
  [faire, laisser,
   brunir, noircir, palir, rajeunir, rougir, approcher, durcir, plier, radoucir, refroidir,
   laver, briser, ecrire, construire, tuer, aimer, adorer, respecter, accompagner,
   suivreDyn, suivreStat, preceder, abandonner, abandonnerStat, delaisser, delaisserStat]

end French.Verbs
