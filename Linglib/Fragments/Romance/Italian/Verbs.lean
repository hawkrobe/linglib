module

public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Italian verbs

Italian introduces a finite complement clause with *che* and an infinitival one with the
prepositional complementizers *di* and *a*, or with no complementizer at all, as after *volere*
'want', *intendere* 'intend' and the causative *fare* 'make'. A verb chooses among *di* and
*a*, and some take both with a difference in meaning: *Marco ha convinto Gianni di avere un
figlio* 'Marco has convinced Gianni that he has a child' reports a belief, *Marco ha convinto
Gianni a avere un figlio* 'Marco has convinced Gianni to have a child' an intention, and
*pensare* 'think' alternates the same way. In its finite complement *volere* takes the
subjunctive, *Gianni vuole che Maria sia contenta* 'Gianni wants Maria to be happy', with the
indicative marginal for some speakers, and so does *sperare* 'hope'; *intendere* takes no finite
complement, and *fare* embeds a finite clause only as *fare sì che* with the subjunctive. A
verb's `clauseTypers` are the complementizers of the complements it takes, and its frames record
the coding of each complement. Fusco and Sgrizzi's analysis of the *di* and *a* alternation is
`Studies/FuscoSgrizzi2026.lean`; the twelve transitive verbs of Palmieri's Appendix A that also
read reciprocally without *si* are ordinary entries here, and `Italian.Reciprocals` lists them
as the lexical reciprocals.

An intransitive verb forms its perfect with *essere* when it expresses a change of location, state
or condition, the continuation of a state or existence in a state, and with *avere* when an
activity is in the foreground, whether or not its subject controls it (`Italian.Verbs.perfect`):
*Maria è arrivata* 'Maria has arrived' but *Mario ha tossito* 'Mario has coughed'. *Correre*
'run' takes *essere* with a phrase that brings it to an endpoint, *È corso al campo sportivo in
un'ora* 'he ran to the sports ground in an hour', and *nuotare* 'swim', which selects no such
phrase, keeps *avere*.

## Implementation notes

The mood and complementizer facts of the attitude and causative entries are Grano's and Fusco
and Sgrizzi's; the attitude classifications and the non-passivizability of *volere*, *sperare*
and *intendere* are carried over from the earlier entries and are not in those sources.

## References

* [fusco-sgrizzi-2026]
* [grano-2024]
* [palmieri-2024]
* [maiden-robustelli-2007]
* [sorace-2000]
* [levin-hovav-1995]
-/

@[expose] public section

namespace Italian

/-- An Italian verb is a verb entry with the clause-typers of the complements it takes, which its
frames cannot record, since *di* and *a* both introduce an infinitive. -/
structure Verb extends _root_.Verb where
  /-- The complementizers of the verb's complements; a bare infinitive contributes none. -/
  clauseTypers : List Complementizer := []

/-- The predicate the entry `v` forms with a path phrase of reading `p`. -/
def Verb.withPath (v : Verb) (p : Adposition.SpatialReading) : Verb :=
  { v with toVerb := v.toVerb.withPath p }

@[simp] theorem Verb.toVerb_withPath (v : Verb) (p : Adposition.SpatialReading) :
    (v.withPath p).toVerb = v.toVerb.withPath p := rfl

end Italian

namespace Italian.Verbs

open ArgumentStructure

/-! ### Clause-typers -/

/-- *che* introduces a finite complement clause, indicative or subjunctive. -/
def che : Complementizer where
  morphs := [.free "che"]
  types := .only .declarative

/-- *di* introduces an infinitival complement. -/
def di : Complementizer where
  morphs := [.free "di"]
  coding := some .infinitive

/-- *a* introduces an infinitival complement. -/
def a : Complementizer where
  morphs := [.free "a"]
  coding := some .infinitive

/-! ### Attitude and causative verbs -/

/-- *convincere* 'convince' takes an infinitive with *di*, which reports a belief and allows
subject or object control, and one with *a*, which reports an intention and allows object
control only. -/
def convincere : Verb where
  form := "convincere"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  opaqueContext := true
  clauseTypers := [di, a]

/-- *pensare* 'think' takes an infinitive with *di* or with *a*, with the same difference in
meaning as *convincere*. -/
def pensare : Verb where
  form := "pensare"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  opaqueContext := true
  clauseTypers := [di, a]

/-- *volere* 'want' takes a *che* clause in the subjunctive, the indicative being marginal for
some speakers, and a bare infinitive under subject control. -/
def volere : Verb where
  form := "volere"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  clauseTypers := [che]

/-- *sperare* 'hope' takes a *che* clause in the subjunctive, the indicative being marginal for
some speakers. -/
def sperare : Verb where
  form := "sperare"
  frames := [ArgumentFrame.subjunctiveClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  clauseTypers := [che]

/-- *intendere* 'intend' takes a bare infinitive under subject control and no finite complement,
in either mood; the periphrasis *avere intenzione di* takes the infinitive with *di*. -/
def intendere : Verb where
  form := "intendere"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- The causative *fare* 'make' takes a bare infinitive under object control, and a finite clause
only as *fare sì che* with the subjunctive, never the indicative. -/
def fare : Verb where
  form := "fare"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.subjunctiveClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  clauseTypers := [che]

/-! ### Transitive verbs with a lexical reciprocal use -/

/-- *abbracciare* 'hug' is transitive and has a lexical reciprocal use. -/
def abbracciare : Verb where
  form := "abbracciare"
  frames := [ArgumentFrame.np]

/-- *baciare* 'kiss' is transitive and has a lexical reciprocal use. -/
def baciare : Verb where
  form := "baciare"
  frames := [ArgumentFrame.np]

/-- *coccolare* 'cuddle' is transitive and has a lexical reciprocal use. -/
def coccolare : Verb where
  form := "coccolare"
  frames := [ArgumentFrame.np]

/-- *conoscere* 'know (of)' is transitive and has a lexical reciprocal use. -/
def conoscere : Verb where
  form := "conoscere"
  frames := [ArgumentFrame.np]

/-- *consultare* 'consult, confer' is transitive and has a lexical reciprocal use. -/
def consultare : Verb where
  form := "consultare"
  frames := [ArgumentFrame.np]

/-- *frequentare* 'date' is transitive and has a lexical reciprocal use. -/
def frequentare : Verb where
  form := "frequentare"
  frames := [ArgumentFrame.np]

/-- *incontrare* 'meet' is transitive and has a lexical reciprocal use. -/
def incontrare : Verb where
  form := "incontrare"
  frames := [ArgumentFrame.np]

/-- *incrociare* 'cross, run into' is transitive and has a lexical reciprocal use. -/
def incrociare : Verb where
  form := "incrociare"
  frames := [ArgumentFrame.np]

/-- *lasciare* 'leave, break up with' is transitive and has a lexical reciprocal use. -/
def lasciare : Verb where
  form := "lasciare"
  frames := [ArgumentFrame.np]

/-- *sposare* 'marry' is transitive and has a lexical reciprocal use. -/
def sposare : Verb where
  form := "sposare"
  frames := [ArgumentFrame.np]

/-- *trovare* 'find, meet' is transitive and has a lexical reciprocal use. -/
def trovare : Verb where
  form := "trovare"
  frames := [ArgumentFrame.np]

/-- *vedere* 'see, meet' is transitive and has a lexical reciprocal use. -/
def vedere : Verb where
  form := "vedere"
  frames := [ArgumentFrame.np]

/-! ### Monadic verbs

The monadic verbs of [sorace-2000]'s Italian examples whose auxiliary [maiden-robustelli-2007]
§14.20 states. -/

/-- *venire* 'come', a verb of change of location. -/
def venire : Verb where
  form := "venire"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .achievement
  direction := some .goal

/-- *arrivare* 'arrive', a verb of change of location. -/
def arrivare : Verb where
  form := "arrivare"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .achievement
  direction := some .goal

/-- *cadere* 'fall', a verb of change with a direction ([levin-hovav-1995] p. 147). -/
def cadere : Verb where
  form := "cadere"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .achievement
  direction := some .goal

/-- *salire* 'go up', a change along a scale of height. -/
def salire : Verb where
  form := "salire"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  scaleDimension := some .height

/-- *marcire* 'go off, rot', a verb of change of state. -/
def marcire : Verb where
  form := "marcire"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment

/-- *fiorire* 'bloom', a verb of change of state. -/
def fiorire : Verb where
  form := "fiorire"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .achievement

/-- *rimanere* 'remain', the persistence of a state. -/
def rimanere : Verb where
  form := "rimanere"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .state
  phasal := some .continuation

/-- *durare* 'last', which takes *essere* for the permanence of a state and *avere* where the
duration is in the foreground. -/
def durare : Verb where
  form := "durare"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .state

/-- *esistere* 'exist', existence in a state. -/
def esistere : Verb where
  form := "esistere"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .state

/-- *bastare* 'be enough', existence in a state. -/
def bastare : Verb where
  form := "bastare"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .state

/-- *sembrare* 'seem', a state predicated of the subject. -/
def sembrare : Verb where
  form := "sembrare"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .state

/-- *appartenere* 'belong', which takes *essere* for a state, *L'anello era appartenuto alla regina
Vittoria*, and *avere* where the subject controls it, *Non ho mai appartenuto al PCI*. -/
def appartenere : Verb where
  form := "appartenere"
  frames := [ArgumentFrame.unaccusative]
  vendlerClass := some .state

/-- *lavorare* 'work', an activity whose subject controls it. -/
def lavorare : Verb where
  form := "lavorare"
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  subjectEntailments := some activitySubjectProfile

/-- *chiacchierare* 'chat', an activity whose subject controls it. -/
def chiacchierare : Verb where
  form := "chiacchierare"
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  subjectEntailments := some activitySubjectProfile

/-- *correre* 'run', a verb of manner of motion that selects a directional phrase. -/
def correre : Verb where
  form := "correre"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.spatialPP]
  vendlerClass := some .activity
  direction := some .place

/-- *saltare* 'jump', a verb of manner of motion that selects a directional phrase. -/
def saltare : Verb where
  form := "saltare"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.spatialPP]
  vendlerClass := some .activity
  direction := some .place

/-- *nuotare* 'swim', a verb of manner of motion that selects no directional phrase. -/
def nuotare : Verb where
  form := "nuotare"
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  direction := some .place

/-- *tossire* 'cough', an activity whose subject does not control it. -/
def tossire : Verb where
  form := "tossire"
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .semelfactive

/-- *squillare* 'ring', an activity whose subject does not control it. -/
def squillare : Verb where
  form := "squillare"
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity

/-! ### The perfect auxiliary -/

/-- The auxiliary of the perfect of `v` on the frame `fr` ([maiden-robustelli-2007] §14.20) is
*avere* for a transitive verb; for an intransitive one *essere* when it is a state or expresses a
change, to an endpoint or along a scale, and *avere* when an activity is in the foreground. -/
def perfect (v : Verb) (fr : ArgumentFrame) : PerfectAux :=
  if fr.HasNominal ∧ ¬ fr.IsUnaccusative then .have
  else if v.vendlerClass.any (fun c ↦ c.dynamicity = .stative ∨ c.telicity = .telic) ∨
      v.scaleDimension.isSome then .be
  else .have

/-- The auxiliaries of §14.20 are *essere* for the changes of location *venire*, *arrivare* and
*salire*, the changes of state *cadere*, *marcire* and *fiorire*, the persistence of a state
*rimanere*, and existence in a state *esistere*, *bastare* and *sembrare*; *avere* for *lavorare*,
*nuotare*, *tossire* and *squillare*, activities, and for *correre* with *verso* 'towards', but
*essere* for *correre* with a phrase that brings it to an endpoint, while *nuotare* keeps *avere*.
-/
example :
    [venire, arrivare, salire, cadere, marcire, fiorire, rimanere, esistere, bastare,
      sembrare].map (perfect · .unaccusative) = List.replicate 10 .be ∧
    [lavorare, nuotare, tossire, squillare, correre].map (perfect · .intransitive) =
      List.replicate 5 .have ∧
    perfect (correre.withPath Adposition.into) .intransitive = .be ∧
    perfect (correre.withPath { Adposition.into with shape := some .approximative })
      .intransitive = .have ∧
    perfect (nuotare.withPath Adposition.into) .intransitive = .have := by
  decide

/-- `allVerbs` lists the entries. -/
def allVerbs : List Verb :=
  [convincere, pensare, volere, sperare, intendere, fare,
   abbracciare, baciare, coccolare, conoscere, consultare, frequentare, incontrare, incrociare,
   lasciare, sposare, trovare, vedere,
   venire, arrivare, cadere, salire, marcire, fiorire, rimanere, durare, esistere, bastare,
   sembrare, appartenere, lavorare, chiacchierare, correre, saltare, nuotare, tossire, squillare]

end Italian.Verbs
