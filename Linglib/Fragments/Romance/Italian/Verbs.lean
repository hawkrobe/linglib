module

public import Linglib.Syntax.Category.Verb.Basic
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
verb's `typers` are the complementizers of the complements it takes, and its frames record the
coding of each complement. Fusco and Sgrizzi's analysis of the *di* and *a* alternation is
`Studies/FuscoSgrizzi2026.lean`; the twelve transitive verbs of Palmieri's Appendix A that also
read reciprocally without *si* are ordinary entries here, and `Italian.Reciprocals` lists them
as the lexical reciprocals.

## Implementation notes

The mood and complementizer facts of the attitude and causative entries are Grano's and Fusco
and Sgrizzi's; the attitude classifications and the non-passivizability of *volere*, *sperare*
and *intendere* are carried over from the earlier entries and are not in those sources.

## References

* [fusco-sgrizzi-2026]
* [grano-2024]
* [palmieri-2024]
-/

@[expose] public section

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

/-- An Italian verb is a verb entry with the clause-typers of the complements it takes. -/
structure Verb extends _root_.Verb where
  /-- The complementizers of the verb's complements; a bare infinitive contributes none. -/
  typers : List Complementizer := []

/-! ### Attitude and causative verbs -/

/-- *convincere* 'convince' takes an infinitive with *di*, which reports a belief and allows
subject or object control, and one with *a*, which reports an intention and allows object
control only. -/
def convincere : Verb where
  form := "convincere"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  opaqueContext := true
  typers := [di, a]

/-- *pensare* 'think' takes an infinitive with *di* or with *a*, with the same difference in
meaning as *convincere*. -/
def pensare : Verb where
  form := "pensare"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  opaqueContext := true
  typers := [di, a]

/-- *volere* 'want' takes a *che* clause in the subjunctive, the indicative being marginal for
some speakers, and a bare infinitive under subject control. -/
def volere : Verb where
  form := "volere"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  typers := [che]

/-- *sperare* 'hope' takes a *che* clause in the subjunctive, the indicative being marginal for
some speakers. -/
def sperare : Verb where
  form := "sperare"
  frames := [ArgumentFrame.subjunctiveClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  typers := [che]

/-- *intendere* 'intend' takes a bare infinitive under subject control and no finite complement,
in either mood; the periphrasis *avere intenzione di* takes the infinitive with *di*. -/
def intendere : Verb where
  form := "intendere"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- The causative *fare* 'make' takes a bare infinitive under object control, and a finite clause
only as *fare sì che* with the subjunctive, never the indicative. -/
def fare : Verb where
  form := "fare"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.subjunctiveClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  causative := some .make
  typers := [che]

/-! ### Transitive verbs with a lexical reciprocal use -/

/-- *abbracciare* 'hug' is transitive and has a lexical reciprocal use. -/
def abbracciare : _root_.Verb where
  form := "abbracciare"
  frames := [ArgumentFrame.np]

/-- *baciare* 'kiss' is transitive and has a lexical reciprocal use. -/
def baciare : _root_.Verb where
  form := "baciare"
  frames := [ArgumentFrame.np]

/-- *coccolare* 'cuddle' is transitive and has a lexical reciprocal use. -/
def coccolare : _root_.Verb where
  form := "coccolare"
  frames := [ArgumentFrame.np]

/-- *conoscere* 'know (of)' is transitive and has a lexical reciprocal use. -/
def conoscere : _root_.Verb where
  form := "conoscere"
  frames := [ArgumentFrame.np]

/-- *consultare* 'consult, confer' is transitive and has a lexical reciprocal use. -/
def consultare : _root_.Verb where
  form := "consultare"
  frames := [ArgumentFrame.np]

/-- *frequentare* 'date' is transitive and has a lexical reciprocal use. -/
def frequentare : _root_.Verb where
  form := "frequentare"
  frames := [ArgumentFrame.np]

/-- *incontrare* 'meet' is transitive and has a lexical reciprocal use. -/
def incontrare : _root_.Verb where
  form := "incontrare"
  frames := [ArgumentFrame.np]

/-- *incrociare* 'cross, run into' is transitive and has a lexical reciprocal use. -/
def incrociare : _root_.Verb where
  form := "incrociare"
  frames := [ArgumentFrame.np]

/-- *lasciare* 'leave, break up with' is transitive and has a lexical reciprocal use. -/
def lasciare : _root_.Verb where
  form := "lasciare"
  frames := [ArgumentFrame.np]

/-- *sposare* 'marry' is transitive and has a lexical reciprocal use. -/
def sposare : _root_.Verb where
  form := "sposare"
  frames := [ArgumentFrame.np]

/-- *trovare* 'find, meet' is transitive and has a lexical reciprocal use. -/
def trovare : _root_.Verb where
  form := "trovare"
  frames := [ArgumentFrame.np]

/-- *vedere* 'see, meet' is transitive and has a lexical reciprocal use. -/
def vedere : _root_.Verb where
  form := "vedere"
  frames := [ArgumentFrame.np]

end Italian.Verbs
