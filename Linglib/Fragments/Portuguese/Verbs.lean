module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Portuguese verbs

Attitude and causative verbs with the mood of the finite complement each selects in an
affirmative declarative clause, the Portuguese data of [grano-2024]'s survey of mood choice:
*querer* 'want' and *pretender* 'intend' take the subjunctive and reject the indicative, *esperar*
'hope' takes either, and the causative *fazer* takes *com que* with the subjunctive.

## References

* [grano-2024]
-/

@[expose] public section

namespace Portuguese.Verbs

open ArgumentStructure

/-- *querer* 'want' takes a *que* clause in the subjunctive and an infinitive under subject
control. -/
def querer : Verb where
  form := "querer"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *esperar* 'hope' takes a *que* clause in the subjunctive or in the indicative. -/
def esperar : Verb where
  form := "esperar"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *pretender* 'intend' takes an infinitive under subject control and a *que* clause in the
subjunctive. -/
def pretender : Verb where
  form := "pretender"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.subjunctiveClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- The causative *fazer* 'make' takes an infinitive under object control, and a finite clause
as *fazer com que* with the subjunctive. -/
def fazer : Verb where
  form := "fazer"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.subjunctiveClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  causative := some .make

end Portuguese.Verbs
