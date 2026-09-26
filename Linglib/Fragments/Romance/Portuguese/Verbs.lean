module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Portuguese verbs

This file defines two groups of Portuguese verbs. The first are the attitude and causative
verbs of Grano's survey of mood choice with the mood of the finite complement each selects:
*querer* 'want' and *pretender* 'intend' take a *que*-clause in the subjunctive and reject the
indicative, *esperar* 'hope' takes either mood, and the causative *fazer* 'make' takes an
infinitive and, as *fazer com que*, a finite clause in the subjunctive alone; *querer* and
*pretender* also take an infinitive under subject control and *fazer* one under object control.
The second are the transitive verbs of Brazilian Portuguese that Palmieri lists as lexical
reciprocals, *abraçar* 'hug', *beijar* 'kiss', *casar* 'marry', *consultar* 'consult',
*cumprimentar* 'greet', *encontrar* 'meet' and *namorar* 'date', whose reciprocal reading
survives without the clitic *se* in finite clauses and analytic causatives; they are ordinary
transitive entries here, and `Portuguese.Reciprocals` lists them.

## Main definitions

* `Portuguese.Verbs.querer`, `Portuguese.Verbs.esperar`, `Portuguese.Verbs.pretender`,
  `Portuguese.Verbs.fazer`: the mood-selecting verbs.
* `Portuguese.Verbs.abracar` and its siblings: the lexical reciprocals.

## References

* [grano-2024]
* [palmieri-2024]
-/

@[expose] public section

namespace Portuguese.Verbs

open ArgumentStructure

/-! ### Mood choice -/

/-- *querer* 'want' takes a *que*-clause in the subjunctive and an infinitive under subject
control. -/
def querer : Verb where
  form := "querer"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]

/-- *esperar* 'hope' takes a *que*-clause in the subjunctive or in the indicative. -/
def esperar : Verb where
  form := "esperar"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.finiteClause]

/-- *pretender* 'intend' takes an infinitive under subject control and a *que*-clause in the
subjunctive. -/
def pretender : Verb where
  form := "pretender"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.subjunctiveClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]

/-- The causative *fazer* 'make' takes an infinitive under object control and, as *fazer com
que*, a finite clause in the subjunctive. -/
def fazer : Verb where
  form := "fazer"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.subjunctiveClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  causative := some .make

/-! ### Lexical reciprocals -/

/-- *abraçar* 'hug'. -/
def abracar : Verb where
  form := "abraçar"
  frames := [ArgumentFrame.np]

/-- *beijar* 'kiss'. -/
def beijar : Verb where
  form := "beijar"
  frames := [ArgumentFrame.np]

/-- *casar* 'marry'. -/
def casar : Verb where
  form := "casar"
  frames := [ArgumentFrame.np]

/-- *consultar* 'consult, confer'. -/
def consultar : Verb where
  form := "consultar"
  frames := [ArgumentFrame.np]

/-- *cumprimentar* 'greet'. -/
def cumprimentar : Verb where
  form := "cumprimentar"
  frames := [ArgumentFrame.np]

/-- *encontrar* 'meet'. -/
def encontrar : Verb where
  form := "encontrar"
  frames := [ArgumentFrame.np]

/-- *namorar* 'date, be partners'. -/
def namorar : Verb where
  form := "namorar"
  frames := [ArgumentFrame.np]

end Portuguese.Verbs
