import Linglib.Syntax.Category.Verb.Basic

/-!
# Spanish verbs

Spanish verbs of change of state form their intransitive in one of two ways. Most take the
reflexive clitic, as *quebrar* 'crack' does in *el florero se quebró*; a small class takes none,
as *mejorar* 'improve' does in *los sueldos mejoraron*. A few allow both: *hervir* 'boil' is
usually bare and marginally takes the clitic, and the unaccusatives *caer* 'fall' and *morir*
'die' occur with and without it. Each verb records this marking and whether it has a transitive
causative use. The proto-role entailments of the subject are those Koontz-Garboden discusses
for the causer, and the classification by marking follows Muñoz Pérez.

The verbs with a lexical reciprocal entry beside their transitive use are those of Palmieri's
appendix. They are ordinary verb entries here, and `Spanish.Reciprocals.lexicalReciprocals`
records which of them are lexical reciprocals.

The attitude and causative verbs record the mood of the finite complement each selects in an
affirmative declarative clause, the data of Grano's survey of mood choice; a subjunctive licensed
by matrix negation or a question is not a frame of the verb.

## References

* [A. Koontz-Garboden, *Anticausativization* (2009)][koontz-garboden-2009]
* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
* [C. Muñoz Pérez, *Stylistic applicatives: A lens into the nature of anticausative SE*
  (2026)][munoz-perez-2026]
* [A. A. Spalek and L. McNally, *The anatomy of a verb* (2026)][spalek-mcnally-2026]
* [T. Grano, *Intention Reports and Eventuality Abstraction in a Theory of Mood Choice*
  (2024)][grano-2024]
-/

namespace Spanish.Verbs

open ArgumentStructure

/-! ### Change-of-state verbs -/

/-- How the intransitive of a change-of-state verb is marked. -/
inductive AnticausativeMarking where
  /-- The intransitive takes the reflexive clitic, as *quebrarse*. -/
  | marked
  /-- The intransitive is bare, as *mejorar*. -/
  | unmarked
  /-- The intransitive occurs with and without the clitic, as *caer* and *caerse*. -/
  | optional
  deriving DecidableEq, Repr

/-- A Spanish verb with its behaviour in the causative alternation. -/
structure SpanishVerbEntry extends Verb where
  /-- The marking of the intransitive. -/
  anticausativeMarking : AnticausativeMarking
  /-- The verb has a transitive causative use beside the intransitive. -/
  causativeAlternation : Bool
  deriving BEq

/-- *abrir* 'open', with a marked intransitive *abrirse*. Its causer may be an agent, an
instrument or a natural force ([koontz-garboden-2009]). -/
def abrir : SpanishVerbEntry :=
  { form := "abrir", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *romper* 'break', with a marked intransitive *romperse*. Its causer may be an agent, an
instrument, a natural force or an event ([koontz-garboden-2009]). -/
def romper : SpanishVerbEntry :=
  { form := "romper", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *hundir* 'sink', with a marked intransitive *hundirse*. Its causer is unrestricted
([koontz-garboden-2009]). -/
def hundir : SpanishVerbEntry :=
  { form := "hundir", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *caer* 'fall', an unaccusative that occurs with and without the clitic, *cayó* and *se cayó*
([munoz-perez-2026]). -/
def caer : SpanishVerbEntry :=
  { form := "caer", frames := [ArgumentFrame.unaccusative],
    anticausativeMarking := .optional,
    causativeAlternation := false }

/-- *morir* 'die', an unaccusative that occurs with and without the clitic, *murió* and
*se murió* ([munoz-perez-2026]). -/
def morir : SpanishVerbEntry :=
  { form := "morir", frames := [ArgumentFrame.unaccusative],
    anticausativeMarking := .optional,
    causativeAlternation := false }

/-- *cerrar* 'close', with a marked intransitive *cerrarse*. -/
def cerrar : SpanishVerbEntry :=
  { form := "cerrar", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true }

/-- *quebrar* 'crack', with a marked intransitive, *el florero se quebró* and never
*el florero quebró* ([munoz-perez-2026]). -/
def quebrar : SpanishVerbEntry :=
  { form := "quebrar", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true }

/-- *hervir* 'boil', whose intransitive is usually bare, *el agua hirvió*, and marginally takes
the clitic ([munoz-perez-2026]). -/
def hervir : SpanishVerbEntry :=
  { form := "hervir", frames := [ArgumentFrame.np],
    anticausativeMarking := .optional,
    causativeAlternation := true }

/-- *olvidar* 'forget', whose intransitive *olvidarse* takes a dative experiencer,
*se me olvidó*. -/
def olvidar : SpanishVerbEntry :=
  { form := "olvidar", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true }

/-- *ocurrir* 'occur', whose marked form *ocurrirse* takes a dative experiencer,
*se me ocurrió una idea*. -/
def ocurrir : SpanishVerbEntry :=
  { form := "ocurrir", frames := [ArgumentFrame.unaccusative],
    anticausativeMarking := .marked,
    causativeAlternation := false }

/-- *mejorar* 'improve', with a bare intransitive, *los sueldos mejoraron* and never
*los sueldos se mejoraron* ([munoz-perez-2026]). -/
def mejorar : SpanishVerbEntry :=
  { form := "mejorar", frames := [ArgumentFrame.np],
    anticausativeMarking := .unmarked,
    causativeAlternation := true }

/-- *rasgar* "tear (gash-like)" — Levin 45.1 equivalent; marked anticausative.
    Unlike English *tear*, *rasgar* requires flimsy/insubstantial patients and
    implies unidirectional (linear, gash-like) separation. Incompatible with
    careful controlled action. [spalek-mcnally-2026] (§3.2). -/
def rasgar : SpanishVerbEntry :=
  { form := "rasgar", frames := [ArgumentFrame.np],
    causative := some .make,
    anticausativeMarking := .marked,
    causativeAlternation := true,
    root := { content := {
      force := {.low, .moderate}
      direction := {.unidirectional}
      patientRobustness := {.insubstantial, .flimsy}
      resultGeometry := {.separation, .surfaceBreach}
      agentControl := {.incompatible, .neutral}
    } } }

/-- *asesinar* "assassinate" — AGENT causer required. No anticausative.
    Reflexivization yields reflexive reading only (*El senador se asesinó*
    = 'The senator killed himself'). [koontz-garboden-2009] exx. 24–29. -/
def asesinar : SpanishVerbEntry :=
  { form := "asesinar", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := false,
    subjectEntailments := some accomplishmentSubjectProfile }

/-- *cortar* 'cut', which requires an agent and has no intransitive in that sense
([koontz-garboden-2009]). In the sense 'snap' it has the marked intransitive of
*se cortó la correa* ([munoz-perez-2026]). -/
def cortar : SpanishVerbEntry :=
  { form := "cortar", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := false,
    subjectEntailments := some accomplishmentSubjectProfile }

/-- *ahogar* "drown" — EFFECTOR causer, but animate theme undergoers
    are typical. Alternates: *ahogarse* is a derived inchoative.
    [koontz-garboden-2009] exx. 50–52. -/
def ahogar : SpanishVerbEntry :=
  { form := "ahogar", frames := [ArgumentFrame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *empeorar* "worsen" — internally caused COS verb. No CAUSE in LSR.
    Rejects *por sí solo*. [koontz-garboden-2009] ex. 65a. -/
def empeorar : SpanishVerbEntry :=
  { form := "empeorar", frames := [ArgumentFrame.np],
    anticausativeMarking := .unmarked,
    causativeAlternation := true }

/-- *crecer* "grow" — internally caused COS verb. No CAUSE in LSR.
    Rejects *por sí solo*. [koontz-garboden-2009] ex. 65c. -/
def crecer : SpanishVerbEntry :=
  { form := "crecer", frames := [ArgumentFrame.unaccusative],
    anticausativeMarking := .unmarked,
    causativeAlternation := false }

/-- The verbs of the fragment. -/
def allVerbs : List SpanishVerbEntry :=
  [abrir, romper, hundir, caer, morir, cerrar, quebrar, hervir, olvidar, ocurrir, mejorar, rasgar,
    asesinar, cortar, ahogar, empeorar, crecer]

/-! ### Verbs with a lexical reciprocal entry -/

/-- *abrazar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abrazar : Verb where
  form := "abrazar"
  frames := [ArgumentFrame.np]

/-- *acurrucar* 'cuddle' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def acurrucar : Verb where
  form := "acurrucar"
  frames := [ArgumentFrame.np]

/-- *besar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def besar : Verb where
  form := "besar"
  frames := [ArgumentFrame.np]

/-- *casar* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def casar : Verb where
  form := "casar"
  frames := [ArgumentFrame.np]

/-- *consultar* 'consult/confer' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def consultar : Verb where
  form := "consultar"
  frames := [ArgumentFrame.np]

/-- *cruzar* 'run into, meet accidentally' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def cruzar : Verb where
  form := "cruzar"
  frames := [ArgumentFrame.np]

/-- *dejar* 'leave/break up' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def dejar : Verb where
  form := "dejar"
  frames := [ArgumentFrame.np]

/-- *encontrar* 'find/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def encontrar : Verb where
  form := "encontrar"
  frames := [ArgumentFrame.np]

/-! ### Attitude and causative verbs -/

/-- *querer* 'want' takes a *que* clause in the subjunctive, with disjoint reference, and an
infinitive under subject control. -/
def querer : Verb where
  form := "querer"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *esperar* 'hope' takes a *que* clause in the subjunctive and an infinitive under subject
control. With an indicative clause about the future the verb means 'expect', a sense this entry
does not cover. -/
def esperar : Verb where
  form := "esperar"
  frames := [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- The causative *hacer* 'make' takes an infinitive under object control and a *que* clause in
the subjunctive. -/
def hacer : Verb where
  form := "hacer"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.subjunctiveClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  causative := some .make

/-- *convencer* 'convince' takes an object and a *de que* clause, which reports an intention in
the subjunctive and a belief in the indicative. -/
def convencer : Verb where
  form := "convencer"
  frames :=
    [⟨some .nominal, [.nominal, .clausal (some .subjunctive) (some .declarative)]⟩,
     ⟨some .nominal, [.nominal, .clausal (some .indicative) (some .declarative)]⟩]
  opaqueContext := true

end Spanish.Verbs
