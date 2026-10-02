module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English causative verbs

The English periphrastic causatives are *cause*, *make*, *let*, *have*, *get*, *force* and
*prevent*, and the lexical causatives here are *kill*, *break* and *tear*. Karttunen counts
*cause*, *make*, *have* and *force* among the verbs whose affirmation implies the complement, and
*prevent* among those whose affirmation implies its negation.

## References

* [karttunen-1971]
* [levin-1993]
* [majid-boster-bowerman-2008]
* [spalek-mcnally-2026]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Causative (Periphrastic) -/

/-- *cause* takes an object and an infinitive, *cause the vase to fall*. -/
def cause : Verb := .mkRegular {
  form := "cause"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  implicative := some ⟨some .positive, none⟩
  levinClasses := {LevinClass.engender} }

/-- *make* takes an object and a bare infinitive, *make him leave*. Levin does not class it (the
*make* of 26.1 is the verb of creation and that of 29.3 the dub verb). -/
def make : Verb where
  form := "make"
  form3sg := "makes"
  formPast := "made"
  formPastPart := "made"
  formPresPart := "making"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .accomplishment
  implicative := some ⟨some .positive, none⟩
  levinExcluded := {LevinClass.build, .dub}

/-- *let* is the permissive causative, *let him leave*. -/
def let_ : Verb where
  form := "let"
  form3sg := "lets"
  formPast := "let"
  formPastPart := "let"
  formPresPart := "letting"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .achievement

/-- *have* in its causative use takes an object and a bare infinitive, *have him leave*. -/
def have_caus : Verb where
  form := "have"
  form3sg := "has"
  formPast := "had"
  formPastPart := "had"
  formPresPart := "having"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .achievement
  implicative := some ⟨some .positive, none⟩
  senseTag := .causative

/-- *get* in its causative use takes an object and an infinitive, *get him to leave*. Levin does
not class it (the *get* of 13.5.1 is the verb of obtaining). -/
def get_caus : Verb where
  form := "get"
  form3sg := "gets"
  formPast := "got"
  formPastPart := "gotten"
  formPresPart := "getting"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  senseTag := .causative
  levinExcluded := {LevinClass.get}

/-- *force* takes an object and an infinitive, *force him to leave*. -/
def force : Verb := .mkRegular {
  form := "force"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  implicative := some ⟨some .positive, none⟩ }

/-- *prevent* takes an object and a *from*-gerund, *prevent him from leaving*. -/
def prevent : Verb := .mkRegular {
  form := "prevent"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .objectControl }]
  vendlerClass := some .accomplishment
  implicative := some ⟨some .negative, none⟩ }

/-! ### Lexical Causatives -/

/-- "kill" — Levin 42.1 murder verbs. -/
def kill : Verb := .mkRegular {
  form := "kill"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.murder} }

/-- "break" — Levin 45.1 break verbs, a change in "material integrity" with no specification
    of how the change comes about ([levin-1993]:241). -/
def break_ : Verb where
  form := "break"
  form3sg := "breaks"
  formPast := "broke"
  formPastPart := "broken"
  formPresPart := "breaking"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  root := { content := {
    force := {.moderate, .high}
    -- direction unconstrained: *break* covers snapping (bidirectional),
    -- hammering (omnidirectional), and directed blows (unidirectional)
    patientRobustness := {.moderate, .robust}
    -- English speakers describe both snapping and smashing with *break*
    -- ([majid-boster-bowerman-2008])
    resultGeometry := {.fracture, .fragmentation}
    agentControl := {.incompatible, .neutral}
  } }
  levinClasses := {LevinClass.appear, .break_, .cheat, .hurt, .split}

/-- "tear" — Levin 45.1 Break Verbs. Contrary-direction separation with force.
    Unlike *break*, *tear* implies a specific directionality (bidirectional /
    pulling apart) and is compatible with careful controlled action.
    Patient restriction: any solid capable of irregular separation.
    [spalek-mcnally-2026] (§3.1–3.2).
    In [majid-boster-bowerman-2008] ten of twenty-eight languages have a verb used only for
    tearing cloth by hand, and English speakers extend *tear* to pulling yarn apart. -/
def tear_ : Verb where
  form := "tear"
  form3sg := "tears"
  formPast := "tore"
  formPastPart := "torn"
  formPresPart := "tearing"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.moderate, .high}
    forceDirection := {.bidirectional, .unidirectional}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.separation}
    agentControl := {.neutral, .compatible}
    instrument := {.hands}
  } }
  levinClasses := {LevinClass.break_, .run, .split}

end English.Verbs
