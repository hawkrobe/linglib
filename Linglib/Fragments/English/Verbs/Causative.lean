module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English causative verbs

This file defines the English periphrastic causatives *cause*, *make*, *let*, *have*, *get*,
*force* and *prevent*, and the lexical causatives *kill*, *break* and *tear*, with the linking
and the entailment each carries.

## References

* [levin-1993]
* [majid-boster-bowerman-2008]
* [nadathur-lauer-2020]
* [spalek-mcnally-2026]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Causative (Periphrastic) -/

/-- "cause" — counterfactual dependence (necessity semantics) -/
def cause : Verb := .mkRegular {
  form := "cause"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  causative := some .cause
  levinClasses := {LevinClass.engender} }

/-- "make" — the periphrastic causative asserting a direct sufficient guarantee, which Levin
    does not class (the *make* of 26.1 is the verb of creation and that of 29.3 the dub verb). -/
def make : Verb where
  form := "make"
  form3sg := "makes"
  formPast := "made"
  formPastPart := "made"
  formPresPart := "making"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .accomplishment
  causative := some .make
  levinExcluded := {LevinClass.build, .dub}

/-- "let" — permissive causative (barrier removal) -/
def let_ : Verb where
  form := "let"
  form3sg := "lets"
  formPast := "let"
  formPastPart := "let"
  formPresPart := "letting"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .achievement
  causative := some .enable

/-- "have" — causative use (directive causation) -/
def have_caus : Verb where
  form := "have"
  form3sg := "has"
  formPast := "had"
  formPastPart := "had"
  formPresPart := "having"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .achievement
  causative := some .make
  senseTag := .causative

/-- "get" — causative use (persuasive causation), which Levin does not class (the *get* of
    13.5.1 is the verb of obtaining). -/
def get_caus : Verb where
  form := "get"
  form3sg := "gets"
  formPast := "got"
  formPastPart := "gotten"
  formPresPart := "getting"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  causative := some .make
  senseTag := .causative
  levinExcluded := {LevinClass.get}

/-- "force" — coercive causative (overcome resistance) -/
def force : Verb := .mkRegular {
  form := "force"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  projectionBehavior := some .hole
  causative := some .force }

/-- "prevent" — blocking causative (barrier addition).
    "X prevented Y from V-ing" entails the effect did NOT occur
    (¬p in w₀) but would have without X's intervention.
    Its semantics `preventSem` is the blocking dual of the necessity reading
    [nadathur-lauer-2020] give *cause*. -/
def prevent : Verb := .mkRegular {
  form := "prevent"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .objectControl }]
  vendlerClass := some .accomplishment
  projectionBehavior := some .hole
  causative := some .prevent }

/-! ### Lexical Causatives -/

/-- "kill" — Levin 42.1 murder verbs. -/
def kill : Verb := .mkRegular {
  form := "kill"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
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
  causative := some .make
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
  causative := some .make
  root := { content := {
    force := {.moderate, .high}
    direction := {.bidirectional, .unidirectional}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.separation}
    agentControl := {.neutral, .compatible}
    instrument := {.hands}
  } }
  levinClasses := {LevinClass.break_, .run, .split}

end English.Verbs
