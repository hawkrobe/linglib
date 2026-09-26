module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English change-of-state verbs

This file defines the English change-of-state verbs: the physical disturbance verbs of Tham's
study, the further change-of-state verbs of Martin, Rose and Nichols's, Levin's class of
*freeze*, *heat*, *bend*, *boil*, *rust* and *increase*, and the degree achievement pairs of
Kennedy's, *straighten*, *flatten*, *open*, *lengthen*, *widen*, *cool* and *warm*, each with
the frames of its causative and anticausative uses.

## References

* [kennedy-2007]
* [rappaport-hovav-2014]
* [tham-2025]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Physical disturbance change-of-state verbs ([tham-2025]) -/

/-- "crack" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale (contra [rappaport-hovav-2014] two-point
    classification), but allows BOTH telic ("cracked in a minute") and atelic
    ("cracked for two days") readings. Compatible with *completely*, *partially*,
    *badly*. The verb is NOT a standard degree achievement: its variable telicity
    does not reduce to scale boundedness alone. -/
def crack : Verb := .mkRegular {
  form := "crack"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  scaleDimension := some .cracking
  causative := some .make
  levinClasses := {LevinClass.break_, .soundEmission} }

/-- "dent" — Levin 21.2 Carve verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale, compatible with *more dented*, *completely
    dented*, *badly dented*. -/
def dent : Verb := .mkRegular {
  form := "dent"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  scaleDimension := some .denting
  causative := some .make
  levinClasses := {LevinClass.carve} }

/-- "scratch" — Levin 21.1 Cut verbs, a physical disturbance CoS verb for
    [tham-2025]: closed scale, compatible with *more scratched*, *completely
    scratched*, *badly scratched*. Levin also lists it among the wipe verbs
    (§10.4.1) and the swat verbs (§18.2) on its manner readings. -/
def scratch : Verb := .mkRegular {
  form := "scratch"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  scaleDimension := some .scratching
  causative := some .make
  levinClasses := {LevinClass.cut, .hurt, .rummage, .scribble, .swat, .wipeManner} }

/-- "shatter" — Levin 45.1 Break verbs. NOT a physical disturbance verb.
    Punctual, non-gradable: *shatter in two minutes* (after, not duration),
    #*shatter for two minutes*, ??*more shattered* ([tham-2025] (12)). -/
def shatter : Verb := .mkRegular {
  form := "shatter"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  causative := some .make
  levinClasses := {LevinClass.break_} }

/-- "burn" — destruction or transformation by fire or heat; Levin 45.4 other change-of-state
    verbs. -/
def burn : Verb := .mkRegular {
  form := "burn"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  causative := some .make
  root := { content := {
    force := {.moderate, .high}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.totalDestruction, .deformation}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.entitySpecificChangeOfState, .entitySpecificModeOfBeing, .hurt,
    .lightEmission, .otherChangeOfState, .tingle} }

/-- "destroy" — Levin 44 destroy verbs. -/
def destroy : Verb := .mkRegular {
  form := "destroy"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  causative := some .make
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.destroy} }

/-- "melt" — change of consistency by heat; Levin 45.4 other change-of-state verbs. A base
    transitive that takes a double-object benefactive ("melt me some ice cream") and an
    indefinite implicit object ("the ice cream melted" / "we're melting"). -/
def melt : Verb := .mkRegular {
  form := "melt"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef), ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  causative := some .make
  root := { content := {
    force := {.low, .moderate}
    patientRobustness := {.moderate, .robust}
    resultGeometry := {.deformation}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.knead, .otherChangeOfState} }

/-! ### Further change-of-state verbs

The causative verbs Martin, Rose and Nichols survey that have no entry elsewhere in this
file. -/

/-- "activate" — sets a device or process in operation; not listed by Levin. -/
def activate : Verb := .mkRegular {
  form := "activate"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
 }

/-- "affect" — Levin 31.1 amuse verbs. -/
def affect : Verb := .mkRegular {
  form := "affect"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.amuse} }

/-- "change" — transformation; Levin 26.6 turn verbs. -/
def change : Verb := .mkRegular {
  form := "change"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.into),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial) (some Adpositions.from_),
      .adpositional (some .spatial) (some Adpositions.into)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.dress, .exchange, .otherChangeOfState, .turn} }

/-- "damage" — partial destruction; not listed by Levin. -/
def damage : Verb := .mkRegular {
  form := "damage"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "eliminate" — removal; Levin 42.1 murder verbs. -/
def eliminate : Verb := .mkRegular {
  form := "eliminate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.murder, .remove} }

/-- "hurt" — Levin 40.8.3 hurt verbs. -/
def hurt : Verb where
  form := "hurt"
  form3sg := "hurts"
  formPast := "hurt"
  formPastPart := "hurt"
  formPresPart := "hurting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse, .hurt, .marvel, .pain}

/-- "restore" — Levin 13.2 contribute verbs. -/
def restore : Verb := .mkRegular {
  form := "restore"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute} }

/-- "trigger" — sets a process off; not listed by Levin. -/
def trigger : Verb := .mkRegular {
  form := "trigger"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement }

/-- "bury" — covering with earth. Levin's concealment class (§16) does not list *bury*. -/
def bury : Verb := .mkRegular {
  form := "bury"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "drop" — Levin 45.6 calibratable change-of-state verbs. -/
def drop : Verb := .mkRegular {
  form := "drop"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.calibratableChangeOfState, .meander, .putDirection, .roll} }

/-- "lift" — Levin 9.4 verbs of putting with a specified direction. -/
def lift : Verb := .mkRegular {
  form := "lift"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.putDirection, .steal} }

/-- "lock" — securing with a lock; Levin lists *lock* only among the tape verbs (§22.4). -/
def lock : Verb := .mkRegular {
  form := "lock"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.tape} }


/-- "shut" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def shut : Verb where
  form := "shut"
  form3sg := "shuts"
  formPast := "shut"
  formPastPart := "shut"
  formPresPart := "shutting"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.otherChangeOfState}

/-- "spread" — Levin 9.7 spray/load verbs. -/
def spread : Verb where
  form := "spread"
  form3sg := "spreads"
  formPast := "spread"
  formPastPart := "spread"
  formPresPart := "spreading"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative, ArgumentFrame.pp (some Adpositions.at_),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.appear, .entitySpecificModeOfBeing, .sprayLoad}

/-- "stretch" — Levin 45.4 other change-of-state verbs. -/
def stretch : Verb := .mkRegular {
  form := "stretch"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.crane, .meander, .otherChangeOfState} }

/-- "switch" — Levin's change-of-state lists do not include *switch*. -/
def switch : Verb := .mkRegular {
  form := "switch"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
 }

/-- "close" — Levin 45.4 other change-of-state verbs, zero-related to the adjective, and
    40.3.2 crane verbs (*close one's eyes*). -/
def close : Verb := .mkRegular {
  form := "close"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.crane, .otherChangeOfState} }

/-- "dry" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def dry : Verb := .mkRegular {
  form := "dry"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  scaleDimension := some .wetness
  scalePolarity := .negative
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "enhance" — improvement in quality; not listed by Levin. -/
def enhance : Verb := .mkRegular {
  form := "enhance"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment }

/-- "extend" — Levin 47.1 exist verbs, 13.2 contribute verbs and 13.3 verbs of future
    having. -/
def extend : Verb := .mkRegular {
  form := "extend"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute, .exist, .futureHaving} }

/-- "lower" — Levin 9.4 verbs of putting with a specified direction. -/
def lower : Verb := .mkRegular {
  form := "lower"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.putDirection} }

/-- "slow" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def slow : Verb := .mkRegular {
  form := "slow"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .activity
  scaleDimension := some .speed
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "turn" — Levin 26.6 turn verbs (*turn the prince into a frog*). -/
def turn : Verb := .mkRegular {
  form := "turn"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.into)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.turn} }

/-- "wake up" — the particle verb of awakening; Levin lists *waken* but not *wake*. -/
def wakeUp : Verb where
  form := "wake up"
  form3sg := "wakes up"
  formPast := "woke up"
  formPastPart := "woken up"
  formPresPart := "waking up"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .achievement

/-! ### Change of State (§ 45) -/

/-- "freeze" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def freeze : Verb where
  form := "freeze"
  form3sg := "freezes"
  formPast := "froze"
  formPastPart := "frozen"
  formPresPart := "freezing"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClasses := {LevinClass.knead, .otherChangeOfState, .weather}

/-- "heat" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def heat : Verb := .mkRegular {
  form := "heat"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClasses := {LevinClass.cooking, .otherChangeOfState} }

/-- "bend" — Levin 45.2 Bend verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (straight → bent, has maximal endpoint). -/
def bend : Verb where
  form := "bend"
  form3sg := "bends"
  formPast := "bent"
  formPastPart := "bent"
  formPresPart := "bending"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .curvature
  causative := some .make
  levinClasses := {LevinClass.assumePosition, .bend, .knead, .spatialConfiguration}

/-- "boil" — Levin 45.3 Cooking verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (reaches boiling point). -/
def boil : Verb := .mkRegular {
  form := "boil"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .boiling
  causative := some .make
  levinClasses := {LevinClass.cooking} }

/-- "rust" — Levin 45.5 Entity-Specific CoS verbs. Inchoative only.
    Degree achievement: open scale (no maximum rustedness). -/
def rust : Verb := .mkRegular {
  form := "rust"
  frames := [ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .activity
  scaleDimension := some .corrosion
  levinClasses := {LevinClass.entitySpecificChangeOfState, .entitySpecificModeOfBeing} }

/-- "increase" — Levin 45.6 Calibratable CoS verbs (degree achievements).
    Degree achievement: open scale (no maximum quantity). -/
def increase : Verb := .mkRegular {
  form := "increase"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .activity
  scaleDimension := some .quantity
  levinClasses := {LevinClass.calibratableChangeOfState, .otherChangeOfState} }

/-! ### Degree achievement verb pairs ([kennedy-2007]) -/

/-- "straighten" — Closed-scale degree achievement (base adj: straight).
    Accomplishment: "straightened the wire in 10 seconds." -/
def straighten : Verb := .mkRegular {
  form := "straighten"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .straightness
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "flatten" — Closed-scale degree achievement (base adj: flat).
    Accomplishment: "flattened the dough in 2 minutes." -/
def flatten : Verb := .mkRegular {
  form := "flatten"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .flatness
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "open" — Closed-scale degree achievement (base adj: open, closed scale).
    Accomplishment: "opened the door in 3 seconds." -/
def open_ : Verb := .mkRegular {
  form := "open"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .openness
  levinClasses := {LevinClass.appear, .crane, .otherChangeOfState, .spatialConfiguration} }

/-- "lengthen" — Open-scale degree achievement (base adj: long, open scale).
    Activity: "lengthened the rope for hours." -/
def lengthen : Verb := .mkRegular {
  form := "lengthen"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .length
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "widen" — Open-scale degree achievement (base adj: wide, open scale).
    Activity: "widened the road for months." -/
def widen : Verb := .mkRegular {
  form := "widen"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .width
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "cool" — Open-scale degree achievement (base adj: cool, open scale).
    Activity: "cooled for an hour." -/
def cool : Verb := .mkRegular {
  form := "cool"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .temperature
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "warm" — Open-scale degree achievement (base adj: warm, open scale).
    Activity: "warmed for an hour." -/
def warm : Verb := .mkRegular {
  form := "warm"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .temperature
  levinClasses := {LevinClass.otherChangeOfState} }

end English.Verbs
