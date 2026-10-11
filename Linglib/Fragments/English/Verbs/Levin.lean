module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English verbs by Levin class

This file defines the English verbs entered under the smaller of Levin's classes, from putting
and removing through creation, perception, judgment, the body, emission, existence and
appearance, motion and weather, each with the frames Levin's alternations require.

## References

* [levin-1993]
* [degen-tonhauser-2022]
* [majid-boster-bowerman-2008]
* [smith-1997]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Putting (§ 9) -/

/-- "place" — Levin 9.1 Put verbs. Instantaneous placement. -/
def place : Verb := .mkRegular {
  morphs := [.root "place"]
  valency := .ofFrame ArgumentFrame.np_pp
  vendlerClass := some .achievement
  levinClasses := {LevinClass.put} }

/-- "water" — Levin 9.9 Butter verbs (denominal putting). -/
def water : Verb := .mkRegular {
  morphs := [.root "water"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  levinClasses := {LevinClass.butter} }

/-- "pour" — Levin 9.5 Pour verbs. Manner of caused motion. -/
def pour : Verb := .mkRegular {
  morphs := [.root "pour"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.pour, .prepare, .substanceEmission, .weather} }

/-- "spray" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def spray : Verb := .mkRegular {
  morphs := [.root "spray"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.sprayLoad} }

/-- "load" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def load : Verb := .mkRegular {
  morphs := [.root "load"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.sprayLoad} }

/-! ### Removing (§ 10) -/

/-- "remove" — Levin 10.1 Remove verbs. -/
def remove : Verb := .mkRegular {
  morphs := [.root "remove"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.banish, .remove} }

/-- "clean" — Levin 10.3 Clear verbs. Incremental by surface area.
    Also a degree achievement: closed scale (maximally clean). -/
def clean : Verb := .mkRegular {
  morphs := [.root "clean"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .accomplishment
  scaleDimension := some .cleanliness
  incrementality := some .strict
  levinClasses := {LevinClass.clear, .otherChangeOfState, .prepare} }

/-- "steal" — Levin 10.5 Steal verbs. -/
def steal : Verb where
  morphs := [.root "steal"]
  form3sg := "steals"
  formPast := "stole"
  formPastPart := "stolen"
  formPresPart := "stealing"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.appear, .get, .steal}

/-! ### Sending and Carrying (§ 11) -/

/-- "send" — Levin 11.1 Send verbs. Alternates DOC/PP.
    Goal does not entail possession (prospective). Neither object implicit alone. -/
def send : Verb where
  morphs := [.root "send"]
  form3sg := "sends"
  formPast := "sent"
  formPastPart := "sent"
  formPresPart := "sending"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send}

/-- "drive" — Levin 11.5 Drive verbs (vehicle-mediated motion). -/
def drive : Verb where
  morphs := [.root "drive"]
  form3sg := "drives"
  formPast := "drove"
  formPastPart := "driven"
  formPresPart := "driving"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.drive, .nonVehicleName}

/-! ### Change of Possession (§ 13) -/

/-- "donate" — Levin 13.2 Contribute verbs. -/
def donate : Verb := .mkRegular {
  morphs := [.root "donate"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute} }

/-- "obtain" — Levin 13.5.2 Obtain verbs. -/
def obtain : Verb := .mkRegular {
  morphs := [.root "obtain"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.obtain} }

/-- "trade" — Levin 13.6 Exchange verbs. -/
def trade : Verb := .mkRegular {
  morphs := [.root "trade"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.exchange, .give} }

/-! ### Learn, Hold, Conceal (§ 14–16) -/

/-- "learn" — Levin 14 Learn verbs. -/
def learn : Verb := .mkRegular {
  morphs := [.root "learn"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.learn} }

/-- "hold" — Levin 15.1 Hold verbs. Stative. -/
def hold : Verb where
  morphs := [.root "hold"]
  form3sg := "holds"
  formPast := "held"
  formPastPart := "held"
  formPresPart := "holding"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 1, 2])]
  vendlerClass := some .state
  levinClasses := {LevinClass.conjecture, .fit, .hold}

/-- "hide" — Levin 16 Conceal verbs. -/
def hide : Verb where
  morphs := [.root "hide"]
  form3sg := "hides"
  formPast := "hid"
  formPastPart := "hidden"
  formPresPart := "hiding"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conceal}

/-! ### Throwing (§ 17) -/

/-- "throw" — Levin 17.1 Throw verbs. Ballistic motion. Alternates DOC/PP.
    Implicit DO in PP frame only (definite). -/
def throw : Verb where
  morphs := [.root "throw"]
  form3sg := "throws"
  formPast := "threw"
  formPastPart := "thrown"
  formPresPart := "throwing"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (⟨some .nominal, [.implicit (some .def), .adpositional]⟩, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amuse, .throw}

/-! ### Contact (§ 19–20) -/

/-- "poke" — Levin 19 Poke verbs. Punctual contact. -/
def poke : Verb := .mkRegular {
  morphs := [.root "poke"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.poke, .rummage} }

/-- "touch" — Levin 20 Touch verbs. Surface contact. -/
def touch : Verb := .mkRegular {
  morphs := [.root "touch"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amuse, .contiguousLocation, .touch} }

/-! ### Cutting (§ 21) -/

/-- "cut" — Levin 21.1 Cut verbs. Incremental by length of cut.
    [majid-boster-bowerman-2008] place cutting at the predictable end of their first
    dimension, a sharp instrument pressed into a firm but yielding object. -/
def cut : Verb where
  morphs := [.root "cut"]
  form3sg := "cuts"
  formPast := "cut"
  formPastPart := "cut"
  formPresPart := "cutting"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    resultGeometry := {.surfaceBreach}
    instrument := {.sharpBlade}
  } }
  levinClasses := {LevinClass.amuse, .braid, .build, .cut, .hurt, .meander, .split}

/-- "chop" — Levin 21.2 Carve verbs. -/
def chop : Verb where
  morphs := [.root "chop"]
  form3sg := "chops"
  formPast := "chopped"
  formPastPart := "chopped"
  formPresPart := "chopping"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.carve}

/-! ### Combining and Separating (§ 22–23) -/

/-- "mix" — Levin 22.1 Mix verbs. Incremental by proportion combined. -/
def mix : Verb := .mkRegular {
  morphs := [.root "mix"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.correspond, .mix, .prepare} }

/-- "separate" — Levin 23.1 Separate verbs. -/
def separate : Verb := .mkRegular {
  morphs := [.root "separate"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.remove, .separate} }

/-! ### Coloring and Image Creation (§ 24–25) -/

/-- "paint" — Levin 24 Color verbs. Incremental by surface area. -/
def paint : Verb := .mkRegular {
  morphs := [.root "paint"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.characterize, .color, .imageImpression, .performance, .scribble} }

/-- "draw" — Levin 25 Image Creation verbs. Incremental by extent. -/
def draw : Verb where
  morphs := [.root "draw"]
  form3sg := "draws"
  formPast := "drew"
  formPastPart := "drawn"
  formPresPart := "drawing"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.objectDrop (some .indef), [0, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.performance, .pushPull, .remove, .scribble, .split}

/-! ### Creation and Transformation (§ 26) -/

/-- "create" — Levin 26.4 Create verbs. -/
def create : Verb := .mkRegular {
  morphs := [.root "create"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.create, .engender} }

/-- "weave" — Levin 26.1 Build verbs. -/
def weave : Verb where
  morphs := [.root "weave"]
  form3sg := "weaves"
  formPast := "wove"
  formPastPart := "woven"
  formPresPart := "weaving"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.outOf), [0, 1, 3]),
     (ArgumentFrame.np_pp (some Adpositions.into), [0, 3, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.build, .meander}

/-- "grow" — Levin 26.2 Grow verbs. Incremental by size. -/
def grow : Verb where
  morphs := [.root "grow"]
  form3sg := "grows"
  formPast := "grew"
  formPastPart := "grown"
  formPresPart := "growing"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.outOf), [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.into), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.appear, .build, .calibratableChangeOfState,
    .entitySpecificModeOfBeing, .grow, .otherChangeOfState}

/-- "perform" — Levin 26.7 Performance verbs. -/
def perform : Verb := .mkRegular {
  morphs := [.root "perform"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.performance} }

/-! ### Predicative Complements (§ 29) -/

/-- "appoint" — Levin 29.1 Appoint verbs. -/
def appoint : Verb := .mkRegular {
  morphs := [.root "appoint"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appoint} }

/-! ### Perception (§ 30) -/

/-- "hear" — Levin 30.1 See verbs. Stative perception. Also embeds
    finite clauses (optionally factive per [degen-tonhauser-2022]). -/
def hear : Verb where
  morphs := [.root "hear"]
  form3sg := "hears"
  formPast := "heard"
  formPastPart := "heard"
  formPresPart := "hearing"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.finiteClause, [0, 1])]
  vendlerClass := some .state
  levinClasses := {LevinClass.see}

/-! ### Judgment and Assessment (§ 33–34) -/

/-- "blame" — a judgment verb by sense, absent from Levin's §33 member lists
    and named only for the blame alternation (§2.10). -/
def blame : Verb := .mkRegular {
  morphs := [.root "blame"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative
 }

/-- "evaluate" — Levin 34 Assessment verbs. -/
def evaluate : Verb := .mkRegular {
  morphs := [.root "evaluate"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.assessment} }

/-! ### Social Interaction (§ 36) -/

/-- "marry" — Levin 36 Social Interaction verbs. -/
def marry : Verb where
  morphs := [.root "marry"]
  form3sg := "marries"
  formPast := "married"
  formPastPart := "married"
  formPresPart := "marrying"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.objectDrop (some .reciprocal), [0, 1])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amalgamate, .marry}

/-! ### Animal Sounds (§ 38) -/

/-- "bark" — Levin 38 Animal Sound verbs. -/
def bark : Verb := .mkRegular {
  morphs := [.root "bark"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .hurt, .mannerOfSpeaking, .pit} }

/-! ### Body (§ 40–41) -/

/-- "breathe" — Levin 40.1 Body Process verbs. -/
def breathe : Verb := .mkRegular {
  morphs := [.root "breathe"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .entitySpecificModeOfBeing} }

/-- "laugh" — Levin 40.2 Nonverbal Expression verbs. -/
def laugh : Verb := .mkRegular {
  morphs := [.root "laugh"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonverbalExpression} }

/-- "cough" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary event, no result state ([smith-1997] §2.4.3). -/
def cough : Verb := .mkRegular {
  morphs := [.root "cough"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.breathe, .nonverbalExpression} }

/-- "hiccup" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary body event ([smith-1997] §2.4.3). -/
def hiccup : Verb := .mkRegular {
  morphs := [.root "hiccup"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hiccup} }

/-- "blink" — a semelfactive, a single instantaneous eye movement by [smith-1997]'s
    characterization of the class. Levin lists *blink (eye)* among the wink verbs (§40.3.1)
    and *blink* among the light-emission verbs (§43.1); this entry is the eye movement, a
    class the library does not name. -/
def blink : Verb where
  morphs := [.root "blink"]
  form3sg := "blinks"
  formPast := "blinked"
  formPastPart := "blinked"
  formPresPart := "blinking"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .bodyPart), [0, 1])]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.wink}
  levinExcluded := {LevinClass.lightEmission}

/-- "knock" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single percussive contact event, [smith-1997]'s standard
    example of the class. -/
def knock : Verb := .mkRegular {
  morphs := [.root "knock"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hit, .nonAgentiveImpact, .soundEmission, .split, .throw} }

/-- "tap" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single light percussive contact event ([smith-1997] §2.4.3). -/
def tap : Verb := .mkRegular {
  morphs := [.root "tap"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hit, .investigate, .throw} }

/-- "flash" — Levin 43.1 Light Emission verbs.
    Semelfactive: single instantaneous light event, by [smith-1997]'s
    characterization of the class. -/
def flash : Verb := .mkRegular {
  morphs := [.root "flash"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.crane, .lightEmission} }

/-- "flinch" — Levin 40.5 Flinch verbs. Involuntary reaction. -/
def flinch : Verb := .mkRegular {
  morphs := [.root "flinch"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.flinch} }

/-- "dress" — Levin 41.1 Dress verbs. -/
def dress : Verb := .mkRegular {
  morphs := [.root "dress"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.objectDrop (some .reflexive), [0, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.dress, .dressingWell} }

/-! ### Killing (§ 42) -/

/-- "drown" — Levin 42.2 Poison verbs. Manner-of-killing. -/
def drown : Verb := .mkRegular {
  morphs := [.root "drown"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.poison, .suffocate} }

/-! ### Emission (§ 43) -/

/-- "glow" — Levin 43.1 Light Emission verbs. -/
def glow : Verb := .mkRegular {
  morphs := [.root "glow"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.lightEmission} }

/-- "buzz" — Levin 43.2 Sound Emission verbs. -/
def buzz : Verb := .mkRegular {
  morphs := [.root "buzz"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .soundEmission} }

/-- "rumble" — Levin 43.2 Sound Emission verbs. -/
def rumble : Verb := .mkRegular {
  morphs := [.root "rumble"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission} }

/-- "bleed" — Levin 43.4 Substance Emission verbs. -/
def bleed : Verb where
  morphs := [.root "bleed"]
  form3sg := "bleeds"
  formPast := "bled"
  formPastPart := "bled"
  formPresPart := "bleeding"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.pp (some Adpositions.from_), [0, 1])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .cheat, .marvel, .substanceEmission}

/-! ### Existence, Appearance, Position (§ 47–50) -/

/-- "exist" — Levin 47.1 Exist verbs. Pure state. -/
def exist : Verb := .mkRegular {
  morphs := [.root "exist"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.exist, .gorge} }

/-- "appear" — Levin 48.1 Appear verbs. Punctual emergence. -/
def appear : Verb := .mkRegular {
  morphs := [.root "appear"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appear} }

/-- "fidget" — Levin 49 Body-Internal Motion verbs. -/
def fidget : Verb := .mkRegular {
  morphs := [.root "fidget"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.bodyInternalMotion} }

/-- "wiggle" — Levin 47.3 Modes of Being Involving Motion and 49 Body-Internal Motion verbs;
    transitive with a body part or small object ("wiggle a tooth"). -/
def wiggle : Verb := .mkRegular {
  morphs := [.root "wiggle"]
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.np, [1, 0])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.modeOfBeingInvolvingMotion, .bodyInternalMotion, .crane} }

/-- "wriggle" — Levin 49 Body-Internal Motion verbs. -/
def wriggle : Verb := .mkRegular {
  morphs := [.root "wriggle"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.bodyInternalMotion} }

/-- "sit" — Levin 50 Assume Position verbs. Stative. -/
def sit : Verb where
  morphs := [.root "sit"]
  form3sg := "sits"
  formPast := "sat"
  formPastPart := "sat"
  formPresPart := "sitting"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.assumePosition, .putInSpatialConfiguration, .spatialConfiguration}

/-- "stand" — Levin 50 Assume Position verbs. Stative. -/
def stand : Verb where
  morphs := [.root "stand"]
  form3sg := "stands"
  formPast := "stood"
  formPastPart := "stood"
  formPresPart := "standing"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .assumePosition, .putInSpatialConfiguration,
    .spatialConfiguration}

/-! ### Motion (§ 51) -/

/-- "walk" — Levin 51.3 Manner of Motion verbs. -/
def walk : Verb := .mkRegular {
  morphs := [.root "walk"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2])]
    [some activitySubjectProfile, none, none]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  levinClasses := {LevinClass.run} }

/-- "swim" — Levin 51.3 Manner of Motion verbs. -/
def swim : Verb where
  morphs := [.root "swim"]
  form3sg := "swims"
  formPast := "swam"
  formPastPart := "swum"
  formPresPart := "swimming"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2])]
    [some activitySubjectProfile, none, none]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  levinClasses := {LevinClass.run, .swarm, .tingle}

/-- "fly" — Levin 51.4 Vehicle Motion verbs. -/
def fly : Verb where
  morphs := [.root "fly"]
  form3sg := "flies"
  formPast := "flew"
  formPastPart := "flown"
  formPresPart := "flying"
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.drive, .nonVehicleName, .run, .spatialConfiguration}

/-- "roll" — Levin 51.3.1 Roll verbs (manner of motion). -/
def roll : Verb := .mkRegular {
  morphs := [.root "roll"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2])]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  levinClasses := {LevinClass.build, .coil, .crane, .prepare, .roll, .run, .shake, .slide,
    .soundEmission, .split} }

/-- "float" — Levin 51.3.1 Roll verbs (manner of motion). -/
def float : Verb := .mkRegular {
  morphs := [.root "float"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.modeOfBeingInvolvingMotion, .roll, .run, .slide} }

/-! ### Avoid, Linger, Rush (§ 52–53) -/

/-- "avoid" — Levin 52 Avoid verbs. Stative. -/
def avoid : Verb := .mkRegular {
  morphs := [.root "avoid"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.avoid} }

/-- "linger" — Levin 53.1 Linger verbs. -/
def linger : Verb := .mkRegular {
  morphs := [.root "linger"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.exist, .linger} }

/-- "rush" — Levin 53.2 Rush verbs. -/
def rush : Verb := .mkRegular {
  morphs := [.root "rush"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.run, .rush} }

/-! ### Weather (§ 57) -/

/-- "rain" — Levin 57 Weather verbs. Expletive subject. -/
def rain : Verb := .mkRegular {
  morphs := [.root "rain"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.weather} }

end English.Verbs
