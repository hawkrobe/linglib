module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English aspectual verbs

This file defines the English aspectual verbs *stop*, *quit*, *start*, *begin*, *continue* and
*keep*, which take a complement denoting the event whose phase they assert and presuppose the
adjacent phase.

## References

* [levin-1993]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Change of State -/

/-- "stop" — phasal cessation, presupposes activity was happening -/
def stop : Verb where
  form := "stop"
  form3sg := "stops"
  formPast := "stopped"
  formPastPart := "stopped"
  formPresPart := "stopping"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  phasal := some .cessation
  levinClasses := {LevinClass.begin, .lodge}

/-- "quit" — phasal cessation -/
def quit : Verb where
  form := "quit"
  form3sg := "quits"
  formPast := "quit"
  formPastPart := "quit"
  formPresPart := "quitting"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .cessation
  levinClasses := {LevinClass.complete}

/-- "start" — phasal inception, presupposes activity wasn't happening -/
def start : Verb := .mkRegular {
  form := "start"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception
  levinClasses := {LevinClass.begin} }

/-- "begin" — phasal inception -/
def begin_ : Verb where
  form := "begin"
  form3sg := "begins"
  formPast := "began"
  formPastPart := "begun"
  formPresPart := "beginning"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception
  levinClasses := {LevinClass.begin}

/-- "continue" — phasal continuation, presupposes activity was happening -/
def continue_ : Verb := .mkRegular {
  form := "continue"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation
  levinClasses := {LevinClass.begin} }

/-- "keep" — phasal continuation -/
def keep : Verb where
  form := "keep"
  form3sg := "keeps"
  formPast := "kept"
  formPastPart := "kept"
  formPresPart := "keeping"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation
  levinClasses := {LevinClass.begin, .get, .keep}

end English.Verbs
