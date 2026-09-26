module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English implicative and control verbs

This file defines the English implicative verbs *manage*, *fail*, *try*, *remember*, *forget*
and *neglect*, the control verbs *persuade* and *promise*, the raising verb *seem*, and the
prerequisite implicatives *dare*, *bother*, *hesitate*, *venture*, *condescend* and *happen*,
with the entailment each carries from its complement.

## References

* [karttunen-1971]
* [landau-2015]
* [solstad-bott-2024]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Implicative / Control -/

/-- "manage" — a positive implicative; "managed to VP" entails "VP", and on the traditional
    analysis the agentive subject controls the complement.
    -/
def manage : Verb := .mkRegular {
  form := "manage"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  implicative := some .positive }

/-- "fail" — a negative implicative; "failed to VP" entails "not VP". -/
def fail : Verb := .mkRegular {
  form := "fail"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .negative }

/-- "try" — subject control, no entailment -/
def try_ : Verb where
  form := "try"
  form3sg := "tries"
  formPast := "tried"
  formPastPart := "tried"
  formPresPart := "trying"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.amuse}

/-- "persuade" — object control, "persuade X to VP" with X the agent of VP. A psychological
    attitude verb whose object comes to form an intention; it projects the AUTHOR coordinate,
    so control is obligatorily *de se* ([landau-2015] table (36)). -/
def persuade : Verb := .mkRegular {
  form := "persuade"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "promise" — subject control across an object, "promise X to VP". A desiderative attitude
    verb whose subject commits to a future action; [landau-2015] (5c) classifies it as
    desiderative, hence logophoric control. -/
def promise : Verb := .mkRegular {
  form := "promise"
  frames := [ArgumentFrame.infinitival,
    ArgumentFrame.np_np, ArgumentFrame.np_pp (some Adpositions.to_)]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.futureHaving} }

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : Verb := .mkRegular {
  form := "remember"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive
  levinClasses := {LevinClass.characterize} }

/-- "forget" — negative implicative with infinitival -/
def forget : Verb where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .negative

/-- "neglect" — negative implicative, listed with *forget* and *fail* among
    [karttunen-1971]'s negative implicatives: neglecting to lock the door
    entails not locking it. -/
def neglect : Verb := .mkRegular {
  form := "neglect"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .negative }

/-! ### Raising -/

/-- "seem" — raising verb (no theta role for subject, unaccusative) -/
def seem : Verb := .mkRegular {
  form := "seem"
  frames := [ArgumentFrame.raising]
  readings := [{ frame := ArgumentFrame.raising, control := some .raising }]
  vendlerClass := some .state
  passivizable := false }

/-! ### Prerequisite implicatives -/

/-! Implicatives whose complement is entailed through a prerequisite the verb names,
[nadathur-2023-implicatives]'s causal analysis of *manage*, *dare* and their kin; the
occasion verbs of [solstad-bott-2024] (*thank*, *criticize*, *congratulate*) presuppose an
occasioning eventuality in a parallel way the authors draw and then set apart. -/

/-- "dare" — a positive implicative whose prerequisite presupposition is courage. "Ana dared
    to enter the cave" entails "Ana entered the cave" and presupposes that a daring action was
    required for the complement to be realized ([nadathur-2023-implicatives] §5.2, ex. 3–4,
    26). -/
def dare : Verb := .mkRegular {
  form := "dare"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

/-- "bother" — a positive implicative whose prerequisite presupposition is engagement. "He
    bothered to answer" entails "He answered" and presupposes that apathy had to be overcome
    ([nadathur-2023-implicatives] §2, ex. 10, 28). -/
def bother : Verb := .mkRegular {
  form := "bother"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive
  levinClasses := {LevinClass.amuse, .pain} }

/-- "hesitate" — polarity-reversing one-way implicative.
    "Amira hesitated to drink a beer" ↛ "Amira did not drink a beer."
    "Amira did not hesitate to drink a beer" → "Amira drank a beer."
    The paper does not explicitly name the prerequisite for *hesitate*;
    it is treated as a polarity-reversing analog of *dare*
    ([nadathur-2023-implicatives] §6.4, ex. 45–47). -/
def hesitate : Verb := .mkRegular {
  form := "hesitate"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  implicative := some .negative
  levinClasses := {LevinClass.linger} }

/-- "venture" — positive implicative, among [karttunen-1971]'s implicative
    predicates: venturing to speak entails speaking. -/
def venture : Verb := .mkRegular {
  form := "venture"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

/-- "condescend" — positive implicative, among [karttunen-1971]'s implicative
    predicates: condescending to help entails helping. -/
def condescend : Verb := .mkRegular {
  form := "condescend"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

/-- "happen" — raising verb, positive implicative, among [karttunen-1971]'s
    implicative predicates: happening to see Mary entails seeing her.
    Raising: "It happened to rain" — no theta role for matrix subject. -/
def happen : Verb := .mkRegular {
  form := "happen"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .raising }]
  passivizable := false
  implicative := some .positive
  levinClasses := {LevinClass.occurrence} }

end English.Verbs
