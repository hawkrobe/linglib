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

/-! ### Implicative / Control -/

/-- "manage" — a positive implicative; "managed to VP" entails "VP", and on the traditional
    analysis the agentive subject controls the complement.
    -/
def manage : Verb where
  morphs := [.root "manage"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- "fail" — a negative implicative; "failed to VP" entails "not VP". -/
def fail : Verb where
  morphs := [.root "fail"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .negative, .some .positive⟩

/-- "try" — subject control, no entailment -/
def try_ : Verb where
  morphs := [.root "try"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.amuse}

/-- "persuade" — object control, "persuade X to VP" with X the agent of VP. A psychological
    attitude verb whose object comes to form an intention; it projects the AUTHOR coordinate,
    so control is obligatorily *de se* ([landau-2015] table (36)). -/
def persuade : Verb where
  morphs := [.root "persuade"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- "promise" — subject control across an object, "promise X to VP". A desiderative attitude
    verb whose subject commits to a future action; [landau-2015] (5c) classifies it as
    desiderative, hence logophoric control. -/
def promise : Verb where
  morphs := [.root "promise"]
  valency := .of
    [(ArgumentFrame.infinitival, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2])]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.futureHaving}

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : Verb where
  morphs := [.root "remember"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩
  levinClasses := {LevinClass.characterize}

/-- "forget" with an infinitive, [karttunen-1971]'s negative implicative: *forgot to lock the
    door* entails *did not lock the door*. The factive sense that takes a finite clause, a
    gerund or a question is `forget_rog`; [williams-2025] takes the two senses to be one verb
    whose plain infinitive carries a covert modal. -/
def forget : Verb where
  morphs := [.root "forget"]
  past := "forgot"
  pastPart := "forgotten"
  doubling := true
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .negative, .some .positive⟩

/-- "neglect" — negative implicative, listed with *forget* and *fail* among
    [karttunen-1971]'s negative implicatives: neglecting to lock the door
    entails not locking it. -/
def neglect : Verb where
  morphs := [.root "neglect"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .negative, .some .positive⟩

/-! ### Raising -/

/-- "seem" — raising verb (no theta role for subject, unaccusative) -/
def seem : Verb where
  morphs := [.root "seem"]
  valency := .ofFrame ArgumentFrame.raising
  readings := [{ frame := ArgumentFrame.raising, control := some .raising }]
  vendlerClass := some .state
  passivizable := false

/-! ### Prerequisite implicatives -/

/-! Implicatives whose complement is entailed through a prerequisite the verb names,
[nadathur-2023-implicatives]'s causal analysis of *manage*, *dare* and their kin; the
occasion verbs of [solstad-bott-2024] (*thank*, *criticize*, *congratulate*) presuppose an
occasioning eventuality in a parallel way the authors draw and then set apart. -/

/-- "dare" — a positive implicative whose prerequisite presupposition is courage. "Ana dared
    to enter the cave" entails "Ana entered the cave" and presupposes that a daring action was
    required for the complement to be realized ([nadathur-2023-implicatives] §5.2, ex. 3–4,
    26). -/
def dare : Verb where
  morphs := [.root "dare"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- "bother" — a positive implicative whose prerequisite presupposition is engagement. "He
    bothered to answer" entails "He answered" and presupposes that apathy had to be overcome
    ([nadathur-2023-implicatives] §2, ex. 10, 28). -/
def bother : Verb where
  morphs := [.root "bother"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩
  levinClasses := {LevinClass.amuse, .marvel, .pain}

/-- "hesitate" — polarity-reversing one-way implicative.
    "Amira hesitated to drink a beer" ↛ "Amira did not drink a beer."
    "Amira did not hesitate to drink a beer" → "Amira drank a beer."
    The paper does not explicitly name the prerequisite for *hesitate*;
    it is treated as a polarity-reversing analog of *dare*
    ([nadathur-2023-implicatives] §6.4, ex. 45–47). -/
def hesitate : Verb where
  morphs := [.root "hesitate"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  implicative := ⟨⊥, .some .positive⟩
  levinClasses := {LevinClass.linger}

/-- "venture" — positive implicative, among [karttunen-1971]'s implicative
    predicates: venturing to speak entails speaking. -/
def venture : Verb where
  morphs := [.root "venture"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- "condescend" — positive implicative, among [karttunen-1971]'s implicative
    predicates: condescending to help entails helping. -/
def condescend : Verb where
  morphs := [.root "condescend"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- "happen" — raising verb, positive implicative, among [karttunen-1971]'s
    implicative predicates: happening to see Mary entails seeing her.
    Raising: "It happened to rain" — no theta role for matrix subject. -/
def happen : Verb where
  morphs := [.root "happen"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .raising }]
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩
  levinClasses := {LevinClass.occurrence}

end English.Verbs
