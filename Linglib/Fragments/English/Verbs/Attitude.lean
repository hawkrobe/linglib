module

public import Linglib.Fragments.English.Verbs.Implicative

/-!
# English attitude verbs

This file defines the English clause-embedding verbs of attitude: the factives *know*, *regret*,
*realize*, *discover* and *notice*, the doxastics *believe* and *think*, the preferentials *want*,
*intend*, *decide*, *hope*, *pray*, *expect*, *wish*, *fear*, *dread* and *worry*, the
clause-embedding predicates of Degen and Tonhauser's experiments, and the question-embedding
*wonder*, *ask*, *investigate* and *depend on* with the rogative senses of *remember* and
*forget*.

## References

* [dayal-2025]
* [degen-tonhauser-2022]
* [fusco-sgrizzi-2026]
* [grano-2024]
* [klecha-2016]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Factive / Semifactive -/

/-- "know" — factive, presupposes complement is true -/
def know : Verb where
  morphs := [.root "know"]
  form3sg := "knows"
  formPast := "knew"
  formPastPart := "known"
  formPresPart := "knowing"
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.question, [0, 1])]
  vendlerClass := some .state
  passivizable := false
  complementSig := some .mono
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture}

/-- "regret" — emotive factive, presupposes complement is true -/
def regret : Verb where
  morphs := [.root "regret"]
  form3sg := "regrets"
  formPast := "regretted"
  formPastPart := "regretted"
  formPresPart := "regretting"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  attitude := some (.preferential .negative true)
  factivity := some .full
  levinClasses := {LevinClass.admire}

/-- "realize" — factive, presupposes complement is true -/
def realize : Verb := .mkRegular {
  morphs := [.root "realize"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .semi }

/-- "discover" — semi-factive, weaker projection -/
def discover : Verb := .mkRegular {
  morphs := [.root "discover"]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.question, [0, 1])]
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture, .sight} }

/-- "notice" — semi-factive -/
def notice : Verb := .mkRegular {
  morphs := [.root "notice"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.see} }

/-! ### Doxastic Attitude -/

/-- "believe" — doxastic attitude verb, creates opaque context -/
def believe : Verb := .mkRegular {
  morphs := [.root "believe"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono
  levinClasses := {LevinClass.declare} }

/-- "think" — doxastic attitude verb -/
def think : Verb where
  morphs := [.root "think"]
  form3sg := "thinks"
  formPast := "thought"
  formPastPart := "thought"
  formPresPart := "thinking"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono
  levinClasses := {LevinClass.declare}

/-! ### Preferential Attitude -/

/-- "want" — preferential attitude verb with infinitival complement -/
def want : Verb := .mkRegular {
  morphs := [.root "want"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.appoint, .want} }

/-- "intend" — intention-reporting attitude verb ([grano-2024]).
    Primary frame: infinitival with subject control ("intend to leave").
    Alternate frame: for-to non-control ("intend for Ben to come along").
    Rejects indicative complements cross-linguistically: *"Kim intends
    that Sandy leaves." Requires eventuality abstraction (cause* binds
    the complement's event argument). -/
def intend : Verb := .mkRegular {
  morphs := [.root "intend"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.characterize} }

/-- "decide" — belief/intention hybrid attitude verb ([grano-2024], §6.1).
    Nonfinite complement → intention formation: "Kim decided to quit smoking"
    Finite complement → belief formation: "Kim decided that smoking is harmful"
    The complement type determines the reading, as with Italian *convincere*
    ([fusco-sgrizzi-2026]). -/
def decide_ : Verb := .mkRegular {
  morphs := [.root "decide"]
  valency := .of [(ArgumentFrame.infinitival, [0, 1]), (ArgumentFrame.finiteClause, [0, 1])]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  opaqueContext := true
  attitude := some (.preferential .positive true) }

/-- "hope" — preferential attitude verb.
    Primary frame: finite clause ("hope that John leaves").
    Alternate frame: infinitival with subject control ("hope to leave"). -/
def hope : Verb := .mkRegular {
  morphs := [.root "hope"]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.infinitival, [0, 1])]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.long} }

/-- "pray" — preferential attitude verb, permits future temporal orientation.
    [klecha-2016]: like *hope*, *pray* can take a circumstantial modal base,
    allowing future-oriented readings under past tense morphology.
    Primary frame: finite clause ("pray that God helps").
    Alternate frame: infinitival with subject control ("pray to be saved"). -/
def pray : Verb := .mkRegular {
  morphs := [.root "pray"]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.infinitival, [0, 1])]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.long} }

/-- "expect" — preferential attitude verb -/
def expect : Verb := .mkRegular {
  morphs := [.root "expect"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true) }

/-- "wish" — preferential attitude verb -/
def wish : Verb where
  morphs := [.root "wish"]
  form3sg := "wishes"
  formPast := "wished"
  formPastPart := "wished"
  formPresPart := "wishing"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.long}

/-- "fear" — a preferential attitude verb of Class 2, which takes questions. -/
def fear : Verb := .mkRegular {
  morphs := [.root "fear"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true)
  levinClasses := {LevinClass.admire, .marvel} }

/-- "dread" — a preferential attitude verb of Class 2, which takes questions. -/
def dread : Verb := .mkRegular {
  morphs := [.root "dread"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true)
  levinClasses := {LevinClass.admire} }

/-- "worry" — preferential attitude verb -/
def worry : Verb where
  morphs := [.root "worry"]
  form3sg := "worries"
  formPast := "worried"
  formPastPart := "worried"
  formPresPart := "worrying"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative false)
  levinClasses := {LevinClass.amuse, .marvel}

/-! ### Clause-Embedding Predicates -/

/-! The 20 clause-embedding predicates of [degen-tonhauser-2022].
    Predicates already defined above: know, discover, see, think, say, hear.
    "be annoyed" and "be right" are copular constructions, not simple verbs. -/

/-- "reveal" — factive communication verb ([degen-tonhauser-2022]: canonically factive) -/
def reveal : Verb := .mkRegular {
  morphs := [.root "reveal"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  attitude := some (.doxastic .veridical)
  factivity := some .full
  levinClasses := {LevinClass.characterize, .say} }

/-- "acknowledge" — optionally factive communication verb
    Levin lists *acknowledge* only among the appoint verbs (§29.1), a different frame. -/
def acknowledge : Verb := .mkRegular {
  morphs := [.root "acknowledge"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appoint} }


/-- "admit" — optionally factive communication verb
    Levin lists *admit* among the conjecture verbs (§29.5). -/
def admit : Verb where
  morphs := [.root "admit"]
  form3sg := "admits"
  formPast := "admitted"
  formPastPart := "admitted"
  formPresPart := "admitting"
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.conjecture}

/-- "announce" — communication verb -/
def announce : Verb := .mkRegular {
  morphs := [.root "announce"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.say} }

/-- "confess" — optionally factive communication verb -/
def confess : Verb := .mkRegular {
  morphs := [.root "confess"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare, .say} }

/-- "inform" — optionally factive communication verb with recipient -/
def inform : Verb := .mkRegular {
  morphs := [.root "inform"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement }

/-- "suggest" — non-factive communication verb -/
def suggest : Verb := .mkRegular {
  morphs := [.root "suggest"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.reflexiveAppearance, .say} }

/-- "pretend" — anti-veridical attitude verb -/
def pretend : Verb := .mkRegular {
  morphs := [.root "pretend"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  opaqueContext := true }

/-- "confirm" — evidential verb -/
def confirm : Verb := .mkRegular {
  morphs := [.root "confirm"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize} }

/-- "demonstrate" — evidential verb -/
def demonstrate : Verb := .mkRegular {
  morphs := [.root "demonstrate"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage} }

/-- "establish" — evidential verb -/
def establish : Verb := .mkRegular {
  morphs := [.root "establish"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize} }

/-- "prove" — evidential verb -/
def prove : Verb := .mkRegular {
  morphs := [.root "prove"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare} }

/-! ### Question-Embedding -/

/-- "wonder" — embeds questions only -/
def wonder : Verb := .mkRegular {
  morphs := [.root "wonder"]
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .state
  opaqueContext := true
  levinClasses := {LevinClass.marvel} }

/-- "ask" — embeds questions -/
def ask : Verb := .mkRegular {
  morphs := [.root "ask"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage} }

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : Verb := .mkRegular {
  morphs := [.root "investigate"]
  valency := .of
    [(ArgumentFrame.question, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.investigate, .sight} }

/-- "depend_on" — rogative, embeds interrogatives only ([dayal-2025]: a rogative predicate) -/
def depend_on : Verb where
  morphs := [.root "depend", .free "on"]
  form3sg := "depends on"
  formPast := "depended on"
  formPastPart := "depended on"
  formPresPart := "depending on"
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .state

/-- "remember" in factive/question-embedding sense. -/
def remember_rog : Verb := .mkRegular {
  morphs := [.root "remember"]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.question, [0, 1])]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  senseTag := .rogative
  levinClasses := {LevinClass.characterize} }

/-- "forget" in factive/question-embedding sense, with a finite clause, a PRO-ing gerund
(*John forgot having stopped by the flower shop*, [williams-2025] (8)) or a question. -/
def forget_rog : Verb where
  morphs := [.root "forget"]
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  valency := .of
    [(ArgumentFrame.finiteClause, [0, 1]),
     (ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.question, [0, 1])]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .full
  senseTag := .rogative

end English.Verbs
