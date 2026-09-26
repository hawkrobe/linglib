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
  form := "know"
  form3sg := "knows"
  formPast := "knew"
  formPastPart := "known"
  formPresPart := "knowing"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  projectionBehavior := some .hole
  complementSig := some .mono
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture}

/-- "regret" — emotive factive, presupposes complement is true -/
def regret : Verb where
  form := "regret"
  form3sg := "regrets"
  formPast := "regretted"
  formPastPart := "regretted"
  formPresPart := "regretting"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full
  levinClasses := {LevinClass.admire}

/-- "realize" — factive, presupposes complement is true -/
def realize : Verb := .mkRegular {
  form := "realize"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi }

/-- "discover" — semi-factive, weaker projection -/
def discover : Verb := .mkRegular {
  form := "discover"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture, .sight} }

/-- "notice" — semi-factive -/
def notice : Verb := .mkRegular {
  form := "notice"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.see} }

/-! ### Doxastic Attitude -/

/-- "believe" — doxastic attitude verb, creates opaque context -/
def believe : Verb := .mkRegular {
  form := "believe"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  projectionBehavior := some .hole
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono
  levinClasses := {LevinClass.declare} }

/-- "think" — doxastic attitude verb -/
def think : Verb where
  form := "think"
  form3sg := "thinks"
  formPast := "thought"
  formPastPart := "thought"
  formPresPart := "thinking"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono
  levinClasses := {LevinClass.declare}

/-! ### Preferential Attitude -/

/-- "want" — preferential attitude verb with infinitival complement -/
def want : Verb := .mkRegular {
  form := "want"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.appoint, .want} }

/-- "intend" — intention-reporting attitude verb ([grano-2024]).
    Primary frame: infinitival with subject control ("intend to leave").
    Alternate frame: for-to non-control ("intend for Ben to come along").
    Rejects indicative complements cross-linguistically: *"Kim intends
    that Sandy leaves." Requires eventuality abstraction (cause* binds
    the complement's event argument). -/
def intend : Verb := .mkRegular {
  form := "intend"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.characterize} }

/-- "decide" — belief/intention hybrid attitude verb ([grano-2024], §6.1).
    Nonfinite complement → intention formation: "Kim decided to quit smoking"
    Finite complement → belief formation: "Kim decided that smoking is harmful"
    The complement type determines the reading, as with Italian *convincere*
    ([fusco-sgrizzi-2026]). -/
def decide_ : Verb := .mkRegular {
  form := "decide"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.finiteClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "hope" — preferential attitude verb.
    Primary frame: finite clause ("hope that John leaves").
    Alternate frame: infinitival with subject control ("hope to leave"). -/
def hope : Verb := .mkRegular {
  form := "hope"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.long} }

/-- "pray" — preferential attitude verb, permits future temporal orientation.
    [klecha-2016]: like *hope*, *pray* can take a circumstantial modal base,
    allowing future-oriented readings under past tense morphology.
    Primary frame: finite clause ("pray that God helps").
    Alternate frame: infinitival with subject control ("pray to be saved"). -/
def pray : Verb := .mkRegular {
  form := "pray"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.long} }

/-- "expect" — preferential attitude verb -/
def expect : Verb := .mkRegular {
  form := "expect"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "wish" — preferential attitude verb -/
def wish : Verb where
  form := "wish"
  form3sg := "wishes"
  formPast := "wished"
  formPastPart := "wished"
  formPresPart := "wishing"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.long}

/-- "fear" — a preferential attitude verb of Class 2, which takes questions. -/
def fear : Verb := .mkRegular {
  form := "fear"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  levinClasses := {LevinClass.admire, .marvel} }

/-- "dread" — a preferential attitude verb of Class 2, which takes questions. -/
def dread : Verb := .mkRegular {
  form := "dread"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  levinClasses := {LevinClass.admire} }

/-- "worry" — preferential attitude verb -/
def worry : Verb where
  form := "worry"
  form3sg := "worries"
  formPast := "worried"
  formPastPart := "worried"
  formPresPart := "worrying"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased)
  levinClasses := {LevinClass.amuse}

/-! ### Clause-Embedding Predicates -/

/-! The 20 clause-embedding predicates of [degen-tonhauser-2022].
    Predicates already defined above: know, discover, see, think, say, hear.
    "be annoyed" and "be right" are copular constructions, not simple verbs. -/

/-- "reveal" — factive communication verb ([degen-tonhauser-2022]: canonically factive) -/
def reveal : Verb := .mkRegular {
  form := "reveal"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  attitude := some (.doxastic .veridical)
  factivity := some .full
  levinClasses := {LevinClass.characterize, .say} }

/-- "acknowledge" — optionally factive communication verb
    Levin lists *acknowledge* only among the appoint verbs (§29.1), a different frame. -/
def acknowledge : Verb := .mkRegular {
  form := "acknowledge"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appoint} }


/-- "admit" — optionally factive communication verb
    Levin lists *admit* among the conjecture verbs (§29.5). -/
def admit : Verb where
  form := "admit"
  form3sg := "admits"
  formPast := "admitted"
  formPastPart := "admitted"
  formPresPart := "admitting"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.conjecture}

/-- "announce" — communication verb -/
def announce : Verb := .mkRegular {
  form := "announce"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.say} }

/-- "confess" — optionally factive communication verb -/
def confess : Verb := .mkRegular {
  form := "confess"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare, .say} }

/-- "inform" — optionally factive communication verb with recipient -/
def inform : Verb := .mkRegular {
  form := "inform"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement }

/-- "suggest" — non-factive communication verb -/
def suggest : Verb := .mkRegular {
  form := "suggest"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.reflexiveAppearance, .say} }

/-- "pretend" — anti-veridical attitude verb -/
def pretend : Verb := .mkRegular {
  form := "pretend"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  opaqueContext := true }

/-- "confirm" — evidential verb -/
def confirm : Verb := .mkRegular {
  form := "confirm"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize} }

/-- "demonstrate" — evidential verb -/
def demonstrate : Verb := .mkRegular {
  form := "demonstrate"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage} }

/-- "establish" — evidential verb -/
def establish : Verb := .mkRegular {
  form := "establish"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize} }

/-- "prove" — evidential verb -/
def prove : Verb := .mkRegular {
  form := "prove"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare} }

/-! ### Question-Embedding -/

/-- "wonder" — embeds questions only -/
def wonder : Verb := .mkRegular {
  form := "wonder"
  frames := [ArgumentFrame.question]
  vendlerClass := some .state
  opaqueContext := true
  levinClasses := {LevinClass.marvel} }

/-- "ask" — embeds questions -/
def ask : Verb := .mkRegular {
  form := "ask"
  speechActVerb := true
  frames := [ArgumentFrame.question]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage} }

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : Verb := .mkRegular {
  form := "investigate"
  frames := [ArgumentFrame.question, ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.investigate, .sight} }

/-- "depend_on" — rogative, embeds interrogatives only ([dayal-2025]: a rogative predicate) -/
def depend_on : Verb where
  form := "depend on"
  form3sg := "depends on"
  formPast := "depended on"
  formPastPart := "depended on"
  formPresPart := "depending on"
  frames := [ArgumentFrame.question]
  vendlerClass := some .state

/-- "remember" in factive/question-embedding sense. -/
def remember_rog : Verb := .mkRegular {
  form := "remember"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  senseTag := .rogative
  levinClasses := {LevinClass.characterize} }

/-- "forget" in factive/question-embedding sense. -/
def forget_rog : Verb where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .full
  senseTag := .rogative

end English.Verbs
