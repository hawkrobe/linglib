/-
# Verb Lexicon Fragment

Unified lexical entries for verbs, bundling everything needed to work with
a verb in semantic/pragmatic analysis:
- Surface form(s)
- Syntactic category/valence
- Semantic type
- Presupposition structure (if any)
- Denotation function

## Design

Each `VerbEntry` provides the complete specification for a verb lexeme.
Downstream applications (RSA, NeoGricean, parsers) import this module
and get all the semantic machinery they need.

## Verb Classes

1. **Simple verbs** (sleep, run): No presupposition, standard denotation
2. **Factive verbs** (know, regret): Presuppose complement truth
3. **Change-of-state verbs** (stop, start): Presuppose prior state
4. **Implicative verbs** (manage, fail): Entailment patterns
5. **Attitude verbs** (believe, think): No presupposition, opaque contexts

## Usage

```lean
import Linglib.Fragments.Verbs

-- Get the lexical entry for "stop"
#check Verbs.stop
-- VerbEntry with:
--   form = "stop"
--   verbClass = .changeOfState
--   presupType = some .softTrigger
--   cosType = some .cessation
```
-/

import Linglib.Core.Basic
import Linglib.Core.Presupposition
import Linglib.Theories.Montague.Lexicon.ChangeOfState.Theory

namespace Fragments.Verbs

open Core.Presupposition
open Montague.Lexicon.ChangeOfState

-- ============================================================================
-- Verb Classification
-- ============================================================================

/--
Semantic class of verb.

This classification determines what semantic machinery is needed:
- Simple verbs just need a standard denotation
- Factives need presupposition projection
- CoS verbs need temporal/change structure
- Attitudes need intensional semantics
-/
inductive VerbClass where
  | simple          -- sleep, run, eat
  | factive         -- know, regret, realize
  | semifactive     -- discover, notice (weaker projection)
  | changeOfState   -- stop, start, continue
  | implicative     -- manage, fail, remember (to)
  | attitude        -- believe, think, want
  | perception      -- see, hear (ambiguous: factive or not)
  | communication   -- say, tell, claim
  deriving DecidableEq, Repr, BEq

/--
Presupposition trigger type (Tonhauser et al. 2013 classification).

- Hard triggers: Always project (too, again, also)
- Soft triggers: Context-sensitive projection (stop, know)
-/
inductive PresupTriggerType where
  | hardTrigger     -- Projective in all contexts
  | softTrigger     -- Can be locally accommodated
  deriving DecidableEq, Repr, BEq

/--
Complement type that the verb selects.

- Finite: "that" clauses ("John knows that Mary left")
- Infinitival: "to" complements ("John managed to leave")
- Gerund: "-ing" complements ("John stopped smoking")
- NP: Direct object ("John kicked the ball")
- None: Intransitive ("John slept")
-/
inductive ComplementType where
  | none            -- Intransitive
  | np              -- Transitive with NP object
  | np_np           -- Ditransitive: "give X Y"
  | np_pp           -- NP + PP: "put X on Y"
  | finiteClause    -- "that" clause
  | infinitival     -- "to" VP
  | gerund          -- "-ing" VP
  | smallClause     -- "consider X happy"
  | question        -- Embedded question "wonder who"
  deriving DecidableEq, Repr, BEq

/--
Theta roles for argument structure.
-/
inductive ThetaRole where
  | agent       -- Volitional causer (John kicked the ball)
  | patient     -- Affected entity (John kicked the ball)
  | theme       -- Entity in a state/location (The book is on the table)
  | experiencer -- Perceiver/cognizer (John knows that p)
  | goal        -- Recipient/target (John gave Mary a book)
  | source      -- Origin (John came from Paris)
  | instrument  -- Means (John opened the door with a key)
  | stimulus    -- Cause of experience (The noise frightened John)
  deriving DecidableEq, Repr, BEq

/--
Control type for verbs with infinitival complements.
-/
inductive ControlType where
  | subjectControl  -- "John tried to leave" (John = leaver)
  | objectControl   -- "John persuaded Mary to leave" (Mary = leaver)
  | raising         -- "John seems to be happy" (no theta role for matrix subject)
  | none            -- Not applicable
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Verb Entry Structure
-- ============================================================================

/--
A complete lexical entry for a verb.

Bundles all information needed for semantic/pragmatic analysis:
- Surface form and basic morphology
- Syntactic selection (complement type, valence)
- Argument structure (theta roles, control)
- Semantic class and presupposition behavior
- Link to compositional semantics (CoS type, factivity, etc.)
-/
structure VerbEntry where
  -- === Morphology ===
  /-- Citation form (infinitive) -/
  form : String
  /-- Third person singular present (for agreement) -/
  form3sg : String
  /-- Past tense form -/
  formPast : String
  /-- Past participle (for passives, perfects) -/
  formPastPart : String
  /-- Present participle / gerund -/
  formPresPart : String

  -- === Argument Structure ===
  /-- What complement does the verb select? -/
  complementType : ComplementType
  /-- Theta role of external argument (subject) -/
  subjectTheta : Option ThetaRole := none
  /-- Theta role of internal argument (object) -/
  objectTheta : Option ThetaRole := none
  /-- Theta role of second internal argument (indirect object) -/
  object2Theta : Option ThetaRole := none
  /-- Control type for infinitival complements -/
  controlType : ControlType := .none
  /-- Is the verb unaccusative? (subject is underlying object) -/
  unaccusative : Bool := false
  /-- Can the verb passivize? -/
  passivizable : Bool := true

  -- === Semantic Class ===
  /-- Semantic verb class -/
  verbClass : VerbClass
  /-- Is the verb a presupposition trigger? -/
  presupType : Option PresupTriggerType := none

  -- === Class-Specific Features ===
  /-- For CoS verbs: which type (cessation, inception, continuation)? -/
  cosType : Option CoSType := none
  /-- For factive verbs: what does it presuppose about its complement? -/
  factivePresup : Bool := false
  /-- For implicative verbs: does success of main verb entail complement? -/
  implicativeEntailment : Option Bool := none

  -- === Intensionality ===
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false
  /-- Can the verb take a question complement? -/
  takesQuestion : Bool := false

  deriving Repr, BEq

-- ============================================================================
-- Simple Verbs (No Presupposition)
-- ============================================================================

/-- "sleep" — intransitive, no presupposition -/
def sleep : VerbEntry where
  form := "sleep"
  form3sg := "sleeps"
  formPast := "slept"
  formPastPart := "slept"
  formPresPart := "sleeping"
  complementType := .none
  subjectTheta := some .agent
  passivizable := false
  verbClass := .simple

/-- "run" — intransitive, no presupposition -/
def run : VerbEntry where
  form := "run"
  form3sg := "runs"
  formPast := "ran"
  formPastPart := "run"
  formPresPart := "running"
  complementType := .none
  subjectTheta := some .agent
  passivizable := false
  verbClass := .simple

/-- "arrive" — unaccusative intransitive -/
def arrive : VerbEntry where
  form := "arrive"
  form3sg := "arrives"
  formPast := "arrived"
  formPastPart := "arrived"
  formPresPart := "arriving"
  complementType := .none
  subjectTheta := some .theme  -- Underlying object
  unaccusative := true
  passivizable := false
  verbClass := .simple

/-- "eat" — transitive, no presupposition -/
def eat : VerbEntry where
  form := "eat"
  form3sg := "eats"
  formPast := "ate"
  formPastPart := "eaten"
  formPresPart := "eating"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .simple

/-- "kick" — transitive -/
def kick : VerbEntry where
  form := "kick"
  form3sg := "kicks"
  formPast := "kicked"
  formPastPart := "kicked"
  formPresPart := "kicking"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .simple

/-- "give" — ditransitive -/
def give : VerbEntry where
  form := "give"
  form3sg := "gives"
  formPast := "gave"
  formPastPart := "given"
  formPresPart := "giving"
  complementType := .np_np
  subjectTheta := some .agent
  objectTheta := some .theme
  object2Theta := some .goal
  verbClass := .simple

/-- "put" — locative -/
def put : VerbEntry where
  form := "put"
  form3sg := "puts"
  formPast := "put"
  formPastPart := "put"
  formPresPart := "putting"
  complementType := .np_pp
  subjectTheta := some .agent
  objectTheta := some .theme
  verbClass := .simple

/-- "see" — transitive, can also embed clauses -/
def see : VerbEntry where
  form := "see"
  form3sg := "sees"
  formPast := "saw"
  formPastPart := "seen"
  formPresPart := "seeing"
  complementType := .np  -- Can also take .finiteClause
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  verbClass := .perception
  factivePresup := true  -- "see that p" presupposes p

-- ============================================================================
-- Factive Verbs (Presuppose Complement Truth)
-- ============================================================================

/-- "know" — factive, presupposes complement is true -/
def know : VerbEntry where
  form := "know"
  form3sg := "knows"
  formPast := "knew"
  formPastPart := "known"
  formPresPart := "knowing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .factive
  presupType := some .softTrigger
  factivePresup := true
  takesQuestion := true  -- "know who/what/whether"

/-- "regret" — factive, presupposes complement is true -/
def regret : VerbEntry where
  form := "regret"
  form3sg := "regrets"
  formPast := "regretted"
  formPastPart := "regretted"
  formPresPart := "regretting"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .factive
  presupType := some .softTrigger
  factivePresup := true

/-- "realize" — factive, presupposes complement is true -/
def realize : VerbEntry where
  form := "realize"
  form3sg := "realizes"
  formPast := "realized"
  formPastPart := "realized"
  formPresPart := "realizing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .factive
  presupType := some .softTrigger
  factivePresup := true

/-- "discover" — semifactive, weaker projection -/
def discover : VerbEntry where
  form := "discover"
  form3sg := "discovers"
  formPast := "discovered"
  formPastPart := "discovered"
  formPresPart := "discovering"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .semifactive
  presupType := some .softTrigger
  factivePresup := true
  takesQuestion := true

/-- "notice" — semifactive -/
def notice : VerbEntry where
  form := "notice"
  form3sg := "notices"
  formPast := "noticed"
  formPastPart := "noticed"
  formPresPart := "noticing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .semifactive
  presupType := some .softTrigger
  factivePresup := true

-- ============================================================================
-- Change-of-State Verbs (Presuppose Prior State)
-- ============================================================================

/-- "stop" — CoS cessation, presupposes activity was happening -/
def stop : VerbEntry where
  form := "stop"
  form3sg := "stops"
  formPast := "stopped"
  formPastPart := "stopped"
  formPresPart := "stopping"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .cessation

/-- "quit" — CoS cessation -/
def quit : VerbEntry where
  form := "quit"
  form3sg := "quits"
  formPast := "quit"
  formPastPart := "quit"
  formPresPart := "quitting"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .cessation

/-- "start" — CoS inception, presupposes activity wasn't happening -/
def start : VerbEntry where
  form := "start"
  form3sg := "starts"
  formPast := "started"
  formPastPart := "started"
  formPresPart := "starting"
  complementType := .gerund  -- Can also take .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .inception

/-- "begin" — CoS inception -/
def begin_ : VerbEntry where
  form := "begin"
  form3sg := "begins"
  formPast := "began"
  formPastPart := "begun"
  formPresPart := "beginning"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .inception

/-- "continue" — CoS continuation, presupposes activity was happening -/
def continue_ : VerbEntry where
  form := "continue"
  form3sg := "continues"
  formPast := "continued"
  formPastPart := "continued"
  formPresPart := "continuing"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .continuation

/-- "keep" — CoS continuation -/
def keep : VerbEntry where
  form := "keep"
  form3sg := "keeps"
  formPast := "kept"
  formPastPart := "kept"
  formPresPart := "keeping"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .continuation

-- ============================================================================
-- Implicative Verbs (Entailment Patterns)
-- ============================================================================

/-- "manage" — positive implicative: "managed to VP" entails "VP" -/
def manage : VerbEntry where
  form := "manage"
  form3sg := "manages"
  formPast := "managed"
  formPastPart := "managed"
  formPresPart := "managing"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeEntailment := some true  -- Success entails complement

/-- "fail" — negative implicative: "failed to VP" entails "not VP" -/
def fail : VerbEntry where
  form := "fail"
  form3sg := "fails"
  formPast := "failed"
  formPastPart := "failed"
  formPresPart := "failing"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeEntailment := some false  -- Success entails NOT complement

/-- "try" — subject control, no entailment -/
def try_ : VerbEntry where
  form := "try"
  form3sg := "tries"
  formPast := "tried"
  formPastPart := "tried"
  formPresPart := "trying"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .simple

/-- "persuade" — object control: "persuade X to VP" (X = agent of VP) -/
def persuade : VerbEntry where
  form := "persuade"
  form3sg := "persuades"
  formPast := "persuaded"
  formPastPart := "persuaded"
  formPresPart := "persuading"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .experiencer  -- The persuadee
  controlType := .objectControl
  verbClass := .simple

/-- "promise" — subject control with object: "promise X to VP" (subject = agent of VP) -/
def promise : VerbEntry where
  form := "promise"
  form3sg := "promises"
  formPast := "promised"
  formPastPart := "promised"
  formPresPart := "promising"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .goal
  controlType := .subjectControl  -- Unusual: subject control despite object
  verbClass := .simple

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : VerbEntry where
  form := "remember"
  form3sg := "remembers"
  formPast := "remembered"
  formPastPart := "remembered"
  formPresPart := "remembering"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeEntailment := some true
  -- Note: "remember that p" is factive, but "remember to VP" is implicative

/-- "forget" — negative implicative with infinitival -/
def forget : VerbEntry where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeEntailment := some false
  -- Note: "forget that p" is factive

-- ============================================================================
-- Attitude Verbs (Opaque Contexts, No Factivity)
-- ============================================================================

/-- "believe" — attitude verb, creates opaque context -/
def believe : VerbEntry where
  form := "believe"
  form3sg := "believes"
  formPast := "believed"
  formPastPart := "believed"
  formPresPart := "believing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true

/-- "think" — attitude verb -/
def think : VerbEntry where
  form := "think"
  form3sg := "thinks"
  formPast := "thought"
  formPastPart := "thought"
  formPresPart := "thinking"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true

/-- "want" — attitude verb with infinitival complement -/
def want : VerbEntry where
  form := "want"
  form3sg := "wants"
  formPast := "wanted"
  formPastPart := "wanted"
  formPresPart := "wanting"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .attitude
  opaqueContext := true

/-- "hope" — attitude verb -/
def hope : VerbEntry where
  form := "hope"
  form3sg := "hopes"
  formPast := "hoped"
  formPastPart := "hoped"
  formPresPart := "hoping"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true

/-- "expect" — attitude verb -/
def expect : VerbEntry where
  form := "expect"
  form3sg := "expects"
  formPast := "expected"
  formPastPart := "expected"
  formPresPart := "expecting"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true

/-- "seem" — raising verb (no theta role for subject) -/
def seem : VerbEntry where
  form := "seem"
  form3sg := "seems"
  formPast := "seemed"
  formPastPart := "seemed"
  formPresPart := "seeming"
  complementType := .infinitival
  subjectTheta := none  -- No theta role - raising
  controlType := .raising
  passivizable := false
  verbClass := .simple

-- ============================================================================
-- Communication Verbs
-- ============================================================================

/-- "say" — communication verb, not factive -/
def say : VerbEntry where
  form := "say"
  form3sg := "says"
  formPast := "said"
  formPastPart := "said"
  formPresPart := "saying"
  verbClass := .communication
  complementType := .finiteClause

/-- "tell" — communication verb with recipient -/
def tell : VerbEntry where
  form := "tell"
  form3sg := "tells"
  formPast := "told"
  formPastPart := "told"
  formPresPart := "telling"
  verbClass := .communication
  complementType := .finiteClause

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : VerbEntry where
  form := "claim"
  form3sg := "claims"
  formPast := "claimed"
  formPastPart := "claimed"
  formPresPart := "claiming"
  verbClass := .communication
  complementType := .finiteClause

-- ============================================================================
-- Question-Embedding Verbs
-- ============================================================================

/-- "wonder" — embeds questions only -/
def wonder : VerbEntry where
  form := "wonder"
  form3sg := "wonders"
  formPast := "wondered"
  formPastPart := "wondered"
  formPresPart := "wondering"
  verbClass := .attitude
  complementType := .question
  takesQuestion := true
  opaqueContext := true

/-- "ask" — embeds questions -/
def ask : VerbEntry where
  form := "ask"
  form3sg := "asks"
  formPast := "asked"
  formPastPart := "asked"
  formPresPart := "asking"
  verbClass := .communication
  complementType := .question
  takesQuestion := true

-- ============================================================================
-- Semantic Functions
-- ============================================================================

/--
Get the CoS semantics for a verb (if it's a CoS verb).

Returns `some (cosSemantics t P)` if the verb has a CoS type,
where `P` is the activity predicate (complement denotation).
-/
def getCoSSemantics {W : Type*} (v : VerbEntry) (P : W → Bool) :
    Option (PrProp W) :=
  v.cosType.map fun t => cosSemantics t P

/--
Does this verb presuppose its complement?
-/
def presupposesComplement (v : VerbEntry) : Bool :=
  v.factivePresup || v.cosType.isSome

/--
Is this verb a presupposition trigger?
-/
def isPresupTrigger (v : VerbEntry) : Bool :=
  v.presupType.isSome

/--
Get all verb entries as a list (for enumeration).
-/
def allVerbs : List VerbEntry := [
  -- Simple
  sleep, run, arrive, eat, kick, give, put, see,
  -- Factive
  know, regret, realize, discover, notice,
  -- Change of State
  stop, quit, start, begin_, continue_, keep,
  -- Implicative / Control
  manage, fail, try_, persuade, promise, remember, forget,
  -- Attitude / Raising
  believe, think, want, hope, expect, seem,
  -- Communication
  say, tell, claim,
  -- Question-embedding
  wonder, ask
]

/--
Look up a verb entry by citation form.
-/
def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (fun v => v.form == form)

-- ============================================================================
-- Derived Syntactic Words
-- ============================================================================

/--
Convert a verb entry to a `Word` (from Core.Basic) in 3sg present form.
-/
def toWord3sg (v : VerbEntry) : Word :=
  { form := v.form3sg
  , cat := .V
  , features := {
      valence := some (match v.complementType with
        | .none => .intransitive
        | .np => .transitive
        | _ => .transitive)  -- Clause-embedding verbs are syntactically transitive
      , number := some .sg
      , person := some .third
      , voice := some .active
      , vform := some .finite
    }
  }

/--
Convert a verb entry to a `Word` in base/infinitive form.
-/
def toWordBase (v : VerbEntry) : Word :=
  { form := v.form
  , cat := .V
  , features := {
      valence := some (match v.complementType with
        | .none => .intransitive
        | _ => .transitive)
      , vform := some .infinitive
    }
  }

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Summary: Verb Lexicon Fragment

### VerbEntry Fields
- `form`, `form3sg`, `formPast`, `formPastPart`, `formPresPart`: Morphological forms
- `verbClass`: Semantic classification (simple, factive, CoS, implicative, attitude)
- `complementType`: What complement the verb selects
- `presupType`: Presupposition trigger classification
- `cosType`: For CoS verbs, the change type (cessation/inception/continuation)
- `factivePresup`: Whether complement truth is presupposed
- `implicativeEntailment`: For implicatives, what is entailed
- `opaqueContext`: Whether the verb creates an opaque context
- `takesQuestion`: Whether the verb can embed questions

### Key Functions
- `getCoSSemantics`: Get PrProp for CoS verbs
- `presupposesComplement`: Check if verb presupposes complement
- `isPresupTrigger`: Check if verb is a presupposition trigger
- `lookup`: Find verb by citation form
- `toWord3sg`, `toWordBase`: Convert to syntactic Word

### Verb Inventory
**Simple**: sleep, run, eat
**Factive**: know, regret, realize, discover, notice
**CoS**: stop, quit, start, begin, continue, keep
**Implicative**: manage, fail, remember, forget
**Attitude**: believe, think, want, hope, expect, wonder
**Communication**: say, tell, claim, ask
-/

end Fragments.Verbs
