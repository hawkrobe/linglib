/-
# The Passive Construction

## The Phenomenon

English has an active-passive alternation:
- Active: "John kicked the ball" (agent = subject, patient = object)
- Passive: "The ball was kicked (by John)" (patient = subject, agent = optional by-phrase)

The passive:
1. Promotes the object to subject position
2. Demotes the subject to an optional by-phrase
3. Uses auxiliary "be" + past participle

## The Data

  (1a)  John kicked the ball.           ✓  active transitive
  (1b)  The ball was kicked.            ✓  passive (short)
  (1c)  The ball was kicked by John.    ✓  passive with agent

  (2a)  Mary chased the cat.            ✓  active transitive
  (2b)  The cat was chased.             ✓  passive (short)
  (2c)  The cat was chased by Mary.     ✓  passive with agent

  (3a) *The ball was kicked the game.   ✗  passive with object (impossible)
  (3b) *Was kicked John.                ✗  passive missing subject

## Lexical Rule Analysis

Following HPSG/LFG, passive can be analyzed as a lexical rule:
  VN → V_passive,prep(by)

This changes:
- The object becomes the subject
- The subject becomes an optional by-phrase
- The verb takes passive morphology (past participle)
-/

import Linglib.Phenomena.Core.Basic
import Linglib.Theories.Surface.Basic

open Lexicon

-- The Empirical Data

/-- Passive construction data -/
def passiveData : PhenomenonData := {
  name := "Passive Construction"
  generalization := "Passive promotes object to subject, demotes subject to optional by-phrase"
  pairs := [
    -- Active vs passive
    { grammatical := [the, ball, was, kicked]
      ungrammatical := [the, ball, was, kicked, the, ball]  -- can't have object in passive
      clauseType := .declarative
      description := "Passive cannot have direct object" },

    { grammatical := [the, cat_, was, chased, by_, john]
      ungrammatical := [the, cat_, was, chased, the, dog]  -- object instead of by-phrase
      clauseType := .declarative
      description := "Passive agent marked with 'by', not bare NP" },

    -- Subject-aux agreement in passive
    { grammatical := [the, ball, was, kicked]
      ungrammatical := [the, balls, was, kicked]  -- agreement mismatch
      clauseType := .declarative
      description := "Passive auxiliary must agree with subject" }
  ]
}

-- Tests

-- Well-formed passives
#eval Surface.passiveOk [the, ball, was, kicked]              -- true
#eval Surface.passiveOk [the, cat_, was, chased]              -- true
#eval Surface.passiveOk [the, cat_, was, chased, by_, john]   -- true
#eval Surface.passiveOk [the, pizza, was, eaten]              -- true
#eval Surface.passiveOk [the, pizza, was, eaten, by_, mary]   -- true

-- Ill-formed: passive with direct object
#eval Surface.passiveOk [the, ball, was, kicked, the, dog]    -- false

-- Active sentences (passiveOk is vacuously true for non-passives)
#eval Surface.passiveOk [john, kicks, ball]                   -- true (not a passive)

-- Combined checks
#eval Surface.checkSentence Surface.defaultGrammar [the, ball, was, kicked] .declarative  -- true
#eval Surface.checkSentence Surface.defaultGrammar [the, cat_, was, chased, by_, john] .declarative  -- true
