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

import Linglib.Core.Basic

namespace Phenomena.ArgumentStructure.Passive

/-- Passive construction data.

Pure empirical data with no theoretical commitments.
Theories interpret this via their Bridge modules. -/
def data : StringPhenomenonData := {
  name := "Passive Construction"
  generalization := "Passive promotes object to subject, demotes subject to optional by-phrase"
  pairs := [
    -- Active vs passive
    { grammatical := "the ball was kicked"
      ungrammatical := "the ball was kicked the ball"  -- can't have object in passive
      clauseType := .declarative
      description := "Passive cannot have direct object" },

    { grammatical := "the cat was chased by John"
      ungrammatical := "the cat was chased the dog"  -- object instead of by-phrase
      clauseType := .declarative
      description := "Passive agent marked with 'by', not bare NP" },

    -- Subject-aux agreement in passive
    { grammatical := "the ball was kicked"
      ungrammatical := "the balls was kicked"  -- agreement mismatch
      clauseType := .declarative
      description := "Passive auxiliary must agree with subject" }
  ]
}

end Phenomena.ArgumentStructure.Passive
