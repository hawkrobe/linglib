import Linglib.Core.Grammar

/-!
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

## Collins (2005) Data @cite{collins-2005}

### C-command asymmetries (§3)

In passive, the derived subject (= original object) c-commands the
by-phrase (= original subject). Evidence:

  (10a)  Every letter₁ was signed by its₁ author.   ✓  bound variable
  (10b) *Its₁ author was arrested by every cop₁.    ✗  no binding into subject
  (10c)  No letter was signed by anyone.             ✓  NPI licensed in by-phrase
  (10d) *Anyone was fired by no manager.             ✗  no NPI licensing of subject

### Particle placement (§3.1)

  (15a)  The cat was let out.                        ✓  passive with particle
  (16a) *The cat was let out the dog.                ✗  no post-particle object in passive
  (16b) *The cat was let the dog out.                ✗  no intercalated object in passive

### Auxiliary selection (§3.3)

  (23a)  John has kicked the ball.                   ✓  have + past participle
  (23b)  The ball was kicked.                        ✓  be + past participle
  (23c) *John has kicking the ball.                  ✗  have requires participle
  (23d) *The ball was kick.                          ✗  be-passive requires participle
-/

namespace Phenomena.ArgumentStructure.Passive

-- ============================================================================
-- § 1: Basic Passive Data
-- ============================================================================

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

-- ============================================================================
-- § 2: C-Command Asymmetries (Collins 2005, §3)
-- ============================================================================

/-- C-command data establishing that the derived subject in passive
    c-commands the by-phrase. This is predicted by smuggling: the object
    raises to Spec-TP (c-commanding everything below), while the external
    argument remains in Spec-vP (inside the by-phrase). -/
def cCommandData : StringPhenomenonData := {
  name := "Passive C-Command Asymmetries"
  generalization := "Passive subject c-commands by-phrase (binding, NPIs, scope)"
  pairs := [
    -- Bound variable: subject binds into by-phrase
    { grammatical := "every letter was signed by its author"
      ungrammatical := "its author was arrested by every cop"
      clauseType := .declarative
      description := "Bound variable: passive subject > by-phrase (Collins 2005, ex. 10a-b)" },

    -- NPI licensing: subject licenses NPI in by-phrase
    { grammatical := "no letter was signed by anyone"
      ungrammatical := "anyone was fired by no manager"
      clauseType := .declarative
      description := "NPI licensing: passive subject > by-phrase (Collins 2005, ex. 10c-d)" }
  ]
}

-- ============================================================================
-- § 3: Particle Evidence (Collins 2005, §3.1)
-- ============================================================================

/-- Particle data showing that in passive, the verb + particle form a
    constituent (PartP) that excludes the object. The object has been
    smuggled out of PartP to Spec-TP, stranding the particle with the verb. -/
def particleData : StringPhenomenonData := {
  name := "Passive Particle Placement"
  generalization := "In passive, particle stays with verb; no object can intervene"
  pairs := [
    { grammatical := "the cat was let out"
      ungrammatical := "the cat was let out the dog"
      clauseType := .declarative
      description := "Particle stranding in passive (Collins 2005, ex. 15-16)" }
  ]
}

-- ============================================================================
-- § 4: Auxiliary Selection (Collins 2005, §3.3)
-- ============================================================================

/-- Auxiliary evidence for PartP as a syntactic constituent.
    Both *have* and passive *be* select a participial complement (PartP).
    *Have* c-selects PartP directly; passive *be* requires PartP to
    move to Spec-VoiceP for licensing (Collins 2005, conditions 24-25). -/
def auxiliaryData : StringPhenomenonData := {
  name := "Auxiliary + Participle Selection"
  generalization := "Passive be and perfect have both require past participle (PartP)"
  pairs := [
    { grammatical := "John has kicked the ball"
      ungrammatical := "John has kicking the ball"
      clauseType := .declarative
      description := "Have c-selects participle (Collins 2005, ex. 23a,c)" },

    { grammatical := "the ball was kicked"
      ungrammatical := "the ball was kick"
      clauseType := .declarative
      description := "Passive be requires participle (Collins 2005, ex. 23b,d)" }
  ]
}

-- ============================================================================
-- § 5: Idiom Preservation (UTAH Evidence)
-- ============================================================================

/-- Idiom chunks preserved under passivization show that the object
    originates in the same VP-internal position in both active and passive.
    This supports UTAH: the external argument is generated in Spec-vP
    in both active and passive (Collins 2005, p. 95). -/
def idiomData : StringPhenomenonData := {
  name := "Idiom Preservation Under Passive"
  generalization := "Idiom chunks survive passivization (supports UTAH)"
  pairs := [
    { grammatical := "the shit was hit by the fan"
      ungrammatical := "the fan was hit by the shit"
      clauseType := .declarative
      description := "Idiom chunk preserved: 'the shit hit the fan' passivizes" },

    { grammatical := "advantage was taken of John"
      ungrammatical := "John was taken of advantage"
      clauseType := .declarative
      description := "Idiom chunk preserved: 'take advantage of' passivizes" }
  ]
}

end Phenomena.ArgumentStructure.Passive
