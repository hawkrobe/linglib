/-
# Subject-Verb Agreement

## The Phenomenon

In English, the verb must agree with its subject in number (and person for some forms).

## The Data

  (1a)  He walks.                    ✓  3sg subject, 3sg verb
  (1b) *He walk.                     ✗  3sg subject, pl verb

  (2a)  They walk.                   ✓  pl subject, pl verb
  (2b) *They walks.                  ✗  pl subject, 3sg verb

  (3a)  The cat sleeps.              ✓  sg subject, sg verb
  (3b) *The cat sleep.               ✗  sg subject, pl verb

  (4a)  The cats sleep.              ✓  pl subject, pl verb
  (4b) *The cats sleeps.             ✗  pl subject, sg verb
-/

import Linglib.Core.Grammar

namespace Phenomena.Agreement

/-- Subject-verb agreement data.

Pure empirical data with no theoretical commitments.
Theories interpret this via their Bridge modules. -/
def data : StringPhenomenonData := {
  name := "Subject-Verb Agreement"
  generalization := "The verb must agree with the subject in number"
  pairs := [
    -- Pronoun subjects
    { grammatical := "he sleeps"
      ungrammatical := "he sleep"
      clauseType := .declarative
      description := "3sg pronoun requires 3sg verb" },

    { grammatical := "they sleep"
      ungrammatical := "they sleeps"
      clauseType := .declarative
      description := "Plural pronoun requires plural verb" },

    -- Proper name subjects (3sg)
    { grammatical := "John sleeps"
      ungrammatical := "John sleep"
      clauseType := .declarative
      description := "Proper name (3sg) requires 3sg verb" },

    { grammatical := "Mary laughs"
      ungrammatical := "Mary laugh"
      clauseType := .declarative
      description := "Proper name (3sg) requires 3sg verb" }
  ]
}

end Phenomena.Agreement
