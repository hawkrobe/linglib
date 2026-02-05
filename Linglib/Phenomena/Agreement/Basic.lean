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

import Linglib.Core.Basic
import Linglib.Theories.Surface.Basic

private def he : Word := ⟨"he", .D, { person := some .third, number := some .sg, case_ := some .nom }⟩
private def sleeps : Word := ⟨"sleeps", .V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
private def they : Word := ⟨"they", .D, { person := some .third, number := some .pl, case_ := some .nom }⟩
private def sleep : Word := ⟨"sleep", .V, { valence := some .intransitive, number := some .pl }⟩
private def john : Word := ⟨"John", .D, { number := some .sg, person := some .third }⟩
private def mary : Word := ⟨"Mary", .D, { number := some .sg, person := some .third }⟩
private def laugh : Word := ⟨"laugh", .V, { valence := some .intransitive, number := some .pl }⟩
private def laughs : Word := ⟨"laughs", .V, { valence := some .intransitive, number := some .sg, person := some .third }⟩

namespace Phenomena.Agreement

-- The Empirical Data

/-- Subject-verb agreement data -/
def agreementData : PhenomenonData := {
  name := "Subject-Verb Agreement"
  generalization := "The verb must agree with the subject in number"
  pairs := [
    -- Pronoun subjects
    { grammatical := [he, sleeps]
      ungrammatical := [he, sleep]
      clauseType := .declarative
      description := "3sg pronoun requires 3sg verb" },

    { grammatical := [they, sleep]
      ungrammatical := [they, sleeps]
      clauseType := .declarative
      description := "Plural pronoun requires plural verb" },

    -- Proper name subjects (3sg)
    { grammatical := [john, sleeps]
      ungrammatical := [john, sleep]
      clauseType := .declarative
      description := "Proper name (3sg) requires 3sg verb" },

    { grammatical := [mary, laughs]
      ungrammatical := [mary, laugh]
      clauseType := .declarative
      description := "Proper name (3sg) requires 3sg verb" }
  ]
}

-- Tests

#eval Surface.agreementOk [he, sleeps]      -- true
#eval Surface.agreementOk [he, sleep]       -- false
#eval Surface.agreementOk [they, sleep]     -- true
#eval Surface.agreementOk [they, sleeps]    -- false
#eval Surface.agreementOk [john, sleeps]    -- true
#eval Surface.agreementOk [john, sleep]     -- false

end Phenomena.Agreement
