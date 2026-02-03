/-
# Case Marking

## The Phenomenon

English pronouns show morphological case:
- Nominative case in subject position: I, he, she, we, they
- Accusative case in object position: me, him, her, us, them

## The Data

  (1a)  He sees her.                 ✓  nom subject, acc object
  (1b) *Him sees her.                ✗  acc in subject position
  (1c) *He sees she.                 ✗  nom in object position

  (2a)  They help us.                ✓  nom subject, acc object
  (2b) *Them help us.                ✗  acc in subject position
  (2c) *They help we.                ✗  nom in object position

  (3a)  I see him.                   ✓  nom subject, acc object
  (3b) *Me see him.                  ✗  acc in subject position
  (3c) *I see he.                    ✗  nom in object position
-/

import Linglib.Phenomena.Basic
import Linglib.Theories.Surface.Basic

open Lexicon

-- ============================================================================
-- The Empirical Data
-- ============================================================================

/-- Case marking data -/
def caseData : PhenomenonData := {
  name := "Case Marking"
  generalization := "Subjects require nominative case; objects require accusative case"
  pairs := [
    -- Subject case
    { grammatical := [he, sees, her]
      ungrammatical := [him, sees, her]
      clauseType := .declarative
      description := "Subject must be nominative, not accusative" },

    { grammatical := [they, see, us]
      ungrammatical := [them, see, us]
      clauseType := .declarative
      description := "Subject must be nominative, not accusative" },

    { grammatical := [i, see, him]
      ungrammatical := [me, see, him]
      clauseType := .declarative
      description := "Subject must be nominative, not accusative" },

    -- Object case
    { grammatical := [he, sees, her]
      ungrammatical := [he, sees, she]
      clauseType := .declarative
      description := "Object must be accusative, not nominative" },

    { grammatical := [they, see, us]
      ungrammatical := [they, see, we]
      clauseType := .declarative
      description := "Object must be accusative, not nominative" },

    { grammatical := [i, see, him]
      ungrammatical := [i, see, he]
      clauseType := .declarative
      description := "Object must be accusative, not nominative" }
  ]
}

-- ============================================================================
-- Tests
-- ============================================================================

#eval Surface.caseOk [he, sees, her]   -- true (nom subj, acc obj)
#eval Surface.caseOk [him, sees, her]  -- false (acc in subj position)
#eval Surface.caseOk [he, sees, she]   -- false (nom in obj position)
#eval Surface.caseOk [they, see, us]   -- true
#eval Surface.caseOk [them, see, us]   -- false
#eval Surface.caseOk [they, see, we]   -- false
