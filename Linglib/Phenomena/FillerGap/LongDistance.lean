/-
# Long-Distance Dependencies (Filler-Gap Constructions)

## The Phenomenon

Long-distance dependencies occur when an element (the "filler") is displaced
from its canonical position, leaving a "gap":

- Wh-questions: "What did you see _?"
- Relative clauses: "the book that I read _"
- Topicalization: "This book, I really like _"

## The Data

  (1a)  What did John see?           ✓  object wh-question
  (1b) *Did John see what?           ✗  wh-in-situ in matrix question

  (2a)  Who saw Mary?                ✓  subject wh-question (no aux needed)
  (2b) *Did who see Mary?            ✗  subject extraction with do-support

  (3a)  the book that John read      ✓  object relative clause
  (3b) *the book that read John      ✗  wrong word order in relative

  (4a)  John wonders what Mary saw   ✓  embedded wh-question
  (4b) *John wonders what saw Mary   ✗  wrong word order in embedded

Reference: Gibson (2025) "Syntax", MIT Press, Section 3.9
-/

import Linglib.Core.Basic

private def what : Word := ⟨"what", .Wh, { wh := true }⟩
private def did : Word := ⟨"did", .Aux, {}⟩
private def john : Word := ⟨"John", .D, { number := some .sg, person := some .third }⟩
private def see : Word := ⟨"see", .V, { valence := some .transitive, number := some .pl }⟩
private def who : Word := ⟨"who", .Wh, { wh := true }⟩
private def sees : Word := ⟨"sees", .V, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def mary : Word := ⟨"Mary", .D, { number := some .sg, person := some .third }⟩
private def does : Word := ⟨"does", .Aux, { number := some .sg, person := some .third }⟩
private def wonder : Word := ⟨"wonder", .V, { valence := some .transitive, number := some .pl }⟩
private def if_ : Word := ⟨"if", .C, {}⟩
private def think : Word := ⟨"think", .V, { valence := some .transitive, number := some .pl }⟩
private def that : Word := ⟨"that", .D, { number := some .sg }⟩
private def the : Word := ⟨"the", .D, {}⟩
private def boy : Word := ⟨"boy", .N, { number := some .sg, countable := some true }⟩
private def book : Word := ⟨"book", .N, { number := some .sg, countable := some true }⟩
private def reads : Word := ⟨"reads", .V, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def sleeps : Word := ⟨"sleeps", .V, { valence := some .intransitive, number := some .sg, person := some .third }⟩

namespace Phenomena.FillerGap.LongDistance

-- The Empirical Data

/-- Long-distance dependency minimal pairs -/
def longDistanceData : PhenomenonData := {
  name := "Long-Distance Dependencies"
  generalization := "Wh-phrases appear clause-initially but are interpreted in gap position"
  pairs := [
    -- Object wh-questions
    { grammatical := [what, did, john, see]
      ungrammatical := [did, john, see, what]
      clauseType := .matrixQuestion
      description := "Object wh-phrase must be fronted in matrix questions" },

    -- Subject wh-questions (no inversion needed)
    { grammatical := [who, sees, mary]
      ungrammatical := [does, who, see, mary]
      clauseType := .matrixQuestion
      description := "Subject wh-questions don't require do-support" },

    -- Embedded wh-questions
    { grammatical := [john, wonder, what, mary, sees]
      ungrammatical := [john, wonder, what, sees, mary]
      clauseType := .declarative
      description := "Embedded wh-clause has subject-verb order" }
  ]
}

/-- Relative clause minimal pairs -/
def relativeClauseData : PhenomenonData := {
  name := "Relative Clauses"
  generalization := "Relative pronouns introduce clauses that modify nouns, with a gap coindexed with the head"
  pairs := [
    -- Object relative
    { grammatical := [the, book, that, john, reads]
      ungrammatical := [the, book, that, reads, john]
      clauseType := .declarative
      description := "Object relative has subject-verb-gap order" },

    -- Subject relative
    { grammatical := [the, boy, that, sees, mary]
      ungrammatical := [the, boy, that, mary, sees]
      clauseType := .declarative
      description := "Subject relative has gap-verb-object order" }
  ]
}

/-- Complement clause minimal pairs -/
def complementClauseData : PhenomenonData := {
  name := "Complement Clauses"
  generalization := "Verbs like 'think' and 'wonder' take clausal complements"
  pairs := [
    -- That-complement
    { grammatical := [john, think, that, mary, sleeps]
      ungrammatical := [john, think, mary, that, sleeps]
      clauseType := .declarative
      description := "'that' must precede the embedded clause" },

    -- If-complement (embedded question)
    { grammatical := [john, wonder, if_, mary, sleeps]
      ungrammatical := [john, wonder, mary, if_, sleeps]
      clauseType := .declarative
      description := "'if' must precede the embedded clause" }
  ]
}

-- Specification Typeclass

/-- A grammar captures long-distance dependencies -/
class CapturesLongDistance (G : Type) [Grammar G] where
  grammar : G
  capturesWhQuestions : Grammar.capturesPhenomenon G grammar longDistanceData
  capturesRelatives : Grammar.capturesPhenomenon G grammar relativeClauseData
  capturesComplements : Grammar.capturesPhenomenon G grammar complementClauseData

-- Helper Functions

/-- Check if a word list has a wh-word in initial position -/
def hasInitialWh (ws : List Word) : Bool :=
  match ws.head? with
  | some w => w.features.wh
  | none => false

/-- Find the position of a wh-word -/
def findWhPosition (ws : List Word) : Option Nat :=
  ws.findIdx? (·.features.wh)

/-- Check if wh-word is fronted (at position 0, 1, or 2 for embedded) -/
def isWhFronted (ws : List Word) : Bool :=
  match findWhPosition ws with
  | some 0 => true
  | some 1 => ws[0]?.map (·.cat == .D) |>.getD false  -- embedded: "John wonders what..."
  | some 2 =>
    let firstIsD := ws[0]?.map (·.cat == .D) |>.getD false
    let secondIsV := ws[1]?.map (·.cat == .V) |>.getD false
    firstIsD && secondIsV
  | some _ => false
  | none => false

end Phenomena.FillerGap.LongDistance
