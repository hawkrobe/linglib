/-
# Subject-Auxiliary Inversion in English

## The Phenomenon

Matrix questions in English require the finite auxiliary to precede the subject;
embedded questions do not.

## The Data

  (1a)  What can John eat?              ✓  matrix wh-question
  (1b) *What John can eat?              ✗  (as matrix question)

  (2a)  Can John eat pizza?             ✓  matrix yes-no question
  (2b) *John can eat pizza?             ✗  (as yes-no question)

  (3a)  I wonder what John can eat.     ✓  embedded question
  (3b) *I wonder what can John eat.     ✗
-/

import Linglib.Core.Basic

private def what : Word := ⟨"what", .Wh, { wh := true }⟩
private def can : Word := ⟨"can", .Aux, {}⟩
private def john : Word := ⟨"John", .D, { number := some .sg, person := some .third }⟩
private def eat : Word := ⟨"eat", .V, { valence := some .transitive, number := some .pl }⟩
private def pizza : Word := ⟨"pizza", .N, { number := some .sg }⟩
private def i : Word := ⟨"I", .D, { person := some .first, number := some .sg, case_ := some .nom }⟩
private def wonder : Word := ⟨"wonder", .V, { valence := some .transitive, number := some .pl }⟩

-- The Empirical Data

/-- The core inversion data -/
def inversionData : PhenomenonData := {
  name := "Subject-Auxiliary Inversion"
  generalization := "Matrix questions require aux-subject order; embedded questions require subject-aux order"
  pairs := [
    { grammatical := [what, can, john, eat]
      ungrammatical := [what, john, can, eat]
      clauseType := .matrixQuestion
      description := "Matrix wh-question requires inversion" },

    { grammatical := [can, john, eat, pizza]
      ungrammatical := [john, can, eat, pizza]
      clauseType := .matrixQuestion
      description := "Matrix yes-no question requires inversion" },

    { grammatical := [i, wonder, what, john, can, eat]
      ungrammatical := [i, wonder, what, can, john, eat]
      clauseType := .embeddedQuestion
      description := "Embedded question prohibits inversion" }
  ]
}

-- Specification Typeclass

/-- A grammar captures subject-aux inversion -/
class CapturesInversion (G : Type) [Grammar G] where
  grammar : G
  captures : Grammar.capturesPhenomenon G grammar inversionData

-- Helper Functions

/-- Check if a word list has aux-before-subject order -/
def hasAuxSubjectOrder (ws : List Word) : Option (Nat × Nat) :=
  let auxPos := ws.findIdx? (·.cat == Cat.Aux)
  let subjPos := ws.findIdx? (·.cat == Cat.D)
  match auxPos, subjPos with
  | some a, some s => if a < s then some (a, s) else none
  | _, _ => none

/-- Check if a word list has subject-before-aux order -/
def hasSubjectAuxOrder (ws : List Word) : Option (Nat × Nat) :=
  let auxPos := ws.findIdx? (·.cat == Cat.Aux)
  let subjPos := ws.findIdx? (·.cat == Cat.D)
  match auxPos, subjPos with
  | some a, some s => if s < a then some (s, a) else none
  | _, _ => none

-- Examples

#eval wordsToString (inversionData.pairs[0]?.map (·.grammatical) |>.getD [])
#eval wordsToString (inversionData.pairs[0]?.map (·.ungrammatical) |>.getD [])
#eval hasAuxSubjectOrder [what, can, john, eat]  -- some (1, 2)
#eval hasSubjectAuxOrder [what, john, can, eat]  -- some (1, 2)
