/-
# Word Grammar Analysis of Subject-Auxiliary Inversion

Word Grammar (Hudson 1984, 1990) handles inversion via:
1. Lexical entries with argument structures specifying direction
2. Non-inverted aux: subject LEFT, main verb RIGHT
3. Inverted aux: subject RIGHT, main verb RIGHT
4. Lexical rule derives inverted from non-inverted

Reference: Hudson (1990), Gibson (2025) Section 3.5-3.6
-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.DependencyGrammar.Core.LexicalRules
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

namespace DepGrammar.Inversion

open DepGrammar

private abbrev what := Fragments.English.Pronouns.what.toWord
private abbrev can := Fragments.English.FunctionWords.can.toWord
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev eat := Fragments.English.Predicates.Verbal.eat.toWordPl
private abbrev pizza := Fragments.English.Nouns.pizza.toWordSg

-- ============================================================================
-- Inversion via Argument Structure Direction
-- ============================================================================

/-- Is this a nominal category that can be a subject? -/
def isSubjectCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Is this word a potential subject? Must be nominal and non-wh. -/
def isSubjectWord (w : Word) : Bool :=
  isSubjectCat w.cat && !w.features.wh

/-- Check if auxiliary precedes subject (inverted order) -/
def auxPrecedesSubject (ws : List Word) : Bool :=
  let auxPos := ws.findIdx? (·.cat == .AUX)
  let subjPos := ws.findIdx? isSubjectWord
  match auxPos, subjPos with
  | some a, some s => a < s
  | _, _ => false

/-- Check if subject precedes auxiliary (non-inverted order) -/
def subjectPrecedesAux (ws : List Word) : Bool :=
  let auxPos := ws.findIdx? (·.cat == .AUX)
  let subjPos := ws.findIdx? isSubjectWord
  match auxPos, subjPos with
  | some a, some s => s < a
  | _, _ => false

-- ============================================================================
-- Licensing via Argument Structure
-- ============================================================================

/-- License a sentence based on clause type and word order
    - Matrix questions require aux-before-subject (inverted)
    - Declaratives require subject-before-aux (non-inverted)
    - Embedded questions require subject-before-aux in embedded clause -/
def depGrammarLicenses (ws : List Word) (ct : ClauseType) : Bool :=
  match ct with
  | .matrixQuestion => auxPrecedesSubject ws
  | .declarative => subjectPrecedesAux ws || !ws.any (·.cat == .AUX)
  | .embeddedQuestion => subjectPrecedesAux ws  -- No inversion in embedded
  | .echo => true  -- Echo questions don't require inversion

-- ============================================================================
-- Example Trees
-- ============================================================================

/-- "What can John eat?" - Matrix wh-question (inverted)
    what ←obj─ can ─subj→ John
               └─aux→ eat
-/
def whatCanJohnEatTree : DepTree :=
  { words := [what, can, john, eat]
    deps := [⟨1, 2, .nsubj⟩, ⟨1, 3, .aux⟩, ⟨3, 0, .obj⟩]
    rootIdx := 1 }

/-- "*What John can eat?" - Ungrammatical as matrix question
    what ←obj─ eat ←aux─ can ←subj─ John
-/
def whatJohnCanEatTree : DepTree :=
  { words := [what, john, can, eat]
    deps := [⟨2, 1, .nsubj⟩, ⟨2, 3, .aux⟩, ⟨3, 0, .obj⟩]
    rootIdx := 2 }

/-- "Can John eat pizza?" - Matrix yes-no question (inverted)
    can ─subj→ John
     └─aux→ eat ─obj→ pizza
-/
def canJohnEatPizzaTree : DepTree :=
  { words := [can, john, eat, pizza]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .aux⟩, ⟨2, 3, .obj⟩]
    rootIdx := 0 }

/-- "*John can eat pizza?" - Ungrammatical as matrix question
    John ←subj─ can ─aux→ eat ─obj→ pizza
-/
def johnCanEatPizzaTree : DepTree :=
  { words := [john, can, eat, pizza]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .aux⟩, ⟨2, 3, .obj⟩]
    rootIdx := 1 }

-- ============================================================================
-- Tests
-- ============================================================================

-- Pair 1: Matrix wh-question
#eval auxPrecedesSubject [what, can, john, eat]  -- true (grammatical)
#eval auxPrecedesSubject [what, john, can, eat]  -- false (ungrammatical)

-- Pair 2: Matrix yes-no question
#eval auxPrecedesSubject [can, john, eat, pizza]  -- true (grammatical)
#eval auxPrecedesSubject [john, can, eat, pizza]  -- false (ungrammatical)

-- Licensing
#eval depGrammarLicenses [what, can, john, eat] .matrixQuestion  -- true
#eval depGrammarLicenses [what, john, can, eat] .matrixQuestion  -- false
#eval depGrammarLicenses [can, john, eat, pizza] .matrixQuestion -- true
#eval depGrammarLicenses [john, can, eat, pizza] .matrixQuestion -- false

-- ============================================================================
-- Dependency Grammar as Grammar Instance
-- ============================================================================

/-- Dependency grammar for inversion -/
structure DepGrammarInversion where

instance : Grammar DepGrammarInversion where
  Derivation := List Word × ClauseType
  realizes d ws ct := d.1 = ws ∧ d.2 = ct
  derives _ ws ct := depGrammarLicenses ws ct = true

-- ============================================================================
-- Proofs for Pair 1: Matrix wh-question
-- ============================================================================

/-- "What can John eat?" is licensed as a matrix question -/
theorem pair1_grammatical :
    depGrammarLicenses [what, can, john, eat] .matrixQuestion = true := rfl

/-- "What John can eat?" is NOT licensed as a matrix question -/
theorem pair1_ungrammatical :
    depGrammarLicenses [what, john, can, eat] .matrixQuestion = false := rfl

-- ============================================================================
-- Proofs for Pair 2: Matrix yes-no question
-- ============================================================================

/-- "Can John eat pizza?" is licensed as a matrix question -/
theorem pair2_grammatical :
    depGrammarLicenses [can, john, eat, pizza] .matrixQuestion = true := rfl

/-- "John can eat pizza?" is NOT licensed as a matrix question -/
theorem pair2_ungrammatical :
    depGrammarLicenses [john, can, eat, pizza] .matrixQuestion = false := rfl

-- ============================================================================
-- Connection to Argument Structure Analysis
-- ============================================================================

/-- The inverted tree satisfies the inverted argument structure -/
theorem inverted_tree_satisfies_inv_argstr :
    satisfiesArgStr canJohnSleepTree 0 argStr_AuxInv = true := rfl

/-- The non-inverted tree satisfies the non-inverted argument structure -/
theorem noninverted_tree_satisfies_argstr :
    satisfiesArgStr johnCanSleepTree 1 argStr_Aux = true := rfl

/-
The Dependency Grammar analysis correctly predicts:

| Sentence              | ClauseType     | Licensed? | Reason                    |
|-----------------------|----------------|-----------|---------------------------|
| What can John eat?    | matrixQuestion | ✓         | aux < subj (inverted)     |
| What John can eat?    | matrixQuestion | ✗         | subj < aux (not inverted) |
| Can John eat pizza?   | matrixQuestion | ✓         | aux < subj (inverted)     |
| John can eat pizza?   | matrixQuestion | ✗         | subj < aux (not inverted) |

The key insight from Gibson: Inversion is captured by the lexical rule that
changes the subject's direction from LEFT to RIGHT in the argument structure.
-/

end DepGrammar.Inversion
