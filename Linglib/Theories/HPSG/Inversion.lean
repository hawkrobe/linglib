/-
# HPSG Analysis of Subject-Auxiliary Inversion

Inversion-specific constraints and licensing.
Builds on the general feature system from Features.lean.

## The Analysis (Sag, Wasow & Bender 2003)

1. Matrix questions require [INV +]
2. [INV +] requires auxiliary-initial order
3. Embedded questions require [INV -]
4. [INV -] requires subject-initial order

This derives the word order asymmetry between matrix and embedded questions.
-/

import Linglib.Theories.HPSG.Features
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

namespace HPSG

-- ============================================================================
-- Clause Type Constraints (Inversion-Specific)
-- ============================================================================

/-- Matrix questions require [INV +] -/
def matrixRequiresInvPlus (ct : ClauseType) (inv : Inv) : Prop :=
  ct = .matrixQuestion → inv = .plus

/-- Embedded questions require [INV -] -/
def embeddedRequiresInvMinus (ct : ClauseType) (inv : Inv) : Prop :=
  ct = .embeddedQuestion → inv = .minus

-- ============================================================================
-- Derived Word Order Predictions
-- ============================================================================

/-- Matrix questions have aux before subject -/
theorem matrix_has_aux_before_subject (inv : Inv) (ws : List Word)
    (hct : matrixRequiresInvPlus .matrixQuestion inv)
    (hord : invPlusImpliesAuxFirst inv ws) :
    auxPrecedesSubject ws = true := by
  have hinv : inv = .plus := hct rfl
  exact hord hinv

/-- Embedded questions have subject before aux -/
theorem embedded_has_subject_before_aux (inv : Inv) (ws : List Word)
    (hct : embeddedRequiresInvMinus .embeddedQuestion inv)
    (hord : invMinusImpliesSubjectFirst inv ws) :
    subjectPrecedesAux ws = true := by
  have hinv : inv = .minus := hct rfl
  exact hord hinv

-- ============================================================================
-- Licensing
-- ============================================================================

/-- A clause: words + INV feature + clause type -/
structure Clause where
  words : List Word
  inv : Inv
  clauseType : ClauseType

/-- Word order must match INV feature -/
def wordOrderMatchesInv (c : Clause) : Prop :=
  invPlusImpliesAuxFirst c.inv c.words ∧
  invMinusImpliesSubjectFirst c.inv c.words

/-- Well-formed clause -/
def wellFormed (c : Clause) : Prop :=
  wordOrderMatchesInv c ∧
  matrixRequiresInvPlus c.clauseType c.inv ∧
  embeddedRequiresInvMinus c.clauseType c.inv

/-- A word sequence is licensed for a clause type if some INV value works -/
def licenses (ws : List Word) (ct : ClauseType) : Prop :=
  ∃ inv : Inv, wellFormed ⟨ws, inv, ct⟩

-- ============================================================================
-- Licensing Theorems
-- ============================================================================

/-- Matrix questions with aux-first order are licensed -/
theorem licenses_matrix_aux_first (ws : List Word)
    (h : auxPrecedesSubject ws = true) :
    licenses ws .matrixQuestion := by
  refine ⟨.plus, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact λ _ => h
  · intro hinv; cases hinv
  · intro _; rfl
  · intro hct; cases hct

/-- Matrix questions with subject-first are NOT licensed -/
theorem not_licenses_matrix_subject_first (ws : List Word)
    (h : auxPrecedesSubject ws = false) :
    ¬ licenses ws .matrixQuestion := by
  intro ⟨inv, wf⟩
  obtain ⟨⟨hord, _⟩, hct, _⟩ := wf
  have hinv : inv = .plus := hct rfl
  have haux : auxPrecedesSubject ws = true := hord hinv
  rw [h] at haux
  cases haux

/-- Embedded questions with subject-first are licensed -/
theorem licenses_embedded_subject_first (ws : List Word)
    (h : subjectPrecedesAux ws = true) :
    licenses ws .embeddedQuestion := by
  refine ⟨.minus, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro hinv; cases hinv
  · exact λ _ => h
  · intro hct; cases hct
  · intro _; rfl

/-- Embedded questions with aux-first are NOT licensed -/
theorem not_licenses_embedded_aux_first (ws : List Word)
    (h : subjectPrecedesAux ws = false) :
    ¬ licenses ws .embeddedQuestion := by
  intro ⟨inv, wf⟩
  obtain ⟨⟨_, hord⟩, _, hct⟩ := wf
  have hinv : inv = .minus := hct rfl
  have hsubj : subjectPrecedesAux ws = true := hord hinv
  rw [h] at hsubj
  cases hsubj

-- ============================================================================
-- Verification
-- ============================================================================

open Lexicon

#eval auxPrecedesSubject [what, can, john, eat]   -- true
#eval auxPrecedesSubject [what, john, can, eat]   -- false
#eval subjectPrecedesAux [john, can, eat]         -- true
#eval subjectPrecedesAux [can, john, eat]         -- false

example : licenses [what, can, john, eat] .matrixQuestion :=
  licenses_matrix_aux_first _ rfl

example : ¬ licenses [what, john, can, eat] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

example : licenses [john, can, eat] .embeddedQuestion :=
  licenses_embedded_subject_first _ rfl

example : ¬ licenses [can, john, eat] .embeddedQuestion :=
  not_licenses_embedded_aux_first _ rfl

-- ============================================================================
-- Connect HPSG.licenses to Grammar.derives
-- ============================================================================

/-- HPSG licensing as a grammar -/
structure HPSGInversionGrammar where

instance : Grammar HPSGInversionGrammar where
  Derivation := List Word × ClauseType
  realizes d ws ct := d.1 = ws ∧ d.2 = ct
  derives _ ws ct := licenses ws ct

-- ============================================================================
-- Proofs for Inversion Minimal Pairs
-- ============================================================================

-- Pair 1: Matrix wh-question
#eval auxPrecedesSubject [what, can, john, eat]  -- true (grammatical)
#eval auxPrecedesSubject [what, john, can, eat]  -- false (ungrammatical)

-- Pair 2: Matrix yes-no question
#eval auxPrecedesSubject [can, john, eat, pizza]  -- true (grammatical)
#eval auxPrecedesSubject [john, can, eat, pizza]  -- false (ungrammatical)

/-- "What can John eat?" is licensed as a matrix question -/
theorem pair1_grammatical : licenses [what, can, john, eat] .matrixQuestion :=
  licenses_matrix_aux_first _ rfl

/-- "What John can eat?" is NOT licensed as a matrix question -/
theorem pair1_ungrammatical : ¬ licenses [what, john, can, eat] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

/-- "Can John eat pizza?" is licensed as a matrix question -/
theorem pair2_grammatical : licenses [can, john, eat, pizza] .matrixQuestion :=
  licenses_matrix_aux_first _ rfl

/-- "John can eat pizza?" is NOT licensed as a matrix question -/
theorem pair2_ungrammatical : ¬ licenses [john, can, eat, pizza] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

/-
The HPSG analysis correctly predicts:

| Sentence              | ClauseType     | Licensed? | Reason           |
|-----------------------|----------------|-----------|------------------|
| What can John eat?    | matrixQuestion | ✓         | aux < subj, INV+ |
| What John can eat?    | matrixQuestion | ✗         | subj < aux, need INV+ |
| Can John eat pizza?   | matrixQuestion | ✓         | aux < subj, INV+ |
| John can eat pizza?   | matrixQuestion | ✗         | subj < aux, need INV+ |

For embedded questions, we would need to extend the model to handle
complex sentences with embedded clauses.
-/

end HPSG
