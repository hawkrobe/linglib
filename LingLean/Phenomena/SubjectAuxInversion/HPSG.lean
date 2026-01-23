/-
# HPSG Analysis of Subject-Auxiliary Inversion

HPSG handles inversion via:
1. An [INV ±] feature on clauses
2. Constraint: matrix interrogatives require [INV +]
3. Constraint: [INV +] requires auxiliary in initial position

This file connects the HPSG inversion analysis to the phenomenon specification.
-/

import LingLean.Phenomena.SubjectAuxInversion.Data
import LingLean.Syntax.HPSG.Inversion

open HPSG Lexicon

-- Note: This file uses HPSG.Inversion which imports HPSG.Features

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
-- Verify word orders for all minimal pairs
-- ============================================================================

-- Pair 1: Matrix wh-question
#eval auxPrecedesSubject [what, can, john, eat]  -- true (grammatical)
#eval auxPrecedesSubject [what, john, can, eat]  -- false (ungrammatical)

-- Pair 2: Matrix yes-no question
#eval auxPrecedesSubject [can, john, eat, pizza]  -- true (grammatical)
#eval auxPrecedesSubject [john, can, eat, pizza]  -- false (ungrammatical)

-- Pair 3: Embedded question (need to check the embedded clause)
-- "I wonder what John can eat" - the embedded clause is "what John can eat"
-- For embedded, we need subject-before-aux in the embedded clause
-- But our current model checks the whole sentence, which is tricky

-- For now, let's verify the core insight works for the simple cases

-- ============================================================================
-- Proofs for Pair 1: Matrix wh-question
-- ============================================================================

/-- "What can John eat?" is licensed as a matrix question -/
theorem pair1_grammatical : licenses [what, can, john, eat] .matrixQuestion :=
  licenses_matrix_aux_first _ rfl

/-- "What John can eat?" is NOT licensed as a matrix question -/
theorem pair1_ungrammatical : ¬ licenses [what, john, can, eat] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

-- ============================================================================
-- Proofs for Pair 2: Matrix yes-no question
-- ============================================================================

/-- "Can John eat pizza?" is licensed as a matrix question -/
theorem pair2_grammatical : licenses [can, john, eat, pizza] .matrixQuestion :=
  licenses_matrix_aux_first _ rfl

/-- "John can eat pizza?" is NOT licensed as a matrix question -/
theorem pair2_ungrammatical : ¬ licenses [john, can, eat, pizza] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

-- ============================================================================
-- Summary
-- ============================================================================

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
