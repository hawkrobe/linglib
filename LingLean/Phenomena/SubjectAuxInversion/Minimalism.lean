/-
# Minimalist Analysis of Subject-Auxiliary Inversion

Minimalism handles inversion via T-to-C movement:
1. Questions have a [+Q] feature on C that needs checking
2. T (bearing the auxiliary) moves to C to check this feature
3. This places the auxiliary before the subject (which is in Spec,TP)

This file connects the Minimalist inversion analysis to the phenomenon specification.
-/

import LingLean.Phenomena.SubjectAuxInversion.Data
import LingLean.Syntax.Minimalism.Inversion

open Minimalism Lexicon

-- ============================================================================
-- Verify word orders for all minimal pairs
-- ============================================================================

-- Pair 1: Matrix wh-question
#eval wordsHaveTBeforeSubject [what, can, john, eat]  -- true (grammatical)
#eval wordsHaveTBeforeSubject [what, john, can, eat]  -- false (ungrammatical)

-- Pair 2: Matrix yes-no question
#eval wordsHaveTBeforeSubject [can, john, eat, pizza]  -- true (grammatical)
#eval wordsHaveTBeforeSubject [john, can, eat, pizza]  -- false (ungrammatical)

-- ============================================================================
-- Proofs for Pair 1: Matrix wh-question
-- ============================================================================

/-- "What can John eat?" is licensed as a matrix question -/
theorem pair1_grammatical : licenses [what, can, john, eat] .matrixQuestion :=
  licenses_matrix_t_first _ rfl

/-- "What John can eat?" is NOT licensed as a matrix question -/
theorem pair1_ungrammatical : ¬ licenses [what, john, can, eat] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

-- ============================================================================
-- Proofs for Pair 2: Matrix yes-no question
-- ============================================================================

/-- "Can John eat pizza?" is licensed as a matrix question -/
theorem pair2_grammatical : licenses [can, john, eat, pizza] .matrixQuestion :=
  licenses_matrix_t_first _ rfl

/-- "John can eat pizza?" is NOT licensed as a matrix question -/
theorem pair2_ungrammatical : ¬ licenses [john, can, eat, pizza] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

-- ============================================================================
-- Comparison: HPSG vs Minimalism
-- ============================================================================

/-
Both frameworks predict the same surface patterns:

| Sentence              | ClauseType     | HPSG           | Minimalism      |
|-----------------------|----------------|----------------|-----------------|
| What can John eat?    | matrixQuestion | INV+ → aux<subj| T-to-C → T<Subj |
| What John can eat?    | matrixQuestion | *needs INV+    | *needs T-to-C   |
| Can John eat pizza?   | matrixQuestion | INV+ → aux<subj| T-to-C → T<Subj |
| John can eat pizza?   | matrixQuestion | *needs INV+    | *needs T-to-C   |

The mechanisms differ:
- HPSG: [INV+] feature constrains word order directly (declarative)
- Minimalism: T-to-C movement derives word order (derivational)

But the predictions are identical for these cases.

Question for future work: Are there cases where the frameworks diverge?
(e.g., languages with different clause structures, or complex sentences)
-/
