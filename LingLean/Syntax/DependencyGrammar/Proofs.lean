/-
# Dependency Grammar Proofs

Formal verification that dependency trees correctly capture linguistic phenomena.
-/

import LingLean.Syntax.DependencyGrammar.Basic
import LingLean.Syntax.DependencyGrammar.Examples
import LingLean.Syntax.Surface.Basic

open Lexicon DepGrammar

-- ============================================================================
-- Structure Proofs
-- ============================================================================

/-- John sleeps tree has unique heads -/
theorem johnSleeps_unique_heads :
    hasUniqueHeads johnSleepsTree = true := rfl

/-- John sleeps tree is acyclic -/
theorem johnSleeps_acyclic :
    isAcyclic johnSleepsTree = true := rfl

/-- John sleeps tree is projective -/
theorem johnSleeps_projective :
    isProjective johnSleepsTree = true := rfl

/-- John sees Mary tree is well-formed -/
theorem johnSeesMary_wellformed :
    isWellFormed johnSeesMaryTree = true := rfl

-- ============================================================================
-- Agreement Proofs
-- ============================================================================

/-- "he sleeps" has correct subject-verb agreement -/
theorem heSleeps_agreement :
    checkSubjVerbAgr heSleepsTree = true := rfl

/-- "he sleep" has incorrect subject-verb agreement -/
theorem heSleep_agreement_bad :
    checkSubjVerbAgr heSleepTree = false := rfl

/-- "these books" has correct det-noun agreement -/
theorem theseBooks_det_agr :
    checkDetNounAgr theseBooksTree = true := rfl

/-- "a girls" has incorrect det-noun agreement -/
theorem aGirls_det_agr_bad :
    checkDetNounAgr aGirlsTree = false := rfl

-- ============================================================================
-- Subcategorization Proofs
-- ============================================================================

/-- Intransitive verb with just subject is well-formed -/
theorem intransitive_subcat :
    checkVerbSubcat johnSleepsTree = true := rfl

/-- Transitive verb with subject and object is well-formed -/
theorem transitive_subcat :
    checkVerbSubcat johnSeesMaryTree = true := rfl

/-- Ditransitive verb with subject, iobj, obj is well-formed -/
theorem ditransitive_subcat :
    checkVerbSubcat johnGivesMaryBookTree = true := rfl

-- ============================================================================
-- Well-formedness Proofs
-- ============================================================================

/-- Well-formed tree: "he sleeps" -/
theorem heSleeps_wellformed :
    isWellFormed heSleepsTree = true := rfl

/-- Ill-formed tree: "he sleep" (agreement violation) -/
theorem heSleep_illformed :
    isWellFormed heSleepTree = false := rfl

/-- Well-formed tree: "the girl sleeps" -/
theorem theGirlSleeps_wellformed :
    isWellFormed theGirlSleepsTree = true := rfl

/-- Well-formed tree: "these books" -/
theorem theseBooks_wellformed :
    isWellFormed theseBooksTree = true := rfl

/-- Ill-formed tree: "a girls" (det-noun agreement) -/
theorem aGirls_illformed :
    isWellFormed aGirlsTree = false := rfl

-- ============================================================================
-- Projectivity Proofs
-- ============================================================================

/-- The example projective tree is indeed projective -/
theorem projective_example :
    isProjective projectiveTree = true := rfl

-- ============================================================================
-- Minimal Pair Proofs
-- ============================================================================

/-- Agreement minimal pair: grammatical vs ungrammatical distinguished -/
theorem agreement_minimal_pair :
    isWellFormed heSleepsTree = true ∧
    isWellFormed heSleepTree = false :=
  ⟨rfl, rfl⟩

/-- Det-noun agreement minimal pair -/
theorem det_noun_minimal_pair :
    isWellFormed theseBooksTree = true ∧
    isWellFormed aGirlsTree = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- Soundness: Well-formedness implies individual constraints
-- ============================================================================

/-- If a tree is well-formed, it has unique heads -/
theorem wellformed_implies_unique_heads (t : DepTree) :
    isWellFormed t = true → hasUniqueHeads t = true := by
  intro h
  simp only [isWellFormed] at h
  cases h_unique : hasUniqueHeads t
  · simp [h_unique] at h
  · rfl

/-- If a tree is well-formed, it is acyclic -/
theorem wellformed_implies_acyclic (t : DepTree) :
    isWellFormed t = true → isAcyclic t = true := by
  intro h
  simp only [isWellFormed] at h
  cases h_acyclic : isAcyclic t
  · simp [h_acyclic] at h
  · rfl

/-- If a tree is well-formed, subject-verb agreement holds -/
theorem wellformed_implies_subj_verb_agr (t : DepTree) :
    isWellFormed t = true → checkSubjVerbAgr t = true := by
  intro h
  simp only [isWellFormed] at h
  cases h_agr : checkSubjVerbAgr t
  · simp [h_agr] at h
  · rfl

-- ============================================================================
-- Framework Comparison Setup
-- ============================================================================

/-- Both Surface and Dependency grammars agree on "he sleeps" being grammatical -/
theorem surface_dep_agree_heSleeps :
    Surface.agreementOk [he, sleeps] = true ∧
    checkSubjVerbAgr heSleepsTree = true :=
  ⟨rfl, rfl⟩

/-- Both Surface and Dependency grammars agree on "he sleep" being ungrammatical -/
theorem surface_dep_agree_heSleep_bad :
    Surface.agreementOk [he, sleep] = false ∧
    checkSubjVerbAgr heSleepTree = false :=
  ⟨rfl, rfl⟩

/-- Both grammars agree on det-noun agreement -/
theorem surface_dep_agree_det_noun :
    (Surface.detNounAgrOk [a, girls] = false ∧ checkDetNounAgr aGirlsTree = false) ∧
    (Surface.detNounAgrOk [these, books] = true ∧ checkDetNounAgr theseBooksTree = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
