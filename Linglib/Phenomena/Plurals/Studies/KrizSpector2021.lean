import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Theories.Semantics.Homogeneity
import Linglib.Phenomena.Plurals.Studies.Kriz2016

/-!
# Križ & Spector (2021): Interpreting Plural Predication
@cite{kriz-spector-2021}

Interpreting Plural Predication: Homogeneity and Non-Maximality.
Linguistics and Philosophy, 44, 1131-1178.

## Core Contribution

Križ & Spector 2021 refine @cite{kriz-2016}'s pragmatic mechanism for
non-maximality. Where Križ 2016 used "Addressing an Issue" (no QUD cell
straddles the true/false boundary), K&S replace this with **strong relevance
filtering**: a candidate interpretation is relevant only if its truth
predicate is constant on each cell of the QUD partition.

## Bridge Theorems

This file proves the correspondence between the two accounts:

1. **`bivalent_addressing_iff_stronglyRelevant`**: For bivalent sentences
   (those modified by `all`), Križ 2016's Addressing constraint is equivalent
   to Križ & Spector 2021's strong relevance of the truth predicate to the QUD.

2. **`all_addressing_iff_relevant`**: Specialization to `all`-sentences:
   Addressing the QUD ↔ `allSatisfy` is strongly relevant.

These theorems connect two independently formalized mechanisms:
- `Semantics.Homogeneity.addressesIssue` (from Križ 2016)
- `Semantics.Lexical.Plural.Distributivity.isStronglyRelevantProp` (from K&S 2021)

showing they agree on the bivalent fragment.
-/

namespace Phenomena.Plurals.Studies.KrizSpector2021

open Core.Duality (Truth3)
open Semantics.Lexical.Plural.Distributivity
open Semantics.Homogeneity
open Phenomena.Plurals.Studies.Kriz2016

variable {Atom W : Type*} [DecidableEq Atom]

-- ============================================================================
-- Section 1: Addressing ↔ Strong Relevance for Bivalent Sentences
-- ============================================================================

/-! For bivalent sentences, the two pragmatic constraints are equivalent.
Križ 2016's Addressing says no QUD cell has both true and false worlds.
K&S 2021's strong relevance says the truth predicate is constant on each
cell. For bivalent sentences these coincide: if the predicate varies within
a cell, one world must be true and the other false (there is no gap). -/

/-- For bivalent sentences, Addressing ↔ strong relevance of the truth predicate.

The Addressing condition says no cell has both true and false worlds.
Strong relevance says the truth predicate is constant on each cell.
For bivalent sentences these are equivalent: if the predicate varies
within a cell, one world must be true and the other false (there is
no gap to break the dichotomy). -/
theorem bivalent_addressing_iff_stronglyRelevant (q : QUD W) (S : SentenceTV W)
    (hbiv : isBivalent S) :
    addressesIssue q S ↔ isStronglyRelevantProp q (bivalentPred S) := by
  constructor
  · -- Addressing → strong relevance
    intro hAddr w₁ w₂ hEquiv
    by_contra hNeq
    simp only [bivalentPred] at hNeq
    -- w₁ and w₂ have different truth values, both bivalent
    cases hbiv w₁ with
    | inl h₁ =>
      cases hbiv w₂ with
      | inl h₂ => exact hNeq (by rw [h₁, h₂])
      | inr h₂ => exact hAddr ⟨w₁, w₂, hEquiv, h₁, h₂⟩
    | inr h₁ =>
      cases hbiv w₂ with
      | inl h₂ =>
        have hEquiv' := q.symm w₁ w₂ ▸ hEquiv
        exact hAddr ⟨w₂, w₁, hEquiv', h₂, h₁⟩
      | inr h₂ => exact hNeq (by rw [h₁, h₂])
  · -- Strong relevance → Addressing
    intro hSR ⟨w₁, w₂, hEquiv, hTrue, hFalse⟩
    have := hSR w₁ w₂ hEquiv
    simp only [bivalentPred] at this
    rw [hTrue, hFalse] at this
    exact absurd this (by decide)

-- ============================================================================
-- Section 2: Specialization to `all`-Sentences
-- ============================================================================

/-! For `all`-sentences, the bridge specializes further: Addressing ↔
`allSatisfy` is strongly relevant to the QUD. This connects directly to
`nonMaximality_from_coarse_qud` in Distributivity.lean: when the QUD groups
an all-true world with a not-all-true world, the `all`-sentence fails to
address the issue, so `all` cannot be used non-maximally. -/

omit [DecidableEq Atom] in
/-- For `all`-sentences, Addressing ↔ `allSatisfy` is strongly relevant.

This bridges Križ 2016's pragmatic mechanism (Addressing) to K&S 2021's
filtering mechanism (strong relevance) for the specific case of universal
quantification over pluralities. -/
theorem all_addressing_iff_relevant (q : QUD W) (P : Atom → W → Bool)
    (x : Finset Atom) :
    addressesIssue q (allPluralTV P x) ↔
    isStronglyRelevantProp q (allSatisfy P x) := by
  rw [bivalent_addressing_iff_stronglyRelevant q _ (all_bivalent P x)]
  constructor <;> intro h w₁ w₂ hEquiv
  · have := h w₁ w₂ hEquiv
    simp only [bivalentPred, allPluralTV] at this
    split_ifs at this with h₁ h₂
    · simp_all
    · exact absurd this (by decide)
    · exact absurd this (by decide)
    · simp_all
  · have := h w₁ w₂ hEquiv
    simp only [bivalentPred, allPluralTV]
    congr 1; split_ifs with h₁ h₂ <;> (first | rfl | simp_all)

end Phenomena.Plurals.Studies.KrizSpector2021
