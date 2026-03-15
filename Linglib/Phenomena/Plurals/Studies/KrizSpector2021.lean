import Linglib.Theories.Semantics.Lexical.Plural.CandidateInterpretation
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

-- ============================================================================
-- Section 3: Candidate Conjunction = Trivalent Semantics (General Bridge)
-- ============================================================================

/-! The two independently developed mechanisms for non-maximality — pragmatic
(`communicatedContent` from Križ 2016) and semantic (candidate conjunction from
K&S 2021) — are connected by this bridge: `communicatedContent` is exactly the
set of worlds where the conjunction of strongly relevant candidates is usable.

For simple cases (single plural DP, distributive predicate), the candidate
conjunction reproduces `pluralTruthValue`. The pragmatic filtering via
strong relevance then determines the communicated content by selecting which
candidates matter. -/

/-- The candidate conjunction matches `pluralTruthValue` when all candidates
    are included (before relevance filtering). This is the central
    correspondence of @cite{kriz-spector-2021} §3: the simple trivalent
    semantics IS truth-on-all-readings applied to the full candidate set.

    This is a restatement of `pluralTruthValue_eq_candidateSemantics` in
    terms of the candidate conjunction operator. -/
theorem candidateConjunction_matches_plural (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    (pluralTruthValue P x w = .true ↔ trueOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .false ↔ falseOnAll (fullCandidateSet P x) w) :=
  let h := pluralTruthValue_eq_candidateSemantics P x w hne
  ⟨h.1, h.2.1⟩

-- ============================================================================
-- Section 4: Homogeneity Parameter Derivation
-- ============================================================================

/-! The H-parameter framework from `Distributivity.lean` provides a deeper
derivation of the same trivalent semantics. Here we connect the three
characterizations:
1. `pluralTruthValue` (supervaluation over atoms)
2. `fullCandidateSet` + conjunction (truth on all readings)
3. `allViaForallH` (∀H quantification)

All three agree: they are three views of the same trivalent denotation. -/

/-- The ∀H characterization of `all` agrees with `allSatisfy`, which agrees
    with `allPluralTV_eq_removeGap`. This closes the triangle:
    ∀H ↔ allSatisfy ↔ removeGap(barePluralTV). -/
theorem forallH_triangle [Fintype Atom] (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ allSatisfy P x w = true :=
  allViaForallH_iff_allSatisfy P x w

-- ============================================================================
-- Section 5: Non-Monotonic Context Finite Model
-- ============================================================================

/-! @cite{kriz-spector-2021} §2.2.3, §3.1: The enriched candidate set
correctly handles plural definites in non-monotonic contexts like
"Exactly one student read the books." Unlike the two-candidate approach
(Krifka 1996), the full candidate set ensures that the conjunction of
candidates captures both "one student read all" AND "the others read none."

We demonstrate this with a concrete model: 2 students, 2 books, 4 worlds.

| World       | Mary reads | John reads | "Exactly one read the books" |
|-------------|-----------|------------|------------------------------|
| maryAll     | a, b      | ∅          | TRUE (intended)              |
| bothAll     | a, b      | a, b       | FALSE                        |
| maryAllJohnA| a, b      | a          | GAP (underdetermined)        |
| noneRead    | ∅         | ∅          | FALSE                        |
-/

section NonMonotonicModel

inductive NMStudent where | mary | john
  deriving DecidableEq, Repr

inductive NMBook where | a | b
  deriving DecidableEq, Repr

inductive NMWorld where
  | maryAll       -- Mary reads {a,b}, John reads ∅
  | bothAll       -- Mary reads {a,b}, John reads {a,b}
  | maryAllJohnA  -- Mary reads {a,b}, John reads {a}
  | noneRead      -- Nobody reads anything
  deriving DecidableEq, Repr

instance : Fintype NMStudent where
  elems := {.mary, .john}
  complete := by intro x; cases x <;> simp

instance : Fintype NMBook where
  elems := {.a, .b}
  complete := by intro x; cases x <;> simp

instance : Fintype NMWorld where
  elems := {.maryAll, .bothAll, .maryAllJohnA, .noneRead}
  complete := by intro x; cases x <;> simp

/-- Did this student read this book in this world? -/
def nmRead : NMStudent → NMBook → NMWorld → Bool
  | .mary, _, .maryAll         => true
  | .mary, _, .bothAll         => true
  | .mary, _, .maryAllJohnA    => true
  | .mary, _, .noneRead        => false
  | .john, _, .maryAll         => false
  | .john, _, .bothAll         => true
  | .john, .a, .maryAllJohnA   => true
  | .john, .b, .maryAllJohnA   => false
  | .john, _, .noneRead        => false

def nmBooks : Finset NMBook := Finset.univ

-- Plural truth value for each student's reading
-- Mary reads the books: TRUE in maryAll/bothAll/maryAllJohnA, FALSE in noneRead
-- John reads the books: FALSE in maryAll, TRUE in bothAll, GAP in maryAllJohnA, FALSE in noneRead

theorem john_reads_gap_maryAllJohnA :
    pluralTruthValue (nmRead .john) nmBooks .maryAllJohnA = .gap := by native_decide

theorem john_reads_false_maryAll :
    pluralTruthValue (nmRead .john) nmBooks .maryAll = .false := by native_decide

theorem mary_reads_true_maryAll :
    pluralTruthValue (nmRead .mary) nmBooks .maryAll = .true := by native_decide

-- In maryAllJohnA, John's reading is a gap — he read some but not all.
-- On Krifka's two-candidate approach ("some" and "all"), the sentence
-- "Exactly one student read the books" would be underdetermined here.
-- On K&S's enriched candidate approach, the additional candidate
-- "John read book a" resolves the gap correctly.

/-- The singleton candidate {a} for John IS a candidate in the full set. -/
theorem singleton_a_is_candidate :
    candidateProp (nmRead .john) {.a} ∈ fullCandidateSet (nmRead .john) nmBooks := by
  exact ⟨{.a}, Finset.mem_powerset.mpr (by simp [nmBooks]),
         ⟨.a, Finset.mem_singleton.mpr rfl⟩, rfl⟩

/-- That singleton candidate is TRUE at maryAllJohnA (John did read book a). -/
theorem singleton_a_true_at_gap :
    candidateProp (nmRead .john) {.a} .maryAllJohnA = true := by native_decide

/-- But the maximal candidate is FALSE (John didn't read all books). -/
theorem maximal_candidate_false_at_gap :
    candidateProp (nmRead .john) nmBooks .maryAllJohnA = false := by native_decide

/-- The gap for John arises from candidate disagreement: some candidates
    are true (singleton {a}) and some are false (maximal {a,b}). This is
    precisely the K&S diagnosis of homogeneity as candidate disagreement. -/
theorem gap_is_candidate_disagreement :
    gapOnCandidates (fullCandidateSet (nmRead .john) nmBooks) .maryAllJohnA := by
  constructor
  · exact ⟨candidateProp (nmRead .john) {.a}, singleton_a_is_candidate,
           singleton_a_true_at_gap⟩
  · exact ⟨candidateProp (nmRead .john) nmBooks,
           ⟨nmBooks, Finset.mem_powerset.mpr (Finset.Subset.refl _),
            ⟨.a, by simp [nmBooks]⟩, rfl⟩,
           maximal_candidate_false_at_gap⟩

end NonMonotonicModel

-- ============================================================================
-- Section 6: Upward Homogeneity Bridge
-- ============================================================================

/-! @cite{kriz-spector-2021} §3.3, Appendix: Upward homogeneity arises when
a predicate is true of a super-plurality containing x but not of x itself.
For example, "The soldiers of my brigade didn't surround the castle" is
false if the brigade *together with other soldiers* surrounded the castle.

The existing `generalisedTV` in `Homogeneity.lean` captures this via the
`overlaps` relation. Here we prove the connection: when an overlapping
super-plurality satisfies P, the sentence about x is gapped, not false. -/

open Semantics.Homogeneity (generalisedTV generalisedTV_true_of_holds)

/-- Upward homogeneity: if P is false of x but true of some overlapping
    super-plurality in the domain, then the generalised truth value is GAP,
    not FALSE. The predicate's truth "leaks upward" through overlap.

    This captures @cite{kriz-spector-2021} §3.3: "The soldiers of my brigade
    didn't surround the castle" is undefined (not false) when the brigade
    participated with other soldiers in surrounding the castle. -/
theorem upward_homogeneity_gap
    (P : Finset Atom → Bool)
    (domain : Finset (Finset Atom))
    (x : Finset Atom)
    (hPx : P x = false)
    (b : Finset Atom) (hb : b ∈ domain)
    (hov : Semantics.Homogeneity.overlaps x b = true)
    (hPb : P b = true) :
    generalisedTV P domain x = .gap := by
  simp only [generalisedTV, hPx, Bool.false_eq_true, ite_false]
  have : ∃ b ∈ domain, Semantics.Homogeneity.overlaps x b = true ∧ P b = true :=
    ⟨b, hb, hov, hPb⟩
  simp [decide_eq_true this]

end Phenomena.Plurals.Studies.KrizSpector2021
