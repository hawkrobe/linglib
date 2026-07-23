import Linglib.Semantics.Plurality.Trivalent
import Linglib.Semantics.Homogeneity.Collective
import Linglib.Semantics.Homogeneity.Plural

/-!
# Križ & Spector (2021): Interpreting Plural Predication
[kriz-spector-2021]

Interpreting Plural Predication: Homogeneity and Non-Maximality.
Linguistics and Philosophy, 44, 1131-1178.

## Core Contribution

Križ & Spector 2021 refine [kriz-2016]'s pragmatic mechanism for
non-maximality. Where Križ 2016 used "Addressing an Question" (no QUD cell
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
- `Semantics.Homogeneity.isStronglyRelevantProp` (substrate, originating with K&S 2021)

showing they agree on the bivalent fragment.
-/

namespace KrizSpector2021

open Semantics.Plurality
open Semantics.Plurality.Trivalent
open Semantics.Homogeneity
open _root_.Trivalent (Prop3)

variable {Atom W : Type*}

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
no gap to break the dichotomy).

`bivalentPred S : W → Bool` is wrapped as `(· = true) : W → Prop` to feed the
Prop-typed `isStronglyRelevantProp`. -/
theorem bivalent_addressing_iff_stronglyRelevant (q : QUD W) (S : Prop3 W)
    (hbiv : S.isBivalent) :
    addressesIssue q S ↔ isStronglyRelevantProp q (fun w => bivalentPred S w = true) := by
  constructor
  · -- Addressing → strong relevance
    intro hAddr w₁ w₂ hEquiv
    simp only [bivalentPred, beq_iff_eq]
    -- w₁ and w₂ have the same truth value because they are q-equivalent
    cases hbiv w₁ with
    | inl h₁ =>
      cases hbiv w₂ with
      | inl h₂ => rw [h₁, h₂]
      | inr h₂ => exact absurd ⟨w₁, w₂, hEquiv, h₁, h₂⟩ hAddr
    | inr h₁ =>
      cases hbiv w₂ with
      | inl h₂ => exact absurd ⟨w₂, w₁, q.iseqv.symm hEquiv, h₂, h₁⟩ hAddr
      | inr h₂ => rw [h₁, h₂]
  · -- Strong relevance → Addressing
    intro hSR ⟨w₁, w₂, hEquiv, hTrue, hFalse⟩
    have hPred1 : bivalentPred S w₁ = true := by simp [bivalentPred, hTrue]
    have hPred2 : bivalentPred S w₂ = true := (hSR w₁ w₂ hEquiv).mp hPred1
    simp [bivalentPred, hFalse] at hPred2

-- ============================================================================
-- Section 2: Specialization to `all`-Sentences
-- ============================================================================

/-! For `all`-sentences, the bridge specializes further: Addressing ↔
`allSatisfy` is strongly relevant to the QUD. This connects directly to
`nonMaximality_from_coarse_qud` in CandidateInterpretation.lean: when the QUD groups
an all-true world with a not-all-true world, the `all`-sentence fails to
address the issue, so `all` cannot be used non-maximally. -/

/-- For `all`-sentences, Addressing ↔ `allSatisfy` is strongly relevant.

This bridges Križ 2016's pragmatic mechanism (Addressing) to K&S 2021's
filtering mechanism (strong relevance) for the specific case of universal
quantification over pluralities. Since `allPlural` is meta-assertion of the
bare plural by definition, the bridge is a pointwise-equivalence result via
`bivalentPred_allPlural_eq_allSatisfy`. -/
theorem all_addressing_iff_relevant (q : QUD W) (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    addressesIssue q (allPlural P x) ↔
    isStronglyRelevantProp q (allSatisfy P x) := by
  rw [bivalent_addressing_iff_stronglyRelevant q _ (isBivalent_allPlural P x)]
  refine ⟨fun h w₁ w₂ hEquiv => ?_, fun h w₁ w₂ hEquiv => ?_⟩
  · exact ((bivalentPred_allPlural_eq_allSatisfy P x w₁).symm.trans
           (h w₁ w₂ hEquiv)).trans (bivalentPred_allPlural_eq_allSatisfy P x w₂)
  · exact ((bivalentPred_allPlural_eq_allSatisfy P x w₁).trans
           (h w₁ w₂ hEquiv)).trans (bivalentPred_allPlural_eq_allSatisfy P x w₂).symm

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
    correspondence of [kriz-spector-2021] §3: the simple trivalent
    semantics IS truth-on-all-readings applied to the full candidate set.

    This is a restatement of `pluralTruthValue_eq_candidateSemantics` in
    terms of the candidate conjunction operator. -/
theorem candidateConjunction_matches_plural (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
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
    with `allPlural` (meta-assertion of the bare plural, by definition).
    This closes the triangle: ∀H ↔ allSatisfy ↔ allPlural. -/
theorem forallH_triangle [Fintype Atom] (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ allSatisfy P x w :=
  allViaForallH_iff_allSatisfy P x w

/-- The full bridge: the *all*-sentence is true iff `allViaForallH` holds.
    This formally connects Križ 2016's mechanism (gap removal) to K&S 2021's
    deeper derivation (`∀H`). The semantic contribution of `all` can be
    understood either as gap removal or as universal H-quantification —
    they are provably the same. -/
theorem allPlural_iff_forallH [Fintype Atom] (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allPlural P x w = .true ↔ allViaForallH P x w :=
  (allPlural_eq_true_iff P x w).trans (forallH_triangle P x w).symm

-- ============================================================================
-- Section 5: Non-Monotonic Context Finite Model
-- ============================================================================

/-! [kriz-spector-2021] §2.2.3, §3.1: The enriched candidate set
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
def nmRead : NMStudent → NMBook → NMWorld → Prop
  | .mary, _, .maryAll         => True
  | .mary, _, .bothAll         => True
  | .mary, _, .maryAllJohnA    => True
  | .mary, _, .noneRead        => False
  | .john, _, .maryAll         => False
  | .john, _, .bothAll         => True
  | .john, .a, .maryAllJohnA   => True
  | .john, .b, .maryAllJohnA   => False
  | .john, _, .noneRead        => False

instance nmRead.instDecidable : ∀ s b w, Decidable (nmRead s b w) := by
  intro s b w; cases s <;> cases b <;> cases w <;> unfold nmRead <;> infer_instance

def nmBooks : Finset NMBook := Finset.univ

-- Plural truth value for each student's reading
-- Mary reads the books: TRUE in maryAll/bothAll/maryAllJohnA, FALSE in noneRead
-- John reads the books: FALSE in maryAll, TRUE in bothAll, GAP in maryAllJohnA, FALSE in noneRead

theorem john_reads_gap_maryAllJohnA :
    pluralTruthValue (nmRead .john) nmBooks .maryAllJohnA = .indet := by native_decide

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
    candidateProp (nmRead .john) {.a} .maryAllJohnA := by decide

/-- But the maximal candidate is FALSE (John didn't read all books). -/
theorem maximal_candidate_false_at_gap :
    ¬ candidateProp (nmRead .john) nmBooks .maryAllJohnA := by decide

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

/-! [kriz-spector-2021] §3.3, Appendix: Upward homogeneity arises when
a predicate is true of a super-plurality containing x but not of x itself.
For example, "The soldiers of my brigade didn't surround the castle" is
false if the brigade *together with other soldiers* surrounded the castle.

The existing `generalisedTruthValue` in `Homogeneity/Collective.lean` captures this via the
`overlaps` relation. Here we prove the connection: when an overlapping
super-plurality satisfies P, the sentence about x is gapped, not false. -/

open Semantics.Homogeneity (generalisedTruthValue generalisedTruthValue_eq_true)

/-- Upward homogeneity: if P is false of x but true of some overlapping
    super-plurality in the domain, then the generalised truth value is GAP,
    not FALSE. The predicate's truth "leaks upward" through overlap.

    This captures [kriz-spector-2021] §3.3: "The soldiers of my brigade
    didn't surround the castle" is undefined (not false) when the brigade
    participated with other soldiers in surrounding the castle. -/
theorem upward_homogeneity_gap [DecidableEq Atom]
    (P : Finset Atom → Prop) [DecidablePred P]
    (domain : Finset (Finset Atom))
    (x : Finset Atom)
    (hPx : ¬ P x)
    (b : Finset Atom) (hb : b ∈ domain)
    (hov : Semantics.Homogeneity.overlaps x b)
    (hPb : P b) :
    generalisedTruthValue P domain x = .indet := by
  have hex : ∃ b ∈ domain, Semantics.Homogeneity.overlaps x b ∧ P b :=
    ⟨b, hb, hov, hPb⟩
  simp [generalisedTruthValue, if_neg hPx, if_pos hex]

end KrizSpector2021
