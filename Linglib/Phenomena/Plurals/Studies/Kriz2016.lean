import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Core.Semantics.Kleene
import Linglib.Phenomena.Plurals.NonMaximality
import Linglib.Phenomena.Plurals.Homogeneity

/-!
# Križ (2016): Homogeneity, Non-Maximality, and All
@cite{kriz-2016}

Homogeneity, Non-Maximality, and All. Journal of Semantics 33(3): 493-539.

## Core Contributions

Non-maximal readings of plural definites ("The professors smiled" true even if
Smith didn't) arise from the interaction of two independent components:

1. **Homogeneity** (semantic): plural predication yields a three-valued truth
   value — true (all satisfy), false (none satisfy), or gap (some but not all).

2. **Weakened Quality** (pragmatic): the maxim of quality is weakened to "say
   only what is true enough for current purposes," where "current purposes"
   are formalized as an issue (partition of possible worlds).

The semantic effect of `all` is to remove the extension gap, making positive
and negative extensions complementary. This prevents non-maximal readings
because the pragmatic mechanism (Sufficient Truth + Addressing) has no gap
to exploit.

## Key Definitions

- **Positive/negative extension**: ⟦S⟧⁺ = {w | S true at w}, ⟦S⟧⁻ = {w | S false at w}
- **Homogeneous sentence**: ⟦S⟧⁺ ∪ ⟦S⟧⁻ ≠ W (the gap is non-empty)
- **Sufficient Truth**: S is "true enough" at w wrt issue I iff ∃w' ∈ ⟦S⟧⁺ s.t. w ≈_I w'
- **Addressing an Issue**: S may address I only if no cell overlaps both ⟦S⟧⁺ and ⟦S⟧⁻
- **Communicated Content**: the set of worlds indistinguishable (under I) from ⟦S⟧⁺

## Connection to Križ & Spector 2021

The later K&S account (formalized in `Distributivity.lean`) replaces Sufficient
Truth with candidate interpretation filtering via strong relevance. We prove the
correspondence: for bivalent sentences (those with `all`), Addressing an Issue
is equivalent to strong relevance of the truth predicate to the QUD.

## Finite Model

A concrete 4-world model demonstrates end-to-end predictions: "the professors
smiled" is usable at a gap-world under a coarse issue but not under a fine one,
and adding "all" blocks non-maximal use entirely.
-/

namespace Phenomena.Plurals.Studies.Kriz2016

open Semantics.Lexical.Plural.Distributivity

variable {Atom W : Type*} [DecidableEq Atom]

-- ============================================================================
-- Section 1: Sentence Extensions
-- ============================================================================

/-- A trivalent sentence denotation: maps worlds to truth values. -/
abbrev SentenceTV (W : Type*) := W → TruthValue

/-- Positive extension: worlds where the sentence is true. -/
def posExt (S : SentenceTV W) : Set W := {w | S w = .true}

/-- Negative extension: worlds where the sentence is false. -/
def negExt (S : SentenceTV W) : Set W := {w | S w = .false}

/-- Extension gap: worlds where the sentence is neither true nor false. -/
def gapExt (S : SentenceTV W) : Set W := {w | S w = .gap}

/-- The three extensions partition the world space. -/
theorem extensions_partition (S : SentenceTV W) (w : W) :
    w ∈ posExt S ∨ w ∈ negExt S ∨ w ∈ gapExt S := by
  simp only [posExt, negExt, gapExt, Set.mem_setOf_eq]
  cases S w <;> simp

/-- The three extensions are pairwise disjoint. -/
theorem posExt_negExt_disjoint (S : SentenceTV W) :
    posExt S ∩ negExt S = ∅ := by
  ext w; simp only [posExt, negExt, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_empty_iff_false]
  exact ⟨λ ⟨h₁, h₂⟩ => by rw [h₁] at h₂; exact absurd h₂ (by decide), False.elim⟩

/-- A sentence is homogeneous if its extension gap is non-empty (Definition 2).
Homogeneity is the source of non-maximal readings: the gap creates worlds
that are neither true nor false, which the pragmatic mechanism can exploit. -/
def isHomogeneous (S : SentenceTV W) : Prop := gapExt S ≠ ∅

-- ============================================================================
-- Section 2: Plural Predication as Sentence Extension
-- ============================================================================

/-- The bare plural sentence "the Xs are P" as a trivalent sentence. -/
def barePluralTV (P : Atom → W → Bool) (x : Finset Atom) : SentenceTV W :=
  λ w => pluralTruthValue P x w

/-- The `all`-sentence "all the Xs are P" as a bivalent sentence.
`all` removes homogeneity: the truth value is always true or false. -/
def allPluralTV (P : Atom → W → Bool) (x : Finset Atom) : SentenceTV W :=
  λ w => if allSatisfy P x w then .true else .false

omit [DecidableEq Atom] in
/-- `all` eliminates the extension gap. -/
theorem all_no_gap (P : Atom → W → Bool) (x : Finset Atom) :
    gapExt (allPluralTV P x) = ∅ := by
  ext w; simp only [gapExt, allPluralTV, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  split <;> simp

omit [DecidableEq Atom] in
/-- `all` removes homogeneity: the `all`-sentence is never homogeneous.
Corresponds to `HomogeneityRemover.all` in `Homogeneity.lean`. -/
theorem all_not_homogeneous (P : Atom → W → Bool) (x : Finset Atom) :
    ¬isHomogeneous (allPluralTV P x) :=
  fun h => h (all_no_gap P x)

omit [DecidableEq Atom] in
/-- A bare plural is homogeneous whenever a gap-world exists: the existence
of a world where some-but-not-all atoms satisfy P makes the sentence
homogeneous, enabling non-maximal readings via Sufficient Truth. -/
theorem bare_plural_homogeneous (P : Atom → W → Bool) (x : Finset Atom)
    (w : W) (hGap : barePluralTV P x w = .gap) :
    isHomogeneous (barePluralTV P x) := by
  intro h; rw [Set.eq_empty_iff_forall_notMem] at h
  exact h w hGap

/-- Positive extensions agree: bare plural and `all`-sentence are true
in the same worlds. -/
theorem all_posExt_eq (P : Atom → W → Bool) (x : Finset Atom) :
    posExt (allPluralTV P x) = posExt (barePluralTV P x) := by
  ext w; simp only [posExt, allPluralTV, barePluralTV, Set.mem_setOf_eq]
  constructor
  · intro h; split_ifs at h; (simp_all [pluralTruthValue])
  · intro h
    rw [pluralTruthValue_eq_true_iff] at h
    simp [h]

omit [DecidableEq Atom] in
/-- `all` absorbs the gap into the negative extension: the negative extension
of the `all`-sentence equals the union of the bare plural's negative extension
and gap. -/
theorem all_negExt_eq (P : Atom → W → Bool) (x : Finset Atom) :
    negExt (barePluralTV P x) ∪ gapExt (barePluralTV P x) =
    negExt (allPluralTV P x) := by
  ext w; simp only [negExt, gapExt, allPluralTV, barePluralTV, Set.mem_union,
    Set.mem_setOf_eq]
  simp only [pluralTruthValue]
  split_ifs with h1 h2 <;> simp_all

-- ============================================================================
-- Section 3: Sufficient Truth and Addressing
-- ============================================================================

/-- Sufficient Truth: a sentence S is "true enough" at world w relative to
issue I (modeled as a QUD) iff there is a world w' that is I-equivalent to w
where S is literally true.

This weakens the standard maxim of quality: a speaker need not assert
something literally true, only something equivalent to something true
for current purposes. -/
def sufficientlyTrue (q : QUD W) (S : SentenceTV W) (w : W) : Prop :=
  ∃ w', q.sameAnswer w w' = true ∧ S w' = .true

/-- Literal truth implies sufficient truth (for any issue). -/
theorem literal_imp_sufficient (q : QUD W) (S : SentenceTV W) (w : W)
    (h : S w = .true) : sufficientlyTrue q S w :=
  ⟨w, q.refl w, h⟩

/-- Addressing an Issue: S may be used to address issue I only if no
cell of I overlaps with both the positive and the negative extension of S.

If a cell contains both true-worlds and false-worlds, then the distinction
between S being true and S being false is relevant to the issue, and S
cannot be used loosely. Gap-worlds are fine — they are "hushed up." -/
def addressesIssue (q : QUD W) (S : SentenceTV W) : Prop :=
  ¬∃ w₁ w₂, q.sameAnswer w₁ w₂ = true ∧ S w₁ = .true ∧ S w₂ = .false

/-- A sentence may be used at w iff: (1) S is not false at w,
(2) S is sufficiently true at w, and (3) S addresses the issue. -/
def usable (q : QUD W) (S : SentenceTV W) (w : W) : Prop :=
  S w ≠ .false ∧ sufficientlyTrue q S w ∧ addressesIssue q S

-- ============================================================================
-- Section 4: The Effect of `all`
-- ============================================================================

/-- A sentence is bivalent if it has no extension gap. -/
def isBivalent (S : SentenceTV W) : Prop :=
  ∀ w, S w = .true ∨ S w = .false

omit [DecidableEq Atom] in
/-- `all`-sentences are bivalent. -/
theorem all_bivalent (P : Atom → W → Bool) (x : Finset Atom) :
    isBivalent (allPluralTV P x) := by
  intro w; simp only [allPluralTV]; split_ifs <;> simp

/-- For bivalent sentences, Sufficient Truth at a gap-world is vacuous
(there are no gap-worlds). -/
theorem bivalent_no_gap_sufficient (q : QUD W) (S : SentenceTV W) (hbiv : isBivalent S)
    (w : W) :
    sufficientlyTrue q S w → S w = .true ∨ S w = .false :=
  λ _ => hbiv w

/-- For bivalent sentences, usability reduces to literal truth + addressing.
A bivalent sentence is usable at w iff it is literally true AND it addresses
the issue. Sufficient Truth adds nothing because there are no gap-worlds
where it could weaken the requirement. -/
theorem bivalent_usable_iff_true_and_addresses (q : QUD W) (S : SentenceTV W)
    (hbiv : isBivalent S) (w : W) :
    usable q S w ↔ S w = .true ∧ addressesIssue q S := by
  constructor
  · intro ⟨hNotFalse, _, hAddr⟩
    exact ⟨by cases hbiv w with | inl h => exact h | inr h => exact absurd h hNotFalse, hAddr⟩
  · intro ⟨hTrue, hAddr⟩
    exact ⟨by simp [hTrue], literal_imp_sufficient q S w hTrue, hAddr⟩

omit [DecidableEq Atom] in
/-- `all` prevents non-maximal use: if an `all`-sentence is usable at w,
then all atoms literally satisfy P at w.

This is the headline result of the paper's analysis of `all`. The bare
plural "the Xs are P" can be used non-maximally (at gap-worlds where
some but not all Xs satisfy P), but "all the Xs are P" cannot — usability
forces literal truth. -/
theorem all_prevents_nonmax (q : QUD W) (P : Atom → W → Bool) (x : Finset Atom)
    (w : W) (h : usable q (allPluralTV P x) w) : allSatisfy P x w = true := by
  cases h_eq : allSatisfy P x w with
  | true => rfl
  | false => exact absurd (show allPluralTV P x w = .false by simp [allPluralTV, h_eq]) h.1

omit [DecidableEq Atom] in
/-- Unmentionability of exceptions (§4.1): if the `all`-sentence is usable
at w, there are no exceptions to mention. "#Although all the professors
smiled, Smith didn't" is contradictory — `all` forces literal truth, so any
exception makes the sentence false, and false sentences cannot be used. -/
theorem all_exceptions_unmentionable (q : QUD W) (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) (a : Atom) (ha : a ∈ x)
    (h : usable q (allPluralTV P x) w) : P a w = true := by
  have := all_prevents_nonmax q P x w h
  simp only [allSatisfy, decide_eq_true_eq] at this
  exact this a ha

-- ============================================================================
-- Section 5: Communicated Content
-- ============================================================================

/-- The communicated content of S relative to issue I: the set of worlds
the hearer considers possible after hearing S.

This is the union of all cells of I that overlap with the positive
extension of S. Equivalently, the set of worlds that are I-equivalent
to some world where S is literally true.

The hearer infers not that S is literally true, but that the actual world
is indistinguishable (relative to current purposes) from one where S is
literally true. For bivalent sentences that address the issue, communicated
content collapses to literal truth (no pragmatic weakening possible). -/
def communicatedContent (q : QUD W) (S : SentenceTV W) : Set W :=
  {w | sufficientlyTrue q S w}

/-- Literal truth is always communicated. -/
theorem posExt_subset_communicated (q : QUD W) (S : SentenceTV W) :
    posExt S ⊆ communicatedContent q S :=
  λ _ hw => literal_imp_sufficient q S _ hw

/-- For bivalent sentences that address the issue, communicated content
equals the positive extension — no pragmatic weakening is possible.

If S is bivalent, every world is either true or false. If a false world
were in the communicated content, there would be a true world in the same
cell, contradicting Addressing. So only true worlds are communicated. -/
theorem bivalent_communicated_eq_posExt (q : QUD W) (S : SentenceTV W)
    (hbiv : isBivalent S) (hAddr : addressesIssue q S) :
    communicatedContent q S = posExt S := by
  ext w
  constructor
  · intro ⟨w', hEq, hTrue⟩
    cases hbiv w with
    | inl h => exact h
    | inr hFalse =>
      have hSymm : q.sameAnswer w' w = true := by rw [q.symm]; exact hEq
      exact absurd ⟨w', w, hSymm, hTrue, hFalse⟩ hAddr
  · exact literal_imp_sufficient q S w

-- ============================================================================
-- Section 6: Bridge to Križ & Spector 2021 (Distributivity.lean)
-- ============================================================================

/-! For bivalent sentences, Addressing an Issue is equivalent to the truth
predicate being strongly relevant to the QUD. This connects Križ 2016's
pragmatic mechanism to Križ & Spector 2021's strong relevance filtering. -/

section Bridge

variable [Fintype W] [DecidableEq W]

/-- Extract the Bool truth predicate from a bivalent sentence. -/
def bivalentPred (S : SentenceTV W) : BProp W :=
  λ w => S w == .true

omit [DecidableEq Atom] [Fintype W] [DecidableEq W] in
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

omit [DecidableEq Atom] [Fintype W] [DecidableEq W] in
/-- Corollary: for `all`-sentences, Addressing ↔ `allSatisfy` is strongly
relevant to the QUD. This connects directly to `nonMaximality_from_coarse_qud`
in Distributivity.lean: when the QUD groups an all-true world with a
not-all-true world, the `all`-sentence fails to address the issue,
so `all` cannot be used non-maximally. -/
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
    · simp at this
    · simp at this
    · simp_all
  · simp only [bivalentPred, allPluralTV]
    have := h w₁ w₂ hEquiv
    split_ifs with h₁ h₂ <;> simp_all

omit [DecidableEq Atom] [Fintype W] [DecidableEq W] in
/-- The gap enables non-maximal use: if the bare plural has a gap at w
and w's cell contains a positive-extension world, then the bare plural
is usable at w (assuming addressing is satisfied). This is the mechanism
Križ 2016 identifies for non-maximality: gap-worlds can be "true enough"
without being literally true. -/
theorem gap_enables_nonmax (q : QUD W) (P : Atom → W → Bool) (x : Finset Atom)
    (w w' : W)
    (hGap : barePluralTV P x w = .gap)
    (hEquiv : q.sameAnswer w w' = true)
    (hTrue : barePluralTV P x w' = .true)
    (hAddr : addressesIssue q (barePluralTV P x)) :
    usable q (barePluralTV P x) w := by
  refine ⟨by simp [hGap], ⟨w', hEquiv, hTrue⟩, hAddr⟩

end Bridge

-- ============================================================================
-- Section 7: Finite Model
-- ============================================================================

/-! A concrete 4-world model demonstrates the theory's predictions end-to-end.
Three professors attend Sue's talk; the predicate is "smiled."

| World          | Smith | Jones | Lee | Bare plural | All   |
|----------------|-------|-------|-----|-------------|-------|
| allSmiled      | ✓     | ✓     | ✓   | TRUE        | true  |
| smithNeutral   | ✗     | ✓     | ✓   | GAP         | false |
| onlyLeeSmiled  | ✗     | ✗     | ✓   | GAP         | false |
| noneSmiled     | ✗     | ✗     | ✗   | FALSE       | false |

Two QUDs:
- **Coarse** ("Was the talk well-received?"): groups allSmiled ≈ smithNeutral
- **Fine** ("Did every professor smile?"): each world in its own cell

Predictions:
- Bare plural usable at smithNeutral under coarse QUD (non-maximal reading)
- Bare plural NOT usable at smithNeutral under fine QUD (maximal only)
- `all`-sentence never usable at smithNeutral (forces literal truth)
-/

section FiniteModel

inductive ProfWorld where
  | allSmiled | smithNeutral | onlyLeeSmiled | noneSmiled
  deriving DecidableEq, Repr

inductive Prof where
  | smith | jones | lee
  deriving DecidableEq, Repr

instance : Fintype ProfWorld where
  elems := {.allSmiled, .smithNeutral, .onlyLeeSmiled, .noneSmiled}
  complete := by intro x; cases x <;> simp

instance : Fintype Prof where
  elems := {.smith, .jones, .lee}
  complete := by intro x; cases x <;> simp

/-- Did this professor smile in this world? -/
def smiled : Prof → ProfWorld → Bool
  | .smith, .allSmiled      => true
  | .smith, .smithNeutral   => false
  | .smith, .onlyLeeSmiled  => false
  | .smith, .noneSmiled     => false
  | .jones, .allSmiled      => true
  | .jones, .smithNeutral   => true
  | .jones, .onlyLeeSmiled  => false
  | .jones, .noneSmiled     => false
  | .lee,   .allSmiled      => true
  | .lee,   .smithNeutral   => true
  | .lee,   .onlyLeeSmiled  => true
  | .lee,   .noneSmiled     => false

/-- All three professors. -/
def profs : Finset Prof := Finset.univ

/-- Reception grade for the coarse QUD. -/
inductive Reception where | positive | mixed | negative
  deriving DecidableEq

def receptionGrade : ProfWorld → Reception
  | .allSmiled => .positive
  | .smithNeutral => .positive
  | .onlyLeeSmiled => .mixed
  | .noneSmiled => .negative

/-- Coarse QUD: "Was Sue's talk well-received?"
Groups allSmiled with smithNeutral (both = positive reception). -/
def coarseQ : QUD ProfWorld := QUD.ofDecEq receptionGrade

/-- Fine QUD: "Did every professor smile?"
Each world is its own cell. -/
def fineQ : QUD ProfWorld := QUD.ofDecEq id

-- Truth values at each world

theorem bare_allSmiled :
    barePluralTV smiled profs .allSmiled = .true := by native_decide

theorem bare_smithNeutral :
    barePluralTV smiled profs .smithNeutral = .gap := by native_decide

theorem bare_onlyLeeSmiled :
    barePluralTV smiled profs .onlyLeeSmiled = .gap := by native_decide

theorem bare_noneSmiled :
    barePluralTV smiled profs .noneSmiled = .false := by native_decide

/-- The bare plural sentence about the professors IS homogeneous —
smithNeutral is in the extension gap. -/
theorem bare_profs_homogeneous :
    isHomogeneous (barePluralTV smiled profs) :=
  bare_plural_homogeneous smiled profs .smithNeutral (by native_decide)

-- End-to-end predictions

/-- The bare plural IS usable at smithNeutral under the coarse QUD.
Smith's failure to smile is irrelevant to whether the talk was well-received,
so the sentence is "true enough." -/
theorem smithNeutral_usable_coarse :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral :=
  ⟨ by native_decide
  , ⟨.allSmiled, by native_decide, by native_decide⟩
  , by intro ⟨w₁, w₂, hEq, hTrue, hFalse⟩
       cases w₁ <;> cases w₂ <;>
         (first | exact absurd hTrue (by native_decide)
                | exact absurd hFalse (by native_decide)
                | exact absurd hEq (by native_decide))
  ⟩

/-- The bare plural is NOT usable at smithNeutral under the fine QUD.
The fine QUD distinguishes allSmiled from smithNeutral, so there is no
literally-true world in smithNeutral's cell. -/
theorem smithNeutral_not_usable_fine :
    ¬usable fineQ (barePluralTV smiled profs) .smithNeutral := by
  intro ⟨_, ⟨w', hEq, hTrue⟩, _⟩
  cases w' <;>
    (first | exact absurd hTrue (by native_decide)
           | exact absurd hEq (by native_decide))

/-- The `all`-sentence is never usable at smithNeutral (under any QUD),
because Smith didn't smile. Concrete instance of `all_prevents_nonmax`. -/
theorem all_not_usable_smithNeutral (q : QUD ProfWorld)
    (h : usable q (allPluralTV smiled profs) .smithNeutral) : False := by
  have := all_prevents_nonmax q smiled profs .smithNeutral h
  revert this; native_decide

/-- Concrete instance of `all_exceptions_unmentionable`: Smith's exception
cannot be mentioned because Smith did smile in every world where the
`all`-sentence is usable. -/
theorem smith_exception_unmentionable (q : QUD ProfWorld) (w : ProfWorld)
    (h : usable q (allPluralTV smiled profs) w) :
    smiled .smith w = true :=
  all_exceptions_unmentionable q smiled profs w .smith (by simp [profs]) h

/-- Communicated content under the coarse QUD includes the gap-world
smithNeutral — the non-maximal reading is communicated. -/
theorem coarse_communicates_gap :
    .smithNeutral ∈ communicatedContent coarseQ (barePluralTV smiled profs) :=
  ⟨.allSmiled, by native_decide, by native_decide⟩

/-- Communicated content under the fine QUD does NOT include smithNeutral. -/
theorem fine_does_not_communicate_gap :
    .smithNeutral ∉ communicatedContent fineQ (barePluralTV smiled profs) := by
  intro ⟨w', hEq, hTrue⟩
  cases w' <;>
    (first | exact absurd hTrue (by native_decide)
           | exact absurd hEq (by native_decide))

end FiniteModel

-- ============================================================================
-- Section 8: Connection to Empirical Data (NonMaximality.lean)
-- ============================================================================

/-! The finite model captures the same pattern as the theory-neutral data
in `NonMaximality.lean`. The switches scenario records that "the switches
are on" is acceptable in a non-maximal context (fire risk from any switch)
but not in a maximal one (fire risk only if all on). This corresponds to
`smithNeutral_usable_coarse` vs `smithNeutral_not_usable_fine`.

Similarly, `switchesAllBlocks` records that "all the switches are on" is
unacceptable even in the permissive context, corresponding to
`all_not_usable_smithNeutral`. -/

open Phenomena.Plurals.NonMaximality in
/-- The switches datum records non-maximal use is acceptable. -/
theorem switches_nonmax_acceptable :
    switchesNonMaximality.acceptableInNonMaximalContext = true := rfl

open Phenomena.Plurals.NonMaximality in
/-- The switches datum records maximal use is not acceptable (in gap scenario). -/
theorem switches_max_not_acceptable :
    switchesNonMaximality.acceptableInMaximalContext = false := rfl

open Phenomena.Plurals.NonMaximality in
/-- "All" blocks non-maximality even in permissive contexts. -/
theorem switches_all_blocks :
    switchesAllBlocks.allAcceptable = false := rfl

open Phenomena.Plurals.NonMaximality in
/-- The coarse issue makes the all/some distinction irrelevant,
which is the precondition for non-maximal readings. -/
theorem coarse_issue_irrelevant :
    switchesNonMaximality.nonMaximalContext.allSomeDistinctionRelevant = false := rfl

-- ============================================================================
-- Section 9: Connection to Homogeneity Data (Homogeneity.lean)
-- ============================================================================

/-! Bridge to the theory-neutral homogeneity data in `Homogeneity.lean`.
The data records `all` as a homogeneity remover and specifies that gap
scenarios yield `.neitherTrueNorFalse` for homogeneous sentences but
`.clearlyFalse` for `all`-sentences. The structural theorems `all_no_gap`
and `all_not_homogeneous` prove this mechanism, and the finite model
demonstrates it concretely via `bare_profs_homogeneous`. -/

open Phenomena.Plurals.Homogeneity in
/-- The homogeneity data lists `all` as a remover. -/
theorem all_is_homogeneity_remover :
    allRemovesHomogeneity.remover = .all := rfl

open Phenomena.Plurals.Homogeneity in
/-- Gap scenarios yield `.neitherTrueNorFalse` for homogeneous sentences:
the signature of the extension gap that enables non-maximal readings. -/
theorem homogeneous_gap_yields_neither :
    allRemovesHomogeneity.homogeneousJudgment = .neitherTrueNorFalse := rfl

open Phenomena.Plurals.Homogeneity in
/-- Adding `all` makes the gap-scenario sentence clearly false — the gap
is absorbed into the negative extension. -/
theorem all_gap_yields_false :
    allRemovesHomogeneity.preciseJudgment = .clearlyFalse := rfl

open Phenomena.Plurals.Homogeneity in
/-- The switches datum records homogeneity in the gap: positive sentence
is neither true nor false when some-but-not-all switches are on. -/
theorem switches_gap_is_neither :
    switchesExample.positiveInGap = .neitherTrueNorFalse := rfl

open Phenomena.Plurals.Homogeneity in
/-- Outside the gap, judgments are clear: all switches on → clearly true. -/
theorem switches_all_on_clearly_true :
    switchesExample.positiveInAll = .clearlyTrue := rfl

end Phenomena.Plurals.Studies.Kriz2016
