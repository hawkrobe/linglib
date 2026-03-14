import Mathlib.Data.Finset.Card
import Linglib.Core.Discourse.QUD
import Linglib.Core.Logic.Truth3
import Linglib.Theories.Semantics.Supervaluation.Basic

/-!
# Homogeneity: General Theory
@cite{kriz-2016} @cite{fine-1975}

Homogeneity is a cross-cutting semantic property that creates trivalent
truth conditions: a sentence may be true, false, or *neither*. This
phenomenon appears across multiple linguistic domains:

- **Plural definites**: "The professors smiled" — gap when some but not all smiled
- **Conditionals**: "If Mary comes, John will be happy" — gap when John is
  happy in some but not all closest worlds (conditional excluded middle)
- **Summative predicates**: "The wall is painted" — gap when part is painted
- **Generics**: "Birds can fly" — gap when most but not all species can

All instances share the same abstract structure: **supervaluation over
specification points** (@cite{fine-1975}). The spec points are atoms (for
plurals), accessible worlds (for conditionals), spatial parts (for
summatives), or subkinds (for generics).

**Non-maximal readings** arise from the interaction of two independent
pragmatic principles:

1. **(Weak) Maxim of Quality**: Say only what is *true enough* for current
   purposes — i.e., equivalent to something literally true given the issue.

2. **Addressing an Issue**: A sentence S may address issue I only if no cell
   of I contains both true-worlds and false-worlds. Gap-worlds are invisible.

The semantic effect of homogeneity removers (`all`, `necessarily`,
`completely`, `whole`) is to eliminate the extension gap, making the sentence
bivalent. This blocks non-maximal readings because the pragmatic mechanism
has no gap to exploit.

This file extracts the general theory from the plural-specific formalization
in `Phenomena/Plurals/Studies/Kriz2016.lean`, making it available for all
homogeneous domains.
-/

namespace Semantics.Homogeneity

open Core.Duality (Truth3)
open Semantics.Supervaluation (SpecSpace superTrue superTrue_true_iff superTrue_false_iff
  superTrue_indet_iff fidelity)

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════════════════
-- § 1. Trivalent Sentence Denotations
-- ════════════════════════════════════════════════════════════════════════════

/-- A trivalent sentence denotation: maps worlds to truth values.
    This is the general type for any sentence that may exhibit homogeneity. -/
abbrev SentenceTV (W : Type*) := W → Truth3

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

/-- The positive and negative extensions are disjoint. -/
theorem posExt_negExt_disjoint (S : SentenceTV W) :
    posExt S ∩ negExt S = ∅ := by
  ext w; simp only [posExt, negExt, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_empty_iff_false]
  exact ⟨λ ⟨h₁, h₂⟩ => by rw [h₁] at h₂; exact absurd h₂ (by decide), False.elim⟩

/-- A sentence is homogeneous if its extension gap is non-empty.
    The gap is what enables non-maximal readings. -/
def isHomogeneous (S : SentenceTV W) : Prop := gapExt S ≠ ∅

/-- A sentence is bivalent if it has no extension gap.
    `all`, `necessarily`, and `completely` make sentences bivalent. -/
def isBivalent (S : SentenceTV W) : Prop :=
  ∀ w, S w = .true ∨ S w = .false

-- ════════════════════════════════════════════════════════════════════════════
-- § 2. Supervaluation as Homogeneity Source
-- ════════════════════════════════════════════════════════════════════════════

/-! Every supervaluation instance gives rise to a trivalent sentence.
    The specification points can be:
    - **Atoms** of a plurality (plural definites)
    - **Accessible worlds** (conditionals)
    - **Spatial parts** (summative predicates)
    - **Subkinds** (generics)

    The shared structure: TRUE iff the predicate holds at ALL spec points,
    FALSE iff it fails at ALL, GAP iff it holds at some but not all. -/

/-- Construct a trivalent sentence from a supervaluation instance.
    `eval w` gives the Bool predicate over spec points at world `w`,
    and `space w` gives the spec space at world `w`. -/
def supervaluationTV {Spec W : Type*} (eval : W → Spec → Bool)
    (space : W → SpecSpace Spec) : SentenceTV W :=
  λ w => superTrue (eval w) (space w)

/-- A supervaluation sentence is true iff the predicate holds at all specs. -/
theorem supervaluationTV_true_iff {Spec W : Type*} (eval : W → Spec → Bool)
    (space : W → SpecSpace Spec) (w : W) :
    supervaluationTV eval space w = .true ↔
    ∀ s ∈ (space w).admissible, eval w s = true :=
  superTrue_true_iff (eval w) (space w)

/-- A supervaluation sentence is false iff the predicate fails at all specs. -/
theorem supervaluationTV_false_iff {Spec W : Type*} (eval : W → Spec → Bool)
    (space : W → SpecSpace Spec) (w : W) :
    supervaluationTV eval space w = .false ↔
    ∀ s ∈ (space w).admissible, eval w s = false :=
  superTrue_false_iff (eval w) (space w)

/-- A supervaluation sentence is gapped iff witnesses exist on both sides. -/
theorem supervaluationTV_gap_iff {Spec W : Type*} (eval : W → Spec → Bool)
    (space : W → SpecSpace Spec) (w : W) :
    supervaluationTV eval space w = .gap ↔
    (∃ s ∈ (space w).admissible, eval w s = true) ∧
    (∃ s ∈ (space w).admissible, eval w s = false) :=
  superTrue_indet_iff (eval w) (space w)

-- ════════════════════════════════════════════════════════════════════════════
-- § 3. Homogeneity Removal
-- ════════════════════════════════════════════════════════════════════════════

/-! A homogeneity remover is any operation that eliminates the extension gap,
    making the sentence bivalent. Linguistically:

    | Domain      | Remover         | Example                          |
    |-------------|-----------------|----------------------------------|
    | Plurals     | `all`           | "All the professors smiled"      |
    | Conditionals| `necessarily`   | "If Mary comes, John will nec…"  |
    | Spatial     | `completely`    | "The flag is completely blue"     |
    | Spatial     | `whole`         | "The whole wall is painted"       |

    Semantically, removal collapses the gap into the negative extension:
    gap-worlds become false-worlds, preserving the positive extension. -/

/-- Remove homogeneity: collapse gap into negative extension.
    The positive extension is preserved; gap and false both become false. -/
def removeGap (S : SentenceTV W) : SentenceTV W :=
  λ w => match S w with
  | .true => .true
  | .false => .false
  | .indet => .false

/-- Removal produces a bivalent sentence. -/
theorem removeGap_bivalent (S : SentenceTV W) :
    isBivalent (removeGap S) := by
  intro w; simp only [removeGap]; cases S w <;> simp

/-- Removal preserves the positive extension. -/
theorem removeGap_posExt_eq (S : SentenceTV W) :
    posExt (removeGap S) = posExt S := by
  ext w; simp only [posExt, removeGap, Set.mem_setOf_eq]
  cases S w <;> simp

/-- Removal absorbs the gap into the negative extension. -/
theorem removeGap_negExt_eq (S : SentenceTV W) :
    negExt (removeGap S) = negExt S ∪ gapExt S := by
  ext w; simp only [removeGap, negExt, gapExt, Set.mem_setOf_eq, Set.mem_union]
  cases S w <;> simp

/-- Removed sentences are never homogeneous. -/
theorem removeGap_not_homogeneous (S : SentenceTV W) :
    ¬isHomogeneous (removeGap S) := by
  intro h; apply h; ext w
  simp only [gapExt, removeGap, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  cases S w <;> simp

-- ════════════════════════════════════════════════════════════════════════════
-- § 4. Pragmatic Usability (Križ 2016 §3)
-- ════════════════════════════════════════════════════════════════════════════

/-! The pragmatic mechanism that derives non-maximal readings from
    the homogeneity gap. Two independent principles interact:

    1. **Sufficient Truth**: weakens Quality to "true enough for current purposes"
    2. **Addressing an Issue**: restricts which sentences can be used for which
       issues, based on alignment between truth-value boundaries and issue cells

    Together, they predict that a sentence can be used at a gap-world iff
    (i) a literally-true world is in the same issue cell, and (ii) no cell
    straddles the true/false boundary. -/

/-- Sufficient Truth: S is "true enough" at world w relative to issue I
    iff there is a world w' that is I-equivalent to w where S is literally true.

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
    cell of I overlaps with both the positive and the negative extension.

    Gap-worlds are invisible: a cell containing true-worlds and gap-worlds
    is fine. Only a cell straddling the true/false boundary is problematic. -/
def addressesIssue (q : QUD W) (S : SentenceTV W) : Prop :=
  ¬∃ w₁ w₂, q.sameAnswer w₁ w₂ = true ∧ S w₁ = .true ∧ S w₂ = .false

/-- A sentence may be used at w iff: (1) S is not false at w,
    (2) S is sufficiently true at w, and (3) S addresses the issue. -/
def usable (q : QUD W) (S : SentenceTV W) (w : W) : Prop :=
  S w ≠ .false ∧ sufficientlyTrue q S w ∧ addressesIssue q S

/-- For bivalent sentences, usability reduces to literal truth + addressing.
    Sufficient Truth adds nothing because there are no gap-worlds. -/
theorem bivalent_usable_iff_true (q : QUD W) (S : SentenceTV W)
    (hbiv : isBivalent S) (w : W) :
    usable q S w ↔ S w = .true ∧ addressesIssue q S := by
  constructor
  · intro ⟨hNotFalse, _, hAddr⟩
    exact ⟨by cases hbiv w with | inl h => exact h | inr h => exact absurd h hNotFalse, hAddr⟩
  · intro ⟨hTrue, hAddr⟩
    exact ⟨by simp [hTrue], literal_imp_sufficient q S w hTrue, hAddr⟩

-- ════════════════════════════════════════════════════════════════════════════
-- § 5. Communicated Content
-- ════════════════════════════════════════════════════════════════════════════

/-- The communicated content of S relative to issue I: the set of worlds
    the hearer considers possible after hearing S.

    This is the union of all issue cells that overlap with ⟦S⟧⁺.
    The hearer infers not that S is literally true, but that the actual world
    is indistinguishable (relative to current purposes) from one where S is
    literally true. -/
def communicatedContent (q : QUD W) (S : SentenceTV W) : Set W :=
  {w | sufficientlyTrue q S w}

/-- Literal truth is always communicated. -/
theorem posExt_subset_communicated (q : QUD W) (S : SentenceTV W) :
    posExt S ⊆ communicatedContent q S :=
  λ _ hw => literal_imp_sufficient q S _ hw

/-- For bivalent sentences that address the issue, communicated content
    equals the positive extension — no pragmatic weakening is possible.

    This is the key consequence of gap removal: `all`/`necessarily`/`completely`
    force literal truth to be communicated. -/
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

/-- Extract the Bool truth predicate from a bivalent sentence.
    Used to bridge between the trivalent Addressing constraint and
    bivalent strong-relevance filtering (Križ & Spector 2021). -/
def bivalentPred (S : SentenceTV W) : W → Bool :=
  λ w => S w == .true

-- ════════════════════════════════════════════════════════════════════════════
-- § 6. Conditional Homogeneity (CEM)
-- ════════════════════════════════════════════════════════════════════════════

/-! @cite{kriz-2016} §6.4: Conditionals are the modal analogue of plural
    definites. "If P, Q" universally quantifies over closest P-worlds, just as
    "the Xs are Q" universally quantifies over atoms. The conditional excluded
    middle (CEM) — the observation that "if P, Q" seems neither true nor false
    when Q holds at some but not all closest P-worlds — IS homogeneity.

    | Plural domain | Conditional domain  |
    |---------------|---------------------|
    | atoms         | closest P-worlds    |
    | `all`         | `necessarily`       |
    | bare plural   | bare conditional    |
    | gap (some)    | CEM (some worlds)   |

    @cite{stalnaker-1981} @cite{von-fintel-1999} -/

section ConditionalHomogeneity

variable {W : Type*} [DecidableEq W]

/-- A bare conditional "if P, Q" as a trivalent sentence.
    The spec points are the closest P-worlds; the eval function is Q.
    TRUE if Q holds at all closest P-worlds, FALSE if Q fails at all,
    GAP otherwise (conditional excluded middle). -/
def conditionalTV (closestPWorlds : W → Finset W) (Q : W → Bool) : SentenceTV W :=
  λ w =>
    let pWorlds := closestPWorlds w
    if h : pWorlds.Nonempty then
      superTrue Q ⟨pWorlds, h⟩
    else .true  -- vacuously true if no closest P-worlds

/-- A strict conditional "if P, necessarily Q" — the `all` of conditionals.
    Defined as gap removal on the bare conditional: `necessarily` collapses
    the homogeneity gap, just as `all` does for plurals. -/
def strictConditionalTV (closestPWorlds : W → Finset W) (Q : W → Bool) :
    SentenceTV W :=
  removeGap (conditionalTV closestPWorlds Q)

omit [DecidableEq W] in
/-- Strict conditionals are bivalent — `necessarily` removes the gap,
    just as `all` removes homogeneity for plurals. -/
theorem strictConditionalTV_bivalent (closestPWorlds : W → Finset W) (Q : W → Bool) :
    isBivalent (strictConditionalTV closestPWorlds Q) :=
  removeGap_bivalent _

omit [DecidableEq W] in
/-- Positive extensions agree: the bare conditional and the strict conditional
    are true in the same worlds. Parallel to `all_posExt_eq` for plurals. -/
theorem conditionalTV_posExt_eq (closestPWorlds : W → Finset W) (Q : W → Bool) :
    posExt (conditionalTV closestPWorlds Q) = posExt (strictConditionalTV closestPWorlds Q) :=
  (removeGap_posExt_eq _).symm

omit [DecidableEq W] in
/-- `necessarily` prevents non-maximal use of conditionals, just as `all`
    does for plurals. If a strict conditional is usable at w, Q holds at
    all closest P-worlds (when they exist). -/
theorem necessarily_prevents_nonmax (q : QUD W) (closestPWorlds : W → Finset W)
    (Q : W → Bool) (w : W) (h : usable q (strictConditionalTV closestPWorlds Q) w)
    (hne : (closestPWorlds w).Nonempty) :
    ∀ w' ∈ closestPWorlds w, Q w' = true := by
  -- strictConditionalTV is bivalent; usability requires not-false, so it's true
  have hTrue : strictConditionalTV closestPWorlds Q w = .true := by
    cases strictConditionalTV_bivalent closestPWorlds Q w with
    | inl h' => exact h'
    | inr h' => exact absurd h' h.1
  -- removeGap S w = .true implies S w = .true
  have hCondTrue : conditionalTV closestPWorlds Q w = .true := by
    simp only [strictConditionalTV, removeGap] at hTrue
    cases hc : conditionalTV closestPWorlds Q w <;> simp_all
  simp only [conditionalTV, dif_pos hne] at hCondTrue
  exact (superTrue_true_iff Q ⟨closestPWorlds w, hne⟩).mp hCondTrue

end ConditionalHomogeneity

-- ════════════════════════════════════════════════════════════════════════════
-- § 7. Generalised Homogeneity for Collective Predicates
-- ════════════════════════════════════════════════════════════════════════════

/-! @cite{kriz-2016} §5.1, Definition (45): Homogeneity for collective predicates
    is defined via **mereological overlap**, not individual atoms. A predicate P
    is undefined of plurality a if a is not in P's positive extension but
    *overlaps* with some plurality that is.

    For distributive predicates, this reduces to the atom-based definition
    in `Distributivity.lean`: the overlapping witness is a singleton {x}
    where x ∈ a and P(x).

    For collective predicates like "perform Hamlet", the overlapping witness
    can be a larger group: "the boys" overlaps with "all the students", and
    if all the students are performing Hamlet, the boys' predication is
    undefined (not false). -/

section GeneralisedHomogeneity

variable {Atom : Type*} [DecidableEq Atom]

/-- Two pluralities overlap if they share at least one individual. -/
def overlaps (a b : Finset Atom) : Bool :=
  !((a ∩ b) == ∅)

/-- Generalised homogeneity: trivalent truth for predicates on pluralities.
    Handles both distributive and collective predicates uniformly.

    - TRUE:  P holds of a
    - GAP:   P doesn't hold of a, but some overlapping plurality in `domain` satisfies P
    - FALSE: no overlapping plurality in `domain` satisfies P

    `domain` is the set of all relevant pluralities (e.g., all subgroups
    of the universe of discourse). For distributive predicates, singletons
    suffice; for collective predicates, larger groups are needed. -/
def generalisedTV (P : Finset Atom → Bool) (domain : Finset (Finset Atom))
    (a : Finset Atom) : Truth3 :=
  if P a then .true
  else if decide (∃ b ∈ domain, overlaps a b = true ∧ P b = true) then .gap
  else .false

/-- Generalised homogeneity is a genuine three-way partition. -/
theorem generalisedTV_trichotomy (P : Finset Atom → Bool)
    (domain : Finset (Finset Atom)) (a : Finset Atom) :
    generalisedTV P domain a = .true ∨
    generalisedTV P domain a = .false ∨
    generalisedTV P domain a = .gap := by
  simp only [generalisedTV]; split_ifs <;> simp

/-- If P holds of a, the generalised truth value is TRUE. -/
theorem generalisedTV_true_of_holds (P : Finset Atom → Bool)
    (domain : Finset (Finset Atom)) (a : Finset Atom) (h : P a = true) :
    generalisedTV P domain a = .true := by
  simp [generalisedTV, h]

/-- Overlap is reflexive for nonempty pluralities. -/
theorem overlaps_self (a : Finset Atom) (hne : a.Nonempty) :
    overlaps a a = true := by
  simp only [overlaps, Finset.inter_self]
  have : a ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hne
  cases h : (a == ∅)
  · rfl
  · exfalso; exact this (beq_iff_eq.mp h)

/-- Overlap is symmetric. -/
theorem overlaps_symm (a b : Finset Atom) : overlaps a b = overlaps b a := by
  simp only [overlaps, Finset.inter_comm]

/-- If two pluralities overlap, they share a member. -/
private theorem overlaps_exists_mem {a b : Finset Atom} (h : overlaps a b = true) :
    ∃ y, y ∈ a ∧ y ∈ b := by
  simp only [overlaps, Bool.not_eq_true', beq_eq_false_iff_ne,
    Finset.nonempty_iff_ne_empty.symm.eq] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, Finset.mem_inter.mp hy⟩

/-- A singleton of a member overlaps with the plurality. -/
private theorem overlaps_singleton_of_mem {a : Finset Atom} {x : Atom} (hx : x ∈ a) :
    overlaps a {x} = true := by
  unfold overlaps
  have hne : (a ∩ {x}).Nonempty :=
    ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_singleton.mpr rfl⟩⟩
  rw [Finset.nonempty_iff_ne_empty] at hne
  cases hq : a ∩ {x} == ∅
  · rfl
  · exact absurd (beq_iff_eq.mp hq) hne

/-- For distributive predicates, the generalised definition coincides with
    supervaluation over atoms when the domain includes all singletons of
    members. The distributive predicate `∀ x ∈ s, pred x` is checked
    against each sub-plurality; the overlap condition reduces to checking
    individual atoms of `a`. -/
theorem generalisedTV_distributive_reduction
    (pred : Atom → Bool) (a : Finset Atom) (hne : a.Nonempty)
    (domain : Finset (Finset Atom))
    (hdomain : ∀ x ∈ a, {x} ∈ domain) :
    generalisedTV (λ s => decide (∀ x ∈ s, pred x = true)) domain a =
    superTrue (λ x => pred x) ⟨a, hne⟩ := by
  by_cases hall : ∀ x ∈ a, pred x = true
  · -- All satisfy: both return .true
    have hLHS : generalisedTV (λ s => decide (∀ x ∈ s, pred x = true)) domain a = .true :=
      generalisedTV_true_of_holds _ domain a (decide_eq_true hall)
    rw [hLHS]; symm; exact (superTrue_true_iff _ _).mpr hall
  · by_cases hnone : ∀ x ∈ a, pred x = false
    · -- None satisfy: both return .false
      -- LHS: P a = false, and no overlap witness exists
      have hPaFalse : (decide (∀ x ∈ a, pred x = true)) = false := decide_eq_false hall
      have hNoWitness : ¬∃ b ∈ domain, overlaps a b = true ∧
          (decide (∀ x ∈ b, pred x = true)) = true := by
        intro ⟨b, _, hov, hPb⟩
        rw [decide_eq_true_iff] at hPb
        obtain ⟨y, hya, hyb⟩ := overlaps_exists_mem hov
        exact absurd (hPb y hyb) (by rw [hnone y hya]; decide)
      simp only [generalisedTV, hPaFalse, Bool.false_eq_true, ite_false,
        decide_eq_false hNoWitness]
      symm; exact (superTrue_false_iff _ _).mpr hnone
    · -- Mixed: both return .indet/.gap
      have hPaFalse : (decide (∀ x ∈ a, pred x = true)) = false := decide_eq_false hall
      -- Find an atom with pred = true
      push_neg at hnone
      obtain ⟨x, hxa, hpx⟩ := hnone
      have hpx_true : pred x = true := by
        cases h : pred x with
        | false => exact absurd h hpx
        | true => rfl
      have hWitness : ∃ b ∈ domain, overlaps a b = true ∧
          (decide (∀ x ∈ b, pred x = true)) = true :=
        ⟨{x}, hdomain x hxa, overlaps_singleton_of_mem hxa,
          decide_eq_true (λ y hy => by rw [Finset.mem_singleton.mp hy]; exact hpx_true)⟩
      simp only [generalisedTV, hPaFalse, Bool.false_eq_true, ite_false,
        decide_eq_true hWitness, ite_true]
      -- Find an atom with pred = false
      push_neg at hall
      obtain ⟨z, hza, hpz⟩ := hall
      have hpz_false : pred z = false := by
        cases h : pred z with
        | false => rfl
        | true => exact absurd h hpz
      -- .gap is abbrev for .indet; use symm to match superTrue_indet_iff
      symm
      exact (superTrue_indet_iff _ _).mpr ⟨⟨x, hxa, hpx_true⟩, ⟨z, hza, hpz_false⟩⟩

end GeneralisedHomogeneity

-- ════════════════════════════════════════════════════════════════════════════
-- § 8. Cross-Domain Unification
-- ════════════════════════════════════════════════════════════════════════════

/-! The central insight of @cite{kriz-2016}: all homogeneity phenomena share
    the same pragmatic mechanism. Once a domain has been identified as
    exhibiting homogeneity (via any of the sources above), the SAME
    `sufficientlyTrue` + `addressesIssue` mechanism derives non-maximal
    readings, and the SAME `removeGap` operation explains why removers
    (`all`, `necessarily`, `completely`, `whole`) block them.

    The following theorems are domain-independent consequences. -/

section CrossDomain

variable {W : Type*}

/-- Any bivalent sentence (one whose gap has been removed) forces literal
    truth for usability. This is the general form of the headline result:
    homogeneity removers prevent non-maximal use. -/
theorem removed_prevents_nonmax (q : QUD W) (S : SentenceTV W) (w : W)
    (h : usable q (removeGap S) w) : removeGap S w = .true := by
  cases hbiv : (removeGap S w) with
  | true => rfl
  | false => exact absurd hbiv h.1
  | indet =>
    -- removeGap never produces .indet
    exfalso; cases hSw : S w <;> simp_all [removeGap]

/-- The gap enables non-maximal use: if S is gapped at w and w's cell
    contains a true-world, then S is usable at w (assuming addressing). -/
theorem gap_enables_nonmax (q : QUD W) (S : SentenceTV W) (w w' : W)
    (hGap : S w = .gap)
    (hEquiv : q.sameAnswer w w' = true)
    (hTrue : S w' = .true)
    (hAddr : addressesIssue q S) :
    usable q S w :=
  ⟨by simp [hGap], ⟨w', hEquiv, hTrue⟩, hAddr⟩

/-- Gap-worlds are never false, so they satisfy the first usability condition. -/
theorem gap_not_false (S : SentenceTV W) (w : W) (h : S w = .gap) :
    S w ≠ .false := by simp [h]

end CrossDomain

end Semantics.Homogeneity
