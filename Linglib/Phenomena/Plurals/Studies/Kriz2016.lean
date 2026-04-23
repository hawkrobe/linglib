import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Core.Logic.Truth3
import Linglib.Theories.Semantics.Plurality.Distributivity
import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Phenomena.Plurals.NonMaximality
import Linglib.Phenomena.Plurals.Homogeneity

/-!
# Križ (2016): Homogeneity, Non-Maximality, and All
@cite{kriz-2016} @cite{fine-1975}

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

## General Homogeneity Theory

The general definitions (trivalent sentence denotations, supervaluation source,
gap removal, pragmatic usability, communicated content) live in the
`Semantics.Homogeneity` namespace within this file. They are domain-independent
and apply to any homogeneity source:

- **Plural definites**: spec points = atoms
- **Conditionals**: spec points = closest P-worlds (CEM)
- **Summative predicates**: spec points = spatial parts
- **Generics**: spec points = subkinds

The shared structure: **supervaluation over specification points** (@cite{fine-1975}).

## Plural-Specific Instantiation

The `Phenomena.Plurals.Studies.Kriz2016` namespace adds plural-specific
instantiations (`barePluralTV`, `allPluralTV`) and a concrete 4-world
finite model demonstrating end-to-end predictions.

## Key Definitions

- **SentenceTV**: trivalent sentence denotation (W → Truth3)
- **posExt / negExt / gapExt**: positive, negative, and gap extensions
- **sufficientlyTrue**: S "true enough" at w wrt issue I
- **addressesIssue**: no cell overlaps both ⟦S⟧⁺ and ⟦S⟧⁻
- **usable**: conjunction of not-false, sufficiently true, addresses issue
- **communicatedContent**: worlds indistinguishable from ⟦S⟧⁺ under I
- **removeGap**: collapse gap into negative extension (what `all` does)

## Finite Model

A concrete 4-world model demonstrates end-to-end predictions: "the professors
smiled" is usable at a gap-world under a coarse issue but not under a fine one,
and adding "all" blocks non-maximal use entirely.
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- General Homogeneity Theory (domain-independent)
-- ══════════════════════════════════════════════════════════════════════════════

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
def gapExt (S : SentenceTV W) : Set W := {w | S w = .indet}

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

/-- Bivalence and homogeneity are complementary:
    a sentence is bivalent iff it has no extension gap. -/
theorem isBivalent_iff_not_homogeneous (S : SentenceTV W) :
    isBivalent S ↔ ¬isHomogeneous S := by
  constructor
  · intro hbiv hhom
    apply hhom; ext w
    simp only [gapExt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    cases hbiv w with | inl h => simp [h] | inr h => simp [h]
  · intro hnotHom w
    have hempty : gapExt S = ∅ := by
      by_contra hne; exact hnotHom hne
    have := (Set.eq_empty_iff_forall_notMem.mp hempty w)
    simp only [gapExt, Set.mem_setOf_eq] at this
    cases hSw : S w with
    | true => left; rfl
    | false => right; rfl
    | indet => exact absurd hSw this

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
    supervaluationTV eval space w = .indet ↔
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
    2. **Addressing an Question**: restricts which sentences can be used for which
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
  ∃ w', q.r w w' ∧ S w' = .true

/-- Literal truth implies sufficient truth (for any issue). -/
theorem literal_imp_sufficient (q : QUD W) (S : SentenceTV W) (w : W)
    (h : S w = .true) : sufficientlyTrue q S w :=
  ⟨w, q.iseqv.refl w, h⟩

/-- Addressing an Question: S may be used to address issue I only if no
    cell of I overlaps with both the positive and the negative extension.

    Gap-worlds are invisible: a cell containing true-worlds and gap-worlds
    is fine. Only a cell straddling the true/false boundary is problematic. -/
def addressesIssue (q : QUD W) (S : SentenceTV W) : Prop :=
  ¬∃ w₁ w₂, q.r w₁ w₂ ∧ S w₁ = .true ∧ S w₂ = .false

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
      have hSymm : q.r w' w := q.iseqv.symm hEq
      exact absurd ⟨w', w, hSymm, hTrue, hFalse⟩ hAddr
  · exact literal_imp_sufficient q S w

/-- Communicated content is antitone in issue refinement: coarser issues
    (bigger cells) communicate more content. If q' refines q (q' is finer),
    then everything communicated under q' is also communicated under q.

    This is @cite{kriz-2016}'s key prediction: coarser QUDs enable more
    non-maximal use. The finite model in `Kriz2016.lean` demonstrates this:
    `coarseQ` communicates `smithNeutral` but `fineQ` does not. -/
theorem communicatedContent_antitone (q q' : QUD W) (S : SentenceTV W)
    (hRef : ∀ w₁ w₂, q'.r w₁ w₂ → q.r w₁ w₂) :
    communicatedContent q' S ⊆ communicatedContent q S :=
  fun _ ⟨w', hEq, hTrue⟩ => ⟨w', hRef _ _ hEq, hTrue⟩

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
    GAP otherwise (conditional excluded middle).

    This is the same computation as `selectionalCounterfactual` in
    `Conditionals/Counterfactual.lean`, which proves the equivalence
    with `superTrue` via `selectional_as_supervaluation`. The two
    formalizations use different input representations (Finset vs List)
    but compute the same three-valued truth value. -/
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
  else if decide (∃ b ∈ domain, overlaps a b = true ∧ P b = true) then .indet
  else .false

/-- Generalised homogeneity is a genuine three-way partition. -/
theorem generalisedTV_trichotomy (P : Finset Atom → Bool)
    (domain : Finset (Finset Atom)) (a : Finset Atom) :
    generalisedTV P domain a = .true ∨
    generalisedTV P domain a = .false ∨
    generalisedTV P domain a = .indet := by
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
theorem overlaps_exists_mem {a b : Finset Atom} (h : overlaps a b = true) :
    ∃ y, y ∈ a ∧ y ∈ b := by
  simp only [overlaps, Bool.not_eq_true', beq_eq_false_iff_ne,
    Finset.nonempty_iff_ne_empty.symm.eq] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, Finset.mem_inter.mp hy⟩

/-- A singleton of a member overlaps with the plurality. -/
theorem overlaps_singleton_of_mem {a : Finset Atom} {x : Atom} (hx : x ∈ a) :
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
    · -- Mixed: both return .indet/.indet
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
      -- .indet is abbrev for .indet; use symm to match superTrue_indet_iff
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
    (hGap : S w = .indet)
    (hEquiv : q.r w w')
    (hTrue : S w' = .true)
    (hAddr : addressesIssue q S) :
    usable q S w :=
  ⟨by simp [hGap], ⟨w', hEquiv, hTrue⟩, hAddr⟩

/-- Gap-worlds are never false, so they satisfy the first usability condition. -/
theorem gap_not_false (S : SentenceTV W) (w : W) (h : S w = .indet) :
    S w ≠ .false := by simp [h]

end CrossDomain

-- ════════════════════════════════════════════════════════════════════════════
-- § 9. Plural Instance
-- ════════════════════════════════════════════════════════════════════════════

/-! `pluralTruthValue` from `Distributivity.lean` is an instance of
    `supervaluationTV` with atoms as specification points. This bridge
    makes the general gap-manipulation machinery (§3, §8) applicable
    to plural predication. -/

section PluralInstance

variable {Atom W : Type*} [DecidableEq Atom]

open Semantics.Plurality.Distributivity (pluralTruthValue allSatisfy)

omit [DecidableEq Atom] in
/-- `pluralTruthValue` is `supervaluationTV` with atoms as spec points. -/
theorem pluralTruthValue_eq_supervaluationTV (P : Atom → W → Bool)
    (x : Finset Atom) (hne : x.Nonempty) (w : W) :
    pluralTruthValue P x w =
    supervaluationTV (fun w a => P a w) (fun _ => ⟨x, hne⟩) w := by
  simp only [pluralTruthValue, supervaluationTV, dif_pos hne]

/-- Gap removal on a plural sentence is true iff all atoms satisfy P.
    This is the formal content of "`all` removes homogeneity." -/
theorem removeGap_plural_true_iff (P : Atom → W → Bool)
    (x : Finset Atom) (hne : x.Nonempty) (w : W) :
    removeGap (fun w => pluralTruthValue P x w) w = .true ↔
    allSatisfy P x w = true := by
  simp only [removeGap, pluralTruthValue, dif_pos hne, superTrue, allSatisfy]
  split_ifs <;> simp_all

end PluralInstance

end Semantics.Homogeneity

-- ══════════════════════════════════════════════════════════════════════════════
-- Plural-Specific Instantiation
-- ══════════════════════════════════════════════════════════════════════════════

namespace Phenomena.Plurals.Studies.Kriz2016

open Core.Duality (Truth3)
open Semantics.Plurality.Distributivity
open Semantics.Homogeneity

variable {Atom W : Type*} [DecidableEq Atom]

-- ============================================================================
-- Section 1: Plural Predication as Sentence Extension
-- ============================================================================

/-- The bare plural sentence "the Xs are P" as a trivalent sentence. -/
def barePluralTV (P : Atom → W → Bool) (x : Finset Atom) : SentenceTV W :=
  λ w => pluralTruthValue P x w

/-- The `all`-sentence "all the Xs are P" as a bivalent sentence.
`all` removes homogeneity: the truth value is always true or false. -/
def allPluralTV (P : Atom → W → Bool) (x : Finset Atom) : SentenceTV W :=
  λ w => if allSatisfy P x w then .true else .false

/-- `all` IS gap removal: the `all`-sentence is the bare plural with its
    extension gap collapsed into the negative extension.

    This is the central structural claim of @cite{kriz-2016}: the semantic
    contribution of `all` is not to add universal quantification (the bare
    plural already universally quantifies), but to remove homogeneity. -/
theorem allPluralTV_eq_removeGap (P : Atom → W → Bool) (x : Finset Atom) :
    allPluralTV P x = removeGap (barePluralTV P x) := by
  ext w; simp only [allPluralTV, barePluralTV, removeGap]
  cases hall : allSatisfy P x w
  · -- allSatisfy = false: need removeGap (pluralTruthValue ...) = .false
    simp only [Bool.false_eq_true, ite_false]
    have hne : pluralTruthValue P x w ≠ .true := by
      intro h; rw [pluralTruthValue_eq_true_iff] at h; simp [hall] at h
    cases hpv : pluralTruthValue P x w with
    | true => exact absurd hpv hne
    | false => rfl
    | indet => rfl
  · -- allSatisfy = true
    simp only [ite_true]
    rw [(pluralTruthValue_eq_true_iff P x w).mpr hall]

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
    (w : W) (hGap : barePluralTV P x w = .indet) :
    isHomogeneous (barePluralTV P x) := by
  intro h; rw [Set.eq_empty_iff_forall_notMem] at h
  exact h w hGap

/-- Positive extensions agree: bare plural and `all`-sentence are true
in the same worlds. -/
theorem all_posExt_eq (P : Atom → W → Bool) (x : Finset Atom) :
    posExt (allPluralTV P x) = posExt (barePluralTV P x) := by
  ext w; simp only [posExt, allPluralTV, barePluralTV, Set.mem_setOf_eq]
  constructor
  · intro h; split_ifs at h <;> simp_all [pluralTruthValue_eq_true_iff]
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
  unfold pluralTruthValue Semantics.Supervaluation.superTrue allSatisfy
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all

-- ============================================================================
-- Section 2: The Effect of `all`
-- ============================================================================

omit [DecidableEq Atom] in
/-- `all`-sentences are bivalent. -/
theorem all_bivalent (P : Atom → W → Bool) (x : Finset Atom) :
    isBivalent (allPluralTV P x) := by
  intro w; simp only [allPluralTV]; split_ifs <;> simp

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
-- Section 3: Gap Enables Non-Maximal Use
-- ============================================================================

omit [DecidableEq Atom] in
/-- The gap enables non-maximal use: if the bare plural has a gap at w
and w's cell contains a positive-extension world, then the bare plural
is usable at w (assuming addressing is satisfied). This is the mechanism
Križ 2016 identifies for non-maximality: gap-worlds can be "true enough"
without being literally true.

This is an instance of the general `Semantics.Homogeneity.gap_enables_nonmax`. -/
theorem plural_gap_enables_nonmax (q : QUD W) (P : Atom → W → Bool) (x : Finset Atom)
    (w w' : W)
    (hGap : barePluralTV P x w = .indet)
    (hEquiv : q.r w w')
    (hTrue : barePluralTV P x w' = .true)
    (hAddr : addressesIssue q (barePluralTV P x)) :
    usable q (barePluralTV P x) w :=
  Semantics.Homogeneity.gap_enables_nonmax q (barePluralTV P x) w w' hGap hEquiv hTrue hAddr

-- ============================================================================
-- Section 4: Finite Model
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
    barePluralTV smiled profs .smithNeutral = .indet := by native_decide

theorem bare_onlyLeeSmiled :
    barePluralTV smiled profs .onlyLeeSmiled = .indet := by native_decide

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
-- Section 5: Connection to Empirical Data (NonMaximality.lean)
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
-- Section 6: Connection to Homogeneity Data (Homogeneity.lean)
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

-- ============================================================================
-- Section 7: Connection to Supervaluation Framework
-- ============================================================================

/-! Plural predication is an instance of supervaluation (@cite{fine-1975}).
    Each atom in the plurality is a specification point: the predicate is
    super-true iff satisfied by all atoms, super-false iff by none, and
    indefinite when some-but-not-all satisfy it (the homogeneity gap).

    This unifies two independent literatures:
    - @cite{fine-1975}: varying the *threshold* for vague predicates
    - @cite{kriz-2016}: varying the *atom* for plural predicates

    Both are instances of `Semantics.Supervaluation.superTrue`. The `dist`
    operator in `Core.Duality` is a third implementation of the same pattern
    over `List Bool`; `selectional_eq_dist` in `Counterfactual.lean` proves
    yet another instance for closest worlds. -/

open Semantics.Supervaluation (SpecSpace superTrue)

omit [DecidableEq Atom] in
/-- **Plural predication = supervaluation over atoms.** The bare plural
    "the Xs are P" at world w has the same truth value as `superTrue`
    with atoms as specification points and `P(·,w)` as the evaluation
    function.

    This is the structural identity connecting homogeneity gaps to
    vagueness gaps: both arise from disagreement across specification
    points (atoms vs thresholds vs comparison classes). -/
theorem barePluralTV_eq_superTrue (P : Atom → W → Bool)
    (x : Finset Atom) (hne : x.Nonempty) (w : W) :
    barePluralTV P x w = superTrue (fun a => P a w) ⟨x, hne⟩ := by
  simp [barePluralTV, pluralTruthValue, dif_pos hne]

omit [DecidableEq Atom] in
/-- Corollary: homogeneity (gap existence) is exactly supervaluation
    indefiniteness. If the bare plural is gapped at w, then `superTrue`
    returns `.indet` — witnesses exist on both sides. -/
theorem homogeneity_gap_is_indefiniteness (P : Atom → W → Bool)
    (x : Finset Atom) (hne : x.Nonempty) (w : W)
    (hgap : barePluralTV P x w = .indet) :
    superTrue (fun a => P a w) ⟨x, hne⟩ = Truth3.indet := by
  rw [← barePluralTV_eq_superTrue P x hne w]; exact hgap

omit [DecidableEq Atom] in
/-- Corollary: `all` removes homogeneity by collapsing the specification
    space to a single point (the universal check). This corresponds to
    Fine's fidelity theorem: singleton specification spaces are classical. -/
theorem all_removes_supervaluation_gap (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) :
    allPluralTV P x w ≠ .indet := by
  simp only [allPluralTV]; split_ifs <;> simp

end Phenomena.Plurals.Studies.Kriz2016
