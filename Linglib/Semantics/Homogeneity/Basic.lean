import Linglib.Core.Logic.Trivalent
import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Supervaluation.Basic

/-!
# Semantics.Homogeneity — Substrate for Trivalent Predication and Pragmatic Usability
[kriz-2015] [kriz-2016] [fine-1975] [beaver-krahmer-2001]

Domain-independent substrate for theories of homogeneity and non-maximality.
The framework is anchored on [kriz-2015] (Križ's dissertation); the
published [kriz-2016] is the first detailed application to plural
definites and `all`. Both rely on Fine's supervaluation ([fine-1975])
and Beaver-Krahmer's assertion operator ([beaver-krahmer-2001], encoded
here as `Trivalent.metaAssert`).

## Layered structure

This file is the substrate for `Kriz2016` (the
plural-specific instantiation) and for downstream consumers across plurals,
conditionals, modality, generics, and summative predicates that exhibit
homogeneity gaps.

## Spec-point instantiations

| Domain                  | Spec points         | Remover                     | Anchored at                                   |
|-------------------------|---------------------|-----------------------------|-----------------------------------------------|
| Plural definites        | atoms               | `all`                       | `Kriz2016`          |
| Conditionals            | closest P-worlds    | `necessarily`               | §6 below + `Conditionals.Counterfactual`      |
| Summative (spatial)     | spatial parts       | `completely` / `whole`      | not yet formalized                            |
| Generics                | subkinds            | `all`                       | not yet formalized; cf. `Cohen1999` (different equation) |
| Modal                   | best worlds         | `necessarily`               | `AghaJeretic2022`  |

The shared structure is supervaluation over specification points.

## Contents

- §1 **Trivalent Sentence Denotations**: `TrivalentProp`, `posExt`/`negExt`/`gapExt`,
   `isHomogeneous`, `isBivalent`.
- §2 **Supervaluation as Homogeneity Source**: `supervaluationTV` via `SpecSpace`.
- §3 **Homogeneity Removal**: `removeGap = Trivalent.metaAssert ∘ ·` lifted pointwise;
   preserves the positive extension while collapsing the gap into the negative.
- §4 **Pragmatic Usability**: `sufficientlyTrue`, `addressesIssue`, `usable`.
- §5 **Communicated Content**: `communicatedContent` + `bivalentPred` bridge.
- §6 **Conditional Homogeneity (CEM)**: `conditionalTV` / `strictConditionalTV`.
   See `Conditionals.Counterfactual.selectional_as_supervaluation` for the
   equivalence with the selectional formulation.
- §7 **Generalised Homogeneity (Collective Predicates)**: `generalisedTV` via
   `Finset` overlap (`¬ Disjoint`), uniformly handling distributive and collective
   predicates.
- §8 **Cross-Domain**: domain-independent consequences (`gap_enables_nonmax`,
   `removed_prevents_nonmax`, `gap_not_false`).
-/

namespace Semantics.Homogeneity

open Semantics.Supervaluation (SpecSpace superTrue superTrue_true_iff superTrue_false_iff
  superTrue_indet_iff fidelity)

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════════════════
-- § 1. Trivalent Sentence Denotations
-- ════════════════════════════════════════════════════════════════════════════

/-- A trivalent sentence denotation: maps worlds to truth values.
    This is the general type for any sentence that may exhibit homogeneity. -/
abbrev TrivalentProp (W : Type*) := W → Trivalent

/-- Positive extension: worlds where the sentence is true. -/
def posExt (S : TrivalentProp W) : Set W := {w | S w = .true}

/-- Negative extension: worlds where the sentence is false. -/
def negExt (S : TrivalentProp W) : Set W := {w | S w = .false}

/-- Extension gap: worlds where the sentence is neither true nor false. -/
def gapExt (S : TrivalentProp W) : Set W := {w | S w = .indet}

/-- The three extensions partition the world space. -/
theorem extensions_partition (S : TrivalentProp W) (w : W) :
    w ∈ posExt S ∨ w ∈ negExt S ∨ w ∈ gapExt S := by
  simp only [posExt, negExt, gapExt, Set.mem_setOf_eq]
  cases S w <;> simp

/-- The positive and negative extensions are disjoint. -/
theorem posExt_negExt_disjoint (S : TrivalentProp W) :
    posExt S ∩ negExt S = ∅ := by
  ext w; simp only [posExt, negExt, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_empty_iff_false]
  exact ⟨λ ⟨h₁, h₂⟩ => by rw [h₁] at h₂; exact absurd h₂ (by decide), False.elim⟩

/-- A sentence is homogeneous if its extension gap is non-empty.
    The gap is what enables non-maximal readings. -/
def isHomogeneous (S : TrivalentProp W) : Prop := gapExt S ≠ ∅

/-- A sentence is bivalent if it has no extension gap.
    `all`, `necessarily`, and `completely` make sentences bivalent. -/
def isBivalent (S : TrivalentProp W) : Prop :=
  ∀ w, S w = .true ∨ S w = .false

/-- A single gap-world witnesses homogeneity. -/
theorem isHomogeneous_of_gap (S : TrivalentProp W) (w : W) (h : S w = .indet) :
    isHomogeneous S := by
  intro he; rw [Set.eq_empty_iff_forall_notMem] at he
  exact he w h

/-- Bivalence and homogeneity are complementary:
    a sentence is bivalent iff it has no extension gap. -/
theorem isBivalent_iff_not_homogeneous (S : TrivalentProp W) :
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
    `eval w` gives the Prop predicate over spec points at world `w`,
    and `space w` gives the spec space at world `w`. -/
def supervaluationTV {Spec W : Type*} (eval : W → Spec → Prop)
    [∀ w s, Decidable (eval w s)] (space : W → SpecSpace Spec) : TrivalentProp W :=
  λ w => superTrue (eval w) (space w)

/-- A supervaluation sentence is true iff the predicate holds at all specs. -/
theorem supervaluationTV_true_iff {Spec W : Type*} (eval : W → Spec → Prop)
    [∀ w s, Decidable (eval w s)] (space : W → SpecSpace Spec) (w : W) :
    supervaluationTV eval space w = .true ↔
    ∀ s ∈ (space w).admissible, eval w s :=
  superTrue_true_iff (eval w) (space w)

/-- A supervaluation sentence is false iff the predicate fails at all specs. -/
theorem supervaluationTV_false_iff {Spec W : Type*} (eval : W → Spec → Prop)
    [∀ w s, Decidable (eval w s)] (space : W → SpecSpace Spec) (w : W) :
    supervaluationTV eval space w = .false ↔
    ∀ s ∈ (space w).admissible, ¬ eval w s :=
  superTrue_false_iff (eval w) (space w)

/-- A supervaluation sentence is gapped iff witnesses exist on both sides. -/
theorem supervaluationTV_gap_iff {Spec W : Type*} (eval : W → Spec → Prop)
    [∀ w s, Decidable (eval w s)] (space : W → SpecSpace Spec) (w : W) :
    supervaluationTV eval space w = .indet ↔
    (∃ s ∈ (space w).admissible, eval w s) ∧
    (∃ s ∈ (space w).admissible, ¬ eval w s) :=
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
    | Spatial     | `completely`    | "The flag is completely blue"    |
    | Spatial     | `whole`         | "The whole wall is painted"      |

    Semantically, removal collapses the gap into the negative extension:
    gap-worlds become false-worlds, preserving the positive extension. The
    pointwise operator is exactly the assertion operator 𝒜 of
    [beaver-krahmer-2001], available as `Trivalent.metaAssert`. -/

/-- Remove homogeneity: collapse gap into negative extension.
    Defined as `Trivalent.metaAssert` lifted pointwise — see `Trivalent.lean`
    for the underlying assertion operator. -/
def removeGap (S : TrivalentProp W) : TrivalentProp W :=
  λ w => Trivalent.metaAssert (S w)

/-- Removal produces a bivalent sentence. -/
theorem removeGap_bivalent (S : TrivalentProp W) :
    isBivalent (removeGap S) := by
  intro w; simp only [removeGap]; cases S w <;> simp

/-- Removal preserves the positive extension. -/
theorem removeGap_posExt_eq (S : TrivalentProp W) :
    posExt (removeGap S) = posExt S := by
  ext w; simp only [posExt, removeGap, Set.mem_setOf_eq]
  cases S w <;> simp

/-- Removal absorbs the gap into the negative extension. -/
theorem removeGap_negExt_eq (S : TrivalentProp W) :
    negExt (removeGap S) = negExt S ∪ gapExt S := by
  ext w; simp only [removeGap, negExt, gapExt, Set.mem_setOf_eq, Set.mem_union]
  cases S w <;> simp

/-- Removed sentences are never homogeneous. -/
theorem removeGap_not_homogeneous (S : TrivalentProp W) :
    ¬isHomogeneous (removeGap S) := by
  intro h; apply h; ext w
  simp only [gapExt, removeGap, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  cases S w <;> simp

-- ════════════════════════════════════════════════════════════════════════════
-- § 4. Pragmatic Usability (Križ 2016 §3)
-- ════════════════════════════════════════════════════════════════════════════

/-! The pragmatic mechanism that derives non-maximal readings from
    the homogeneity gap. Two independent principles interact:

    1. **Sufficient Trivalent**: weakens Quality to "true enough for current purposes"
    2. **Addressing an Question**: restricts which sentences can be used for which
       issues, based on alignment between truth-value boundaries and issue cells

    Together, they predict that a sentence can be used at a gap-world iff
    (i) a literally-true world is in the same issue cell, and (ii) no cell
    straddles the true/false boundary. -/

/-- Sufficient Trivalent: S is "true enough" at world w relative to issue I
    iff there is a world w' that is I-equivalent to w where S is literally true.

    This weakens the standard maxim of quality: a speaker need not assert
    something literally true, only something equivalent to something true
    for current purposes. -/
def sufficientlyTrue (q : QUD W) (S : TrivalentProp W) (w : W) : Prop :=
  ∃ w', q.r w w' ∧ S w' = .true

instance sufficientlyTrue.instDecidable [Fintype W] (q : QUD W) (S : TrivalentProp W) (w : W) :
    Decidable (sufficientlyTrue q S w) :=
  inferInstanceAs (Decidable (∃ w', q.r w w' ∧ S w' = .true))

/-- Literal truth implies sufficient truth (for any issue). -/
theorem literal_imp_sufficient (q : QUD W) (S : TrivalentProp W) (w : W)
    (h : S w = .true) : sufficientlyTrue q S w :=
  ⟨w, q.iseqv.refl w, h⟩

/-- Addressing an Question: S may be used to address issue I only if no
    cell of I overlaps with both the positive and the negative extension.

    Gap-worlds are invisible: a cell containing true-worlds and gap-worlds
    is fine. Only a cell straddling the true/false boundary is problematic. -/
def addressesIssue (q : QUD W) (S : TrivalentProp W) : Prop :=
  ¬∃ w₁ w₂, q.r w₁ w₂ ∧ S w₁ = .true ∧ S w₂ = .false

instance addressesIssue.instDecidable [Fintype W] (q : QUD W) (S : TrivalentProp W) :
    Decidable (addressesIssue q S) :=
  inferInstanceAs (Decidable (¬∃ w₁ w₂, q.r w₁ w₂ ∧ S w₁ = .true ∧ S w₂ = .false))

/-- A sentence may be used at w iff: (1) S is not false at w,
    (2) S is sufficiently true at w, and (3) S addresses the issue. -/
def usable (q : QUD W) (S : TrivalentProp W) (w : W) : Prop :=
  S w ≠ .false ∧ sufficientlyTrue q S w ∧ addressesIssue q S

instance usable.instDecidable [Fintype W] (q : QUD W) (S : TrivalentProp W) (w : W) :
    Decidable (usable q S w) :=
  inferInstanceAs (Decidable (S w ≠ .false ∧ sufficientlyTrue q S w ∧ addressesIssue q S))

/-- For bivalent sentences, usability reduces to literal truth + addressing.
    Sufficient Trivalent adds nothing because there are no gap-worlds. -/
theorem bivalent_usable_iff_true (q : QUD W) (S : TrivalentProp W)
    (hbiv : isBivalent S) (w : W) :
    usable q S w ↔ S w = .true ∧ addressesIssue q S := by
  constructor
  · intro ⟨hNotFalse, _, hAddr⟩
    exact ⟨by cases hbiv w with | inl h => exact h | inr h => exact absurd h hNotFalse, hAddr⟩
  · intro ⟨hTrue, hAddr⟩
    exact ⟨by simp [hTrue], literal_imp_sufficient q S w hTrue, hAddr⟩

/-! ### Strong relevance (K&S 2021)

Bivalent counterpart of `addressesIssue`: a `W → Prop` is *strongly relevant*
to a QUD when it is constant on each cell of the partition. For bivalent
sentences this is equivalent to `addressesIssue` (bridge:
`bivalent_addressing_iff_stronglyRelevant` in `Studies/KrizSpector2021.lean`).

Originates with [kriz-spector-2021] §3; consolidated here as substrate
since it is a generic property of partition-respecting predicates, not
specific to plural predication. -/

/-- A proposition is **strongly relevant** to a QUD iff it is constant on
    each cell of the QUD partition. -/
def isStronglyRelevantProp (q : QUD W) (p : W → Prop) : Prop :=
  ∀ w₁ w₂ : W, q.r w₁ w₂ → (p w₁ ↔ p w₂)

/-- Filter a set of propositions to those strongly relevant to `q`. -/
def stronglyRelevantSet (q : QUD W) (candidates : Set (W → Prop)) :
    Set (W → Prop) :=
  { p ∈ candidates | isStronglyRelevantProp q p }

/-- With the trivial QUD (all worlds in one cell), strong relevance reduces
    to constancy on `W`. -/
theorem trivial_relevant_iff_constant (p : W → Prop) :
    isStronglyRelevantProp (QUD.trivial (M := W)) p ↔
    ∀ w₁ w₂ : W, p w₁ ↔ p w₂ := by
  simp only [isStronglyRelevantProp, QUD.trivial_r]
  exact ⟨fun h w₁ w₂ => h w₁ w₂ ⟨⟩, fun h _ _ _ => h _ _⟩

/-- With the exact QUD (singleton cells), every proposition is strongly
    relevant. -/
theorem exact_all_relevant [BEq W] [LawfulBEq W] (p : W → Prop) :
    isStronglyRelevantProp (QUD.exact (M := W)) p := by
  intro w₁ w₂ h
  rw [show w₁ = w₂ from h]

/-- With the exact QUD, the strongly-relevant filter is the identity. -/
theorem exact_stronglyRelevantSet_eq [BEq W] [LawfulBEq W]
    (candidates : Set (W → Prop)) :
    stronglyRelevantSet (QUD.exact (M := W)) candidates = candidates := by
  ext p
  simp only [stronglyRelevantSet, Set.mem_sep_iff]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, exact_all_relevant p⟩⟩

/-! ### Communicated Content -/

/-- The communicated content of S relative to issue I: the set of worlds
    the hearer considers possible after hearing S.

    This is the union of all issue cells that overlap with ⟦S⟧⁺.
    The hearer infers not that S is literally true, but that the actual world
    is indistinguishable (relative to current purposes) from one where S is
    literally true. -/
def communicatedContent (q : QUD W) (S : TrivalentProp W) : Set W :=
  {w | sufficientlyTrue q S w}

/-- Literal truth is always communicated. -/
theorem posExt_subset_communicated (q : QUD W) (S : TrivalentProp W) :
    posExt S ⊆ communicatedContent q S :=
  λ _ hw => literal_imp_sufficient q S _ hw

/-- For bivalent sentences that address the issue, communicated content
    equals the positive extension — no pragmatic weakening is possible.

    This is the key consequence of gap removal: `all`/`necessarily`/`completely`
    force literal truth to be communicated. -/
theorem bivalent_communicated_eq_posExt (q : QUD W) (S : TrivalentProp W)
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

    This is [kriz-2016]'s key prediction: coarser QUDs enable more
    non-maximal use. The finite model in `Kriz2016`
    demonstrates this: `coarseQ` communicates `smithNeutral` but `fineQ`
    does not. -/
theorem communicatedContent_antitone (q q' : QUD W) (S : TrivalentProp W)
    (hRef : ∀ w₁ w₂, q'.r w₁ w₂ → q.r w₁ w₂) :
    communicatedContent q' S ⊆ communicatedContent q S :=
  fun _ ⟨w', hEq, hTrue⟩ => ⟨w', hRef _ _ hEq, hTrue⟩

/-- Extract the Bool truth predicate from a bivalent sentence.
    Used to bridge between the trivalent Addressing constraint and
    bivalent strong-relevance filtering (Križ & Spector 2021). -/
def bivalentPred (S : TrivalentProp W) : W → Bool :=
  λ w => S w == .true

-- ════════════════════════════════════════════════════════════════════════════
-- § 6. Conditional Homogeneity (CEM)
-- ════════════════════════════════════════════════════════════════════════════

/-! [kriz-2016] §6.4: Conditionals are the modal analogue of plural
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

    [stalnaker-1981] [von-fintel-1999] -/

section ConditionalHomogeneity

variable {W : Type*} [DecidableEq W]

/-- A bare conditional "if P, Q" as a trivalent sentence.
    The spec points are the closest P-worlds; the eval function is Q.
    TRUE if Q holds at all closest P-worlds, FALSE if Q fails at all,
    GAP otherwise (conditional excluded middle).

    This is the same computation as `selectionalCounterfactual` in
    `Semantics.Conditionals.Counterfactual`, which proves the
    equivalence with `superTrue` via `selectional_as_supervaluation`. The
    two formalizations use different input representations (Finset vs
    SimilarityOrdering) but compute the same three-valued truth value. -/
def conditionalTV (closestPWorlds : W → Finset W) (Q : W → Prop) [DecidablePred Q] :
    TrivalentProp W :=
  λ w =>
    let pWorlds := closestPWorlds w
    if h : pWorlds.Nonempty then
      superTrue Q ⟨pWorlds, h⟩
    else .true  -- vacuously true if no closest P-worlds

/-- A strict conditional "if P, necessarily Q" — the `all` of conditionals.
    Defined as gap removal on the bare conditional: `necessarily` collapses
    the homogeneity gap, just as `all` does for plurals. -/
def strictConditionalTV (closestPWorlds : W → Finset W) (Q : W → Prop) [DecidablePred Q] :
    TrivalentProp W :=
  removeGap (conditionalTV closestPWorlds Q)

omit [DecidableEq W] in
/-- Strict conditionals are bivalent — `necessarily` removes the gap,
    just as `all` removes homogeneity for plurals. -/
theorem strictConditionalTV_bivalent (closestPWorlds : W → Finset W)
    (Q : W → Prop) [DecidablePred Q] :
    isBivalent (strictConditionalTV closestPWorlds Q) :=
  removeGap_bivalent _

omit [DecidableEq W] in
/-- Positive extensions agree: the bare conditional and the strict conditional
    are true in the same worlds. Parallel to `all_posExt_eq` for plurals. -/
theorem conditionalTV_posExt_eq (closestPWorlds : W → Finset W)
    (Q : W → Prop) [DecidablePred Q] :
    posExt (conditionalTV closestPWorlds Q) = posExt (strictConditionalTV closestPWorlds Q) :=
  (removeGap_posExt_eq _).symm

omit [DecidableEq W] in
/-- `necessarily` prevents non-maximal use of conditionals, just as `all`
    does for plurals. If a strict conditional is usable at w, Q holds at
    all closest P-worlds (when they exist). -/
theorem necessarily_prevents_nonmax (q : QUD W) (closestPWorlds : W → Finset W)
    (Q : W → Prop) [DecidablePred Q] (w : W)
    (h : usable q (strictConditionalTV closestPWorlds Q) w)
    (hne : (closestPWorlds w).Nonempty) :
    ∀ w' ∈ closestPWorlds w, Q w' := by
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

/-! [kriz-2016] §5.1: Homogeneity for collective predicates is defined
    via **mereological overlap**, not individual atoms. A predicate P is
    undefined of plurality a if a is not in P's positive extension but
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

/-- Two pluralities overlap if they share at least one individual.
    Defined as `¬ Disjoint`, the mathlib idiom. -/
def overlaps (a b : Finset Atom) : Prop := ¬ Disjoint a b

instance (a b : Finset Atom) : Decidable (overlaps a b) :=
  inferInstanceAs (Decidable (¬ Disjoint a b))

/-- Generalised homogeneity: trivalent truth for predicates on pluralities.
    Handles both distributive and collective predicates uniformly.

    - TRUE:  P holds of a
    - GAP:   P doesn't hold of a, but some overlapping plurality in `domain` satisfies P
    - FALSE: no overlapping plurality in `domain` satisfies P

    `domain` is the set of all relevant pluralities (e.g., all subgroups
    of the universe of discourse). For distributive predicates, singletons
    suffice; for collective predicates, larger groups are needed. -/
def generalisedTV (P : Finset Atom → Prop) [DecidablePred P]
    (domain : Finset (Finset Atom)) (a : Finset Atom) : Trivalent :=
  if P a then .true
  else if ∃ b ∈ domain, overlaps a b ∧ P b then .indet
  else .false

/-- Generalised homogeneity is a genuine three-way partition. -/
theorem generalisedTV_trichotomy (P : Finset Atom → Prop) [DecidablePred P]
    (domain : Finset (Finset Atom)) (a : Finset Atom) :
    generalisedTV P domain a = .true ∨
    generalisedTV P domain a = .false ∨
    generalisedTV P domain a = .indet := by
  simp only [generalisedTV]; split_ifs <;> simp

/-- If P holds of a, the generalised truth value is TRUE. -/
theorem generalisedTV_true_of_holds (P : Finset Atom → Prop) [DecidablePred P]
    (domain : Finset (Finset Atom)) (a : Finset Atom) (h : P a) :
    generalisedTV P domain a = .true := by
  simp [generalisedTV, h]

/-- For distributive predicates, the generalised definition coincides with
    supervaluation over atoms when the domain includes all singletons of
    members. The distributive predicate `∀ x ∈ s, pred x` is checked
    against each sub-plurality; the overlap condition reduces to checking
    individual atoms of `a`. -/
theorem generalisedTV_distributive_reduction
    (pred : Atom → Prop) [DecidablePred pred] (a : Finset Atom) (hne : a.Nonempty)
    (domain : Finset (Finset Atom))
    (hdomain : ∀ x ∈ a, {x} ∈ domain) :
    generalisedTV (fun s => ∀ x ∈ s, pred x) domain a =
    superTrue pred ⟨a, hne⟩ := by
  unfold generalisedTV superTrue
  by_cases hall : ∀ x ∈ a, pred x
  · rw [if_pos hall, if_pos hall]
  · rw [if_neg hall, if_neg hall]
    by_cases hnone : ∀ x ∈ a, ¬ pred x
    · -- None satisfy: both return .false
      have hNoWitness : ¬ ∃ b ∈ domain, overlaps a b ∧ ∀ x ∈ b, pred x := by
        rintro ⟨b, _, hov, hPb⟩
        obtain ⟨y, hy⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hov
        rw [Finset.mem_inter] at hy
        exact hnone y hy.1 (hPb y hy.2)
      rw [if_neg hNoWitness, if_pos hnone]
    · -- Mixed: both return .indet
      push Not at hnone
      obtain ⟨x, hxa, hpx⟩ := hnone
      have hOv : overlaps a {x} := by
        unfold overlaps
        rw [Finset.disjoint_singleton_right]
        exact fun h => h hxa
      have hWitness : ∃ b ∈ domain, overlaps a b ∧ ∀ y ∈ b, pred y :=
        ⟨{x}, hdomain x hxa, hOv,
          fun y hy => by rw [Finset.mem_singleton.mp hy]; exact hpx⟩
      rw [if_pos hWitness, if_neg]
      intro hf; exact hf x hxa hpx

end GeneralisedHomogeneity

-- ════════════════════════════════════════════════════════════════════════════
-- § 8. Cross-Domain Unification
-- ════════════════════════════════════════════════════════════════════════════

/-! The central insight of [kriz-2016]: all homogeneity phenomena share
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
theorem removed_prevents_nonmax (q : QUD W) (S : TrivalentProp W) (w : W)
    (h : usable q (removeGap S) w) : removeGap S w = .true := by
  cases hbiv : (removeGap S w) with
  | true => rfl
  | false => exact absurd hbiv h.1
  | indet =>
    -- removeGap never produces .indet
    exfalso; cases hSw : S w <;> simp_all [removeGap]

/-- The gap enables non-maximal use: if S is gapped at w and w's cell
    contains a true-world, then S is usable at w (assuming addressing). -/
theorem gap_enables_nonmax (q : QUD W) (S : TrivalentProp W) (w w' : W)
    (hGap : S w = .indet)
    (hEquiv : q.r w w')
    (hTrue : S w' = .true)
    (hAddr : addressesIssue q S) :
    usable q S w :=
  ⟨by simp [hGap], ⟨w', hEquiv, hTrue⟩, hAddr⟩

/-- Gap-worlds are never false, so they satisfy the first usability condition. -/
theorem gap_not_false (S : TrivalentProp W) (w : W) (h : S w = .indet) :
    S w ≠ .false := by simp [h]

/-- Unmentionability of exceptions ([kriz-2016] §4.1): when `S` is used
    at `w` under issue `q`, an exception-mentioning sentence `E` — true at `w`
    but false wherever `S` is literally true — cannot address the same issue.
    `w`'s cell contains a literally-true world (by `sufficientlyTrue`), and
    `E` straddles the true/false boundary between `w` and that world. -/
theorem exception_unaddressable (q : QUD W) (S E : TrivalentProp W) (w : W)
    (hUse : usable q S w) (hEw : E w = .true)
    (hEfalse : ∀ w', S w' = .true → E w' = .false) :
    ¬ addressesIssue q E := by
  obtain ⟨-, ⟨w', hEq, hTrue⟩, -⟩ := hUse
  exact λ hAddr => hAddr ⟨w, w', hEq, hEw, hEfalse w' hTrue⟩

end CrossDomain

end Semantics.Homogeneity
