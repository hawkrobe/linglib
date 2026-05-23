import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Semantics.Exhaustification.Tolerant
import Mathlib.Tactic.DeriveFintype

/-!
# Structural-pattern theorems for IE and tolerant exhaustification
@cite{fox-2007} @cite{chierchia-2013} @cite{alonso-ovalle-moghiseh-2025}

The algorithmic characterizations of innocent exclusion (Fox 2007) and
tolerant exhaustification (Chierchia 2013) live in
`Linglib/Semantics/Exhaustification/Operators/{Basic,Decidable}.lean`,
exposed through the `Excluder` packaging in
`InnocentExclusion.lean` / `Tolerant.lean`. *Concrete* paper analyses
typically need a different shape of theorem: "for an alternative set of
structural shape X (singleton excludable / pairwise-disjoint cover /
complement-partition / Kripke-frame lift / ...), the operator returns
this specific value." That bridging layer is what this file provides.

## Main results

* `tolerant_exh_eq_empty_iff` — `tolerant.exh ALT φ = ∅` iff every
  φ-world belongs to some non-entailed alternative. This is the
  algorithm-level characterization of "contradictory tolerant
  exhaustification" used in @cite{alonso-ovalle-moghiseh-2025}'s
  eq. 92 / root_full_tolerant_contradiction.

* `innocent_exh_pairwise_disjoint_partial` — when `(φ \ ALT.sup id)`
  is nonempty (the alts don't cover `φ`), every alternative is
  innocently excludable and `innocent.exh ALT φ = φ \ ALT.sup id`.
  The partial-cover witness suffices for joint
  full-exclusion-consistency across all `α ∈ ALT` simultaneously.
  Drives @cite{alonso-ovalle-moghiseh-2025}'s root domain-only
  result (eq. 93b) and the deontic split-exh results (eq. 119, 120).

* `innocent_exh_singleton_proper` — corollary of the above for
  `|ALT| = 1`: when `α ⊊ φ`, `innocent.exh {α} φ = φ \ α`. Drives
  yek-i's root uniqueness reading
  (@cite{alonso-ovalle-moghiseh-2025} eq. 93a).

* `tolerant_exh_subset_innocent_exh` — Chierchia's tolerant operator
  is always ⊆ Fox's innocent operator. Concrete form of the
  "tolerant excludes ≥ as much" lemma motivating the IE/tolerant
  divergence on EFCI alternative sets.

## Implementation notes

The theorems here are stated against `innocent.exh` / `tolerant.exh`
(the `Excluder` packagings) rather than the lower-level
`Innocent.innocentlyExcludable` substrate. This is the API consumed by
study files, so theorems at this layer slot in directly.

Pure-logic facts about "exclusive satisfiers of a predicate"
(`P d ∧ ∀ e ≠ d, ¬P e`) — which characterize the structural shape of
*pre-exhaustified* domain alternatives — live in
`Linglib/Core/Logic/Quantification/Exclusive.lean`. That file is
framework-agnostic; this file is the Excluder-API specialization.

## Todo

* `innocent_exh_pairwise_disjoint_cover` — when ALT's members are
  pairwise disjoint and their union covers φ, IE = ∅ (the Spector
  closure-failure case driving @cite{alonso-ovalle-moghiseh-2025}
  eq. 101's missing third MCE). Stated as a `sorry` for now; proof
  requires constructing MCEs as ALT-minus-one-element subsets and
  showing their intersection is empty.

* Kripke-frame lift: a `D → Bool` predicate transports to
  `W → Bool` via `λ w => Acc w ∧ ∃ d, P d w`. The structural results
  about D-shape ALT sets should lift through this transport.
-/

namespace Exhaustification

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ## Tolerant: structural characterizations -/

/-- **Tolerant vacuity (forward)**: if every φ-world belongs to some
non-entailed alternative, then `tolerant.exh ALT φ = ∅`. The "tolerant
contradiction" case driving @cite{alonso-ovalle-moghiseh-2025} eq. 92. -/
theorem tolerant_exh_eq_empty_of_covered
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : ∀ w ∈ φ, ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α) :
    tolerant.exh ALT φ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro w hmem
  rw [mem_tolerant_exh_iff] at hmem
  obtain ⟨hw_phi, hw_neg⟩ := hmem
  obtain ⟨α, hα_ALT, hα_neg, hw_α⟩ := h w hw_phi
  exact hw_neg α hα_ALT hα_neg hw_α

/-- **Tolerant vacuity (backward)**: if `tolerant.exh ALT φ = ∅`, then
every φ-world belongs to some non-entailed alternative. -/
theorem covered_of_tolerant_exh_eq_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : tolerant.exh ALT φ = ∅) (w : W) (hw : w ∈ φ) :
    ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α := by
  by_contra hcon
  push Not at hcon
  have hw_exh : w ∈ tolerant.exh ALT φ := by
    rw [mem_tolerant_exh_iff]
    refine ⟨hw, fun α hα_ALT hα_neg hw_α => ?_⟩
    exact hcon α hα_ALT hα_neg hw_α
  simp [h] at hw_exh

/-- **Tolerant vacuity, biconditional**: combines the two directions. -/
theorem tolerant_exh_eq_empty_iff (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.exh ALT φ = ∅ ↔ ∀ w ∈ φ, ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α :=
  ⟨covered_of_tolerant_exh_eq_empty, tolerant_exh_eq_empty_of_covered⟩

/-! ## Innocent: structural characterizations -/

/-- **Innocent ≤ tolerant**: Fox's IE operator returns at least as many
worlds as Chierchia's tolerant operator. Equivalently, the tolerant
exhaustified set is contained in the innocent one.

The reason: tolerant excludes *every* non-entailed alternative
unconditionally; innocent only excludes those in every MCE. The MCE
condition is strictly stronger, so fewer alternatives get excluded,
which means fewer worlds get removed from `φ`. -/
theorem tolerant_exh_subset_innocent_exh
    (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.exh ALT φ ⊆ innocent.exh ALT φ := by
  intro w hw
  rw [mem_tolerant_exh_iff] at hw
  rw [Excluder.mem_exh_iff]
  obtain ⟨hw_phi, hw_neg⟩ := hw
  refine ⟨hw_phi, fun a ha_ie hw_a => ?_⟩
  have ha_alt : a ∈ ALT := Innocent.innocentlyExcludable_subset ALT φ ha_ie
  -- a is innocently excludable, so its negation is consistent with φ —
  -- i.e., there is some φ-world outside a. So ¬(φ ⊆ a), and tolerant
  -- negates a. Then if w ∈ a, tolerant would have excluded w, contra.
  apply hw_neg a ha_alt
  · -- ¬ φ ⊆ a: follows from a being innocently excludable.
    intro hsub
    -- Bridge Finset → Set, then apply `not_isInnocentlyExcludable_of_phi_subset`.
    have hSet : Exhaustification.IsInnocentlyExcludable
        (Innocent.asSetOfSets ALT) (↑φ : Set W) (↑a : Set W) :=
      (Innocent.isInnocentlyExcludable_iff ALT φ a).mpr ha_ie
    have hfin : Set.Finite (Innocent.asSetOfSets ALT) :=
      (Set.toFinite _).image _
    have hsat : ∃ x : W, (↑φ : Set W) x := ⟨w, hw_phi⟩
    have h_subset_set : (↑φ : Set W) ⊆ (↑a : Set W) := fun x hx => hsub hx
    exact Exhaustification.not_isInnocentlyExcludable_of_phi_subset
        hfin hsat h_subset_set hSet
  · exact hw_a

/-- **Partial-cover alts**: when `(φ \ ALT.sup id).Nonempty`, every
alternative in `ALT` is innocently excludable, and
`innocent.exh ALT φ = φ \ ALT.sup id`.

The "consumer-intent" hypotheses one might expect — `∀ α ∈ ALT, α ⊆ φ`
and `(ALT : Set _).PairwiseDisjoint id` — turn out to be *unused*. The
single witness `w ∈ φ \ ALT.sup id` discharges
`IsInnocentlyExcludable.of_full_exclusion_consistent` for every
`α ∈ ALT` simultaneously: the witness condition `w ∈ φ ∧ ∀ b ∈ ALT, w ∉ b`
doesn't depend on which `α` is being shown excludable. The MC-set
`{φ} ∪ ((univ \ ·) '' ALT)` is then unique and contains every
complement, so `innocentlyExcludable ALT φ = ALT`.

This lets the same substrate result fire on consumer patterns where the
alts aren't subsets of `φ` (e.g., AOM 2025's `□`-side pre-exhaustified
domain alts — `boxB1 ∧ ¬boxB2` extends outside `□(b₁⊻b₂)` to worlds
where `canJoint` is true). `φ \ ALT.sup id` masks the out-of-φ portion
of each alt automatically.

Generalizes `innocent_exh_singleton_proper` (the `|ALT| = 1` case;
derived as a corollary below). The complementary case where
`ALT.sup id ⊇ φ` (so `hcompat` fails) is covered by
`innocent_exh_eq_phi_of_innocentlyExcludable_empty` when IE collapses. -/
theorem innocent_exh_pairwise_disjoint_partial
    {ALT : Finset (Finset W)} {φ : Finset W}
    (hcompat : (φ \ ALT.sup id).Nonempty) :
    innocent.exh ALT φ = φ \ ALT.sup id := by
  -- Step 1: innocentlyExcludable ALT φ = ALT.
  have h_ie_eq : Innocent.innocentlyExcludable ALT φ = ALT := by
    refine Finset.Subset.antisymm (Innocent.innocentlyExcludable_subset _ _) ?_
    intro α hα
    rw [← Innocent.isInnocentlyExcludable_iff]
    apply Exhaustification.IsInnocentlyExcludable.of_full_exclusion_consistent
    · exact Innocent.mem_asSetOfSets.mpr ⟨α, hα, rfl⟩
    · obtain ⟨w, hw⟩ := hcompat
      rw [Finset.mem_sdiff] at hw
      obtain ⟨hw_phi, hw_not_sup⟩ := hw
      refine ⟨w, hw_phi, ?_⟩
      intro b hb
      rcases Innocent.mem_asSetOfSets.mp hb with ⟨β, hβ_mem, rfl⟩
      intro hw_β
      apply hw_not_sup
      rw [Finset.sup_eq_biUnion]
      exact Finset.mem_biUnion.mpr ⟨β, hβ_mem, hw_β⟩
  -- Step 2: unfold `exh` and convert `biUnion id` to `sup id`.
  show φ \ ((Innocent.innocentlyExcludable ALT φ).biUnion id) = φ \ ALT.sup id
  rw [h_ie_eq, ← Finset.sup_eq_biUnion]

/-- **Singleton excludable alt**: when `ALT = {α}` and `α ⊊ φ`,
exhaustification returns `φ \ α`. This is yek-i's partial-scalar
exhaustification result (@cite{alonso-ovalle-moghiseh-2025} eq. 93a):
with a single innocently-excludable alternative, IE returns it exactly,
giving "exactly one" semantics.

Corollary of `innocent_exh_pairwise_disjoint_partial`: `{α}.sup id = α`,
and `α ⊂ φ` provides the partial-cover witness. -/
theorem innocent_exh_singleton_proper {α φ : Finset W} (h : α ⊂ φ) :
    innocent.exh ({α} : Finset (Finset W)) φ = φ \ α := by
  have hsup : ({α} : Finset (Finset W)).sup id = α := Finset.sup_singleton
  have hcompat : (φ \ ({α} : Finset (Finset W)).sup id).Nonempty := by
    rw [hsup]; exact (Finset.exists_of_ssubset h).imp fun _ ⟨h₁, h₂⟩ =>
      Finset.mem_sdiff.mpr ⟨h₁, h₂⟩
  rw [innocent_exh_pairwise_disjoint_partial hcompat, hsup]

end Exhaustification

/-! ## Smoke test

A 2-world finite example that exercises the API surface:
- Worlds: `Two = w0 | w1`
- φ = {w0, w1}
- α = {w0}
- Expected: `innocent.exh {α} φ = {w1}` (= `φ \ α`), but proved
  directly via `decide` rather than the (still-`sorry`) general
  `innocent_exh_singleton_proper`.

The smoke test ensures the imports + namespace + Finset wrangling
compose correctly even before the general theorems are fully proved.
-/

section SmokeTest

inductive Two : Type
  | w0 | w1
  deriving DecidableEq, Repr, Fintype

open Exhaustification

private def twoPhi : Finset Two := Finset.univ
private def twoAlt : Finset Two := {Two.w0}
private def twoALT : Finset (Finset Two) := {twoAlt}

example : innocent.exh twoALT twoPhi = {Two.w1} := by decide

example : tolerant.exh twoALT twoPhi = {Two.w1} := by decide

end SmokeTest
