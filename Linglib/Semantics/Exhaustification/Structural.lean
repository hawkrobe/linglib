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

* `innocent_exh_singleton_proper` — when `ALT = {α}` with `α ⊊ φ`,
  the IE operator returns `φ \ α`. This is the partial-scalar
  exhaustification case (yek-i's root uniqueness reading,
  @cite{alonso-ovalle-moghiseh-2025} eq. 93a).

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
  -- a is innocently excludable, so a ∈ every MC-set, in particular it's
  -- consistently negatable alongside φ. So φ ⊄ a (there's a φ-world
  -- outside a). Therefore tolerant negates a too. So if w were in a,
  -- tolerant would have excluded w from φ, contradicting hw_neg.
  apply hw_neg a ha_alt
  · -- ¬ φ ⊆ a: follows from a being innocently excludable
    intro hsub
    -- If φ ⊆ a, then negating a is inconsistent with φ — contradicts IE
    have hφ_mem : φ ∈ Innocent.innocentlyExcludable ALT φ →
                  False := by
      sorry -- needs lemma "if φ ⊆ a then a ∉ IE"
    sorry -- TODO: complete via existing characterization
  · exact hw_a

/-- **Singleton excludable alt**: when `ALT = {α}` and `α ⊊ φ`,
exhaustification returns `φ \ α`. This is yek-i's partial-scalar
exhaustification result (@cite{alonso-ovalle-moghiseh-2025} eq. 93a):
with a single innocently-excludable alternative, IE returns it exactly,
giving "exactly one" semantics.

**TODO**: proof requires showing `innocentlyExcludable {α} φ = {α}`
when `α ⊊ φ`, via the existing MCE characterization (the unique MCE is
`{α}` itself; intersecting over a singleton family gives `{α}`). -/
theorem innocent_exh_singleton_proper {α φ : Finset W}
    (_hsub : α ⊆ φ) (_hne : α ≠ φ) :
    innocent.exh ({α} : Finset (Finset W)) φ = φ \ α := by
  sorry

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
