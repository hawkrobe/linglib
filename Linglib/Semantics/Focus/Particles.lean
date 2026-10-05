module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Presupposition.Defs

/-!
# The focus particles *only* and *even*

This file defines the exclusive *only* and the scalar presupposition of *even*, with
propositions as `Set W`. Following Coppock and Beaver, *only* relates its prejacent to a set of
alternative propositions ranked by strength: it presupposes that some true alternative is at
least as strong as the prejacent and asserts that no true alternative is stronger. On the
entailment scale the assertion is the exclusion `Exhaustification.excludes`, and with the
prejacent among the alternatives the presupposition is the prejacent itself, von Fintel's entry
for propositional *only*; on the identity scale the assertion is Rooth's.

A likelihood is a monotone map from propositions into a partial order, so that a stronger
proposition is at most as likely; the presupposition of *even*, after Karttunen and Peters, is
that the prejacent is less likely than every focus alternative.

## Main definitions

* `Focus.Particles.atLeast`, `Focus.Particles.atMost`: some true alternative is at least as
  strong as the prejacent, and no true alternative is stronger.
* `Focus.Particles.only`: the exclusive, presupposing `atLeast` and asserting `atMost`.
* `Focus.Particles.evenPresup`: the prejacent is less likely than every alternative.

## Main results

* `Focus.Particles.only_subset_eq`, `Focus.Particles.truthSet_only_subset`: on the entailment
  scale *only* presupposes its prejacent and asserts the exclusion, and is true exactly where the
  exhaustification `Exhaustification.exh` is.
* `Focus.Particles.atMost_eq_eq_atMost_subset`: the identity-scale assertion is the
  entailment-scale one when the prejacent entails no other alternative.
* `Focus.Particles.antitone_atMost`: on a scale refining entailment, strengthening the prejacent
  strengthens the assertion.
* `Focus.Particles.not_evenPresup_of_subset`: under a monotone likelihood an alternative that
  entails the prejacent refutes the presupposition of *even*, the clash from which Lahiri derives
  the distribution of *even one* items.
* `Focus.Particles.evenPresup_iff_ne`: when the prejacent entails every alternative, the
  presupposition asks only that no alternative be exactly as likely.

## Implementation notes

The scale is a relation `S`, with `S q p` read as `q` being at least as strong as `p`; the
entailment scale is `(· ⊆ ·)`. Coppock and Beaver's existential presupposition is used rather
than Beaver and Clark's, which also requires the lower-ranked alternatives to be false.
Francescotti weakens the universal force of the presupposition of *even* to a majority
threshold, in `Studies/Francescotti1995.lean`.

## References

* [coppock-beaver-2014]
* [beaver-clark-2008]
* [rooth-1992]
* [von-fintel-1999]
* [karttunen-peters-1979]
* [lahiri-1998]
* [crnic-2014]
* [francescotti-1995]
-/

@[expose] public section

namespace Focus.Particles

open Exhaustification Presupposition

/-! ### *Only* -/

section Only

variable {W : Type*} (S : Set W → Set W → Prop) (C : Set (Set W)) (p : Set W)

/-- `atLeast S C p` holds where some true alternative in `C` is at least as strong as `p` on the
scale `S` ([coppock-beaver-2014]'s MIN). -/
def atLeast : Set W := {w | ∃ q ∈ C, w ∈ q ∧ S q p}

/-- `atMost S C p` holds where every true alternative in `C` is at most as strong as `p` on the
scale `S` ([coppock-beaver-2014]'s MAX). -/
def atMost : Set W := {w | ∀ q ∈ C, w ∈ q → S p q}

/-- *Only p* over the alternatives `C` ranked by `S` presupposes `atLeast S C p` and asserts
`atMost S C p` ([coppock-beaver-2014]'s (73)). -/
def only : PartialProp W := ⟨(· ∈ atLeast S C p), (· ∈ atMost S C p)⟩

variable {S C p} {q : Set W} {w : W}

@[simp] theorem mem_atLeast : w ∈ atLeast S C p ↔ ∃ q ∈ C, w ∈ q ∧ S q p := Iff.rfl

@[simp] theorem mem_atMost : w ∈ atMost S C p ↔ ∀ q ∈ C, w ∈ q → S p q := Iff.rfl

theorem only_presup : (only S C p).presup = (· ∈ atLeast S C p) := rfl

theorem only_assertion : (only S C p).assertion = (· ∈ atMost S C p) := rfl

/-- A true alternative that `p` does not reach on the scale refutes the assertion. -/
theorem notMem_atMost (hq : q ∈ C) (hw : w ∈ q) (h : ¬ S p q) : w ∉ atMost S C p :=
  fun hm ↦ h (hm q hq hw)

/-- On a scale on which a weaker proposition never outranks a stronger one, strengthening the
prejacent strengthens the assertion. -/
theorem antitone_atMost (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) : Antitone (atMost S C) :=
  fun _ _ hpq _ hw r hr hwr ↦ hS hpq (hw r hr hwr)

/-! #### The entailment scale -/

/-- On the entailment scale the assertion is the exclusion `Exhaustification.excludes`. -/
theorem atMost_subset : atMost (· ⊆ ·) C p = excludes C p := rfl

/-- On the entailment scale the presupposition entails the prejacent. -/
theorem atLeast_subset_subset : atLeast (· ⊆ ·) C p ⊆ p := fun _ ⟨_, _, hw, hq⟩ ↦ hq hw

/-- On the entailment scale, with the prejacent among the alternatives, the presupposition is the
prejacent. -/
theorem atLeast_subset_eq (hp : p ∈ C) : atLeast (· ⊆ ·) C p = p :=
  atLeast_subset_subset.antisymm fun _ hw ↦ ⟨p, hp, hw, subset_rfl⟩

/-- On the entailment scale, with the prejacent among the alternatives, *only* presupposes its
prejacent and asserts the exclusion ([von-fintel-1999]'s (68a)). -/
theorem only_subset_eq (hp : p ∈ C) : only (· ⊆ ·) C p = ⟨(· ∈ p), (· ∈ excludes C p)⟩ :=
  PartialProp.ext (by rw [only_presup, atLeast_subset_eq hp]) rfl

/-- Where it is defined and true, *only* on the entailment scale is the exhaustification
`Exhaustification.exh`. -/
theorem truthSet_only_subset (hp : p ∈ C) : (only (· ⊆ ·) C p).truthSet = exh C p := by
  rw [only_subset_eq hp]
  rfl

/-! #### The identity scale -/

/-- When the prejacent entails no other alternative, the identity-scale assertion, that every true
alternative is the prejacent, is the entailment-scale one. -/
theorem atMost_eq_eq_atMost_subset (h : ∀ q ∈ C, p ⊆ q → q = p) :
    atMost (· = ·) C p = atMost (· ⊆ ·) C p :=
  Set.ext fun _ ↦ (forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ eq_comm).trans
    (mem_excludes_iff_forall_eq h).symm

end Only

/-! ### *Even* -/

section Even

variable {W α : Type*} [PartialOrder α] {μ : Set W → α} {p q : Set W} {alts : Set (Set W)}

/-- The scalar presupposition of *even* ([karttunen-peters-1979]) under a likelihood `μ` holds
when the prejacent `p` is less likely than every focus alternative. -/
def evenPresup (μ : Set W → α) (p : Set W) (alts : Set (Set W)) : Prop :=
  ∀ q ∈ alts, μ p < μ q

/-- Under a likelihood respecting entailment, an alternative that entails the prejacent is at
least as likely and so refutes the presupposition of *even*. -/
theorem not_evenPresup_of_subset (hμ : Monotone μ) (hq : q ∈ alts) (hqp : q ⊆ p) :
    ¬ evenPresup μ p alts :=
  fun h ↦ lt_irrefl _ (lt_of_lt_of_le (h q hq) (hμ hqp))

/-- When the prejacent entails every alternative, the presupposition of *even* asks only that
no alternative be exactly as likely. -/
theorem evenPresup_iff_ne (hμ : Monotone μ) (h : ∀ q ∈ alts, p ⊆ q) :
    evenPresup μ p alts ↔ ∀ q ∈ alts, μ p ≠ μ q :=
  forall₂_congr fun q hq ↦ lt_iff_le_and_ne.trans (and_iff_right (hμ (h q hq)))

end Even

end Focus.Particles
