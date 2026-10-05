/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Data.Examples.GrubicRenansDuah2019
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Grubic, Renans, and Duah (2019): Focus, Exhaustivity and Existence in Akan, Ga and Ngamo

Grubic, Renans and Duah analyse the marked focus/background constructions of Akan, Ga and Ngamo
(section 8), whose data, the rows of `Data.Examples.GrubicRenansDuah2019`, they collect in
sections 5 and 6. In none of the three is the exhaustive inference asserted: negating the
construction targets the prejacent, so an additive continuation loses its antecedent, where
negating overt *only*, the substrate's `Focus.Particles.only`, keeps it. The Akan *nà* and Ga
*ni* constructions are clefts that assert the prejacent and presuppose conditional exhaustivity,
that if the prejacent holds no other alternative does, together with existence. The Ngamo
*=i/ye* construction only presupposes that its background is salient.

## Main results

* `negated_only_licenses_also`, `negated_cleft_assertion`: negating *only* keeps an antecedent for
  *also*, negating a marked construction does not.
* `cleft_neg_of_alt`, `cleft_exhaustive`, `cleft_existence`: the conditional exhaustivity of the
  cleft projects through negation, cannot be cancelled, and comes with existence.
* `marked_exhaustivity_cancellable`, `marked_of_not_exists`: the Ngamo construction's exhaustive
  inference is a cancellable implicature, and it carries no existence presupposition.

## Implementation notes

Constructions are partial propositions over an arbitrary set of alternatives containing the
prejacent, so the theorems are general rather than checked on a two-world model. The background
of (78) is the existential closure of the alternatives, and its salience an abstract predicate on
propositions. Section 4's contrast finding, which the paper concludes is pragmatic rather than
conventional, and section 7's argument that salience is not givenness are not formalized.

## References

* [grubic-renans-duah-2019]
* [kiss-1998]
-/

@[expose] public section

namespace GrubicRenansDuah2019

open Exhaustification Presupposition Focus Focus.Particles

variable {W : Type*} (alts : Set (Set W)) (p : Set W)

/-- The Akan *nà* and Ga *ni* constructions, (75) and (76), assert the prejacent and presuppose
conditional exhaustivity together with existence. -/
def cleft : PartialProp W :=
  ⟨fun w ↦ (w ∈ p → w ∈ excludes alts p) ∧ w ∈ ⋃₀ alts, (· ∈ p)⟩

/-- The Ngamo *=i/ye* construction (78) asserts the prejacent and presupposes the salience of the
background, the existential closure of the alternatives. -/
def marked (salient : Set W → Prop) : PartialProp W := ⟨fun _ ↦ salient (⋃₀ alts), (· ∈ p)⟩

/-! ### The exhaustive inference is not asserted, section 5.2.1 -/

/-- Negating overt *only* keeps the prejacent and denies exhaustivity, so some alternative the
prejacent does not entail holds and *also* has its antecedent, (36b) and (37b). -/
theorem negated_only_licenses_also {w : W} (h : (only (· ⊆ ·) alts p).neg.assertion w)
    (hp : (only (· ⊆ ·) alts p).neg.presup w) : w ∈ p ∧ ∃ q ∈ alts, ¬ p ⊆ q ∧ w ∈ q := by
  refine ⟨atLeast_subset_subset hp, ?_⟩
  by_contra hno
  push Not at hno
  exact h fun q hq hwq ↦ by_contra fun hne ↦ hno q hq hne hwq

/-- Negating a marked construction targets the prejacent, so *also* lacks its antecedent, (36a)
to (38a). -/
theorem negated_cleft_assertion {w : W} (h : (cleft alts p).neg.assertion w) : w ∉ p := h

/-! ### Implicature in Ngamo, presupposition in Akan and Ga, section 5.2.2 -/

/-- The Ngamo construction is satisfied, presupposition included, at a world where an alternative
the prejacent does not entail holds too, so its exhaustive inference is cancellable ((42) and
(45)). -/
theorem marked_exhaustivity_cancellable {salient : Set W → Prop} {q : Set W} {w : W}
    (hs : salient (⋃₀ alts)) (hq : q ∈ alts) (hne : ¬ p ⊆ q) (hw : w ∈ p ∩ q) :
    (marked alts p salient).holds w ∧ w ∉ excludes alts p :=
  ⟨⟨hs, hw.1⟩, fun h ↦ hne (h q hq hw.2)⟩

/-- The cleft, wherever it is defined and true, is exhaustive ((43), (44) and (77)); a further
true alternative makes it undefined, so it cannot answer a mention-some question, (49) and
(50). -/
theorem cleft_exhaustive {w : W} (h : (cleft alts p).holds w) : w ∈ excludes alts p :=
  h.1.1 h.2

/-- The conditional presupposition projects, (54). A negated cleft is defined and true at a
world where the prejacent fails and another alternative holds, so *it wasn't Fred she invited* is
compatible with her inviting Peter and Paul. -/
theorem cleft_neg_of_alt {q : Set W} {w : W} (hq : q ∈ alts) (hw : w ∈ q) (hp : w ∉ p) :
    (cleft alts p).neg.holds w :=
  ⟨⟨fun h ↦ absurd h hp, q, hq, hw⟩, hp⟩

/-! ### Existence, section 6 -/

/-- The cleft presupposes that some alternative holds, so a focused negative quantifier clashes
with it ((60) and (61)). -/
theorem cleft_existence {w : W} (h : (cleft alts p).defined w) : w ∈ ⋃₀ alts := h.2

/-- The Ngamo construction is defined at a world where no alternative holds, so it carries no
existence presupposition (59). -/
theorem marked_of_not_exists {salient : Set W → Prop} (hs : salient (⋃₀ alts)) {w : W}
    (_ : w ∉ ⋃₀ alts) : (marked alts p salient).defined w :=
  hs

end GrubicRenansDuah2019
