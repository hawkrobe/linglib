/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Focus.Control
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Data.Examples.GrubicRenansDuah2019
import Mathlib.Data.Set.Lattice

/-!
# Grubic, Renans, and Duah (2019): Focus, Exhaustivity and Existence in Akan, Ga and Ngamo

This file formalizes the analysis in section 8 of [grubic-renans-duah-2019], "Focus,
exhaustivity and existence in Akan, Ga and Ngamo", of the three languages' marked
focus/background constructions, whose data, rows of `Data.Examples.GrubicRenansDuah2019`, the
paper collects in sections 5 and 6. In none of the three is the exhaustive inference asserted:
negating the construction targets the prejacent, so an additive continuation loses its antecedent,
(36) to (38), where negating overt *only* keeps it (`negated_only_licenses_also`). The Akan *nà*
and Ga *ni* constructions are clefts, (75) and (76): they assert the prejacent and presuppose the
conditional exhaustivity of Büring (2011), that if the prejacent holds no other alternative does,
together with existence (`cleft`). The conditional form is what projects through negation, (54):
the negated cleft is defined when another alternative holds instead (`cleft_neg_of_alt`), while
the unnegated one cannot be cancelled by a further alternative, (43), (44), and (77)
(`cleft_exhaustive`), and is undefined where no alternative holds, (60) and (61)
(`cleft_existence`). The Ngamo *=i/ye* construction, (78), only presupposes that its
background is salient: its exhaustive inference is a cancellable implicature, (42) and (45)
(`marked_exhaustivity_cancellable`), and it carries no existence presupposition, (59)
(`marked_of_not_exists`).

## Implementation notes

Constructions are two-dimensional meanings over an arbitrary set of alternatives containing the
prejacent, so the theorems are general rather than checked on a two-world model. The background
of (78) is the existential closure of the alternatives, and its salience an abstract predicate on
propositions. Section 4's contrast finding, which the paper concludes is pragmatic rather than
conventional, and section 7's argument that salience is not givenness are not formalized.

## References

* [grubic-renans-duah-2019]
* [kiss-1998]
-/

namespace GrubicRenansDuah2019

open Pragmatics.Expressives Focus

variable {W : Type*} (alts : Set (Set W)) (p : Set W)

/-- Overt *only*, (36b) and (37b): the prejacent projects and exhaustivity is at issue. -/
def onlyStyle : TwoDimProp W := .withCI (· ∈ onlyVia alts p) (· ∈ p)

/-- The Akan *nà* and Ga *ni* constructions, (75) and (76): the prejacent is asserted, and
conditional exhaustivity together with existence is presupposed. -/
def cleft : TwoDimProp W :=
  .withCI (· ∈ p) λ w => (w ∈ p → w ∈ onlyVia alts p) ∧ w ∈ ⋃₀ alts

/-- The Ngamo *=i/ye* construction, (78): the prejacent is asserted, and the salience of the
background, the existential closure of the alternatives, is presupposed. -/
def marked (salient : Set W → Prop) : TwoDimProp W := .withCI (· ∈ p) λ _ => salient (⋃₀ alts)

/-! ### The exhaustive inference is not asserted, section 5.2.1 -/

/-- Negating overt *only* keeps the prejacent and denies exhaustivity, so some other alternative
holds and *also* has its antecedent, (36b) and (37b). -/
theorem negated_only_licenses_also {w : W} (h : (onlyStyle alts p).neg.atIssue w)
    (hp : (onlyStyle alts p).neg.ci w) : w ∈ p ∧ ∃ q ∈ alts, q ≠ p ∧ w ∈ q := by
  refine ⟨hp, ?_⟩
  by_contra hno
  push Not at hno
  exact h λ q hq hwq => by_contra λ hne => hno q hq hne hwq

/-- Negating a marked construction targets the prejacent, so *also* lacks its antecedent, (36a)
to (38a). -/
theorem negated_cleft_atIssue {w : W} (h : (cleft alts p).neg.atIssue w) : w ∉ p := h

/-! ### Implicature in Ngamo, presupposition in Akan and Ga, section 5.2.2 -/

/-- (42) and (45): the Ngamo construction is satisfied, presupposition included, at a world where
another alternative holds too; its exhaustive inference is cancellable. -/
theorem marked_exhaustivity_cancellable {salient : Set W → Prop} {q : Set W} {w : W}
    (hs : salient (⋃₀ alts)) (hq : q ∈ alts) (hne : q ≠ p) (hw : w ∈ p ∩ q) :
    (marked alts p salient).atIssue w ∧ (marked alts p salient).ci w ∧ w ∉ onlyVia alts p :=
  ⟨hw.1, hs, λ h => hne (h q hq hw.2)⟩

/-- (43), (44), and (77): the cleft, wherever it is defined and true, is exhaustive; a further
true alternative makes it undefined, so it cannot answer a mention-some question, (49) and
(50). -/
theorem cleft_exhaustive {w : W} (ha : (cleft alts p).atIssue w) (hc : (cleft alts p).ci w) :
    w ∈ onlyVia alts p :=
  hc.1 ha

/-- (54): the conditional presupposition projects. A negated cleft is defined at a world where
the prejacent fails and another alternative holds, so *it wasn't Fred she invited* is compatible
with her inviting Peter and Paul. -/
theorem cleft_neg_of_alt {q : Set W} {w : W} (hq : q ∈ alts) (hw : w ∈ q) (hp : w ∉ p) :
    (cleft alts p).neg.atIssue w ∧ (cleft alts p).neg.ci w :=
  ⟨hp, λ h => absurd h hp, q, hq, hw⟩

/-! ### Existence, section 6 -/

/-- (60) and (61): the cleft presupposes that some alternative holds, so a focused negative
quantifier clashes with it. -/
theorem cleft_existence {w : W} (hc : (cleft alts p).ci w) : w ∈ ⋃₀ alts := hc.2

/-- (59): the Ngamo construction is defined at a world where no alternative holds; it carries
no existence presupposition. -/
theorem marked_of_not_exists {salient : Set W → Prop} (hs : salient (⋃₀ alts)) {w : W}
    (_ : w ∉ ⋃₀ alts) : (marked alts p salient).ci w :=
  hs

end GrubicRenansDuah2019
