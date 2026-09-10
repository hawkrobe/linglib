/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Focus.Control
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Data.Examples.Grubic2015
import Mathlib.Data.Set.Lattice

/-!
# Grubic (2015): Focus and Alternative Sensitivity in Ngamo

This file formalizes the question-under-discussion analysis of the Ngamo alternative-sensitive
particles in chapter 7 of [grubic-2015], "Focus and alternative sensitivity in Ngamo
(West-Chadic)", against the data of chapter 6, rows of `Data.Examples.Grubic2015`. The
exclusive *yak('i)* has the entry (2) of [coppock-beaver-2014]'s exclusives: it presupposes
that some alternative at least as strong as the prejacent on a salient scale is true and asserts
that no true alternative is stronger (`yak`). On an entailment scale, the complement-exclusion
reading of section 6.1.1, the presupposition entails the prejacent, which therefore projects
through negation as in (29) (`prejacent_projects`), and over the conjunctions of independent
atomic answers, the lattice of (11), the total content is the prejacent with every other atom
false, the exclusive inference of (166) (`total_yak`). The additive *ke('e)* has no
truth-conditional content and presupposes a salient antecedent about a different topic
situation, (45), one that need not be true, (46), and one that parallel background-marked
antecedents, being anaphoric, cannot supply, (44) and (49) (`ke_undefined_of_anaphoric`). The
scalar *har('i)* asserts its prejacent and presupposes that a contextual implication of it, in
the sense of (18), ranks highest among its alternatives, (17) (`har`).

## Implementation notes

The scale is a relation `S q p` read as `q` at least as strong as `p`, the entailment scale
being `(· ⊆ ·)`; the VP and NP variants (5) and (6), which reach the propositional entry by the
Geach rule, are not repeated. Topic situations are abstracted to a map from answers to a type
of situations, so that the non-overlap of (45) is distinctness. The association facts of
section 6.2, on which *yak('i)* alone associates with focus conventionally, are data rows and
not theorems.

## References

* [grubic-2015]
* [coppock-beaver-2014]
* [beaver-clark-2008]
-/

namespace Grubic2015

open Pragmatics.Expressives Focus

variable {W T : Type*} (S : Set W → Set W → Prop) (C : Set (Set W)) (p : Set W)

/-! ### The exclusive *yak('i)*, section 7.1 -/

/-- (2i): some alternative at least as strong as the prejacent is true, the presupposition of
*yak('i)*. -/
def atLeast : Set W := {w | ∃ q ∈ C, w ∈ q ∧ S q p}

/-- (2ii): no true alternative is stronger than the prejacent, the assertion of *yak('i)*. -/
def atMost : Set W := {w | ∀ q ∈ C, w ∈ q → S p q}

/-- *yak('i)* 'only', the propositional entry (2). -/
def yak : TwoDimProp W := .withCI (· ∈ atMost S C p) (· ∈ atLeast S C p)

/-- The total content of a two-dimensional meaning, at-issue and presupposed together. -/
def total (m : TwoDimProp W) : Set W := {w | m.atIssue w ∧ m.ci w}

/-- On an entailment scale the presupposition entails the prejacent. -/
theorem atLeast_subset : atLeast (· ⊆ ·) C p ⊆ p := λ _ ⟨_, _, hw, hq⟩ => hq hw

/-- (29): negation leaves the presupposition in place, so *not only Dimza built a house* still
has Dimza building a house; on a rank-order scale, where alternatives need not entail the
prejacent, nothing of the kind follows. -/
theorem prejacent_projects {w : W} (h : (yak (· ⊆ ·) C p).neg.ci w) : w ∈ p :=
  atLeast_subset C p h

/-- The answers of (11): the nonempty conjunctions of a set of atomic answers. -/
def conjunctions (atoms : Set (Set W)) : Set (Set W) :=
  {q | ∃ A ⊆ atoms, A.Nonempty ∧ q = ⋂₀ A}

/-- (166) and (25): over the conjunctions of independent atomic answers, the total content of
*yak('i)* on the entailment scale is the prejacent with no other atom true, the exclusive
inference in the form of the library's `Focus.onlyVia`. -/
theorem total_yak {atoms : Set (Set W)} (hp : p ∈ atoms) (hind : ∀ q ∈ atoms, p ⊆ q → q = p) :
    total (yak (· ⊆ ·) (conjunctions atoms) p) = p ∩ onlyVia atoms p := by
  ext w
  constructor
  · rintro ⟨hmost, _, ⟨A, hA, -, rfl⟩, hw, hq⟩
    refine ⟨hq hw, λ r hr hwr => hind r hr λ x hx => ?_⟩
    exact (hmost (p ∩ r) ⟨{p, r}, by simp [Set.insert_subset_iff, hp, hr], by simp, by simp⟩
      ⟨hq hw, hwr⟩ hx).2
  · rintro ⟨hw, honly⟩
    refine ⟨?_, p, ⟨{p}, by simpa, Set.singleton_nonempty p, (Set.sInter_singleton p).symm⟩, hw,
      subset_rfl⟩
    rintro q ⟨A, hA, -, rfl⟩ hwq x hx
    refine Set.mem_sInter.mpr λ a ha => ?_
    rw [honly a (hA ha) (Set.mem_sInter.mp hwq a ha)]
    exact hx

/-! ### The additive *ke('e)*, section 7.3 -/

/-- *ke('e)* 'also', (45): no truth-conditional contribution, and the presupposition of a salient
antecedent about a different topic situation, one that need not itself be true, (46). -/
def ke (given : Set (Set W)) (topic : Set W → T) : TwoDimProp W :=
  .withCI (· ∈ p) (λ _ => ∃ q ∈ given, topic q ≠ topic p)

/-- (44) and (49): when every salient antecedent is anaphoric to the host's topic situation, as
parallel background-marked antecedents are by default, *ke('e)* is undefined. -/
theorem ke_undefined_of_anaphoric {given : Set (Set W)} {topic : Set W → T}
    (h : ∀ q ∈ given, topic q = topic p) (w : W) : ¬ (ke p given topic).ci w :=
  λ ⟨q, hq, hne⟩ => hne (h q hq)

/-! ### The scalar *har('i)*, section 7.2 -/

/-- A contextual implication, (18): entailed by the common ground updated with the prejacent
but not by the common ground alone. -/
def CImpl (CG q : Set W) : Prop := ¬ CG ⊆ q ∧ CG ∩ p ⊆ q

/-- *har('i)* 'even', (17): asserts the prejacent and presupposes that some contextual
implication of it ranks highest among its alternatives on the salient scale. -/
def har (CG : Set W) (alt : Set W → Set (Set W)) : TwoDimProp W :=
  .withCI (· ∈ p) (λ w => ∃ q, CImpl p CG q ∧ ∀ q' ∈ alt q, w ∈ q' → S q q')

/-- At a world of the common ground where the prejacent holds, the implication *har('i)*
presupposes holds as well, so the scale is anchored by a true alternative. -/
theorem har_impl_holds {CG : Set W} {alt : Set W → Set (Set W)} {w : W} (hw : w ∈ CG)
    (hp : w ∈ p) (h : (har S p CG alt).ci w) : ∃ q, CImpl p CG q ∧ w ∈ q :=
  let ⟨q, hq, _⟩ := h
  ⟨q, hq, hq.2 ⟨hw, hp⟩⟩

end Grubic2015
