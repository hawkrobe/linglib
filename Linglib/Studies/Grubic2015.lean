/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Data.Examples.Grubic2015
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Grubic (2015): Focus and Alternative Sensitivity in Ngamo

Grubic analyses the Ngamo alternative-sensitive particles of chapter 7 against the data of
chapter 6, the rows of `Data.Examples.Grubic2015`, in a question-under-discussion framework. The
exclusive *yak('i)* has Coppock and Beaver's entry for exclusives, the substrate's
`Focus.Particles.only`: it presupposes that some alternative at least as strong as the prejacent
on a salient scale is true and asserts that no true alternative is stronger. The additive
*ke('e)* has no truth-conditional content and presupposes a salient antecedent about a different
topic situation, and the scalar *har('i)* asserts its prejacent and presupposes that a contextual
implication of it ranks highest among its alternatives.

## Main results

* `prejacent_projects`: on an entailment scale, the complement-exclusion reading, the
  presupposition of *yak('i)* entails the prejacent, which therefore projects through negation.
* `truthSet_only_conjunctions`: over the conjunctions of independent atomic answers *yak('i)* is
  defined and true exactly where the prejacent holds and every other atom fails.
* `ke_undefined_of_anaphoric`: parallel background-marked antecedents, being anaphoric, cannot
  supply the antecedent of *ke('e)*.

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

@[expose] public section

namespace Grubic2015

open Exhaustification Presupposition Focus Focus.Particles

variable {W T : Type*} (S : Set W → Set W → Prop) (C : Set (Set W)) (p : Set W)

/-! ### The exclusive *yak('i)*, section 7.1 -/

/-- Negation leaves the presupposition in place, so *not only Dimza built a house* still has
Dimza building a house (29); on a rank-order scale, where alternatives need not entail the
prejacent, nothing of the kind follows. -/
theorem prejacent_projects {w : W} (h : (only (· ⊆ ·) C p).neg.presup w) : w ∈ p :=
  atLeast_subset_subset h

/-- The answers of (11) are the nonempty conjunctions of a set of atomic answers. -/
def conjunctions (atoms : Set (Set W)) : Set (Set W) :=
  {q | ∃ A ⊆ atoms, A.Nonempty ∧ q = ⋂₀ A}

/-- Over the conjunctions of atomic answers, the truth set of *yak('i)* on the entailment scale
is the prejacent with no other atom true, the exhaustification `Exhaustification.exh` over the
atoms ((166) and (25)). -/
theorem truthSet_only_conjunctions {atoms : Set (Set W)} (hp : p ∈ atoms) :
    (only (· ⊆ ·) (conjunctions atoms) p).truthSet = exh atoms p := by
  ext w
  constructor
  · rintro ⟨⟨_, ⟨A, hA, -, rfl⟩, hw, hq⟩, hmost⟩
    refine ⟨hq hw, fun r hr hwr x hx ↦ ?_⟩
    exact (hmost (p ∩ r) ⟨{p, r}, by simp [Set.insert_subset_iff, hp, hr], by simp, by simp⟩
      ⟨hq hw, hwr⟩ hx).2
  · rintro ⟨hw, honly⟩
    refine ⟨⟨p, ⟨{p}, by simpa, Set.singleton_nonempty p, (Set.sInter_singleton p).symm⟩, hw,
      subset_rfl⟩, ?_⟩
    rintro q ⟨A, hA, -, rfl⟩ hwq x hx
    exact Set.mem_sInter.mpr fun a ha ↦ honly a (hA ha) (Set.mem_sInter.mp hwq a ha) hx

/-! ### The additive *ke('e)*, section 7.3 -/

/-- *ke('e)* 'also' (45) makes no truth-conditional contribution and presupposes a salient
antecedent about a different topic situation, one that need not itself be true (46). -/
def ke (given : Set (Set W)) (topic : Set W → T) : PartialProp W :=
  ⟨fun _ ↦ ∃ q ∈ given, topic q ≠ topic p, (· ∈ p)⟩

/-- When every salient antecedent is anaphoric to the host's topic situation, as parallel
background-marked antecedents are by default, *ke('e)* is undefined ((44) and (49)). -/
theorem ke_undefined_of_anaphoric {given : Set (Set W)} {topic : Set W → T}
    (h : ∀ q ∈ given, topic q = topic p) (w : W) : ¬ (ke p given topic).defined w :=
  fun ⟨q, hq, hne⟩ ↦ hne (h q hq)

/-! ### The scalar *har('i)*, section 7.2 -/

/-- A contextual implication (18) is entailed by the common ground updated with the prejacent but
not by the common ground alone. -/
def CImpl (CG q : Set W) : Prop := ¬ CG ⊆ q ∧ CG ∩ p ⊆ q

/-- *har('i)* 'even' (17) asserts the prejacent and presupposes that some contextual implication
of it ranks highest among its alternatives on the salient scale. -/
def har (CG : Set W) (alt : Set W → Set (Set W)) : PartialProp W :=
  ⟨fun w ↦ ∃ q, CImpl p CG q ∧ ∀ q' ∈ alt q, w ∈ q' → S q q', (· ∈ p)⟩

/-- At a world of the common ground where the prejacent holds, the implication *har('i)*
presupposes holds as well, so the scale is anchored by a true alternative. -/
theorem har_impl_holds {CG : Set W} {alt : Set W → Set (Set W)} {w : W} (hw : w ∈ CG)
    (hp : w ∈ p) (h : (har S p CG alt).presup w) : ∃ q, CImpl p CG q ∧ w ∈ q :=
  let ⟨q, hq, _⟩ := h
  ⟨q, hq, hq.2 ⟨hw, hp⟩⟩

end Grubic2015
