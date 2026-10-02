/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Person.Features
public import Linglib.Semantics.Reference.Prominence

/-!
# Person feature geometry

Béjar and Rezac, extending Harley and Ritter's geometry of morphological φ-features to the
features Agree sees, order the person features by entailment, [speaker] ⇒ [participant] ⇒ [π],
so that a person is a privative set of features closed downward along the chain. Pancheva and
Zubizarreta add [proximate] below [participant] for the Person Case Constraint: first and second
persons are inherently [+proximate], and a third person is [−proximate] by default but may be
marked [+proximate] beside another third person.

The geometry drives relativized probing: a probe seeking [participant] skips the DPs that lack it,
targeting only first and second persons, and a probe seeking [plural] skips singulars (Preminger
§4.2, after Rizzi's Relativized Minimality). Béjar and Rezac's split person and number probes,
person probing first, and their Person Licensing Condition derive the Person Case Constraint with
an unrelativized person probe; Preminger ports the system to Kichean Agent Focus, adds the
relativization of the probes, and argues against salience scales such as
`[+participant] > [+plural] > default` (chapter 7).

## Main definitions

* `Minimalist.DecomposedPerson`: the positive features among [proximate], [participant] and
  [author], a lower set of the chain.
* `Minimalist.DecomposedPerson.toFeatures`: the [±participant, ±author] core.
* `Minimalist.decomposePerson`: the decomposition of a person value.
* `Minimalist.probeVisible`, `Minimalist.probeResolutionRank`: relativized probing and its
  effect on a single DP.

## Main results

* `Minimalist.DecomposedPerson.card_wellFormed`: three dependent features give four cells.
* `Minimalist.decomposePerson_toFeatures_eq`: the decomposition agrees with `Person.toFeatures`.

## Implementation notes

`probeResolutionRank` summarizes the two-probe system on a single DP; its agreement with cascade
resolution over the two probes is `Preminger2014.afTarget_eq_rank`, so it is a derived summary
and not a salience scale.

## References

* [bejar-rezac-2009], (6), p. 43
* [harley-ritter-2002]
* [bejar-rezac-2003]
* [preminger-2014]
* [pancheva-zubizarreta-2018]
* [rizzi-1990]
* [halpert-2012]
-/

@[expose] public section

namespace Minimalist

open Reference.Prominence

/-! ### The decomposition -/

namespace DecomposedPerson

/-- The features of the decomposition, each entailing the next along the chain
`[author] → [participant] → [proximate]`. [proximate] marks potential point-of-view centres,
[participant] the first and second person, and [author] the first. They are privative, a third
person lacking [participant] rather than bearing [−participant], which the set of positive
features renders directly. -/
inductive Feature where
  | proximate
  | participant
  | author
  deriving DecidableEq, Repr, Fintype

/-- `Feature.rank` places proximate below participant below author on the dependency chain. -/
def Feature.rank : Feature → Fin 3
  | .proximate => 0
  | .participant => 1
  | .author => 2

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

instance : LocallyFiniteOrderBot Feature := Fintype.toLocallyFiniteOrderBot

/-- `Feature.ofCore` embeds the framework-neutral person features. -/
def Feature.ofCore : Person.Feature → Feature
  | .participant => .participant
  | .author => .author

end DecomposedPerson

/-- A person decomposed by the geometry is the set of its positive features. -/
abbrev DecomposedPerson := Finset DecomposedPerson.Feature

namespace DecomposedPerson

/-- The core of a decomposition is its participant and author features. -/
def toFeatures (dp : DecomposedPerson) : Person.Features :=
  Finset.univ.filter fun f ↦ Feature.ofCore f ∈ dp

/-- Three dependent features give four cells passing the containment filter. -/
theorem card_wellFormed :
    Fintype.card {dp : DecomposedPerson // IsLowerSet (↑dp : Set Feature)} = 4 := by
  rw [Fintype.card_subtype_isLowerSet]; rfl

end DecomposedPerson

/-- The first person bears all three features, the second [proximate] and [participant], and the
third none; contextual [+proximate] marking of a third person is left to the evaluation of the
P-Constraint. -/
def decomposePerson : Person → DecomposedPerson
  | .first | .firstInclusive | .firstExclusive => {.proximate, .participant, .author}
  | .second => {.proximate, .participant}
  | .third | .zero => ∅

/-! ### Probe targets -/

/-- In the Agent Focus construction two probes operate, π⁰ seeking [participant] and #⁰ seeking
[plural]; π⁰ is merged below #⁰ and probes first, person-before-number probing inherited from
Béjar and Rezac. -/
inductive Probe.Target where
  /-- π⁰, the person probe, seeks [participant]. -/
  | participant
  /-- #⁰, the number probe, seeks [plural]. -/
  | plural
  deriving DecidableEq, Repr

/-- A DP with person `person` and number `isPlural` is visible to a probe iff it bears the
feature the probe seeks; probes skip the DPs that lack it. -/
def probeVisible (target : Probe.Target) (person : Person) (isPlural : Bool) : Bool :=
  match target with
  | .participant => decide (.participant ∈ decomposePerson person)
  | .plural => isPlural

/-! ### Probe resolution rank -/

/-- Under the two-probe system a DP visible to π⁰ ranks 2, one visible only to #⁰ ranks 1, and one
visible to neither ranks 0. The rank summarizes the effect of the probes on a single DP: π⁰ probes
first and its clitic output beats other exponence in the single slot. -/
def probeResolutionRank (person : Person) (isPlural : Bool) : Nat :=
  if .participant ∈ decomposePerson person then 2
  else if isPlural then 1
  else 0

/-! ### Agreement with the neutral decomposition -/

/-- Every person value decomposes into a lower set of the chain. -/
theorem all_decompositions_wellFormed (p : Person) :
    IsLowerSet (↑(decomposePerson p) : Set DecomposedPerson.Feature) := by
  cases p <;> decide

/-- The [±participant, ±author] core of the decomposition agrees with `Person.toFeatures`. -/
theorem decomposePerson_toFeatures_eq (p : Person) :
    ∀ f, p.toFeatures = some f → (decomposePerson p).toFeatures = f := by
  cases p <;> intro f hf <;>
    simp only [Person.toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> decide

/-- A DP visible to π⁰ outranks one visible only to #⁰, which outranks one visible to neither. -/
theorem rank_hierarchy :
    probeResolutionRank .first false > probeResolutionRank .third true ∧
    probeResolutionRank .third true > probeResolutionRank .third false := by decide

example :
    .participant ∈ decomposePerson .first ∧
    .author ∈ decomposePerson .first ∧
    .author ∉ decomposePerson .second ∧
    .participant ∉ decomposePerson .third ∧
    probeVisible .participant .first false = true ∧
    probeVisible .participant .third false = false ∧
    probeVisible .plural .third true = true ∧
    probeVisible .plural .third false = false ∧
    probeResolutionRank .first false = 2 ∧
    probeResolutionRank .second false = 2 ∧
    probeResolutionRank .third true = 1 ∧
    probeResolutionRank .third false = 0 := by decide

end Minimalist
