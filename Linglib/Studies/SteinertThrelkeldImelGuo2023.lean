import Linglib.Core.Combinatorics.SimpleGraph.Prod
import Linglib.Semantics.Modality.Universals
import Linglib.Fragments.Washo.Modals
import Linglib.Fragments.Koryak.Modals
import Linglib.Fragments.Javanese.Modals
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Steinert-Threlkeld, Imel and Guo (2023): A semantic universal for modality

This file formalizes the Independence of Force and Flavor universal of
[steinert-threlkeld-imel-guo-2023], the substrate's `Modality.ForceFlavorIndependent`,
against the Single Axis of Variability universal of [nauze-2008] it replaces. The Washo verb
*-eʔ* of [bochnak-2015a] varies on both axes yet is a product, the hypothetical *mighst* is
neither, and the singleton meanings of Paciran Javanese ([vander-klok-2013a]) satisfy the
universal trivially. The paper's equivalence of independence with convexity for the grid
betweenness of [chemla-buccola-dautriche-2019] is the substrate's
`forceFlavorIndependent_iff_pair_product_subset`.

The paper offers path-connectedness as a weaker fallback universal, defined by replacing the
"and" of independence with an "or" and glossed in a footnote as any two points being joined by a
path. The two readings come apart. Read as a path through the rook's graph on the force-flavor
grid, whose edges change one coordinate, the property follows from the "or" formulation
(`PathConnected.connected`), but the second modal of Table 1, given as satisfying
path-connectedness without independence, is connected in the grid and fails the "or"
formulation: its weak teleological and strong epistemic points share no corner
(`table1b_connected_not_pathConnected`).

## Implementation notes

The paper's space has two forces, weak and strong, and the flavors epistemic, deontic and
teleological; the library folds teleological into circumstantial.

## References

* [steinert-threlkeld-imel-guo-2023]
* [nauze-2008]
* [chemla-buccola-dautriche-2019]
* [bochnak-2015a]
* [mocnik-abramovitz-2019]
* [vander-klok-2013a]
-/

namespace SteinertThrelkeldImelGuo2023

open Modality SimpleGraph

/-- Washo *-eʔ* varies on both axes, against Nauze's universal, and is the product of two forces
and two flavors. -/
theorem washo_modalEq :
    ¬ SingleAxis Washo.Modals.modalEq.meaning ∧
      ForceFlavorIndependent Washo.Modals.modalEq.meaning := by
  decide

/-- Koryak *ivək* ([mocnik-abramovitz-2019]) satisfies the universal; with its doxastic and
assertive flavors both epistemic in the fragment's space it varies on a single axis too. -/
theorem koryak_modalIvek :
    ForceFlavorIndependent Koryak.Modals.modalIvek.meaning ∧
      SingleAxis Koryak.Modals.modalIvek.meaning := by
  decide

/-- Paciran Javanese *mesthi*, *oleh* and *iso* express one pair each. -/
theorem javanese_singletons :
    ForceFlavorIndependent Javanese.Modals.mesthi.meaning ∧
      ForceFlavorIndependent Javanese.Modals.oleh.meaning ∧
      ForceFlavorIndependent Javanese.Modals.iso.meaning :=
  ⟨.singleton _, .singleton _, .singleton _⟩

/-- The hypothetical *mighst* expresses epistemic possibility and deontic necessity only, which
the universal rules out; it is the third modal of Table 1. -/
def mighst : Finset ForceFlavor := {(.possibility, .epistemic), (.necessity, .deontic)}

theorem not_forceFlavorIndependent_mighst : ¬ ForceFlavorIndependent mighst := by decide

/-! ### Table 1 and the two readings of path-connectedness -/

/-- The first modal of Table 1 expresses both forces with the epistemic and teleological
flavors. -/
def table1a : Finset ForceFlavor :=
  {(.possibility, .epistemic), (.possibility, .circumstantial),
   (.necessity, .epistemic), (.necessity, .circumstantial)}

/-- The second modal of Table 1 expresses weak deontic and teleological and strong epistemic and
deontic. -/
def table1b : Finset ForceFlavor :=
  {(.possibility, .deontic), (.possibility, .circumstantial),
   (.necessity, .epistemic), (.necessity, .deontic)}

theorem table1a_forceFlavorIndependent :
    ForceFlavorIndependent table1a ∧ ¬ SingleAxis table1a := by
  decide

/-- The rook's graph on the force-flavor grid, in which pairs differing in exactly one coordinate
are adjacent. -/
abbrev rookGraph : SimpleGraph ForceFlavor := (⊤ : SimpleGraph ModalForce) □ ⊤

/-- Two pairs of a meaning sharing a coordinate are joined in the rook's graph. -/
theorem reachable_of_fst_eq_or_snd_eq {m : Finset ForceFlavor} {p q : ForceFlavor} (hp : p ∈ m) (hq : q ∈ m)
    (h : p.1 = q.1 ∨ p.2 = q.2) :
    (rookGraph.induce ↑m).Reachable ⟨p, hp⟩ ⟨q, hq⟩ := by
  by_cases hpq : p = q
  · subst hpq; rfl
  refine Adj.reachable ?_
  rw [induce_adj, boxProd_adj, top_adj, top_adj]
  rcases h with h | h
  · exact Or.inr ⟨λ h₂ => hpq (Prod.ext h h₂), h⟩
  · exact Or.inl ⟨λ h₁ => hpq (Prod.ext h₁ h), h⟩

/-- A path-connected meaning induces a connected subgraph of the rook's graph, any two pairs
being joined through a corner, so the "or" formulation implies the footnote's. -/
theorem PathConnected.connected {m : Finset ForceFlavor} (h : PathConnected m) (hm : m.Nonempty) :
    (rookGraph.induce ↑m).Connected := by
  have := (Finset.coe_nonempty.2 hm).to_subtype
  refine ⟨λ ⟨p, hp⟩ ⟨q, hq⟩ => ?_⟩
  rcases h p hp q hq with hc | hc
  · exact (reachable_of_fst_eq_or_snd_eq hp hc (Or.inl rfl)).trans
      (reachable_of_fst_eq_or_snd_eq hc hq (Or.inr rfl))
  · exact (reachable_of_fst_eq_or_snd_eq hp hc (Or.inr rfl)).trans
      (reachable_of_fst_eq_or_snd_eq hc hq (Or.inl rfl))

/-- The second modal of Table 1 fails independence and the "or" formulation of
path-connectedness, yet is connected in the rook's graph. -/
theorem table1b_connected_not_pathConnected :
    ¬ ForceFlavorIndependent table1b ∧ ¬ PathConnected table1b ∧
      (rookGraph.induce ↑table1b).Connected := by
  decide +kernel

/-- *mighst*, the third modal, is disconnected on either reading. -/
theorem mighst_not_connected :
    ¬ PathConnected mighst ∧ ¬ (rookGraph.induce ↑mighst).Connected := by
  decide +kernel

end SteinertThrelkeldImelGuo2023
