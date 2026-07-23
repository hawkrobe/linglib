import Linglib.Semantics.Homogeneity.Usable
import Linglib.Semantics.Supervaluation.Basic

/-!
# Homogeneity: the conditional instantiation

Conditionals as the modal instantiation of the homogeneity substrate
([kriz-2016] §6.4): "if P, Q" quantifies over closest P-worlds as the bare
plural quantifies over atoms, conditional excluded middle is the
homogeneity gap, and *necessarily* is the gap remover, as *all* is for
plurals (`Homogeneity.Plural`). `bareConditional` computes the same
three-valued truth value as `selectionalCounterfactual` in
`Semantics.Conditionals.Counterfactual` (see
`selectional_as_supervaluation`); the two differ only in input
representation.

## Main definitions

* `bareConditional`: "if P, Q" over closest P-worlds, as a `Prop3`.
* `strictConditional`: "if P, necessarily Q", its gap removal.

## References

* [M. Križ, *Homogeneity, Non-Maximality, and All*][kriz-2016]
* [R. Stalnaker, *A Defense of Conditional Excluded Middle*][stalnaker-1981]
* [K. von Fintel, *The Presupposition of Subjunctive
  Conditionals*][von-fintel-1999]
-/

namespace Semantics.Homogeneity

open Trivalent (Prop3)
open Semantics.Supervaluation (superTrue superTrue_true_iff)

variable {W : Type*} (closestPWorlds : W → Finset W) (Q : W → Prop)
  [DecidablePred Q]

/-- The bare conditional "if P, Q": true if `Q` holds at all closest
    P-worlds, false if at none, gapped otherwise (conditional excluded
    middle); vacuously true when there are no closest P-worlds. -/
def bareConditional : Prop3 W :=
  λ w =>
    let pWorlds := closestPWorlds w
    if h : pWorlds.Nonempty then
      superTrue Q ⟨pWorlds, h⟩
    else .true

/-- The strict conditional "if P, necessarily Q": gap removal on the bare
    conditional, as *all* is gap removal on the bare plural. -/
def strictConditional : Prop3 W :=
  (bareConditional closestPWorlds Q).metaAssert

/-- Strict conditionals are bivalent. -/
theorem isBivalent_strictConditional :
    (strictConditional closestPWorlds Q).isBivalent :=
  Trivalent.Prop3.isBivalent_metaAssert _

/-- The bare and strict conditionals are true in the same worlds. -/
theorem posExt_strictConditional :
    (strictConditional closestPWorlds Q).posExt =
    (bareConditional closestPWorlds Q).posExt :=
  Trivalent.Prop3.posExt_metaAssert _

/-- *necessarily* prevents non-maximal use: a usable strict conditional
    makes `Q` hold at every closest P-world. -/
theorem necessarily_prevents_nonmax (q : QUD W) (w : W)
    (h : usable q (strictConditional closestPWorlds Q) w)
    (hne : (closestPWorlds w).Nonempty) :
    ∀ w' ∈ closestPWorlds w, Q w' := by
  have hTrue : strictConditional closestPWorlds Q w = .true :=
    metaAssert_prevents_nonmax q _ w h
  have hCondTrue : bareConditional closestPWorlds Q w = .true :=
    (Set.ext_iff.mp (posExt_strictConditional closestPWorlds Q) w).mp hTrue
  simp only [bareConditional, dif_pos hne] at hCondTrue
  exact (superTrue_true_iff Q ⟨closestPWorlds w, hne⟩).mp hCondTrue

end Semantics.Homogeneity
