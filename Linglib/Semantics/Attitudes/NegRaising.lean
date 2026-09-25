module

public import Linglib.Semantics.Attitudes.Doxastic
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Logic.Modal.Defs

/-!
# Neg-raising as O→E strengthening

This file states neg-raising over a doxastic predicate: the negation of an attitude verb read as
the attitude applied to the negated complement, *I don't think it's raining* as *I think it's not
raining*, ¬Bel(p) strengthened to Bel(¬p) ([horn-2001] §5.2). On the doxastic square of
opposition (`doxasticSquare`, with A = Bel(p), E = Bel(¬p), I = ◇p, O = ¬Bel(p)) this is O→E
strengthening, and it goes through exactly under [gajewski-2007]'s excluded-middle
presupposition, that the agent is `Opinionated` about the complement, by disjunctive syllogism
(`negRaisesAt_of_opinionated`). Opinionatedness about every complement at once is the
degenerate limit in which the agent sees at most one world (`forall_opinionated_iff`), the
dichotomous case [horn-2001] excludes from neg-raising. A veridical predicate cannot neg-raise
without asserting the complement's falsity (`not_of_negRaises_veridical`).

## Main definitions

* `doxasticSquare`: the square of opposition of a belief predicate.
* `NegRaisesAt`, `Opinionated`: the O→E inference and the excluded-middle premise about a
  complement.

## Main results

* `negRaisesAt_of_opinionated`: the excluded-middle premise licenses neg-raising.
* `forall_opinionated_iff`: opinionatedness about every complement is a one-world doxastic
  state.
* `not_of_negRaises_veridical`: neg-raising a veridical predicate asserts the complement false.

## References

* [horn-2001]
* [gajewski-2007]
-/

@[expose] public section

namespace NegRaising

open Aristotelian (Square)
open Doxastic (DoxasticPredicate BoxAt DiamondAt)

variable {W E : Type*} (R : E → W → W → Prop) (agent : E) (worlds : List W) (p : W → Prop)
  (w : W)

/-! ### The doxastic square -/

/-- The doxastic square of a belief predicate: A = Bel(p), E = Bel(¬p), I = ◇p, O = ¬Bel(p). -/
def doxasticSquare : Square (W → Prop) where
  A := fun w ↦ BoxAt R agent w worlds p
  E := fun w ↦ BoxAt R agent w worlds (fun w' ↦ ¬ p w')
  I := fun w ↦ DiamondAt R agent w worlds p
  O := fun w ↦ ¬ BoxAt R agent w worlds p

/-- The A–O diagonal is a contradiction. -/
theorem doxasticSquare_contradAO :
    (doxasticSquare R agent worlds p).A w ↔ ¬ (doxasticSquare R agent worlds p).O w := by
  simp only [doxasticSquare, not_not]

/-- The E–I diagonal is a contradiction: the diamond is the dual of the box. -/
theorem doxasticSquare_contradEI :
    (doxasticSquare R agent worlds p).E w ↔ ¬ (doxasticSquare R agent worlds p).I w := by
  simp only [doxasticSquare, BoxAt, DiamondAt]
  constructor
  · rintro h ⟨w', hw', hR, hp⟩
    exact h w' hw' hR hp
  · intro h w' hw' hR hp
    exact h ⟨w', hw', hR, hp⟩

/-- The doxastic box is the modal box over the relation restricted to `worlds`. -/
theorem boxAt_iff_box :
    BoxAt R agent w worlds p ↔ ModalLogic.box (fun u v ↦ v ∈ worlds ∧ R agent u v) p w := by
  simp only [BoxAt, ModalLogic.box, and_imp]

/-! ### Neg-raising and the excluded-middle premise -/

/-- Neg-raising: the O→E inference `¬Bel(p) → Bel(¬p)` at a world. -/
def NegRaisesAt : Prop :=
  ¬ BoxAt R agent w worlds p → BoxAt R agent w worlds (fun w' ↦ ¬ p w')

/-- The excluded-middle premise: the agent is opinionated about `p`, believing `p` or believing
`¬p`, [gajewski-2007]'s presupposition of a neg-raising predicate. -/
def Opinionated : Prop :=
  BoxAt R agent w worlds p ∨ BoxAt R agent w worlds (fun w' ↦ ¬ p w')

/-- Opinionatedness about `p` licenses the O→E strengthening by disjunctive syllogism. -/
theorem negRaisesAt_of_opinionated (h : Opinionated R agent worlds p w) :
    NegRaisesAt R agent worlds p w :=
  fun hnot ↦ h.resolve_left hnot

/-- The agent is opinionated about every complement at once iff the doxastic state at `w` has at
most one world: the degenerate limit in which the attitude is dichotomous, which [horn-2001]
excludes from neg-raising. -/
theorem forall_opinionated_iff :
    (∀ p : W → Prop, Opinionated R agent worlds p w) ↔
      ∀ ⦃v⦄, v ∈ worlds ∧ R agent w v → ∀ ⦃u⦄, u ∈ worlds ∧ R agent w u → v = u := by
  simp only [Opinionated, boxAt_iff_box]
  exact ModalLogic.box_or_box_not_at_iff

/-! ### Veridicality -/

/-- Neg-raising a veridical predicate asserts the complement false: if *know p* is denied and
strengthened to *know ¬p*, then `¬p` holds at the world. Neg-raising is therefore confined to
non-veridical predicates, without every non-veridical predicate neg-raising. -/
theorem not_of_negRaises_veridical (V : DoxasticPredicate W E) (hV : V.veridicality = .veridical)
    (hnr : ¬ V.HoldsAt agent p w worlds → V.HoldsAt agent (fun v ↦ ¬ p v) w worlds)
    (hnot : ¬ V.HoldsAt agent p w worlds) : ¬ p w :=
  Doxastic.veridical_entails_complement V hV agent _ w worlds (hnr hnot)

end NegRaising
