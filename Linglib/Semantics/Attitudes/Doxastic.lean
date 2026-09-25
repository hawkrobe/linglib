module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Attitudes.Basic
public import Linglib.Logic.Modal.Basic

/-!
# Doxastic attitude semantics

Accessibility-based semantics for doxastic attitude verbs (*believe*, *know*, *think*) in the
tradition of [hintikka-1962]: `R x w w'` reads "`w'` is compatible with what `x` believes or
knows in `w`", and ⟦x believes p⟧(w) is the relational box `□[R x] p w` of `Logic/Modal/Defs`,
so closure under known implication is the K axiom `ModalLogic.box_K`.

A `DoxasticPredicate` pairs an accessibility relation with a veridicality value. Applied to a
complement it is a partial proposition (`toPartialProp`) whose presupposition is the veridicality
requirement (`VeridicalityHolds`: a veridical verb requires its complement at the evaluation
world) and whose assertion is the box. `HoldsAt` is the satisfaction of both, so a veridical
predicate entails its complement (`veridical_entails_complement`). Over reflexive accessibility
the veridicality requirement is redundant by the T axiom (`holdsAt_iff_box`), which is how
[hintikka-1962] obtains the factivity of *know* (`Studies/Hintikka1962.lean`).

The presuppositional typology of doxastic verbs ([glass-2025]) is in `Studies/Glass2025.lean`,
and [schlenker-2003]'s quantification over reported contexts, of which the box is the world-only
case, in `Studies/Schlenker2003.lean`.

## References

* [hintikka-1962]
* [glass-2025]
* [schlenker-2003]
-/

@[expose] public section

namespace Doxastic

open ModalLogic Presupposition

variable {W E : Type*}

/-- The veridicality requirement on a complement `p` at `w`: a veridical verb requires `p w`, a
non-veridical one nothing. -/
def VeridicalityHolds (v : Veridicality) (p : W → Prop) (w : W) : Prop :=
  match v with
  | .veridical => p w
  | .nonVeridical => True

instance (v : Veridicality) (p : W → Prop) [DecidablePred p] (w : W) :
    Decidable (VeridicalityHolds v p w) :=
  match v with
  | .veridical => inferInstanceAs (Decidable (p w))
  | .nonVeridical => inferInstanceAs (Decidable True)

/-- A doxastic attitude predicate: an accessibility relation for each attitude holder, and a
veridicality value. -/
structure DoxasticPredicate (W E : Type*) where
  /-- `access x w w'`: `w'` is compatible with the attitude of `x` in `w`. -/
  access : E → W → W → Prop
  /-- Whether the predicate requires its complement to be true. -/
  veridicality : Veridicality

namespace DoxasticPredicate

variable (V : DoxasticPredicate W E) (agent : E) (p : W → Prop) (w : W)

/-- The predicate applied to a holder and a complement, as a partial proposition: the
presupposition is the veridicality requirement and the assertion is the box. -/
def toPartialProp : PartialProp W where
  presup := VeridicalityHolds V.veridicality p
  assertion := □[V.access agent] p

/-- ⟦x V that p⟧(w) is true: the presupposition and the assertion of `toPartialProp` both hold. -/
def HoldsAt : Prop := (V.toPartialProp agent p).holds w

theorem holdsAt_iff :
    V.HoldsAt agent p w ↔ VeridicalityHolds V.veridicality p w ∧ □[V.access agent] p w :=
  Iff.rfl

instance [Fintype W] [∀ v, Decidable (V.access agent w v)] [DecidablePred p] :
    Decidable (V.HoldsAt agent p w) :=
  inferInstanceAs (Decidable (VeridicalityHolds V.veridicality p w ∧ □[V.access agent] p w))

variable {V agent p w}

/-- A veridical predicate entails its complement: if `x` knows `p` at `w`, then `p w`. -/
theorem veridical_entails_complement (hV : V.veridicality = .veridical)
    (h : V.HoldsAt agent p w) : p w := by
  rw [holdsAt_iff, hV] at h
  exact h.1

/-- Over reflexive accessibility the veridicality requirement is redundant: the predicate holds
exactly when its complement is true at every accessible world. -/
theorem holdsAt_iff_box [Std.Refl (V.access agent)] :
    V.HoldsAt agent p w ↔ □[V.access agent] p w := by
  rw [holdsAt_iff, and_iff_right_iff_imp]
  intro h
  cases V.veridicality
  exacts [box_T h, trivial]

end DoxasticPredicate

end Doxastic
