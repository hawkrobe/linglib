module

public import Mathlib.Data.Finset.Defs

/-!
# Kripke models

This file defines `KripkeModel`, the finite Kripke carrier — successor
`Finset`s and a `Bool` valuation — that the team-semantic modal logics
(BSML, QBSML, modal dependence and inclusion logic, InqML) evaluate on.
It is the decidable specialization of the relational primitives of
`Logic/Modal/Defs.lean`: `KripkeModel.Accessible` is the successor
function as the `W → W → Prop` relation those primitives take.

## References

* [vaananen-2008] — modal dependence logic and team semantics
-/

@[expose] public section

namespace ModalLogic

/-- A **Kripke model** over worlds `W` and atoms `Atom`. -/
structure KripkeModel (W : Type*) (Atom : Type*) where
  /-- Accessibility: `access w` is the set of worlds accessible from `w`. -/
  access : W → Finset W
  /-- Valuation: `val p w` is the truth value of atom `p` at world `w`. -/
  val : Atom → W → Bool

variable {W : Type*} {Atom : Type*}

/-- The accessibility relation of `M`: `v` is accessible from `w` when `v ∈ M.access w`.
    This is the relation that `box` and `diamond` of `Logic/Modal/Defs.lean` take. -/
def KripkeModel.Accessible (M : KripkeModel W Atom) (w v : W) : Prop :=
  v ∈ M.access w

instance [DecidableEq W] (M : KripkeModel W Atom) : DecidableRel M.Accessible :=
  fun w v ↦ inferInstanceAs (Decidable (v ∈ M.access w))

end ModalLogic
