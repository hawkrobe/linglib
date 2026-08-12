import Mathlib.Data.Finset.Defs

/-!
# Kripke models

This file defines `KripkeModel`, the finite Kripke carrier — successor
`Finset`s and a `Bool` valuation — that the team-semantic modal logics
(BSML, QBSML, modal dependence and inclusion logic, InqML) evaluate on.
It is the decidable specialization of the relational primitives of
`Logic/Modal/Defs.lean`.

## References

* [vaananen-2008] — modal dependence logic and team semantics
-/

namespace ModalLogic

/-- A **Kripke model** over worlds `W` and atoms `Atom`. -/
structure KripkeModel (W : Type*) (Atom : Type*) where
  /-- Accessibility: `access w` is the set of worlds accessible from `w`. -/
  access : W → Finset W
  /-- Valuation: `val p w` is the truth value of atom `p` at world `w`. -/
  val : Atom → W → Bool

end ModalLogic
