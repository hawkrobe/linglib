import Mathlib.Order.Lattice
import Mathlib.Order.PropInstances
import Mathlib.Order.BoundedOrder.Basic

/-!
# Relational nouns: the relationalizer and its closures

Type shifters for relational nouns and possessive constructions, following [barker-2011]. A noun
with a relatum slot denotes a situation-indexed relation `E → E → S → Prop`, possessor first; a
sortal noun denotes `E → S → Prop`. The relationalizer `π P R` opens a slot on a sortal `P` with a
free relation `R`, and applied to a possessor `x` it is the modifier genitive `λy. P y ∧ R x y`,
the noun conjoined with the bare predicate possessive `R x` (`pi_apply`). The argument genitive is
application itself: a relational noun `R` applied to its possessor is `R x`. `Ex` and
`ExPossessor` close the relatum and the possessor slot, the domain and codomain of the relation at
each situation.

## Main declarations

* `π P R`: Barker's relationalizer, `π P R x y s ↔ P y s ∧ R x y s`.
* `Ex R`, `ExPossessor R`: existential closure of the relatum (`Ex R x s ↔ ∃ y, R x y s`) and of
  the possessor (`ExPossessor R y s ↔ ∃ x, R x y s`), the alienator of [adamson-2024].

## Main statements

* `pi_apply`: `π P R x = P ⊓ R x`, the modifier genitive as intersective modification by the
  predicate possessive ([partee-borschev-2001]).
* `pi_top`: `π ⊤ R = R`.
* `exPossessor_pi`: the alienator over a relationalized noun keeps the sortal core.

## References

* [barker-2011]
* [adamson-2024]
* [partee-borschev-2001]
-/

namespace Possession
variable {E S : Type*}

/-! ### The relationalizer -/

/-- Barker's relationalizer: `π P R x y s ↔ P y s ∧ R x y s`. Applied to a possessor `x` it is the
modifier genitive `λy. P y ∧ R x y`; coercing the sortal to a relation and taking the possessor as
its argument ([jensen-vikner-1994]) and modifying the sortal by the possessor's free relation
([partee-1997]) assemble the same term `π P R x`. -/
def π (P : E → S → Prop) (R : E → E → S → Prop) : E → E → S → Prop :=
  λ x y s => P y s ∧ R x y s

/-- The modifier genitive is the noun conjoined with the bare predicate possessive `R x`. -/
theorem pi_apply (P : E → S → Prop) (R : E → E → S → Prop) (x : E) : π P R x = P ⊓ R x := rfl

/-- Over the trivial restrictor the relationalizer is the relation itself. -/
@[simp] theorem pi_top (R : E → E → S → Prop) : π ⊤ R = R := by
  funext x; rw [pi_apply, top_inf_eq]

/-! ### Existential closures -/

/-- Existential closure of the relatum, `Ex R x s ↔ ∃ y, R x y s`: the domain of `R` at `s`. -/
def Ex (R : E → E → S → Prop) : E → S → Prop :=
  λ x s => ∃ y, R x y s

/-- Existential closure of the possessor, `ExPossessor R y s ↔ ∃ x, R x y s`: the codomain of `R`
at `s`, the alienator nominalizer of [adamson-2024] that closes a relational noun's possessor
slot. -/
def ExPossessor (R : E → E → S → Prop) : E → S → Prop :=
  λ y s => ∃ x, R x y s

/-- The alienator over a relationalized noun keeps the sortal core and closes the relation. -/
theorem exPossessor_pi (P : E → S → Prop) (R : E → E → S → Prop) (y : E) (s : S) :
    ExPossessor (π P R) y s ↔ P y s ∧ ∃ x, R x y s := by
  simp only [ExPossessor, π, exists_and_left]

end Possession