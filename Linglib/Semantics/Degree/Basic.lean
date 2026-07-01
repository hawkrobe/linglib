import Linglib.Semantics.Degree.Defs

/-!
# Degree Semantics: Positive-Form Semantics

Threshold-comparison predicates on the concrete `Degree max` /
`Threshold max` carriers declared in `Defs.lean` [kennedy-2007]
[heim-2001] [kennedy-mcnally-2005]. The abstract positive-form
predicate `μ(x) ≥ θ` is just `Comparison.ge.over μ θ` — used directly
where needed. Kennedy 2007's interpretive economy lives in the sibling
`Kennedy.lean`.

## Main definitions

* `positiveMeaning`, `negativeMeaning`, `antonymMeaning` — concrete
  threshold-comparison predicates on `Degree max` / `Threshold max`

## Main theorems

* `positiveMeaning_monotone` — monotonicity in the threshold

## Relationship to `Gradability.Basic`

This module's concrete `Degree max := Fin (max + 1)` predicates serve
computation in RSA models and Fragment entries. `Gradability.Basic`
serves the same clients; this module is imported by
`Degree/Comparative.lean` and other framework siblings, while
`Gradability.Basic` is imported by `Fragments/English/` and gradability
`Studies/` files.
-/

namespace Degree

/-! ### Concrete threshold-based meanings

Threshold-comparison predicates on the concrete `Degree max` /
`Threshold max` carriers. These are general degree operations, not
adjective-specific. Decidability is inherited from the underlying
`Degree`/`Threshold` order. -/

section Concrete

variable {max : Nat}

/-- Positive form: `t < d`. -/
def positiveMeaning (d : Degree max) (t : Threshold max) : Prop :=
  (t : Degree max) < d

/-- Negative form: `d < t`. -/
def negativeMeaning (d : Degree max) (t : Threshold max) : Prop :=
  d < (t : Degree max)

/-- Antonym: `d ≤ t`. -/
def antonymMeaning (d : Degree max) (t : Threshold max) : Prop :=
  d ≤ (t : Degree max)

instance (d : Degree max) (t : Threshold max) : Decidable (positiveMeaning d t) :=
  inferInstanceAs (Decidable (_ < _))

instance (d : Degree max) (t : Threshold max) : Decidable (negativeMeaning d t) :=
  inferInstanceAs (Decidable (_ < _))

instance (d : Degree max) (t : Threshold max) : Decidable (antonymMeaning d t) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Monotonicity of `positiveMeaning` in the threshold: a higher threshold
is informationally stronger. If `d > θ_strong` and `θ_weak ≤ θ_strong`,
then `d > θ_weak`. Grounds the weak-vs-strong-adjective distinction
(`InformationalStrength`). -/
theorem positiveMeaning_monotone (d : Degree max) (θ_weak θ_strong : Threshold max)
    (h_ord : θ_weak ≤ θ_strong) (h_strong : positiveMeaning d θ_strong) :
    positiveMeaning d θ_weak :=
  lt_of_le_of_lt h_ord h_strong

end Concrete

end Degree
