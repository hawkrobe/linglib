import Linglib.Semantics.Degree.Defs

/-!
# Degree Semantics: Positive-Form Semantics

Positive-form semantic operations on the types declared in `Defs.lean`,
plus threshold-comparison predicates on the concrete `Degree max` /
`Threshold max` carriers [kennedy-2007] [heim-2001]
[kennedy-mcnally-2005]. Kennedy 2007's interpretive economy lives
in the sibling `Kennedy.lean`.

## Main definitions

* `positiveSem` — abstract positive-form predicate `μ(x) ≥ θ`
* `positiveMeaning`, `negativeMeaning`, `antonymMeaning` — concrete
  threshold-comparison predicates on `Degree max` / `Threshold max`

## Main theorems

* `positiveMeaning_monotone` — monotonicity in the threshold

## Relationship to `Gradability.Basic`

This module uses abstract types (`Entity D : Type*` with `LinearOrder D`)
for framework-level theorems. `Gradability.Basic` uses concrete
`Degree max := Fin (max + 1)` for computation in RSA models and Fragment
entries. The two serve different clients: this module is imported by
`Degree/Comparative.lean` and other framework siblings; `Gradability.Basic`
is imported by `Fragments/English/` and gradability `Studies/` files.
-/

namespace Semantics.Degree

open Semantics.Degree (Degree Threshold)
section Abstract

variable {Entity D : Type*} [LinearOrder D]

/-- The positive (unmarked) form of a gradable adjective:
"Kim is tall" is true iff `μ(Kim) ≥ θ` for a contextual standard `θ`.

This is the common core across Kennedy and Heim:
* Kennedy: `⟦tall⟧ = λd.λx. height(x) ≥ d`, with `θ = pos(tall)`
* Heim: `⟦tall⟧ = λx. height(x) ≥ θ_c`

Klein's approach is different: "tall" is true relative to a comparison
class, with no degree parameter. -/
def positiveSem (μ : Entity → D) (θ : D) (x : Entity) : Prop :=
  μ x ≥ θ

end Abstract

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

end Semantics.Degree
