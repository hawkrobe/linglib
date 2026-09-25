module

public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Order.Bounds.Basic

/-!
# Exceptive quantifiers

This file defines the semantics of exceptive constructions, *every student but John*, over
generalized quantifiers. An exceptive subtracts an exception set `C` from the restrictor of a
determiner. `ExcRestrictive Q A C B` is domain subtraction with restrictiveness, `Q (A \ C) B`
and not `Q A B`, the semantics [von-fintel-1993] gives free exceptives, *except for John*.
`ExcLeast Q A C B` is his semantics of the *but*-phrase: `C` is the least set whose subtraction
makes the quantification true, so that the phrase names the set responsible for the falsehood
of the quantification.

## Main definitions

* `ExcRestrictive`, `ExcLeast` — domain subtraction with restrictiveness, and with the least
  exception.

## Main results

* `ExcLeast.unique`, `ExcLeast.sInf_eq` — the least exception is unique and is the intersection
  of the sets whose subtraction verifies the quantification.
* `ExcLeast.not_of_restrictorUpwardMono`, `ExcRestrictive.not_of_restrictorUpwardMono` — a
  left-upward-monotone determiner admits only the empty exception, and no restrictive one.
* `ExcRestrictive.mono` — under a left-downward-monotone determiner restrictiveness is preserved
  by enlarging the exception, the inference the least exception blocks.

## References

* [von-fintel-1993]
-/

@[expose] public section

namespace Quantifier.Exceptive

open Quantifier Quantifier.GQ

variable {α : Type*}

/-! ### Domain subtraction with restrictiveness and with the least exception -/

/-- Domain subtraction with restrictiveness, where the quantification holds with `C` subtracted
from the restrictor and fails without, (17) of [von-fintel-1993] and the semantics of the free
exceptive (38). -/
def ExcRestrictive (Q : GQ α) (A C B : α → Prop) : Prop :=
  Q (λ x => A x ∧ ¬ C x) B ∧ ¬ Q A B

/-- The least-exception semantics of the *but*-phrase, (20) and (21) of [von-fintel-1993]: `C`
is the least set whose subtraction from the restrictor makes the quantification true. -/
def ExcLeast (Q : GQ α) (A C B : α → Prop) : Prop :=
  IsLeast {S | Q (λ x => A x ∧ ¬ S x) B} C

variable {Q : GQ α} {A C B : α → Prop}

namespace ExcRestrictive

/-- A left-upward-monotone determiner falsifies every restrictive exceptive. -/
theorem not_of_restrictorUpwardMono (hQ : RestrictorUpwardMono Q) : ¬ ExcRestrictive Q A C B :=
  λ h => h.2 (hQ _ _ _ (λ _ ha => ha.1) h.1)

/-- Under a left-downward-monotone determiner a restrictive exceptive survives enlarging the
exception set. -/
theorem mono (hQ : RestrictorDownwardMono Q) (h : ExcRestrictive Q A C B) {C' : α → Prop}
    (hC : C ≤ C') : ExcRestrictive Q A C' B :=
  ⟨hQ _ _ _ (λ _ ha => ⟨ha.1, λ hc => ha.2 (hC _ hc)⟩) h.1, h.2⟩

end ExcRestrictive

namespace ExcLeast

/-- The exception set is unique. -/
theorem unique (h : ExcLeast Q A C B) {C' : α → Prop} (h' : ExcLeast Q A C' B) : C = C' :=
  IsLeast.unique h h'

/-- The exception set is the intersection of the sets whose subtraction verifies the
quantification. -/
theorem sInf_eq (h : ExcLeast Q A C B) : sInf {S | Q (λ x => A x ∧ ¬ S x) B} = C :=
  h.isGLB.sInf_eq

/-- A left-upward-monotone determiner has no nonempty least exception: once the quantification
holds with `C` subtracted it holds with nothing subtracted, so the least exception is empty. -/
theorem not_of_restrictorUpwardMono (hQ : RestrictorUpwardMono Q) (h : ExcLeast Q A C B) (x : α) :
    ¬ C x :=
  λ hx => h.2 (hQ _ _ _ (λ _ ha => ⟨ha.1, id⟩) h.1) x hx

/-- A nonempty least exception is restrictive, so the uniqueness condition subsumes
restrictiveness. -/
theorem excRestrictive (h : ExcLeast Q A C B) {x : α} (hx : C x) : ExcRestrictive Q A C B :=
  ⟨h.1, λ hQ => h.2 (show Q (λ x => A x ∧ ¬ False) B from
    (congrArg (Q · B) (funext λ _ => propext (and_iff_left id))).mpr hQ) x hx⟩

end ExcLeast

end Quantifier.Exceptive
