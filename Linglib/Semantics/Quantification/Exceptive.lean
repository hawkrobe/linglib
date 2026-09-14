import Linglib.Semantics.Quantification.Counting
import Mathlib.Order.Bounds.Basic

/-!
# Exceptive quantifiers

This file defines the semantics of exceptive constructions, *every student but John*, over
generalized quantifiers. An exceptive subtracts an exception set `C` from the restrictor of a
determiner. `ExcRestrictive Q A C B` is domain subtraction with restrictiveness, `Q (A \ C) B`
and not `Q A B`, the semantics [von-fintel-1993] gives free exceptives, *except for John*.
`ExcLeast Q A C B` is his semantics of the *but*-phrase: `C` is the least set whose subtraction
makes the quantification true, so that the phrase names the set responsible for the falsehood
of the quantification. `ExcW` and `ExcS` are the weak and strong exceptives of
[peters-westerstahl-2006], which state the exception in terms of counterexamples to the
generalization.

## Main definitions

* `ExcRestrictive`, `ExcLeast` — domain subtraction with restrictiveness, and with the least
  exception.
* `IsException`, `ExcW`, `ExcS` and their negative variants.

## Main results

* `ExcLeast.unique`, `ExcLeast.sInf_eq` — the least exception is unique and is the intersection
  of the sets whose subtraction verifies the quantification.
* `ExcLeast.not_of_restrictorUpwardMono`, `ExcRestrictive.not_of_restrictorUpwardMono` — a
  left-upward-monotone determiner admits only the empty exception, and no restrictive one.
* `ExcRestrictive.mono` — under a left-downward-monotone determiner restrictiveness is preserved
  by enlarging the exception, the inference the least exception blocks.

## References

* [von-fintel-1993]
* [peters-westerstahl-2006]
-/

namespace Quantification.Exceptive

open Quantification

variable {α : Type*}

/-! ### Domain subtraction with restrictiveness and with the least exception -/

/-- Domain subtraction with restrictiveness: the quantification holds with `C` subtracted from
the restrictor and fails without, (17) of [von-fintel-1993] and the semantics of the free
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

/-- A nonempty least exception is restrictive: the uniqueness condition subsumes
restrictiveness. -/
theorem excRestrictive (h : ExcLeast Q A C B) {x : α} (hx : C x) : ExcRestrictive Q A C B :=
  ⟨h.1, λ hQ => h.2 (show Q (λ x => A x ∧ ¬ False) B from
    (congrArg (Q · B) (funext λ _ => propext (and_iff_left id))).mpr hQ) x hx⟩

end ExcLeast

/-! ### Peters & Westerståhl (2006) Exceptive Operators -/

/-- Whether an element is an "exception" for a positive generalization Q₁(A, B):
    an element of A that is NOT in B (i.e., a counterexample to the generalization).

    For "every student passed", John is an exception if John is a student who
    did not pass — i.e., John ∈ A \ B.

    For negative generalizations (like "no"), the notion inverts: an exception
    would be an element of A ∩ B. We handle this via `IsExceptionNeg`.

    [peters-westerstahl-2006] Ch 8, p299. -/
def IsException (a : α) (A B : α → Prop) : Prop :=
  A a ∧ ¬ B a

/-- Whether an element is an "exception" for a negative generalization:
    an element of A that IS in B (a counterexample to "no A is B").

    [peters-westerstahl-2006] Ch 8, p299. -/
def IsExceptionNeg (a : α) (A B : α → Prop) : Prop :=
  A a ∧ B a

/-- Weak exceptive ([peters-westerstahl-2006] Ch 8, (8.31)):

    `Exc_w(Q₁, C)(A, B) ⟺ Q₁(A \ C, B) ∧ something in A ∩ C is an exception for Q₁`

    "Every student but John passed" (weak reading):
    = every(student \ {John}, passed) ∧ ∃x ∈ student ∩ {John}, x ∉ passed
    = every(student \ {John}, passed) ∧ John didn't pass

    The weak version only requires SOME excepted element to be an actual exception. -/
def ExcW (Q₁ : GQ α) (C A B : α → Prop) : Prop :=
  Q₁ (λ x => A x ∧ ¬ C x) B ∧
  (∃ x, A x ∧ C x ∧ IsException x A B)

/-- Strong exceptive ([peters-westerstahl-2006] Ch 8, (8.33)):

    `Exc_s(Q₁, C)(A, B) ⟺ Q₁(A \ C, B) ∧ A ∩ C ≠ ∅ ∧ everything in A ∩ C is an exception for Q₁`

    "Every student but John passed" (strong reading):
    = every(student \ {John}, passed) ∧ {John} ∩ student ≠ ∅ ∧ ∀x ∈ student ∩ {John}, x ∉ passed
    = every(student \ {John}, passed) ∧ John is a student ∧ John didn't pass

    The strong version requires EVERY excepted element to be an actual exception,
    and that the exception set is non-empty.

    P&W argue this is the correct analysis: the UC (Uniqueness Condition)
    follows from Exc_s but not from Exc_w. -/
def ExcS (Q₁ : GQ α) (C A B : α → Prop) : Prop :=
  Q₁ (λ x => A x ∧ ¬ C x) B ∧
  (∃ x, A x ∧ C x) ∧
  (∀ x, A x → C x → IsException x A B)

/-- Weak exceptive for negative quantifiers ([peters-westerstahl-2006] Ch 8, (8.31)):

    `Exc_w(no, C)(A, B) ⟺ no(A \ C, B) ∧ something in A ∩ C is in B`

    "No student but John passed" (weak reading):
    = no(student \ {John}, passed) ∧ John passed -/
def ExcWNeg (Q₁ : GQ α) (C A B : α → Prop) : Prop :=
  Q₁ (λ x => A x ∧ ¬ C x) B ∧
  (∃ x, A x ∧ C x ∧ IsExceptionNeg x A B)

/-- Strong exceptive for negative quantifiers ([peters-westerstahl-2006] Ch 8, (8.33)):

    `Exc_s(no, C)(A, B) ⟺ no(A \ C, B) ∧ A ∩ C ≠ ∅ ∧ everything in A ∩ C is in B`

    "No student but John passed" (strong reading):
    = no(student \ {John}, passed) ∧ John is a student ∧ John passed -/
def ExcSNeg (Q₁ : GQ α) (C A B : α → Prop) : Prop :=
  Q₁ (λ x => A x ∧ ¬ C x) B ∧
  (∃ x, A x ∧ C x) ∧
  (∀ x, A x → C x → IsExceptionNeg x A B)

end Quantification.Exceptive
