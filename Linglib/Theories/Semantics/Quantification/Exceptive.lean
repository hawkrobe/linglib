import Linglib.Core.Logic.Quantification

/-!
# Exceptive Quantifiers
@cite{peters-westerstahl-2006} @cite{von-fintel-1993} @cite{gajewski-2002}

Semantic operators for "but"-exceptive constructions:

  "every student but John passed" = every(student \ {John}, passed) ∧ ¬passed(John)

Only universal quantifiers (positive or negative) license exceptives.

## Von Fintel (1993) Operators

- `ExcI`: the inclusive exceptive operator (every...but)
- `ExcE`: the exclusive exceptive operator (no...but)
- `ExceptiveCompatible`: which quantifiers license exceptives

## Peters & Westerståhl (2006) Operators

- `IsException`: whether an element is an exception for a quantifier
- `ExcW`: the weak exceptive operator (@cite{peters-westerstahl-2006} Ch 8, (8.31))
- `ExcS`: the strong exceptive operator (@cite{peters-westerstahl-2006} Ch 8, (8.33))

## Key Results

Under CONSERV, only PositiveStrong/NegativeStrong quantifiers produce
non-trivial exceptive readings — explaining the universal-only pattern.
-/

namespace Semantics.Quantification.Exceptive

open Core.Quantification

variable {α : Type*}

-- ============================================================================
-- §1 Von Fintel (1993) Exceptive Operators
-- ============================================================================

/-- Inclusive exceptive (@cite{von-fintel-1993}): Q(A \ E, B) ∧ ¬Q(A, B).

    "Every student but John passed" =
      every(student \ {John}, passed) ∧ ¬every(student, passed)

    The second conjunct asserts that the exception *matters*: without
    removing E, the quantified claim would be false. -/
def ExcI (Q : GQ α) (A E B : α → Prop) : Prop :=
  Q (λ x => A x ∧ ¬ E x) B ∧ ¬ Q A B

/-- Exclusive exceptive (@cite{von-fintel-1993}): Q(A \ E, B) ∧ complement condition on E.

    "No student but John passed" =
      no(student \ {John}, passed) ∧ John passed

    The complement condition requires that all excepted elements satisfy B. -/
def ExcE (Q : GQ α) (A E B : α → Prop) : Prop :=
  Q (λ x => A x ∧ ¬ E x) B ∧ (∀ x, E x → A x → B x)

-- ============================================================================
-- §2 Peters & Westerståhl (2006) Exceptive Operators
-- ============================================================================

/-- Whether an element is an "exception" for a positive generalization Q₁(A, B):
    an element of A that is NOT in B (i.e., a counterexample to the generalization).

    For "every student passed", John is an exception if John is a student who
    did not pass — i.e., John ∈ A \ B.

    For negative generalizations (like "no"), the notion inverts: an exception
    would be an element of A ∩ B. We handle this via `IsExceptionNeg`.

    @cite{peters-westerstahl-2006} Ch 8, p299. -/
def IsException (a : α) (A B : α → Prop) : Prop :=
  A a ∧ ¬ B a

/-- Whether an element is an "exception" for a negative generalization:
    an element of A that IS in B (a counterexample to "no A is B").

    @cite{peters-westerstahl-2006} Ch 8, p299. -/
def IsExceptionNeg (a : α) (A B : α → Prop) : Prop :=
  A a ∧ B a

/-- Weak exceptive (@cite{peters-westerstahl-2006} Ch 8, (8.31)):

    `Exc_w(Q₁, C)(A, B) ⟺ Q₁(A \ C, B) ∧ something in A ∩ C is an exception for Q₁`

    "Every student but John passed" (weak reading):
    = every(student \ {John}, passed) ∧ ∃x ∈ student ∩ {John}, x ∉ passed
    = every(student \ {John}, passed) ∧ John didn't pass

    The weak version only requires SOME excepted element to be an actual exception. -/
def ExcW (Q₁ : GQ α) (C A B : α → Prop) : Prop :=
  Q₁ (λ x => A x ∧ ¬ C x) B ∧
  (∃ x, A x ∧ C x ∧ IsException x A B)

/-- Strong exceptive (@cite{peters-westerstahl-2006} Ch 8, (8.33)):

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

/-- Weak exceptive for negative quantifiers (@cite{peters-westerstahl-2006} Ch 8, (8.31)):

    `Exc_w(no, C)(A, B) ⟺ no(A \ C, B) ∧ something in A ∩ C is in B`

    "No student but John passed" (weak reading):
    = no(student \ {John}, passed) ∧ John passed -/
def ExcWNeg (Q₁ : GQ α) (C A B : α → Prop) : Prop :=
  Q₁ (λ x => A x ∧ ¬ C x) B ∧
  (∃ x, A x ∧ C x ∧ IsExceptionNeg x A B)

/-- Strong exceptive for negative quantifiers (@cite{peters-westerstahl-2006} Ch 8, (8.33)):

    `Exc_s(no, C)(A, B) ⟺ no(A \ C, B) ∧ A ∩ C ≠ ∅ ∧ everything in A ∩ C is in B`

    "No student but John passed" (strong reading):
    = no(student \ {John}, passed) ∧ John is a student ∧ John passed -/
def ExcSNeg (Q₁ : GQ α) (C A B : α → Prop) : Prop :=
  Q₁ (λ x => A x ∧ ¬ C x) B ∧
  (∃ x, A x ∧ C x) ∧
  (∀ x, A x → C x → IsExceptionNeg x A B)

-- ============================================================================
-- §3 Compatibility (von Fintel 1993)
-- ============================================================================

/-- A quantifier is exceptive-compatible iff there exist A, E, B such that
    ExcI(Q, A, E, B). @cite{von-fintel-1993}: only (variants of)
    every and no are compatible. -/
def ExceptiveCompatible (Q : GQ α) : Prop :=
  ∃ (A E B : α → Prop), ExcI Q A E B

/-- PositiveStrong quantifiers can yield non-trivial inclusive exceptives.

    For "every": every(A\E, B) can be true (all non-excepted As are Bs)
    while every(A, B) is false (the excepted elements fail B).
    @cite{von-fintel-1993}, @cite{peters-westerstahl-2006} Ch 8. -/
theorem positiveStrong_exceptive
    (Q : GQ α) (hCons : Conservative Q) (hPS : PositiveStrong Q)
    (hNontriv : ∃ A B, ¬ Q A B) :
    ExceptiveCompatible Q := by
  obtain ⟨A, B, hFalse⟩ := hNontriv
  -- Take E = A \ B (elements of A not in B)
  -- Then A \ E = A ∩ B
  refine ⟨A, (λ x => A x ∧ ¬ B x), B, ?_, hFalse⟩
  -- Goal: Q (λ x => A x ∧ ¬ (A x ∧ ¬ B x)) B
  have hSimpl : (λ x => A x ∧ ¬ (A x ∧ ¬ B x)) = (λ x => A x ∧ B x) := by
    funext x
    apply propext
    constructor
    · rintro ⟨hA, h⟩
      refine ⟨hA, ?_⟩
      by_contra hNB
      exact h ⟨hA, hNB⟩
    · rintro ⟨hA, hB⟩
      refine ⟨hA, ?_⟩
      rintro ⟨_, hNB⟩
      exact hNB hB
  rw [hSimpl]
  -- Goal: Q (λ x => A x ∧ B x) B; use conservativity then PS
  rw [hCons (λ x => A x ∧ B x) B]
  have hSimpl2 : (λ x => (A x ∧ B x) ∧ B x) = (λ x => A x ∧ B x) := by
    funext x; apply propext; tauto
  rw [hSimpl2]
  exact hPS _

/-- Symmetric quantifiers are NOT exceptive-compatible (under CONSERV + PS).

    Intuition: under CONSERV + SYMM, Q depends only on |A ∩ B|. Removing
    elements from A while keeping them out of E cannot simultaneously
    make Q(A\E, B) true and Q(A, B) false, because the intersection
    |A∩B| ⊇ |(A\E)∩B| — removing elements from A can only shrink
    the intersection, not enlarge it.
    @cite{von-fintel-1993}, @cite{peters-westerstahl-2006} Ch 8. -/
theorem symmetric_not_exceptive (Q : GQ α)
    (hCons : Conservative Q) (hSym : QSymmetric Q)
    (hPS : PositiveStrong Q) :
    ¬ExceptiveCompatible Q := by
  rintro ⟨A, _E, B, _hQAEB, hQABf⟩
  apply hQABf
  have hInt := (conserv_symm_iff_int Q hCons).mp hSym
  have h1 := hInt A B (λ x => A x ∧ B x) (λ x => A x ∧ B x)
    (λ x => by tauto)
  rw [h1]
  exact hPS _

end Semantics.Quantification.Exceptive
