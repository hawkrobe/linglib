/-
# CDRT Embedding into Dynamic Ty2

CDRT IS Dynamic Ty2 - Muskens created both.
The embedding is essentially definitional.

## References

- Muskens (1996). Combining Montague Semantics and Discourse Representation.
-/

import Linglib.Theories.DynamicSemantics.Core.DynamicTy2
import Linglib.Theories.DynamicSemantics.CDRT.Basic

namespace Theories.DynamicSemantics.CDRT

open Theories.DynamicSemantics.Core.DynamicTy2

-- ============================================================================
-- PART 1: Type Identification
-- ============================================================================

/-- CDRT Register = Dynamic Ty2 Assignment -/
theorem register_eq {E : Type*} : Register E = (Nat → E) := rfl

/-- CDRT dref: register lookup -/
def dref {E : Type*} (n : Nat) : Dref (Register E) E := fun r => r n

-- ============================================================================
-- PART 2: Embedding (Identity!)
-- ============================================================================

/-- CDRT DProp IS a DRS -/
def toDRS {E : Type*} (φ : DProp E) : DRS (Register E) := φ

/-- DRS IS CDRT DProp -/
def ofDRS {E : Type*} (D : DRS (Register E)) : DProp E := D

@[simp] theorem toDRS_ofDRS {E : Type*} (φ : DProp E) : ofDRS (toDRS φ) = φ := rfl
@[simp] theorem ofDRS_toDRS {E : Type*} (D : DRS (Register E)) : toDRS (ofDRS D) = D := rfl

-- ============================================================================
-- PART 3: Connective Preservation
-- ============================================================================

theorem ofStatic_eq_test {E : Type*} (p : SProp E) :
    toDRS (DProp.ofStatic p) = test p := by
  ext i o
  simp only [toDRS, DProp.ofStatic, test, eq_iff_iff]
  constructor
  · intro ⟨heq, hp⟩; exact ⟨heq, by rw [← heq]; exact hp⟩
  · intro ⟨heq, hp⟩; exact ⟨heq, by rw [heq]; exact hp⟩

theorem seq_eq_dseq {E : Type*} (φ ψ : DProp E) :
    toDRS (φ ;; ψ) = dseq (toDRS φ) (toDRS ψ) := by
  ext i o
  simp only [toDRS, DProp.seq, dseq]

theorem neg_eq_test_dneg {E : Type*} (φ : DProp E) :
    toDRS (DProp.neg φ) = test (dneg (toDRS φ)) := by
  ext i o
  simp only [toDRS, DProp.neg, test, dneg, eq_iff_iff]
  constructor
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [← heq]; exact hnex⟩
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [heq]; exact hnex⟩

theorem impl_eq_test_dimpl {E : Type*} (φ ψ : DProp E) :
    toDRS (DProp.impl φ ψ) = test (dimpl (toDRS φ) (toDRS ψ)) := by
  ext i o
  simp only [toDRS, DProp.impl, test, dimpl, eq_iff_iff]
  constructor
  · intro ⟨heq, hall⟩; exact ⟨heq, by rw [← heq]; exact hall⟩
  · intro ⟨heq, hall⟩; exact ⟨heq, by rw [heq]; exact hall⟩

theorem trueAt_eq_closure {E : Type*} (φ : DProp E) (i : Register E) :
    φ.true_at i ↔ closure (toDRS φ) i := by
  simp only [DProp.true_at, closure, toDRS]

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-!
## CDRT ≅ Dynamic Ty2 (Isomorphism)

CDRT is not just embedded - it IS Dynamic Ty2:
- `Register E = Nat → E` is the S parameter
- `DProp E = DRS (Register E)` (definitionally!)
- `SProp E = Condition (Register E)`

Connective correspondence:
- ofStatic = test
- ;; = ⨟
- neg = test ∘ dneg
- impl = test ∘ dimpl
- true_at = closure
-/

end Theories.DynamicSemantics.CDRT
