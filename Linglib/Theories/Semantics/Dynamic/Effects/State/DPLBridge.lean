/-
# DPL Embedding into Dynamic Ty2

DPL embeds directly into Dynamic Ty2 with S = Nat → E.
DPL assignments ARE Dynamic Ty2 assignments.
DPL relations ARE DRS meanings.

## References

- Groenendijk & Stokhof (1991). Dynamic Predicate Logic.
- Muskens (1996). Combining Montague Semantics and Discourse Representation.
-/

import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Semantics.Dynamic.Effects.State.DPL

namespace DynamicSemantics.DPL

open DynamicSemantics.Core.DynamicTy2


/-- DPL assignment type = Dynamic Ty2 S parameter -/
abbrev Assignment (E : Type*) := Nat → E

/-- DPL dref: projection function for variable n -/
def dref {E : Type*} (n : Nat) : Dref (Assignment E) E := λ g => g n

/-- Functional update -/
def extend {E : Type*} (g : Assignment E) (n : Nat) (e : E) : Assignment E :=
  λ m => if m = n then e else g m

theorem extend_at {E : Type*} (g : Assignment E) (n : Nat) (e : E) :
    dref n (extend g n e) = e := by simp [dref, extend]

theorem extend_other {E : Type*} (g : Assignment E) (n m : Nat) (e : E) (h : n ≠ m) :
    dref m (extend g n e) = dref m g := by simp [dref, extend, h.symm]


/-- DPL relation IS a DRS -/
def toDRS {E : Type*} (φ : DPLRel E) : DRS (Assignment E) := φ

/-- DRS IS a DPL relation -/
def ofDRS {E : Type*} (D : DRS (Assignment E)) : DPLRel E := D

@[simp] theorem toDRS_ofDRS {E : Type*} (φ : DPLRel E) : ofDRS (toDRS φ) = φ := rfl
@[simp] theorem ofDRS_toDRS {E : Type*} (D : DRS (Assignment E)) : toDRS (ofDRS D) = D := rfl


theorem atom_eq_test {E : Type*} (p : Assignment E → Prop) :
    toDRS (DPLRel.atom p) = test (λ g => p g) := by
  ext g h
  simp only [toDRS, DPLRel.atom, test, eq_iff_iff]
  constructor
  · intro ⟨heq, hp⟩; exact ⟨heq, by rw [← heq]; exact hp⟩
  · intro ⟨heq, hp⟩; exact ⟨heq, by rw [heq]; exact hp⟩

theorem conj_eq_dseq {E : Type*} (φ ψ : DPLRel E) :
    toDRS (DPLRel.conj φ ψ) = dseq (toDRS φ) (toDRS ψ) := by
  ext g h
  simp only [toDRS, DPLRel.conj, dseq]

theorem neg_eq_test_dneg {E : Type*} (φ : DPLRel E) :
    toDRS (DPLRel.neg φ) = test (dneg (toDRS φ)) := by
  ext g h
  simp only [toDRS, DPLRel.neg, test, dneg, eq_iff_iff]
  constructor
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [← heq]; exact hnex⟩
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [heq]; exact hnex⟩

theorem exists_eq {E : Type*} (x : Nat) (φ : DPLRel E) :
    toDRS (DPLRel.exists_ x φ) = λ g h => ∃ d : E, toDRS φ (extend g x d) h := by
  -- The definitions are definitionally equal (just variable renaming)
  rfl

end DynamicSemantics.DPL
