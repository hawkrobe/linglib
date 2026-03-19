/-
# DPL Embedding into Dynamic Ty2

DPL embeds directly into Dynamic Ty2 with S = Nat → E.
DPL assignments ARE Dynamic Ty2 assignments.
DPL relations ARE DRS meanings.

-/

import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Semantics.Dynamic.DPL.Basic
import Linglib.Theories.Semantics.Dynamic.Core.CCP
import Linglib.Core.CylindricAlgebra

namespace Semantics.Dynamic.DPL

open Semantics.Dynamic.Core.DynamicTy2
open Semantics.Dynamic.Core

/-- DPL dref: projection function for variable n -/
def dref {E : Type*} (n : Nat) : Dref (Assignment E) E := λ g => g n

/-- DPL extend is Assignment.update. -/
abbrev extend {E : Type*} (g : Assignment E) (n : Nat) (e : E) : Assignment E :=
  g.update n e

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

-- ════════════════════════════════════════════════════════════════
-- § Cylindric Algebra Bridge
-- ════════════════════════════════════════════════════════════════

/-! ### DPL as a cylindric set algebra

The fundamental observation of @cite{groenendijk-stokhof-1991}: DPL's
existential quantifier IS cylindrification. DPL's identity test IS
a diagonal element. These are not analogies — they are algebraic
identities under `closure`. -/

open Core.CylindricAlgebra

/-- **DPL existential = cylindrification.**

`closure(∃x.φ) = cₓ(closure(φ))`: the truth-conditional content of
DPL's existential quantifier at variable `x` is exactly cylindrification
at register `x`. This is the defining correspondence between DPL
and cylindric set algebra. -/
theorem closure_exists_eq_cylindrify {E : Type*} (x : Nat) (φ : DPLRel E) :
    closure (toDRS (DPLRel.exists_ x φ)) =
    cylindrify x (closure (toDRS φ)) := by
  ext g; simp only [closure, toDRS, DPLRel.exists_, cylindrify]
  exact ⟨fun ⟨h, d, hφ⟩ => ⟨d, h, hφ⟩, fun ⟨d, h, hφ⟩ => ⟨h, d, hφ⟩⟩

/-- **DPL identity test = diagonal element.**

`closure(atom(g(x) = g(y))) = Dxy`: the truth condition of the DPL
atomic formula `x = y` is the diagonal element `Dxy` from cylindric
algebra. -/
theorem closure_identity_eq_diagonal {E : Type*} (x y : Nat) :
    closure (toDRS (DPLRel.atom (fun g : Assignment E => g x = g y))) =
    @diagonal E x y := by
  ext g; simp only [closure, toDRS, DPLRel.atom, diagonal]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

/-- DPL negation under closure is a test for non-cylindrifiability:
`closure(¬φ)(g)` iff no assignment update satisfies φ. -/
theorem closure_neg_eq {E : Type*} (φ : DPLRel E) :
    closure (toDRS (DPLRel.neg φ)) =
    fun g => ¬ closure (toDRS φ) g := by
  ext g; simp only [closure, toDRS, DPLRel.neg]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § Bridges for Implication, Disjunction, Universal, Closure
-- ════════════════════════════════════════════════════════════════

/-- **DPL implication = test of dynamic implication.**

`toDRS(φ → ψ) = test(dimpl(toDRS φ)(toDRS ψ))` -/
theorem impl_eq_test_dimpl {E : Type*} (φ ψ : DPLRel E) :
    toDRS (DPLRel.impl φ ψ) = test (dimpl (toDRS φ) (toDRS ψ)) := by
  ext g h
  simp only [toDRS, DPLRel.impl, test, dimpl, eq_iff_iff]
  constructor
  · intro ⟨heq, hall⟩; exact ⟨heq, by rw [← heq]; exact hall⟩
  · intro ⟨heq, hall⟩; exact ⟨heq, by rw [heq]; exact hall⟩

/-- **DPL disjunction = test of dynamic disjunction.**

`toDRS(φ ∨ ψ) = test(ddisj(toDRS φ)(toDRS ψ))` -/
theorem disj_eq_test_ddisj {E : Type*} (φ ψ : DPLRel E) :
    toDRS (DPLRel.disj φ ψ) = test (ddisj (toDRS φ) (toDRS ψ)) := by
  ext g h
  simp only [toDRS, DPLRel.disj, test, ddisj, eq_iff_iff]
  constructor
  · intro ⟨heq, hd⟩; exact ⟨heq, by rw [← heq]; exact hd⟩
  · intro ⟨heq, hd⟩; exact ⟨heq, by rw [heq]; exact hd⟩

/-- **DPL closure = test of existential closure.**

`toDRS(◇φ) = test(closure(toDRS φ))` -/
theorem close_eq_test_closure {E : Type*} (φ : DPLRel E) :
    toDRS (DPLRel.close φ) = test (closure (toDRS φ)) := by
  ext g h
  simp only [toDRS, DPLRel.close, test, closure, eq_iff_iff]
  constructor
  · intro ⟨heq, hc⟩; exact ⟨heq, by rw [← heq]; exact hc⟩
  · intro ⟨heq, hc⟩; exact ⟨heq, by rw [heq]; exact hc⟩

/-- **DPL truth = existential closure.**

`trueAt φ g ↔ closure(toDRS φ) g` -/
theorem trueAt_eq_closure {E : Type*} (φ : DPLRel E) (g : Assignment E) :
    DPLRel.trueAt φ g ↔ closure (toDRS φ) g := Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § Unified API: Re-exports for single-import usage
-- ════════════════════════════════════════════════════════════════

/-! Importing `DPL.Bridge` gives access to both the DPL-specific
operations (from `Basic`) and the shared dynamic algebra (from
`DynProp`/`DynamicTy2`). This avoids the need to separately import
`Core.DynProp` or `Core.CCP` for standard DPL work. -/

export DPLRel (atom conj exists_ neg impl disj forall_ close)

end Semantics.Dynamic.DPL
