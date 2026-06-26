/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.BirkhoffFactorizationSemiring
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Feature consistency as Birkhoff renormalization

[marcolli-chomsky-berwick-2025]'s account of the syntax–semantics interface replaces a per-feature
checking *lifecycle* (activate → check → erase, with a `convergesAtLF`/`convergesAtSpellOut`
verdict) by a **single recursive map** `φ₊` — the renormalized character of a Birkhoff
factorization over the Connes–Kreimer Hopf algebra of the syntactic object, which "recursively
modifies an initially chosen assignment of semantic values so as to incorporate the consistency
checking over all substructures" (§3.1.5).

This file instantiates that map for **feature consistency** in the Boolean (parsing) semiring of
§3.5: the target `Consistency = {inconsistent, consistent}` with `∨`/`∧`. The syntactic object `S`
(a `Nonplanar SOLabel` subtree, `SOLabel = LIToken ⊕ Unit`) embeds into the Hopf algebra via
`ofTree S.val` (no head decoration — the single MCB carrier, `FreeCommMagma`/`toNonplanar`
retired). A local feature character `φ` is renormalized by the weight-`+1` semiring Birkhoff
factorization (`RootedTree.ConnesKreimer.SemiringRenorm`) into the consistency map `φ₊`.

The Birkhoff machinery is noncomputable (the coproduct goes through `Quotient.out`), so `φ₊` is a
*specification* of consistency, not an executable checker; concrete verdicts are established by
structural proof.

## Main definitions

- `Consistency`: the Boolean consistency semiring (MCB §3.5 Boolean parsing).
- `SyntacticObject.toCK`: the SO → Connes–Kreimer Hopf algebra bridge `ofTree S.val`.

## References

[marcolli-chomsky-berwick-2025] (§3.1.5, §3.5, Def. 3.1.2, Prop. 3.1.9)
-/

namespace Minimalist

open RootedTree RootedTree.ConnesKreimer

/-! ### The Boolean consistency semiring -/

/-- The **Boolean consistency semiring** `{inconsistent, consistent}`: the two-element idempotent
    commutative semiring with `∨` ("some decomposition is consistent") as addition and `∧` ("all
    parts agree") as multiplication. The target of the feature-consistency character
    ([marcolli-chomsky-berwick-2025] §3.5's Boolean parsing semiring). -/
inductive Consistency where
  | inconsistent
  | consistent
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Consistency

/-- Disjunction (`+`): consistent iff at least one argument is. -/
def or : Consistency → Consistency → Consistency
  | consistent, _ => consistent
  | _, consistent => consistent
  | _, _ => inconsistent

/-- Conjunction (`*`): consistent iff both arguments are. -/
def and : Consistency → Consistency → Consistency
  | consistent, consistent => consistent
  | _, _ => inconsistent

instance : CommSemiring Consistency where
  add := or
  mul := and
  zero := inconsistent
  one := consistent
  nsmul n a := n.rec inconsistent fun _ acc => or acc a
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  add_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  zero_add := by rintro ⟨⟩ <;> rfl
  add_zero := by rintro ⟨⟩ <;> rfl
  add_comm := by rintro ⟨⟩ ⟨⟩ <;> rfl
  mul_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  one_mul := by rintro ⟨⟩ <;> rfl
  mul_one := by rintro ⟨⟩ <;> rfl
  mul_comm := by rintro ⟨⟩ ⟨⟩ <;> rfl
  left_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  right_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  zero_mul := by rintro ⟨⟩ <;> rfl
  mul_zero := by rintro ⟨⟩ <;> rfl

end Consistency

/-! ### The SO → Hopf algebra bridge -/

/-- The syntactic object as an element of the Connes–Kreimer Hopf algebra over `ℕ`: the singleton
    forest of its underlying nonplanar tree `S.val : Nonplanar SOLabel`. The base ring is `ℕ`
    (every commutative semiring, including `Consistency`, is an `ℕ`-algebra; a Boolean target is
    not a `ℤ`-algebra). This is the bridge on which a consistency character acts — no head
    decoration, since the single MCB carrier already *is* a `Nonplanar SOLabel` subtype. -/
noncomputable def SyntacticObject.toCK (S : SyntacticObject) :
    ConnesKreimer ℕ (Nonplanar SOLabel) :=
  ofTree S.val

/-! ### The feature-consistency map -/

open scoped TensorProduct

/-- The **feature-consistency map** `φ₊` on a syntactic object: the renormalized value of a feature
    character `φ` (with weight-`+1` Rota–Baxter operator `R`) at the SO. This is
    [marcolli-chomsky-berwick-2025]'s "single recursive map [that] recursively modifies an
    initially chosen assignment of semantic values so as to incorporate the consistency checking
    over all substructures" — superseding the per-feature `convergesAtLF` lifecycle. -/
noncomputable def featureConsistency
    (φ : ConnesKreimer ℕ (Nonplanar SOLabel) →ₗ[ℕ] Consistency)
    (RB : RotaBaxterSemiring Consistency) (S : SyntacticObject) : Consistency :=
  SemiringRenorm.birkhoffPlusTree φ RB S.val

/-- The feature-consistency map factors as the semiring Birkhoff convolution `φ₊ = φ₋ ⋆ φ`
    ([marcolli-chomsky-berwick-2025] Def. 3.1.6, Prop. 3.1.9): on the SO's Hopf-algebra image
    `S.toCK`, the convolution of the Bogolyubov counterterm `φ₋` with the character `φ` recovers the
    consistency verdict. Needs `φ` unital. -/
theorem featureConsistency_eq_convMul
    (φ : ConnesKreimer ℕ (Nonplanar SOLabel) →ₗ[ℕ] Consistency)
    (RB : RotaBaxterSemiring Consistency) (hφ : φ 1 = 1) (S : SyntacticObject) :
    LinearMap.mul' ℕ Consistency
        ((TensorProduct.map (SemiringRenorm.birkhoffMinus φ RB).toLinearMap φ)
          (comulAlgHomN S.toCK))
      = featureConsistency φ RB S :=
  SemiringRenorm.birkhoffFactorization_ofTree φ RB hφ S.val

end Minimalist
