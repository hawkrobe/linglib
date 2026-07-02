/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.BirkhoffFactorizationSemiring
import Linglib.Syntax.Minimalist.SyntacticObject.Basic
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Feature consistency as Birkhoff renormalization

[marcolli-chomsky-berwick-2025]'s account of the syntax–semantics interface replaces a per-feature
checking *lifecycle* (the retired activate → check → erase state machine with a Boolean
`convergesAtLF`-style verdict) by a **single recursive map** `φ₊` — the renormalized character of a Birkhoff
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

/-- The **identity Rota–Baxter operator** (weight `+1`) on `Consistency`
    ([marcolli-chomsky-berwick-2025] Lemma 3.2.7, `R = id`): valid because `∨` is idempotent, so
    the weight-`+1` divergence term is absorbed (`a ∧ b = (a∧b) ∨ (a∧b) ∨ (a∧b)`). On a Boolean
    target the threshold/ReLU operator collapses to `id`, since disagreement already *is* the
    additive zero `inconsistent`. -/
def rbId : RotaBaxterSemiring Consistency where
  op := AddMonoidHom.id Consistency
  rotaBaxter := by rintro ⟨⟩ ⟨⟩ <;> rfl

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
    over all substructures" — superseding the retired per-feature checking lifecycle. -/
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

/-! ### The head-following feature character `ϕ_{Υ,s,h}` (MCB Lemma 3.2.5)

[marcolli-chomsky-berwick-2025]'s interface character (Lemma 3.2.5) follows the **head**: a probe
`Υ` (testing agreement/disagreement with a semantic hypothesis) is applied to the semantic value of
the §1.13 selection head `h(T)` of a tree, with `−∞` (here `inconsistent`) when `T` has no
well-defined head. We instantiate it for *features*: the probe `Υ : LIToken → Consistency` tests
the head lexical item's features. The head is the genuine `selCheckN` (Lemma 1.13.7), so the
character is grounded in the real selection-driven head, not a stipulation. (This is MCB's §3.2.1
head-following toy model — deliberately the simplest illustration; §3.2.2 refines it via convexity.)
-/

/-- **The head-probe value on a tree** `Υ_{s,h}` ([marcolli-chomsky-berwick-2025] eq. (3.2.1)): the
    probe `Υ` applied to `T`'s §1.13 selection head (`selCheckN`); `inconsistent` (`−∞`) when `T`
    has no well-defined head (off the endocentric domain). -/
def headProbeTree (Υ : LIToken → Consistency) (T : Nonplanar SOLabel) : Consistency :=
  (selCheckN T).elim Consistency.inconsistent fun p => Υ p.1

/-- `Υ_{s,h}` extended multiplicatively to forests (the semiring character of Lemma 3.2.5): a
    workspace is consistent iff each of its trees is. Mirrors `birkhoffMinusMonoidHom`. -/
def headProbeMonoidHom (Υ : LIToken → Consistency) :
    Multiplicative (Forest (Nonplanar SOLabel)) →* Consistency where
  toFun F := (F.toAdd.map (headProbeTree Υ)).prod
  map_one' := by
    show ((0 : Forest (Nonplanar SOLabel)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (headProbeTree Υ)).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- **The head-following feature character** `φ = ϕ_{Υ,s,h}` ([marcolli-chomsky-berwick-2025]
    Lemma 3.2.5) as an algebra hom `H →ₐ[ℕ] Consistency`: the unrenormalized feature assignment
    whose Birkhoff renormalization is the consistency map. -/
noncomputable def headProbeChar (Υ : LIToken → Consistency) :
    ConnesKreimer ℕ (Nonplanar SOLabel) →ₐ[ℕ] Consistency :=
  ConnesKreimer.lift (headProbeMonoidHom Υ)

@[simp] theorem headProbeChar_apply_of' (Υ : LIToken → Consistency)
    (F : Forest (Nonplanar SOLabel)) :
    headProbeChar Υ (of' F) = (F.map (headProbeTree Υ)).prod := by
  rw [headProbeChar, ConnesKreimer.lift_of']
  rfl

@[simp] theorem headProbeChar_apply_ofTree (Υ : LIToken → Consistency) (T : Nonplanar SOLabel) :
    headProbeChar Υ (ofTree T) = headProbeTree Υ T := by
  unfold ofTree
  rw [headProbeChar_apply_of', Multiset.map_singleton, Multiset.prod_singleton]

theorem headProbeChar_one (Υ : LIToken → Consistency) : headProbeChar Υ 1 = 1 := map_one _

/-- **The feature-consistency verdict on a syntactic object** ([marcolli-chomsky-berwick-2025]
    §3.1.5, Lemma 3.2.5/3.2.7): the Birkhoff renormalization (with `R = id`) of the head-following
    feature character `ϕ_{Υ,s,h}`, evaluated at `S`. This *is* the "single recursive map [that]
    incorporates the consistency checking over all substructures" — the replacement for the
    retired checking lifecycle. `consistent` iff the head-probe agreements cohere across all
    substructures of `S`. -/
noncomputable def headConsistency (Υ : LIToken → Consistency) (S : SyntacticObject) : Consistency :=
  featureConsistency (headProbeChar Υ).toLinearMap Consistency.rbId S

/-- The head-driven consistency verdict factors as the semiring Birkhoff convolution `φ₊ = φ₋ ⋆ φ`
    of the head-following character ([marcolli-chomsky-berwick-2025] Def. 3.1.6, Lemma 3.2.7). -/
theorem headConsistency_eq_convMul (Υ : LIToken → Consistency) (S : SyntacticObject) :
    LinearMap.mul' ℕ Consistency
        ((TensorProduct.map
            (SemiringRenorm.birkhoffMinus (headProbeChar Υ).toLinearMap Consistency.rbId).toLinearMap
            (headProbeChar Υ).toLinearMap)
          (comulAlgHomN S.toCK))
      = headConsistency Υ S :=
  featureConsistency_eq_convMul _ _ (headProbeChar_one Υ) S

end Minimalist
