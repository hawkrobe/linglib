/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.BirkhoffFactorizationSemiring
import Linglib.Syntax.Minimalist.Linearization.Externalization
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Marcolli, Chomsky and Berwick (2025): Mathematical Structure of Syntactic Merge

This file formalizes the worked examples of externalization of
[marcolli-chomsky-berwick-2025] on the `SyntacticObject` carrier of the Minimalist
substrate: the harmonic head-initial and head-final orders of a determiner–noun Merge, the
head-side convention flipping the yield, and exocentric elimination, two saturated nouns
determining no head and hence no order. The framework itself is the `Syntax/Minimalist/`
theory layer; the examples are kernel-checked against it.

The book's syntax–semantics interface (Chapter 3) replaces per-feature checking by a single
recursive map, the Birkhoff renormalization of a character of the Connes–Kreimer Hopf algebra
of the syntactic object. The Boolean parsing semiring `Consistency` of §3.5 is the target,
`toCK` embeds a syntactic object into the Hopf algebra, `featureConsistency` is the renormalized
character, and `headConsistency` instantiates it for the head-following character of Lemma 3.2.5,
whose probe reads the §1.13 selection head. The machinery is noncomputable, so these are
specifications of consistency rather than checkers.

## TODO

The book's section locators (§1.12.1, §1.13, §1.13.2) are transcribed from an earlier
version of this file and are UNVERIFIED against the published text.

## References

* [marcolli-chomsky-berwick-2025]
-/

namespace MarcolliChomskyBerwick2025

open RoseTree UnorderedTree Minimalist SyntacticObject ConnesKreimer

/-- A determiner over a noun: `D` selects `N`, so `D` projects. -/
private def theDog : SyntacticObject :=
  ⟨UnorderedTree.mk (.node (Sum.inr none)
    [.node (Sum.inl ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

/-- Harmonic head-initial: the projecting `D`'s yield comes first. -/
example : (theDog.linearize .initial).map (·.map (·.id)) = some [0, 1] := by decide

/-- Harmonic head-final: the same head function, mirrored. -/
example : (theDog.linearize .final).map (·.map (·.id)) = some [1, 0] := by decide

example : theDog.phonYield .initial = some ["the", "dog"] := by decide
example : theDog.phonYield .final = some ["dog", "the"] := by decide

/-- Exocentric Merge: two saturated `N`s, neither selecting the other, so no head and no
order. -/
private def exoNN : SyntacticObject :=
  ⟨UnorderedTree.mk (.node (Sum.inr none)
    [.node (Sum.inl ⟨.simple .N [] (phonForm := "cats"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

example : exoNN.linearize .initial = none := by decide
example : exoNN.linearize .final = none := by decide

/-! ### Feature consistency as Birkhoff renormalization (Chapter 3) -/

/-- The Boolean consistency semiring of §3.5, the two-element idempotent commutative semiring
with disjunction as addition, some decomposition being consistent, and conjunction as
multiplication, all parts agreeing. -/
inductive Consistency where
  | inconsistent
  | consistent
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Consistency

/-- Disjunction, consistent iff at least one argument is. -/
def or : Consistency → Consistency → Consistency
  | consistent, _ => consistent
  | _, consistent => consistent
  | _, _ => inconsistent

/-- Conjunction, consistent iff both arguments are. -/
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

/-- The identity Rota–Baxter operator of weight `+1` on `Consistency` (Lemma 3.2.7), valid
because disjunction is idempotent, so the weight-`+1` term is absorbed. On a Boolean target the
threshold operator collapses to the identity, since disagreement already is the additive zero. -/
def rbId : RotaBaxterSemiring Consistency where
  op := AddMonoidHom.id Consistency
  rotaBaxter := by rintro ⟨⟩ ⟨⟩ <;> rfl

end Consistency

/-- A syntactic object as an element of the Connes–Kreimer Hopf algebra over `ℕ`, the singleton
forest of its underlying nonplanar tree. The base ring is `ℕ` because every commutative
semiring, `Consistency` included, is an `ℕ`-algebra, while a Boolean target is no `ℤ`-algebra. -/
noncomputable def toCK (S : SyntacticObject) : ConnesKreimer ℕ (UnorderedTree Vertex) :=
  ofTree S.val

open scoped TensorProduct

/-- The feature-consistency map `φ₊` on a syntactic object, the renormalized value of a feature
character `φ` with weight-`+1` Rota–Baxter operator `RB` at the object, the single recursive map
of §3.1.5 that incorporates consistency checking over all substructures. -/
noncomputable def featureConsistency
    (φ : ConnesKreimer ℕ (UnorderedTree Vertex) →ₗ[ℕ] Consistency)
    (RB : RotaBaxterSemiring Consistency) (S : SyntacticObject) : Consistency :=
  SemiringRenorm.birkhoffPlusTree φ RB S.val

/-- The feature-consistency map factors as the semiring Birkhoff convolution `φ₊ = φ₋ ⋆ φ` on
the object's Hopf-algebra image (Definition 3.1.6, Proposition 3.1.9), for a unital `φ`. -/
theorem featureConsistency_eq_convMul
    (φ : ConnesKreimer ℕ (UnorderedTree Vertex) →ₗ[ℕ] Consistency)
    (RB : RotaBaxterSemiring Consistency) (hφ : φ 1 = 1) (S : SyntacticObject) :
    LinearMap.mul' ℕ Consistency
        ((TensorProduct.map (SemiringRenorm.birkhoffMinus φ RB).toLinearMap φ)
          (comulAlgHomN (toCK S)))
      = featureConsistency φ RB S :=
  SemiringRenorm.birkhoffFactorization_ofTree φ RB hφ S.val

/-- The head-probe value `Υ_{s,h}` on a tree (equation (3.2.1)), the probe `Υ` applied to the
tree's selection head, and `inconsistent` when the tree has no well-defined head. -/
def headProbeTree (Υ : LIToken → Consistency) (T : UnorderedTree Vertex) : Consistency :=
  (selCheckN T).head.elim Consistency.inconsistent Υ

/-- `Υ_{s,h}` extended multiplicatively to forests, the semiring character of Lemma 3.2.5, so
that a workspace is consistent iff each of its trees is. -/
def headProbeMonoidHom (Υ : LIToken → Consistency) :
    Multiplicative (Forest (UnorderedTree Vertex)) →* Consistency where
  toFun F := (F.toAdd.map (headProbeTree Υ)).prod
  map_one' := by
    show ((0 : Forest (UnorderedTree Vertex)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (headProbeTree Υ)).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- The head-following feature character `ϕ_{Υ,s,h}` of Lemma 3.2.5 as an algebra homomorphism,
the unrenormalized feature assignment whose Birkhoff renormalization is the consistency map. -/
noncomputable def headProbeChar (Υ : LIToken → Consistency) :
    ConnesKreimer ℕ (UnorderedTree Vertex) →ₐ[ℕ] Consistency :=
  ConnesKreimer.lift (headProbeMonoidHom Υ)

@[simp] theorem headProbeChar_apply_of' (Υ : LIToken → Consistency)
    (F : Forest (UnorderedTree Vertex)) :
    headProbeChar Υ (of' F) = (F.map (headProbeTree Υ)).prod := by
  rw [headProbeChar, ConnesKreimer.lift_of']
  rfl

@[simp] theorem headProbeChar_apply_ofTree (Υ : LIToken → Consistency) (T : UnorderedTree Vertex) :
    headProbeChar Υ (ofTree T) = headProbeTree Υ T := by
  unfold ofTree
  rw [headProbeChar_apply_of', Multiset.map_singleton, Multiset.prod_singleton]

theorem headProbeChar_one (Υ : LIToken → Consistency) : headProbeChar Υ 1 = 1 := map_one _

/-- The feature-consistency verdict on a syntactic object (§3.1.5, Lemmas 3.2.5 and 3.2.7), the
Birkhoff renormalization with the identity operator of the head-following character, consistent
iff the head-probe agreements cohere across all substructures. -/
noncomputable def headConsistency (Υ : LIToken → Consistency) (S : SyntacticObject) :
    Consistency :=
  featureConsistency (headProbeChar Υ).toLinearMap Consistency.rbId S

/-- The head-driven verdict factors as the semiring Birkhoff convolution `φ₊ = φ₋ ⋆ φ` of the
head-following character (Definition 3.1.6, Lemma 3.2.7). -/
theorem headConsistency_eq_convMul (Υ : LIToken → Consistency) (S : SyntacticObject) :
    LinearMap.mul' ℕ Consistency
        ((TensorProduct.map
            (SemiringRenorm.birkhoffMinus (headProbeChar Υ).toLinearMap
              Consistency.rbId).toLinearMap
            (headProbeChar Υ).toLinearMap)
          (comulAlgHomN (toCK S)))
      = headConsistency Υ S :=
  featureConsistency_eq_convMul _ _ (headProbeChar_one Υ) S

end MarcolliChomskyBerwick2025
