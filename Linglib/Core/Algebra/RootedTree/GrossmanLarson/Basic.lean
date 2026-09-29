/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Core.Algebra.RootedTree.PreLie.ChapotonLivernet
public import Linglib.Core.Algebra.RootedTree.PreLie.InsertSum
public import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
public import Linglib.Core.Algebra.RootedTree.PreLie.InsertionUnordered
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.OrderedMonoid
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The Grossman–Larson product

This file defines the Grossman–Larson product on the free module of forests of nonplanar rooted
trees. The product `F ⋆ G` sums, over the sub-multisets `G₁` of `G`, the forests obtained by
grafting the trees of `G₁` onto vertices of `F` in all ways, with the remaining trees `G - G₁`
placed alongside. Grossman and Larson introduce the product; the closed form used here is
Foissy's, through the Guin–Oudom extension of the grafting pre-Lie product. The product is
associative (`GrossmanLarson/Monoid.lean`) and dual to the pruning coproduct under the
symmetry-weighted pairing (`GrossmanLarson/Pairing.lean`).

## Main definitions

* `GrossmanLarson R α`: forests of `UnorderedTree α` with coefficients in `R`, a synonym of
  `ConnesKreimer R (UnorderedTree α)` whose multiplication is the Grossman–Larson product.
* `GrossmanLarson.insertTree`: grafting one tree onto one vertex of a forest, in all ways.
* `GrossmanLarson.insertion`: the bilinear insertion `F • G`, grafting every tree of `G` at once.
* `GrossmanLarson.product`: `F ⋆ G = Σ_{G₁ ≤ G} (F • G₁) · (G - G₁)`, the `Mul` instance.

## Main results

* `GrossmanLarson.mul_one`, `GrossmanLarson.one_mul`: the empty forest is a two-sided unit.
* `GrossmanLarson.map_product`: the product commutes with change of coefficients.
* `GrossmanLarson.toGrossmanLarson_mul`: on one-tree forests the insertion is the grafting
  product of `ChapotonLivernet`.

## Implementation notes

The insertion `F • G` grafts every tree of `G` onto the original `F`. It is not iterated
one-tree insertion, which would also graft later trees onto earlier ones. As for `MulOpposite`,
`op` and `unop` pass between the synonym and `ConnesKreimer R (UnorderedTree α)`, so that the
disjoint-union product stays available inside definitions.

The insertion Lie algebra of Marcolli, Chomsky and Berwick comes from a different pre-Lie
product, which inserts a binary tree by subdividing an edge rather than by grafting at a vertex.

## References

* [grossman-larson-1989]
* [foissy-2021]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

open RoseTree UnorderedTree

/-! ### The carrier -/

/-- `GrossmanLarson R α` is the free `R`-module on forests of `UnorderedTree α`, which the `Mul`
instance below equips with the Grossman–Larson product. -/
def GrossmanLarson (R : Type*) [CommSemiring R] (α : Type*) : Type _ :=
  ConnesKreimer R (UnorderedTree α)

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### Module structure

The additive structure is that of `ConnesKreimer R (UnorderedTree α)`. Its disjoint-union
product is not forwarded, since the synonym carries the Grossman–Larson product. -/

noncomputable instance instAddCommMonoid : AddCommMonoid (GrossmanLarson R α) :=
  inferInstanceAs (AddCommMonoid (ConnesKreimer R (UnorderedTree α)))

noncomputable instance instModule : Module R (GrossmanLarson R α) :=
  inferInstanceAs (Module R (ConnesKreimer R (UnorderedTree α)))

noncomputable instance instOne : One (GrossmanLarson R α) :=
  inferInstanceAs (One (ConnesKreimer R (UnorderedTree α)))

instance instFunLike : FunLike (GrossmanLarson R α) (Forest (UnorderedTree α)) R :=
  inferInstanceAs (FunLike (ConnesKreimer R (UnorderedTree α)) (Forest (UnorderedTree α)) R)

/-! ### Passing to the underlying module

`op` and `unop` are the identity maps between the synonym and `ConnesKreimer R (UnorderedTree α)`,
as for `MulOpposite`. They make the disjoint-union product available inside definitions without
putting it on `GrossmanLarson R α`. -/

/-- `op x` is `x` read in the synonym. -/
def op (x : ConnesKreimer R (UnorderedTree α)) : GrossmanLarson R α := x

/-- `unop x` is `x` read in `ConnesKreimer R (UnorderedTree α)`. -/
def unop (x : GrossmanLarson R α) : ConnesKreimer R (UnorderedTree α) := x

omit [DecidableEq α] in
@[simp] theorem op_unop (x : GrossmanLarson R α) :
    op (unop (R := R) x) = x := rfl

omit [DecidableEq α] in
@[simp] theorem unop_op (x : ConnesKreimer R (UnorderedTree α)) :
    unop (op (R := R) (α := α) x) = x := rfl

/-! ### Basis vectors -/

/-- `of' F` is the basis vector of the forest `F`. -/
noncomputable def of' (F : Forest (UnorderedTree α)) : GrossmanLarson R α :=
  ConnesKreimer.of' (R := R) F

/-- `ofTree t` is the basis vector of the one-tree forest `{t}`. -/
noncomputable def ofTree (t : UnorderedTree α) : GrossmanLarson R α :=
  ConnesKreimer.ofTree (R := R) t

omit [DecidableEq α] in
@[simp] theorem of'_zero :
    (of' (R := R) (0 : Forest (UnorderedTree α)) : GrossmanLarson R α) = 1 :=
  ConnesKreimer.of'_zero

/-! ### Linear extension from the basis -/

/-- `basisLift f` is the `R`-linear map that agrees with `f` on basis forests. -/
noncomputable def basisLift {M : Type*} [AddCommMonoid M] [Module R M]
    (f : Forest (UnorderedTree α) → M) : GrossmanLarson R α →ₗ[R] M :=
  (Finsupp.linearCombination R f).comp
    ((AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
      (ConnesKreimer.toFinsuppAlgEquiv (R := R) (T := UnorderedTree α)).toLinearMap)

omit [DecidableEq α] in
private theorem basisLift_single {M : Type*} [AddCommMonoid M] [Module R M]
    (f : Forest (UnorderedTree α) → M) (F : Forest (UnorderedTree α)) (r : R) :
    basisLift f (ConnesKreimer.single F r) = r • f F := by
  show Finsupp.linearCombination R f
    ((AddMonoidAlgebra.coeffLinearEquiv R) (ConnesKreimer.single F r).toFinsupp) = r • f F
  rw [ConnesKreimer.toFinsupp_single]
  simp [Finsupp.linearCombination_single]

omit [DecidableEq α] in
private theorem basisLift_of' {M : Type*} [AddCommMonoid M] [Module R M]
    (f : Forest (UnorderedTree α) → M) (F : Forest (UnorderedTree α)) :
    basisLift f (of' (R := R) F) = f F :=
  (basisLift_single f F 1).trans (one_smul _ _)

omit [DecidableEq α] in
private theorem basisLift_one {M : Type*} [AddCommMonoid M] [Module R M]
    (f : Forest (UnorderedTree α) → M) :
    basisLift f (1 : GrossmanLarson R α) = f 0 := by
  rw [← of'_zero (R := R) (α := α)]; exact basisLift_of' f 0

omit [DecidableEq α] in
/-- Extending `of'` linearly gives the identity. -/
private theorem basisLift_of'_apply (x : GrossmanLarson R α) :
    basisLift (of' (R := R) (α := α)) x = x := by
  have key : (basisLift (of' (R := R) (α := α))).toAddMonoidHom
      = (LinearMap.id : GrossmanLarson R α →ₗ[R] GrossmanLarson R α).toAddMonoidHom := by
    apply ConnesKreimer.addHom_ext
    intro F r
    show basisLift (of' (R := R) (α := α)) (ConnesKreimer.single F r)
        = ConnesKreimer.single F r
    rw [basisLift_single]
    exact (ConnesKreimer.smul_single_one F r).symm
  simpa using DFunLike.congr_fun key x

/-! ### One-tree insertion

`insertTreeForest T F` grafts `T` onto one vertex of one tree `S` of `F`: for each occurrence of
`S` in `F` it sums, over the summands `S'` of `S ◁ T`, the forest with `S` replaced by `S'`. -/

/-- `insertTreeForest T F` grafts `T` onto one vertex of one tree of `F`, in all ways. -/
noncomputable def insertTreeForest (T : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    GrossmanLarson R α :=
  (F.bind fun S =>
    (UnorderedTree.insertSum S T).map fun S' => of' (R := R) (S' ::ₘ F.erase S)).sum

@[simp] theorem insertTreeForest_zero (T : UnorderedTree α) :
    insertTreeForest (R := R) T (0 : Forest (UnorderedTree α)) = 0 := by
  simp only [insertTreeForest, Multiset.zero_bind, Multiset.sum_zero]

/-- `insertTree T` is the linear extension of `insertTreeForest T`. -/
noncomputable def insertTree (T : UnorderedTree α) :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  basisLift (insertTreeForest T)

@[simp] theorem insertTree_of' (T : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    insertTree (R := R) T (of' F) = insertTreeForest T F :=
  basisLift_of' (insertTreeForest T) F

/-- One-tree insertion into `S ::ₘ F` grafts into `S` or into `F`, read in the underlying
module. -/
private theorem unop_insertTreeForest_cons
    (T S : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    unop (insertTreeForest (R := R) T (S ::ₘ F)) =
      ((UnorderedTree.insertSum S T).map
        (fun S' => unop (of' (R := R) (S' ::ₘ F)))).sum +
      unop (of' (R := R) ({S} : Forest (UnorderedTree α))) *
        unop (insertTreeForest (R := R) T F) := by
  -- `unop` is the identity; unfolding both `unop` and `insertTreeForest`
  -- + `of'` (which is `ConnesKreimer.of'` definitionally) reduces the
  -- statement to a pure CK equality.
  show ((((S : UnorderedTree α) ::ₘ F).bind fun S₀ =>
          (UnorderedTree.insertSum S₀ T).map fun S' =>
            ConnesKreimer.of' (R := R) (S' ::ₘ ((S : UnorderedTree α) ::ₘ F).erase S₀)).sum)
      = ((UnorderedTree.insertSum S T).map fun S' =>
          ConnesKreimer.of' (R := R) (S' ::ₘ F)).sum +
        ConnesKreimer.of' (R := R) ({S} : Forest (UnorderedTree α)) *
          ((F.bind fun S₀ =>
            (UnorderedTree.insertSum S₀ T).map fun S' =>
              ConnesKreimer.of' (R := R) (S' ::ₘ F.erase S₀)).sum)
  rw [Multiset.cons_bind, Multiset.sum_add]
  congr 1
  · -- Front: erase_cons_head simplifies (S ::ₘ F).erase S to F
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intros
    rw [Multiset.erase_cons_head]
  · -- Tail: factor `of' {S}` from each summand
    have h_erase : ∀ S₀ ∈ F,
        ((S : UnorderedTree α) ::ₘ F).erase S₀ = S ::ₘ F.erase S₀ := fun S₀ hS₀ => by
      by_cases h : S₀ = S
      · subst h; rw [Multiset.erase_cons_head, Multiset.cons_erase hS₀]
      · exact Multiset.erase_cons_tail _ (Ne.symm h)
    have h_factor : ∀ S₀ ∈ F,
        ((UnorderedTree.insertSum S₀ T).map fun S' =>
            ConnesKreimer.of' (R := R) (S' ::ₘ ((S : UnorderedTree α) ::ₘ F).erase S₀))
        = ((UnorderedTree.insertSum S₀ T).map fun S' =>
            ConnesKreimer.of' (R := R) ({S} : Forest (UnorderedTree α)) *
              ConnesKreimer.of' (R := R) (S' ::ₘ F.erase S₀)) := fun S₀ hS₀ => by
      apply Multiset.map_congr rfl
      intro S' _
      rw [h_erase S₀ hS₀, Multiset.cons_swap, ← Multiset.singleton_add,
          ConnesKreimer.of'_add]
    rw [Multiset.bind_congr h_factor]
    -- Pull out `of' {S}`: sum_bind, sum_map_mul_left (pointwise), again, reverse.
    rw [Multiset.sum_bind,
        Multiset.map_congr (rfl : F = F) (fun _ _ => Multiset.sum_map_mul_left),
        Multiset.sum_map_mul_left, ← Multiset.sum_bind]

/-- One-tree insertion into `S ::ₘ F` grafts into `S` or into `F`. -/
theorem insertTreeForest_cons (T S : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    insertTreeForest (R := R) T (S ::ₘ F) =
      ((UnorderedTree.insertSum S T).map
        (fun S' => of' (R := R) (S' ::ₘ F))).sum +
      op (unop (of' (R := R) ({S} : Forest (UnorderedTree α))) *
          unop (insertTreeForest T F)) :=
  unop_insertTreeForest_cons T S F

/-! ### Multi-tree insertion

The bilinear insertion `F • G` grafts every tree of `G` onto a vertex of the original `F`; on
basis forests it is `UnorderedTree.insertionMultiset`. It is not iterated one-tree insertion,
which would also graft later trees onto the vertices of earlier ones. -/

/-- `insertionBasis F G` sums the basis vectors of the forests in `insertionMultiset F G`. -/
noncomputable def insertionBasis (F_basis G_basis : Forest (UnorderedTree α)) :
    GrossmanLarson R α :=
  ((UnorderedTree.insertionMultiset F_basis G_basis).map
    fun F' => of' (R := R) F').sum

/-- `insertionBasisLin G` is the linear extension of `insertionBasis · G`. -/
noncomputable def insertionBasisLin (G_basis : Forest (UnorderedTree α)) :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  basisLift (fun F_basis => insertionBasis (R := R) F_basis G_basis)

omit [DecidableEq α] in
private theorem insertionBasisLin_of' (G_basis F_basis : Forest (UnorderedTree α)) :
    insertionBasisLin (R := R) G_basis (of' F_basis) = insertionBasis F_basis G_basis :=
  basisLift_of' _ F_basis

/-- `insertion F G` is the bilinear extension of `insertionBasis`. -/
noncomputable def insertion :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  (basisLift (insertionBasisLin (R := R) (α := α))).flip

omit [DecidableEq α] in
/-- On basis vectors, `insertion` is `insertionBasis`. -/
theorem insertion_of'_of' (F G : Forest (UnorderedTree α)) :
    insertion (R := R) (of' F) (of' G) = insertionBasis F G := by
  show (basisLift (insertionBasisLin (R := R) (α := α))).flip (of' F) (of' G) = _
  rw [LinearMap.flip_apply, basisLift_of', insertionBasisLin_of']

/-! ### The Grossman–Larson product

`F ⋆ G` sums, over the sub-multisets `G₁` of `G`, the insertion of `G₁` into `F` multiplied by
the disjoint union with `G - G₁`, the closed form of Foissy's Theorem 5.1. -/

/-- `productForest F G` is the Grossman–Larson product of `F` with the basis forest `G`. -/
noncomputable def productForest (F : GrossmanLarson R α)
    (G : Forest (UnorderedTree α)) : GrossmanLarson R α :=
  (G.powerset.map fun G₁ =>
    op (unop (insertion F (of' (R := R) G₁)) * unop (of' (R := R) (G - G₁)))).sum

private theorem productForest_zero_left (G : Forest (UnorderedTree α)) :
    productForest (0 : GrossmanLarson R α) G = 0 := by
  unfold productForest
  rw [show (G.powerset.map fun G₁ =>
        op (unop (insertion (R := R) (α := α) 0 (of' (R := R) G₁)) *
            unop (of' (R := R) (G - G₁)))) =
      G.powerset.map (fun _ => (0 : GrossmanLarson R α)) from ?_]
  · rw [Multiset.map_const', Multiset.sum_replicate, smul_zero]
  · apply Multiset.map_congr rfl
    intro G₁ _
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_zero, LinearMap.zero_apply]
    show op ((0 : ConnesKreimer R (UnorderedTree α)) *
        unop (of' (R := R) (G - G₁))) = 0
    rw [zero_mul]
    rfl

/-- The product with a basis forest is additive in the first factor. -/
theorem productForest_add_left
    (F₁ F₂ : GrossmanLarson R α) (G : Forest (UnorderedTree α)) :
    productForest (F₁ + F₂) G = productForest F₁ G + productForest F₂ G := by
  show ((G.powerset.map fun G₁ =>
      op (unop (insertion (F₁ + F₂) (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum : GrossmanLarson R α) =
    (G.powerset.map fun G₁ =>
      op (unop (insertion F₁ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum +
    (G.powerset.map fun G₁ =>
      op (unop (insertion F₂ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum
  rw [← Multiset.sum_map_add]
  congr 1
  apply Multiset.map_congr rfl
  intro G₁ _
  rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_add, LinearMap.add_apply]
  show op ((unop (insertion F₁ (of' (R := R) G₁)) +
            unop (insertion F₂ (of' (R := R) G₁))) *
           unop (of' (R := R) (G - G₁))) =
      op (unop (insertion F₁ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁))) +
      op (unop (insertion F₂ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))
  rw [add_mul]
  rfl

/-- The product with a basis forest is `R`-linear in the first factor. -/
theorem productForest_smul_left
    (c : R) (F : GrossmanLarson R α) (G : Forest (UnorderedTree α)) :
    productForest (c • F) G = c • productForest F G := by
  show ((G.powerset.map fun G₁ =>
      op (unop (insertion (c • F) (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum : GrossmanLarson R α) =
    c • (G.powerset.map fun G₁ =>
      op (unop (insertion F (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum
  rw [Multiset.smul_sum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro G₁ _
  rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_smul, LinearMap.smul_apply]
  show op ((c • unop (insertion F (of' (R := R) G₁))) *
           unop (of' (R := R) (G - G₁))) =
      (fun x => c • x) (op (unop (insertion F (of' (R := R) G₁)) *
                            unop (of' (R := R) (G - G₁))))
  show op ((c • unop (insertion F (of' (R := R) G₁))) *
           unop (of' (R := R) (G - G₁))) =
      c • op (unop (insertion F (of' (R := R) G₁)) *
              unop (of' (R := R) (G - G₁)))
  rw [smul_mul_assoc]
  rfl

/-- `productForestLin G` is `productForest · G` as a linear map. -/
noncomputable def productForestLin (G : Forest (UnorderedTree α)) :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α where
  toFun F := productForest F G
  map_add' F₁ F₂ := productForest_add_left F₁ F₂ G
  map_smul' c F := productForest_smul_left c F G

/-- The Grossman–Larson product, bilinear in both factors. -/
noncomputable def product :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  (basisLift (productForestLin (R := R) (α := α))).flip

/-! ### Multiplicative structure

The `Semigroup` and `Monoid` instances are in `GrossmanLarson/Monoid.lean`. -/

noncomputable instance instMul : Mul (GrossmanLarson R α) where
  mul x y := product x y

theorem mul_def (x y : GrossmanLarson R α) : x * y = product x y := rfl

instance instLeftDistribClass : LeftDistribClass (GrossmanLarson R α) where
  left_distrib a b c := by
    show product a (b + c) = product a b + product a c
    exact map_add (product a) b c

instance instRightDistribClass : RightDistribClass (GrossmanLarson R α) where
  right_distrib a b c := by
    show product (a + b) c = product a c + product b c
    rw [show product (a + b) = product a + product b from
        map_add product a b]
    rfl

/-- These are theorems rather than a `MulZeroClass` instance, whose `Mul` and `Zero` parents
would not agree with the instances already on the synonym. -/
theorem zero_mul_gl (x : GrossmanLarson R α) : (0 : GrossmanLarson R α) * x = 0 := by
  show product 0 x = 0
  rw [map_zero]
  rfl

theorem mul_zero_gl (x : GrossmanLarson R α) : x * (0 : GrossmanLarson R α) = 0 := by
  show product x 0 = 0
  exact map_zero _

theorem smul_mul_gl (r : R) (a b : GrossmanLarson R α) :
    (r • a) * b = r • (a * b) := by
  show product (r • a) b = r • product a b
  rw [LinearMap.map_smul]
  rfl

theorem mul_smul_gl (s : R) (a b : GrossmanLarson R α) :
    a * (s • b) = s • (a * b) :=
  LinearMap.map_smul (product a) s b

/-- The product with a basis forest is `productForest`. -/
theorem product_of' (x : GrossmanLarson R α) (G : Forest (UnorderedTree α)) :
    product x (of' (R := R) G) = productForest x G := by
  show (basisLift (productForestLin (R := R) (α := α))).flip x (of' G)
      = productForest x G
  rw [LinearMap.flip_apply, basisLift_of']
  rfl

/-- The product of two basis forests is `productForest`. -/
theorem of'_mul_of' (F G : Forest (UnorderedTree α)) :
    (of' F : GrossmanLarson R α) * of' G = productForest (of' F) G :=
  product_of' (of' F) G

/-! ### The unit -/

omit [DecidableEq α] in
/-- Inserting no guests leaves the host unchanged. -/
private theorem insertionBasis_zero_right (F_basis : Forest (UnorderedTree α)) :
    insertionBasis (R := R) F_basis (0 : Forest (UnorderedTree α)) = of' F_basis := by
  unfold insertionBasis
  rw [UnorderedTree.insertionMultiset_zero_right, Multiset.map_singleton,
      Multiset.sum_singleton]

omit [DecidableEq α] in
private theorem insertionBasis_zero_zero :
    insertionBasis (R := R) (0 : Forest (UnorderedTree α)) 0 = 1 := by
  rw [insertionBasis_zero_right, of'_zero]

omit [DecidableEq α] in
private theorem insertionBasis_zero_left_of_ne_zero
    (G_basis : Forest (UnorderedTree α)) (h : G_basis ≠ 0) :
    insertionBasis (R := R) (0 : Forest (UnorderedTree α)) G_basis = 0 := by
  unfold insertionBasis
  rw [UnorderedTree.insertionMultiset_zero_left_of_ne_zero G_basis h,
      Multiset.map_zero, Multiset.sum_zero]

omit [DecidableEq α] in
theorem insertion_one_right (F : GrossmanLarson R α) :
    insertion F (1 : GrossmanLarson R α) = F := by
  show (basisLift (insertionBasisLin (R := R) (α := α))).flip F 1 = F
  rw [LinearMap.flip_apply, basisLift_one]
  -- Goal: `insertionBasisLin 0 F = F`; the basis map is `of'`, extended to `id`.
  show basisLift (fun F_basis : Forest (UnorderedTree α) =>
      insertionBasis (R := R) F_basis (0 : Forest (UnorderedTree α))) F = F
  rw [show (fun F_basis : Forest (UnorderedTree α) =>
        insertionBasis (R := R) F_basis (0 : Forest (UnorderedTree α)))
      = of' (R := R) (α := α) from funext insertionBasis_zero_right]
  exact basisLift_of'_apply F

theorem mul_one (F : GrossmanLarson R α) : F * 1 = F := by
  show product F 1 = F
  show (basisLift (productForestLin (R := R) (α := α))).flip F 1 = F
  rw [LinearMap.flip_apply, basisLift_one]
  show productForest F 0 = F
  show ((((0 : Forest (UnorderedTree α)).powerset).map fun G₁ =>
        op (unop (insertion F (of' (R := R) G₁)) *
            unop (of' (R := R) ((0 : Forest (UnorderedTree α)) - G₁)))).sum
      : GrossmanLarson R α) = F
  rw [Multiset.powerset_zero, Multiset.map_singleton, Multiset.sum_singleton,
      tsub_self, of'_zero]
  show op (unop (insertion F (of' (R := R) (0 : Forest (UnorderedTree α)))) *
           unop (1 : GrossmanLarson R α)) = F
  rw [show unop (1 : GrossmanLarson R α) = (1 : ConnesKreimer R (UnorderedTree α))
      from rfl, _root_.mul_one]
  show op (unop (insertion F (of' (R := R) (0 : Forest (UnorderedTree α))))) = F
  show insertion F (of' (R := R) (0 : Forest (UnorderedTree α))) = F
  rw [show (of' (R := R) (0 : Forest (UnorderedTree α)) : GrossmanLarson R α) =
        (1 : GrossmanLarson R α) from of'_zero]
  exact insertion_one_right F

omit [DecidableEq α] in
private theorem insertion_one_of'_zero :
    insertion (1 : GrossmanLarson R α)
        (of' (R := R) (0 : Forest (UnorderedTree α))) =
      (1 : GrossmanLarson R α) := by
  conv_lhs => rw [← of'_zero (R := R) (α := α)]
  rw [insertion_of'_of', insertionBasis_zero_zero]

omit [DecidableEq α] in
/-- The empty forest has no vertices, so it takes no guests. -/
theorem insertion_one_of'_ne_zero (G₁ : Forest (UnorderedTree α))
    (h : G₁ ≠ 0) :
    insertion (1 : GrossmanLarson R α) (of' (R := R) G₁) =
      (0 : GrossmanLarson R α) := by
  conv_lhs => rw [← of'_zero (R := R) (α := α)]
  rw [insertion_of'_of', insertionBasis_zero_left_of_ne_zero G₁ h]

/-- The empty multiset occurs once among the sub-multisets of `s`. -/
private theorem count_zero_powerset (s : Multiset (UnorderedTree α)) :
    Multiset.count (0 : Forest (UnorderedTree α)) s.powerset = 1 := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.powerset_zero, Multiset.count_singleton_self]
  | cons a s ih =>
    rw [Multiset.powerset_cons, Multiset.count_add, ih]
    have hmap : Multiset.count (0 : Forest (UnorderedTree α))
                  (s.powerset.map (a ::ₘ ·)) = 0 := by
      rw [Multiset.count_eq_zero, Multiset.mem_map]
      rintro ⟨x, _, hx⟩
      exact Multiset.cons_ne_zero hx
    rw [hmap]

private theorem productForest_one_left (G_basis : Forest (UnorderedTree α)) :
    productForest (1 : GrossmanLarson R α) G_basis = of' G_basis := by
  unfold productForest
  -- Split powerset as `0 ::ₘ powerset.erase 0`
  have h0_mem : (0 : Forest (UnorderedTree α)) ∈ G_basis.powerset :=
    Multiset.zero_mem_powerset _
  rw [← Multiset.cons_erase h0_mem, Multiset.map_cons, Multiset.sum_cons]
  -- Simplify the `G₁ = 0` summand to `of' G_basis`
  have hf0 :
      op (unop (insertion (1 : GrossmanLarson R α)
                (of' (R := R) (0 : Forest (UnorderedTree α)))) *
          unop (of' (R := R) (G_basis - 0)))
        = of' (R := R) G_basis := by
    rw [insertion_one_of'_zero, tsub_zero]
    show op ((1 : ConnesKreimer R (UnorderedTree α)) *
              unop (of' (R := R) G_basis)) = _
    rw [_root_.one_mul]; rfl
  -- The `erase 0` part has every G₁ ≠ 0, so each summand vanishes
  have h_no_zero : (0 : Forest (UnorderedTree α)) ∉ G_basis.powerset.erase 0 := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self,
        count_zero_powerset G_basis]
  have hrest :
      ((G_basis.powerset.erase 0).map fun G₁ =>
          op (unop (insertion (1 : GrossmanLarson R α) (of' (R := R) G₁)) *
              unop (of' (R := R) (G_basis - G₁)))).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨G₁, hG₁_mem, hG₁_eq⟩ := hx
    have hG₁_ne : G₁ ≠ 0 := fun h => h_no_zero (h ▸ hG₁_mem)
    rw [← hG₁_eq, insertion_one_of'_ne_zero G₁ hG₁_ne]
    show op ((0 : ConnesKreimer R (UnorderedTree α)) *
              unop (of' (R := R) (G_basis - G₁))) = 0
    rw [zero_mul]; rfl
  rw [hf0, hrest, add_zero]

theorem one_mul (F : GrossmanLarson R α) : (1 : GrossmanLarson R α) * F = F := by
  suffices h : (product (R := R) (α := α)) 1 = LinearMap.id by
    show product 1 F = F
    rw [h, LinearMap.id_apply]
  apply LinearMap.toAddMonoidHom_injective
  apply ConnesKreimer.addHom_ext
  intro G r
  show product (R := R) 1 (ConnesKreimer.single G r) = ConnesKreimer.single G r
  show (basisLift (productForestLin (R := R) (α := α))).flip 1 (ConnesKreimer.single G r) = _
  rw [LinearMap.flip_apply, basisLift_single, LinearMap.smul_apply]
  show r • productForest (1 : GrossmanLarson R α) G = ConnesKreimer.single G r
  rw [productForest_one_left]
  exact (ConnesKreimer.smul_single_one G r).symm

/-! ### Closed powerset-sum forms -/

/-- The product with a basis forest, with `productForest` unfolded. -/
theorem mul_of'_sum_form (X : GrossmanLarson R α) (G : Forest (UnorderedTree α)) :
    X * of' G =
      (G.powerset.map fun G₁ =>
        op (unop (insertion X (of' G₁)) *
            unop (of' (G - G₁)))).sum :=
  product_of' X G

omit [DecidableEq α] in
/-- `insertion` distributes over a `Multiset.sum` in its first argument. -/
theorem insertion_sum_left (s : Multiset (GrossmanLarson R α))
    (G : GrossmanLarson R α) :
    insertion (R := R) s.sum G = (s.map (fun X => insertion X G)).sum :=
  map_multiset_sum ((insertion (R := R) (α := α)).flip G) s

/-- The product of two basis forests, as a sum over sub-multisets of guests of the insertion
multiset. -/
theorem of'_mul_of'_nim_form (F₁ F₂ : Forest (UnorderedTree α)) :
    (of' F₁ : GrossmanLarson R α) * of' F₂ =
      (F₂.powerset.bind fun B₁ =>
        (UnorderedTree.insertionMultiset F₁ B₁).map
          fun X => (of' (R := R) (X + (F₂ - B₁)) : GrossmanLarson R α)).sum := by
  rw [mul_of'_sum_form, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro B₁ _
  rw [insertion_of'_of']
  unfold insertionBasis
  show ((((UnorderedTree.insertionMultiset F₁ B₁).map
            (fun F' => (ConnesKreimer.of' (R := R) F' :
              ConnesKreimer R (UnorderedTree α)))).sum *
          (ConnesKreimer.of' (R := R) (F₂ - B₁) :
            ConnesKreimer R (UnorderedTree α))) :
            ConnesKreimer R (UnorderedTree α)) =
      ((UnorderedTree.insertionMultiset F₁ B₁).map
        (fun X => (ConnesKreimer.of' (R := R) (X + (F₂ - B₁)) :
          ConnesKreimer R (UnorderedTree α)))).sum
  rw [← Multiset.sum_map_mul_right]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro X _
  show (ConnesKreimer.of' (R := R) X : ConnesKreimer R (UnorderedTree α)) *
        ConnesKreimer.of' (R := R) (F₂ - B₁) =
      ConnesKreimer.of' (R := R) (X + (F₂ - B₁))
  rw [ConnesKreimer.of'_add]

/-! ### Change of coefficients

The product commutes with `ConnesKreimer.map`, since its structure constants are natural
numbers. -/

section Map
variable {S : Type*} [CommSemiring S] (f : R →+* S)

omit [DecidableEq α] in
@[simp] theorem map_of' (F : Forest (UnorderedTree α)) :
    ConnesKreimer.map f (of' (R := R) F : GrossmanLarson R α) = of' F :=
  ConnesKreimer.map_of' f F

omit [DecidableEq α] in
theorem map_insertionBasis (F G : Forest (UnorderedTree α)) :
    ConnesKreimer.map f (insertionBasis (R := R) F G) = insertionBasis F G := by
  unfold insertionBasis
  rw [ConnesKreimer.map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun F' _ => map_of' f F')

omit [DecidableEq α] in
theorem map_insertion (x : GrossmanLarson R α) (G : Forest (UnorderedTree α)) :
    ConnesKreimer.map f (insertion x (of' (R := R) G)) =
      insertion (ConnesKreimer.map f x) (of' G) := by
  induction x using ConnesKreimer.induction_linear with
  | zero =>
    rw [LinearMap.map_zero₂, ConnesKreimer.map_zero, LinearMap.map_zero₂]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [LinearMap.map_add₂, ConnesKreimer.map_add, ih₁, ih₂,
        ConnesKreimer.map_add, LinearMap.map_add₂]
  | single F r =>
    rw [ConnesKreimer.smul_single_one, LinearMap.map_smul₂,
        ConnesKreimer.map_smul, ConnesKreimer.map_smul,
        ConnesKreimer.map_single, map_one, LinearMap.map_smul₂]
    exact congrArg (f r • ·)
      (show ConnesKreimer.map f (insertion (of' (R := R) F) (of' G))
          = insertion (of' (R := S) F) (of' G) from by
        rw [insertion_of'_of', insertion_of'_of', map_insertionBasis])

theorem map_productForest (x : GrossmanLarson R α) (G : Forest (UnorderedTree α)) :
    ConnesKreimer.map f (productForest x G) =
      productForest (ConnesKreimer.map f x) G := by
  unfold productForest
  rw [ConnesKreimer.map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun G₁ _ => ?_)
  show ConnesKreimer.map f
      (unop (insertion x (of' G₁)) * unop (of' (R := R) (G - G₁))) = _
  rw [ConnesKreimer.map_mul]
  exact congrArg₂ (· * ·) (map_insertion f x G₁) (map_of' f (G - G₁))

/-- `ConnesKreimer.map` respects the Grossman–Larson product. -/
theorem map_product (x y : GrossmanLarson R α) :
    ConnesKreimer.map f (product x y) =
      product (ConnesKreimer.map f x) (ConnesKreimer.map f y) := by
  induction y using ConnesKreimer.induction_linear with
  | zero =>
    rw [map_zero, ConnesKreimer.map_zero, map_zero]
  | add y₁ y₂ ih₁ ih₂ =>
    rw [map_add, ConnesKreimer.map_add, ih₁, ih₂, ConnesKreimer.map_add, map_add]
  | single G r =>
    rw [ConnesKreimer.smul_single_one, map_smul, ConnesKreimer.map_smul,
        ConnesKreimer.map_smul, ConnesKreimer.map_single, map_one, map_smul]
    exact congrArg (f r • ·)
      (show ConnesKreimer.map f (product x (of' (R := R) G))
          = product (ConnesKreimer.map f x) (of' G) from by
        rw [product_of', product_of', map_productForest])

end Map

/-! ### Trees as one-tree forests

Sending a tree to the one-tree forest maps the pre-Lie algebra of trees into the Grossman–Larson
algebra, and turns the grafting product into the insertion. -/

/-- `toGrossmanLarson` sends each tree to its one-tree forest. -/
noncomputable def toGrossmanLarson : ChapotonLivernet R α →ₗ[R] GrossmanLarson R α :=
  (Finsupp.linearCombination R ofTree).comp ChapotonLivernet.coeffLinearEquiv.toLinearMap

omit [DecidableEq α] in
@[simp] theorem toGrossmanLarson_single (T : UnorderedTree α) (r : R) :
    toGrossmanLarson (ChapotonLivernet.single T r) = r • ofTree (R := R) T :=
  Finsupp.linearCombination_single R r T

omit [DecidableEq α] in
theorem insertion_ofTree_ofTree (T S : UnorderedTree α) :
    insertion (ofTree (R := R) T) (ofTree S) = ((T ◁ S).map ofTree).sum := by
  change insertion (of' {T}) (of' {S}) = _
  rw [insertion_of'_of', insertionBasis, insertionMultiset_singleton_singleton, Multiset.map_map]
  rfl

omit [DecidableEq α] in
/-- The grafting product of trees is the insertion of their one-tree forests. -/
theorem toGrossmanLarson_mul (x y : ChapotonLivernet R α) :
    toGrossmanLarson (x * y) = insertion (toGrossmanLarson x) (toGrossmanLarson y) := by
  induction x using ChapotonLivernet.induction_linear with
  | zero => rw [zero_mul, map_zero, map_zero, LinearMap.zero_apply]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, map_add, LinearMap.add_apply]
  | single T a =>
    induction y using ChapotonLivernet.induction_linear with
    | zero => rw [mul_zero, map_zero, map_zero]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, map_add]
    | single S b =>
      rw [ChapotonLivernet.single_mul_single, map_smul, toGrossmanLarson_single,
        toGrossmanLarson_single, map_smul, map_smul, LinearMap.smul_apply,
        insertion_ofTree_ofTree, ChapotonLivernet.graft, map_multiset_sum, Multiset.map_map,
        smul_smul, mul_comm b a]
      simp

end GrossmanLarson

