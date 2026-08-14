import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
import Linglib.Core.Combinatorics.RootedTree.Cut
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# The pruning coproduct Δ^ρ

The admissible-cut, root-component pruning coproduct on unordered rooted
trees ([marcolli-chomsky-berwick-2025] Definition 1.2.6 and Lemma
1.2.11 — per their Remark 1.2.9, the Connes-Kreimer Hopf-algebra
coproduct of [foissy-introduction-hopf-algebras-trees]), with the
Hochschild 1-cocycle property of grafting and the counit laws. Δ^ρ
deletes cut subtrees outright, unlike the trace variant Δ^c
(`Coproduct/TraceNonplanar.lean`), which leaves marker leaves.

## Main definitions

* `ConnesKreimer.comulTreeN`, `ConnesKreimer.comulForestN`,
  `ConnesKreimer.comulAlgHomN` — the Δ^ρ coproduct, as the generic
  admissible-cut coproduct (`Coproduct/WithCuts.lean`) at the
  enumeration `cutSummandsN`.
* `ConnesKreimer.bPlusLin` — grafting `B+_a` as a linear map.

## Main results

* `ConnesKreimer.comulAlgHomN_bPlusLin_cocycle` — the Hochschild
  1-cocycle law `Δ^ρ ∘ B+_a = B+_a ⊗ 1 + (id ⊗ B+_a) ∘ Δ^ρ`.
* `ConnesKreimer.counit_rTensor_comulAlgHomN`,
  `ConnesKreimer.counit_lTensor_comulAlgHomN` — the counit laws.

## Implementation notes

`B+` only well-defines on unordered children
(`Multiset (Nonplanar α) → Nonplanar α`); on planar trees it would need
a canonical ordering — hence the cocycle and everything downstream live
at the `Nonplanar` level. The clean-coassoc route through the cocycle
does not generalize to Δ^c (B+ is not a 1-cocycle for the trace
variant, which instead uses the direct double-cut bijection).

Coassociativity and the `Bialgebra` instance live downstream in
`Coproduct/PruningDuality.lean` (the GL/CK duality proof needs the B⁻
calculus of `BMinus.lean`, which imports this file); the full
`HopfAlgebra` instance is in `HopfAlgebraNonplanar.lean`.

## Status

`[UPSTREAM]` candidate.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## Nonplanar tree- and forest-level Δ^ρ

Definitional instantiations of the generic admissible-cut coproduct
(`Coproduct/WithCuts.lean`) at the Δ^ρ enumeration `cutSummandsN`. -/

/-- The **nonplanar tree-level Δ^ρ**: `comulTreeNG` at
    `cuts := cutSummandsN`. -/
noncomputable def comulTreeN :
    Nonplanar α →
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  comulTreeNG cutSummandsN

/-- The nonplanar forest-level Δ^ρ (multiplicative extension). -/
noncomputable def comulForestN :
    Forest (Nonplanar α) →
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  comulForestNG cutSummandsN

@[simp] theorem comulForestN_zero :
    comulForestN (R := R) (0 : Forest (Nonplanar α)) = 1 :=
  comulForestNG_zero _

@[simp] theorem comulForestN_add (F G : Forest (Nonplanar α)) :
    comulForestN (R := R) (F + G) =
      comulForestN (R := R) F * comulForestN (R := R) G :=
  comulForestNG_add _ F G

/-- Recursive formula: `comulForestN (T ::ₘ F) = comulTreeN T * comulForestN F`. -/
@[simp] theorem comulForestN_cons (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    comulForestN (R := R) (T ::ₘ F) =
      comulTreeN (R := R) T * comulForestN (R := R) F :=
  comulForestNG_cons _ T F

/-- The **Δ^ρ coproduct on `ConnesKreimer R (Nonplanar α)`** as an
    algebra hom: `comulAlgHomNG` at `cuts := cutSummandsN`. -/
noncomputable def comulAlgHomN :
    ConnesKreimer R (Nonplanar α) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  comulAlgHomNG cutSummandsN

@[simp] theorem comulAlgHomN_apply_of' (F : Forest (Nonplanar α)) :
    comulAlgHomN (R := R) (α := α) (of' F) = comulForestN F :=
  comulAlgHomNG_apply_of' _ F

@[simp] theorem comulAlgHomN_apply_ofTree (T : Nonplanar α) :
    comulAlgHomN (R := R) (α := α) (ofTree T) = comulTreeN T :=
  comulAlgHomNG_apply_ofTree _ T

/-! ## Hochschild 1-cocycle for `B+_a`

`B+_a : Forest (Nonplanar α) → Nonplanar α` is the smart constructor
`Nonplanar.node a`. Linearly extended to `bPlusLin a : H →ₗ[R] H` (sending
basis element `of' F` to `ofTree (Nonplanar.node a F)`), it satisfies
the **Hochschild 1-cocycle** property (Foissy / MCB §1.2.11):

  Δ^ρ ∘ B+_a = (·) ⊗ 1 ∘ B+_a + (id ⊗ B+_a) ∘ Δ^ρ

i.e., for every `x : H`:

  Δ^ρ (B+_a x) = (B+_a x) ⊗ 1 + (id ⊗ B+_a)(Δ^ρ x).

This is the algebraic input to Foissy's clean inductive proof of
coassociativity (§A.7-δ): the subalgebra `A := {x | (Δ ⊗ id)(Δ x) =
(id ⊗ Δ)(Δ x)}` is closed under `B+_a`, contains all leaves (which are
`B+_a 1`), hence equals the whole algebra. -/

/-! ### B+_a as a linear map -/

/-- The **B+_a linear map**: linearly extend the smart constructor `Nonplanar.node a`
    to an `R`-linear endomorphism of `ConnesKreimer R (Nonplanar α)`,
    sending the basis element `of' F` to `ofTree (Nonplanar.node a F)`. -/
noncomputable def bPlusLin (a : α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.linearLift (fun F => ofTree (Nonplanar.node a F))

@[simp] theorem bPlusLin_of' (a : α) (F : Forest (Nonplanar α)) :
    bPlusLin (R := R) a (of' F) = ofTree (Nonplanar.node a F) := by
  rw [bPlusLin, ConnesKreimer.linearLift_of']

@[simp] theorem bPlusLin_one (a : α) :
    bPlusLin (R := R) a (1 : ConnesKreimer R (Nonplanar α)) =
      ofTree (Nonplanar.leaf a) := by
  show bPlusLin (R := R) a (of' 0) = _
  rw [bPlusLin_of']
  show ofTree (Nonplanar.node a 0) = ofTree (Nonplanar.leaf a)
  rfl

/-! ### `comulForestN` as a sum over forest cuts

Together with `cutSummandsN_node` (`Combinatorics/RootedTree/Cut.lean`),
the expansion `comulForestN_eq_sum` drives the cocycle: cuts of a node
decompose along the per-tree decisions of `cutForestSummandsN`, and
`comulForestN` expands as the matching multiset sum. -/

/-- The forest coproduct `comulForestN F` expands as a multiset sum of
    `of' cf ⊗ of' rem` over `(cf, rem) ∈ cutForestSummandsN F`: the generic
    `comulForestNG_eq_sum` at `cuts := cutSummandsN`, transported along
    `cutForestSummandsN_eq_forestCutsG`. -/
theorem comulForestN_eq_sum (F : Forest (Nonplanar α)) :
    comulForestN (R := R) F = ((cutForestSummandsN F).map
      (fun pf => of' (R := R) pf.1 ⊗ₜ[R] of' (R := R) pf.2)).sum := by
  rw [cutForestSummandsN_eq_forestCutsG]
  exact comulForestNG_eq_sum cutSummandsN F

/-! ### The cocycle theorem (basis-level) -/

/-- The tree-level coproduct on a leaf:
    `comulTreeN (leaf a) = ofTree (leaf a) ⊗ 1 + 1 ⊗ ofTree (leaf a)`. -/
theorem comulTreeN_leaf (a : α) :
    comulTreeN (R := R) (Nonplanar.leaf a) =
      ofTree (Nonplanar.leaf a) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ofTree (Nonplanar.leaf a) := by
  unfold comulTreeN comulTreeNG
  rw [cutSummandsN_leaf, Multiset.map_singleton, Multiset.sum_singleton, of'_zero]

/-- The **Hochschild 1-cocycle property of B+_a**, on basis elements:
    for every forest `F`, the coproduct of the grafted tree
    `Nonplanar.node a F` decomposes as the explicit primitive term plus
    the right-channel B+ application of `comulForestN F`. Proven via
    the substrate `cutSummandsN_node` (cuts of a node decompose along
    `cutForestSummandsN F`) and `comulForestN_eq_sum` (forest coproduct
    expands as the matching multiset sum); the `LinearMap.lTensor`
    distributes over the sum via `map_multiset_sum`, and the per-summand
    check reduces to `LinearMap.lTensor_tmul` + `bPlusLin_of'`. -/
theorem comulTreeN_node_cocycle (a : α) (F : Forest (Nonplanar α)) :
    comulTreeN (R := R) (Nonplanar.node a F) =
      ofTree (Nonplanar.node a F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulForestN F) := by
  unfold comulTreeN comulTreeNG
  rw [cutSummandsN_node, comulForestN_eq_sum,
      map_multiset_sum (LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
        (bPlusLin (R := R) a))]
  simp only [Multiset.map_map]
  refine congr_arg (_ + ·) (congr_arg Multiset.sum
    (Multiset.map_congr rfl (fun pf _ => ?_)))
  show of' (R := R) pf.1 ⊗ₜ[R] ofTree (Nonplanar.node a pf.2) =
       (LinearMap.lTensor (ConnesKreimer R (Nonplanar α)) (bPlusLin (R := R) a))
         (of' (R := R) pf.1 ⊗ₜ[R] of' (R := R) pf.2)
  rw [LinearMap.lTensor_tmul, bPlusLin_of']

/-- The cocycle, lifted to the algebra-hom level on tree basis elements. -/
theorem comulAlgHomN_bPlusLin_cocycle (a : α) (F : Forest (Nonplanar α)) :
    comulAlgHomN (R := R) (bPlusLin (R := R) a (of' F)) =
      bPlusLin (R := R) a (of' F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulAlgHomN (of' F)) := by
  rw [bPlusLin_of', comulAlgHomN_apply_ofTree, comulAlgHomN_apply_of']
  exact comulTreeN_node_cocycle a F

/-! ## Counit laws

`(ε ⊗ id) ∘ Δ^ρ = lid⁻¹` and `(id ⊗ ε) ∘ Δ^ρ = rid⁻¹`: reduce to `of' F`
via `ConnesKreimer.algHom_ext`, then close the tree case by strong induction
on depth through the cocycle `comulTreeN_node_cocycle`.

Coassociativity (`comulRhoN_coassoc`, from the GL/CK duality
`pairing_gl_eq_pairing_coproduct_Rho` + `GrossmanLarson.mul_assoc` via
`pairing₃_unique`) and the `Bialgebra` instance live downstream in
`Coproduct/PruningDuality.lean`. -/

/-! ### Counit ⊗ id commutation with `lTensor (bPlusLin a)`

The factor-wise commutation `(counit ⊗ id) ∘ (id ⊗ B+_a) = (id ⊗ B+_a) ∘ (counit ⊗ id)`
(where the right `id` is on different domains: `H` on the left, `R` on the right).
Pure `TensorProduct.induction_on` calculation; both sides reduce to
`counit x ⊗ B+_a y` on simple tensors. Used in the tree-level counit law. -/

private theorem counit_rTensor_lTensor_bPlus_apply (a : α)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.lTensor R (bPlusLin (R := R) a))
      ((Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α)))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        LinearMap.lTensor_tmul]
  | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

/-! ### Tree-level counit law (depth induction)

`(counit ⊗ id)(Δ T) = 1 ⊗ T` for every nonplanar tree `T`. Strong induction
on `T.depth`: present `T` as `Nonplanar.node a F` via a planar rep, then the
cocycle `comulTreeN_node_cocycle`, the commutation
`counit_rTensor_lTensor_bPlus_apply`, and the forest law on the strictly
shallower children close the goal. -/

private theorem comulForestN_counit_rTensor (F : Forest (Nonplanar α))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α)))) (comulTreeN T) =
      (1 : R) ⊗ₜ ofTree T) :
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
      (comulForestN F) = (1 : R) ⊗ₜ of' F := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestN_zero, map_one, of'_zero, Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    rw [comulForestN_cons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        show (ofTree T : ConnesKreimer R (Nonplanar α)) * of' F' =
              of' (T ::ₘ F') from by
          rw [show (T ::ₘ F' : Forest (Nonplanar α)) = {T} + F' from
                (Multiset.singleton_add T F').symm,
              of'_add, of'_singleton]]

private theorem comulForestN_counit_lTensor (F : Forest (Nonplanar α))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R))) (comulTreeN T) =
      ofTree T ⊗ₜ (1 : R)) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R)))
      (comulForestN F) = of' F ⊗ₜ (1 : R) := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestN_zero, map_one, of'_zero, Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    rw [comulForestN_cons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        show (ofTree T : ConnesKreimer R (Nonplanar α)) * of' F' =
              of' (T ::ₘ F') from by
          rw [show (T ::ₘ F' : Forest (Nonplanar α)) = {T} + F' from
                (Multiset.singleton_add T F').symm,
              of'_add, of'_singleton]]

private theorem comulTreeN_counit_rTensor (T : Nonplanar α) :
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
      (comulTreeN T) = (1 : R) ⊗ₜ ofTree T := by
  -- Strong induction on T.depth.
  suffices aux : ∀ n : ℕ, ∀ T : Nonplanar α, T.depth = n →
      (Algebra.TensorProduct.map (counit (R := R))
          (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
        (comulTreeN T) = (1 : R) ⊗ₜ ofTree T by
    exact aux T.depth T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hT
    -- Pick a tree-level rep T = mk (.node a children).
    obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
      ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
    obtain ⟨a, children⟩ := T₀
    rw [show (Nonplanar.mk (RoseTree.node a children) : Nonplanar α) =
        Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))
        from (Nonplanar.node_mk_tree_list a children).symm]
    -- Use cocycle.
    rw [comulTreeN_node_cocycle, map_add]
    -- First summand vanishes via counit_ofTree.
    rw [show (Algebra.TensorProduct.map (counit (R := R))
            (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
          (ofTree (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))) ⊗ₜ
            (1 : ConnesKreimer R (Nonplanar α))) = 0 from by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, counit_ofTree,
          TensorProduct.zero_tmul], zero_add]
    -- Second summand: commutation + forest law.
    rw [counit_rTensor_lTensor_bPlus_apply,
        comulForestN_counit_rTensor (R := R)
          (Multiset.ofList (children.map Nonplanar.mk))
          (fun T' hT' => by
            apply IH T'.depth ?_ T' rfl
            have hlt := Nonplanar.depth_lt_of_mem T' _ hT' a
            rw [show (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk)) :
                  Nonplanar α) =
                Nonplanar.mk (RoseTree.node a children) from
                Nonplanar.node_mk_tree_list a children] at hlt
            rw [hT] at hlt
            exact hlt),
        LinearMap.lTensor_tmul, bPlusLin_of']

/-- `counit ∘ B+_a = 0` as a linear map. The image of `B+_a` lies in the
    span of `ofTree`s on non-leaf trees, all of which have card-1 forests
    so counit kills them. Proven by reducing the linear-map equality to
    basis vectors via `ConnesKreimer.lhom_ext`, then computing on `of' F`. -/
private theorem counit_bPlusLin (a : α) (y : ConnesKreimer R (Nonplanar α)) :
    counit (R := R) (bPlusLin (R := R) a y) = 0 := by
  -- Both maps are R-linear; reduce to checking equality of the composite with 0
  -- as a LinearMap, then evaluate at y.
  have h : ((counit (R := R)).toLinearMap.comp (bPlusLin (R := R) a) :
           ConnesKreimer R (Nonplanar α) →ₗ[R] R) = 0 := by
    apply ConnesKreimer.lhom_ext
    intro F r
    show counit (bPlusLin a (ConnesKreimer.single F r)) = (0 : R)
    -- Convert `single F r` to `r • of' F`, then push through linearity.
    have hr : (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α))
              = (r : R) • (of' F : ConnesKreimer R (Nonplanar α)) :=
      ConnesKreimer.smul_single_one F r
    rw [hr]
    -- Force re-elaboration through Module-flavored smul.
    change counit (R := R) (bPlusLin a ((r : R) • (of' F : ConnesKreimer R (Nonplanar α)))) =
           (0 : R)
    rw [(bPlusLin (R := R) a).map_smul, bPlusLin_of',
        _root_.map_smul (counit (R := R)) r, counit_ofTree, smul_zero]
  -- Apply h pointwise to y.
  have := congrFun (congrArg DFunLike.coe h) y
  simpa using this

private theorem comulTreeN_counit_lTensor (T : Nonplanar α) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R)))
      (comulTreeN T) = ofTree T ⊗ₜ (1 : R) := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
    ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
  obtain ⟨a, children⟩ := T₀
  rw [show (Nonplanar.mk (RoseTree.node a children) : Nonplanar α) =
      Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))
      from (Nonplanar.node_mk_tree_list a children).symm]
  -- Use cocycle: comulTreeN T = ofTree T ⊗ 1 + (id ⊗ bPlusLin a)(comulForestN F).
  rw [comulTreeN_node_cocycle, map_add]
  -- First summand: (id ⊗ counit)(ofTree T ⊗ 1) = ofTree T ⊗ counit(1) = ofTree T ⊗ 1.
  rw [show (Algebra.TensorProduct.map
            (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
            (counit (R := R)))
        (ofTree (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))) ⊗ₜ
          (1 : ConnesKreimer R (Nonplanar α))) =
      ofTree (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))) ⊗ₜ
        (1 : R) from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]]
  -- Second summand: (id ⊗ counit) ∘ (lTensor (bPlusLin a)) z is zero,
  -- because counit ∘ bPlusLin a = 0 (any tree from B+_a has counit 0).
  rw [show (Algebra.TensorProduct.map
            (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
            (counit (R := R)))
        ((LinearMap.lTensor _ (bPlusLin (R := R) a))
          (comulForestN (Multiset.ofList (children.map Nonplanar.mk)))) = 0 from by
    generalize comulForestN (R := R)
      (Multiset.ofList (children.map Nonplanar.mk)) = z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x y =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, counit_bPlusLin, TensorProduct.tmul_zero]
    | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, add_zero]]
  rw [add_zero]

/-! ### Counit laws (algebra-hom level)

Reduce to `of' F` via `ConnesKreimer.algHom_ext`; the forest laws
`comulForestN_counit_rTensor` and `comulForestN_counit_lTensor` close from
the tree-level laws. -/

theorem counit_rTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (counit (R := R)) (AlgHom.id R _)).comp comulAlgHomN =
      (Algebra.TensorProduct.lid R (ConnesKreimer R (Nonplanar α))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (counit (R := R))
          (AlgHom.id R (ConnesKreimer R (Nonplanar α)))) (comulAlgHomN (of' F)) =
       (Algebra.TensorProduct.lid R (ConnesKreimer R (Nonplanar α))).symm (of' F)
  rw [comulAlgHomN_apply_of', Algebra.TensorProduct.lid_symm_apply]
  exact comulForestN_counit_rTensor F (fun T _ => comulTreeN_counit_rTensor T)

theorem counit_lTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (AlgHom.id R _) (counit (R := R))).comp comulAlgHomN =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R (Nonplanar α))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
          (counit (R := R))) (comulAlgHomN (of' F)) =
       (Algebra.TensorProduct.rid R R (ConnesKreimer R (Nonplanar α))).symm (of' F)
  rw [comulAlgHomN_apply_of', Algebra.TensorProduct.rid_symm_apply]
  exact comulForestN_counit_lTensor F (fun T _ => comulTreeN_counit_lTensor T)

/-! ### Δ^ρ coassoc and Bialgebra instance: moved

The GL/CK duality theorem (`pairing_gl_eq_pairing_coproduct_Rho`), the
coassociativity of `comulAlgHomN`, and the `Bialgebra` instance live in
`Coproduct/PruningDuality.lean`, downstream of `BMinus.lean` (whose B⁻
calculus drives the duality proof). -/

end ConnesKreimer

