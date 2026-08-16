import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
import Linglib.Core.Combinatorics.RootedTree.Cut
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Bialgebra.Basic
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
(`Coproduct/Trace.lean`), which leaves marker leaves.

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
* `ConnesKreimer.comulAlgHomN_coassoc_algHom`, `comulRhoN_coassoc` —
  coassociativity, by Foissy's subalgebra argument
  ([foissy-introduction-hopf-algebras-trees]; [grinberg-reiner-2020]).
* `ConnesKreimer.instBialgebraRho` — the Δ^ρ `Bialgebra`
  ([marcolli-chomsky-berwick-2025] Lemma 1.2.11), over any `CommSemiring`.

## Implementation notes

`B+` only well-defines on unordered children
(`Multiset (Nonplanar α) → Nonplanar α`); on planar trees it would need
a canonical ordering — hence the cocycle and everything downstream live
at the `Nonplanar` level. The clean-coassoc route through the cocycle
does not generalize to Δ^c (B+ is not a 1-cocycle for the trace
variant, which instead uses the direct double-cut bijection).

The GL/CK duality theorem lives downstream in
`Coproduct/PruningDuality.lean` (its proof needs the B⁻ calculus of
`BMinus.lean`, which imports this file); the full `HopfAlgebra`
instance is in `HopfAlgebra.lean`.

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

Coassociativity (`comulRhoN_coassoc`, Foissy's subalgebra argument) and
the `Bialgebra` instance follow below. -/

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

section CoassocFoissy
-- The nested tensor squares `CK ⊗ (CK ⊗ CK)` of the coassociativity statement
-- need one extra pending step during instance synthesis.
set_option maxSynthPendingDepth 2

/-! ### Coassociativity: Foissy's subalgebra argument

Foissy's clean proof ([foissy-introduction-hopf-algebras-trees]; for the
connected-graded-bialgebra framing see [grinberg-reiner-2020]): the set
`A := {x | (id ⊗ Δ)(Δ x) = assoc ((Δ ⊗ id)(Δ x))}` is a subalgebra, closed
under `B+_a` by the Hochschild cocycle, and contains every `ofTree T` by
depth induction — hence `A = ⊤`. Works over any `CommSemiring`, with no
pairing or nondegeneracy input. -/

/-- The "compute coassociativity left-hand side" algebra hom:
    `x ↦ assoc((Δ ⊗ id)(Δ x))`. -/
noncomputable def coassocLHS :
    ConnesKreimer R (Nonplanar α) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R]
        (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :=
  (Algebra.TensorProduct.assoc R R R _ _ _).toAlgHom.comp
    ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
      (AlgHom.id R _)).comp comulAlgHomN)

/-- The "compute coassociativity right-hand side" algebra hom:
    `x ↦ (id ⊗ Δ)(Δ x)`. -/
noncomputable def coassocRHS :
    ConnesKreimer R (Nonplanar α) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R]
        (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :=
  (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
    (comulAlgHomN (R := R) (α := α))).comp comulAlgHomN

/-- The **Foissy coassociativity subalgebra**: elements where the two
    sides of coassociativity agree. By Foissy's clean argument
    (`coassocSubalg_eq_top`), this is all of `H`. -/
noncomputable def coassocSubalg : Subalgebra R (ConnesKreimer R (Nonplanar α)) :=
  AlgHom.equalizer (coassocLHS (R := R) (α := α)) coassocRHS

theorem mem_coassocSubalg (x : ConnesKreimer R (Nonplanar α)) :
    x ∈ coassocSubalg (R := R) (α := α) ↔ coassocLHS x = coassocRHS x :=
  AlgHom.mem_equalizer _ _ _

/-! ### Linear extension of the cocycle

The cocycle `comulAlgHomN_bPlusLin_cocycle` is stated for `of' F`. Since
both sides are R-linear in `x : H`, it extends to arbitrary `x` via
`ConnesKreimer.lhom_ext` (all linear maps out of `H = R[Forest]` are determined
by their action on basis vectors `of' F = ConnesKreimer.single F 1`). -/

/-- The cocycle, extended to arbitrary `x : H` via linearity. -/
theorem comulAlgHomN_bPlusLin_cocycle_general (a : α)
    (x : ConnesKreimer R (Nonplanar α)) :
    comulAlgHomN (bPlusLin (R := R) a x) =
      bPlusLin (R := R) a x ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulAlgHomN x) := by
  -- LHS and RHS are both R-linear in x. Reduce to checking on ConnesKreimer.single F r
  -- (= r • of' F), then to F = of' F (r = 1) via scalar linearity, then apply cocycle.
  have heq :
      ((comulAlgHomN (R := R) (α := α)).toLinearMap.comp (bPlusLin (R := R) a) :
        ConnesKreimer R (Nonplanar α) →ₗ[R]
          ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) =
      ((TensorProduct.mk R _ _).flip 1).comp (bPlusLin (R := R) a) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)).comp
        (comulAlgHomN (R := R) (α := α)).toLinearMap := by
    apply ConnesKreimer.lhom_ext
    intro F r
    -- Convert single F r to r • of' F, then use cocycle. Use `change` to force the
    -- smul to elaborate via Module instance (matching what map_smul expects), avoiding
    -- the SMulZeroClass mismatch.
    show comulAlgHomN.toLinearMap (bPlusLin a (ConnesKreimer.single F r)) =
         (TensorProduct.mk R _ _).flip 1 (bPlusLin a (ConnesKreimer.single F r)) +
         LinearMap.lTensor _ (bPlusLin a) (comulAlgHomN.toLinearMap (ConnesKreimer.single F r))
    have hr : ConnesKreimer.single F r = (r : R) • (of' F : ConnesKreimer R (Nonplanar α)) := ConnesKreimer.smul_single_one F r
    rw [hr]
    -- Force re-elaboration through Module-flavored smul:
    change comulAlgHomN.toLinearMap (bPlusLin a ((r : R) • (of' F : ConnesKreimer R (Nonplanar α)))) =
           (TensorProduct.mk R _ _).flip 1
              (bPlusLin a ((r : R) • (of' F : ConnesKreimer R (Nonplanar α)))) +
           LinearMap.lTensor _ (bPlusLin a)
              (comulAlgHomN.toLinearMap ((r : R) • (of' F : ConnesKreimer R (Nonplanar α))))
    rw [(bPlusLin (R := R) a).map_smul,
        (comulAlgHomN (R := R) (α := α)).toLinearMap.map_smul,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
        comulAlgHomN_bPlusLin_cocycle, smul_add, TensorProduct.smul_tmul']
    -- Now match the second summand on both sides:
    --   r • (lTensor _ (bPlusLin a)) (comulAlgHomN (of' F))
    --   = (lTensor _ (bPlusLin a)) (comulAlgHomN (r • of' F))
    -- via map_smul on comulAlgHomN and lTensor in turn.
    simp only [LinearMap.flip_apply, TensorProduct.mk_apply]
    congr 1
    -- Now isolate the r-smul mismatch: (lTensor _ ...) (r • _) vs r • (lTensor _ ...) _.
    change (r : R) • (LinearMap.lTensor _ (bPlusLin (R := R) a))
              (comulAlgHomN (of' F)) =
           (LinearMap.lTensor _ (bPlusLin (R := R) a))
              (comulAlgHomN ((r : R) • (of' F : ConnesKreimer R (Nonplanar α))))
    rw [_root_.map_smul (comulAlgHomN (R := R) (α := α)), (LinearMap.lTensor _ (bPlusLin (R := R) a)).map_smul]
  exact congr($heq x)

/-! ### Closure of `coassocSubalg` under `B+_a`

The substantive Foissy bit. Uses the cocycle (twice) plus tensor-algebra
calculations. Sketch (Sweedler-style, with `Δ x = Σᵢ aᵢ ⊗ bᵢ`):

* `Δ(B+_a x) = (B+_a x) ⊗ 1 + Σᵢ aᵢ ⊗ B+_a bᵢ` (cocycle).
* `(Δ ⊗ id)(Δ(B+_a x)) = Δ(B+_a x) ⊗ 1 + Σᵢ Δ(aᵢ) ⊗ B+_a bᵢ`. Re-apply cocycle to
  `Δ(B+_a x)` to expand the first summand.
* `assoc((Δ ⊗ id)(Δ(B+_a x))) = (B+_a x) ⊗ (1 ⊗ 1) + Σᵢ aᵢ ⊗ (B+_a bᵢ ⊗ 1) +
  Σᵢ assoc(Δ(aᵢ) ⊗ B+_a bᵢ)`.
* `(id ⊗ Δ)(Δ(B+_a x)) = (B+_a x) ⊗ (1 ⊗ 1) + Σᵢ aᵢ ⊗ (B+_a bᵢ ⊗ 1) +
  Σᵢ aᵢ ⊗ ((id ⊗ B+_a)(Δ bᵢ))`.
* The "shared" first two summands match by inspection. The third summands match via
  `(id ⊗ id ⊗ B+_a)` applied to the hypothesis `assoc((Δ ⊗ id)(Δ x)) = (id ⊗ Δ)(Δ x)`.

A clean Lean implementation would extract a `LinearMap`-level helper
`assoc_lTensor_bPlus_eq : assoc ∘ (Δ ⊗ id) ∘ (id ⊗ B+_a) = (id ⊗ id ⊗ B+_a) ∘ assoc ∘ (Δ ⊗ id)`
(provable by `TensorProduct.induction_on`), then close by `congrArg ((id ⊗ id ⊗ B+_a))` on `hx`. -/
/-! ### Helper commutations for the bPlus closure proof

Three commutation/identity lemmas for the substantive Foissy bit:

* `comulAlgHomN_lTensor_bPlus_commute`: `(Δ ⊗ id) ∘ (id ⊗ B+) = (id ⊗ id ⊗ B+) ∘ (Δ ⊗ id)`,
  i.e., the comul on the left factor commutes with B+ on the right factor.
* `assoc_lTensor_bPlus_commute`: `assoc ∘ (id ⊗ id_R ⊗ B+ on (H⊗H)⊗H) =
  (id ⊗ id ⊗ B+ on H⊗(H⊗H)) ∘ assoc`, i.e., the associator commutes with B+
  acting on the rightmost factor.
* `lTensor_id_Δ_bPlus_eq`: `(id ⊗ Δ) ∘ (id ⊗ B+) z = assoc((id ⊗ B+)(z) ⊗ 1) +
  (id ⊗ id ⊗ B+) ∘ (id ⊗ Δ)(z)`, by cocycle on the right factor of `(id ⊗ B+)(z)`. -/

private theorem comulAlgHomN_lTensor_bPlus_commute (a : α)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    (Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.lTensor _ (bPlusLin (R := R) a))
      ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α)))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        LinearMap.lTensor_tmul]
  | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

private theorem assoc_lTensor_bPlus_commute (a : α)
    (z : (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) ⊗[R]
          ConnesKreimer R (Nonplanar α)) :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α)) (ConnesKreimer R (Nonplanar α)))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
      ((Algebra.TensorProduct.assoc R R R (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α)) (ConnesKreimer R (Nonplanar α))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w c =>
    -- w : H ⊗ H, c : H. Need to induct on w to expose the (a ⊗ b) ⊗ c form.
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.assoc_tmul,
          Algebra.TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
          LinearMap.lTensor_tmul]
    | add w₁ w₂ ih₁ ih₂ =>
      simp only [TensorProduct.add_tmul, map_add]
      rw [ih₁, ih₂]
  | add z₁ z₂ ih₁ ih₂ =>
    simp only [map_add]
    rw [ih₁, ih₂]

private theorem lTensor_id_Δ_bPlus_eq (a : α)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (comulAlgHomN (R := R) (α := α)))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α)) (ConnesKreimer R (Nonplanar α)))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a) z) ⊗ₜ
        (1 : ConnesKreimer R (Nonplanar α))) +
    (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
      ((Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (comulAlgHomN (R := R) (α := α))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    -- LHS: (map id Δ)((lTensor B+a)(x ⊗ y)) = (map id Δ)(x ⊗ B+a y) = x ⊗ Δ(B+a y)
    --    = x ⊗ ((B+a y) ⊗ 1 + (lTensor B+a)(Δ y)) = x ⊗ ((B+a y) ⊗ 1) + x ⊗ (lTensor B+a)(Δ y)
    -- RHS: assoc((x ⊗ B+a y) ⊗ 1) + (lTensor (lTensor B+a))(x ⊗ Δy)
    --    = x ⊗ ((B+a y) ⊗ 1) + x ⊗ (lTensor B+a)(Δ y)
    -- ✓ by simp with all the relevant tmul + cocycle lemmas.
    simp only [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
               Algebra.TensorProduct.assoc_tmul, AlgHom.id_apply,
               comulAlgHomN_bPlusLin_cocycle_general, TensorProduct.tmul_add]
  | add z₁ z₂ ih₁ ih₂ =>
    simp only [map_add, TensorProduct.add_tmul]
    rw [ih₁, ih₂]
    abel

theorem bPlus_mem_coassocSubalg (a : α) (x : ConnesKreimer R (Nonplanar α))
    (hx : x ∈ coassocSubalg (R := R) (α := α)) :
    bPlusLin (R := R) a x ∈ coassocSubalg (R := R) (α := α) := by
  rw [mem_coassocSubalg] at hx ⊢
  -- The proof structure: express both `coassocLHS (B+_a x)` and `coassocRHS (B+_a x)`
  -- in the form `shared + (lTensor H (lTensor H B+_a))(coassocXXX x)` with the
  -- *same* shared part, then use hx (coassocLHS x = coassocRHS x) to conclude.
  --
  -- shared := (B+_a x) ⊗ (1 ⊗ 1) + assoc(((lTensor H B+_a)(Δ x)) ⊗ 1)
  show (Algebra.TensorProduct.assoc R R R _ _ _)
        ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
          (AlgHom.id R _)) (comulAlgHomN (bPlusLin (R := R) a x))) =
       (Algebra.TensorProduct.map (AlgHom.id R _)
          (comulAlgHomN (R := R) (α := α))) (comulAlgHomN (bPlusLin (R := R) a x))
  -- Apply cocycle on x: Δ(B+_a x) = (B+_a x) ⊗ 1 + (lTensor _ B+_a)(Δ x).
  rw [comulAlgHomN_bPlusLin_cocycle_general]
  -- Distribute (map ⊗ id), (map id ⊗ ·), assoc through the addition.
  rw [map_add, map_add, map_add]
  -- LHS first term: assoc((map Δ id)(Bx ⊗ 1)) = assoc(Δ(Bx) ⊗ 1)
  --                  = assoc(((Bx ⊗ 1) + (lTensor _ B+a)(Δx)) ⊗ 1) [cocycle on Bx]
  --                  = assoc((Bx ⊗ 1) ⊗ 1) + assoc(((lTensor _ B+a)(Δx)) ⊗ 1)
  --                  = Bx ⊗ (1 ⊗ 1) + assoc(((lTensor _ B+a)(Δx)) ⊗ 1)
  rw [show (Algebra.TensorProduct.assoc R R R _ _ _)
        ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
          (AlgHom.id R _)) (bPlusLin (R := R) a x ⊗ₜ
            (1 : ConnesKreimer R (Nonplanar α)))) =
      (bPlusLin (R := R) a x) ⊗ₜ ((1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ
        (1 : ConnesKreimer R (Nonplanar α))) +
      (Algebra.TensorProduct.assoc R R R _ _ _)
        ((LinearMap.lTensor _ (bPlusLin (R := R) a))
          (comulAlgHomN x) ⊗ₜ (1 : ConnesKreimer R (Nonplanar α))) from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        comulAlgHomN_bPlusLin_cocycle_general, TensorProduct.add_tmul, map_add,
        Algebra.TensorProduct.assoc_tmul]]
  -- LHS second term: use Δ⊗id-vs-id⊗B+a commutation, then assoc-vs-B+a commutation.
  rw [comulAlgHomN_lTensor_bPlus_commute, assoc_lTensor_bPlus_commute]
  -- RHS first term: (map id Δ)(Bx ⊗ 1) = Bx ⊗ Δ(1) = Bx ⊗ (1 ⊗ 1).
  rw [show (Algebra.TensorProduct.map (AlgHom.id R _)
            (comulAlgHomN (R := R) (α := α)))
          (bPlusLin (R := R) a x ⊗ₜ (1 : ConnesKreimer R (Nonplanar α))) =
        (bPlusLin (R := R) a x) ⊗ₜ
          ((1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ
            (1 : ConnesKreimer R (Nonplanar α))) from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
        Algebra.TensorProduct.one_def]]
  -- RHS second term: use cocycle-driven identity `lTensor_id_Δ_bPlus_eq`.
  rw [lTensor_id_Δ_bPlus_eq]
  -- Now both sides are `Bx ⊗ (1⊗1) + assoc(...) + (lTensor (lTensor B+a))(coassocXXX_inner x)`,
  -- modulo associativity. Use hx (coassocLHS x = coassocRHS x — defeq to the inner forms)
  -- to bridge the two third summands; then `abel` for reordering.
  have hlift : (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
                ((Algebra.TensorProduct.assoc R R R _ _ _)
                  ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
                    (AlgHom.id R _)) (comulAlgHomN x))) =
              (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
                ((Algebra.TensorProduct.map (AlgHom.id R _)
                  (comulAlgHomN (R := R) (α := α))) (comulAlgHomN x)) :=
    congrArg _ hx
  rw [hlift]
  abel

/-! ### Tree induction: every `ofTree T` is in `coassocSubalg` -/

/-- Helper: `of' F` is in `coassocSubalg` whenever every `ofTree T` for `T ∈ F` is.
    By Multiset.induction on F using `of'_singleton`, `of'_zero`, `of'_add`, plus
    subalgebra closure under * and 1. -/
private theorem of'_mem_coassocSubalg_of_trees (F : Forest (Nonplanar α))
    (h : ∀ T ∈ F, ofTree T ∈ coassocSubalg (R := R) (α := α)) :
    of' (R := R) F ∈ coassocSubalg (R := R) (α := α) := by
  induction F using Multiset.induction with
  | empty =>
    rw [show ((0 : Forest (Nonplanar α)) : Forest (Nonplanar α)) = (0 : Forest (Nonplanar α)) from rfl,
        of'_zero]
    exact one_mem _
  | cons T F' ih =>
    have hT : ofTree T ∈ coassocSubalg (R := R) (α := α) := h T (Multiset.mem_cons_self T F')
    have hF' : ∀ T' ∈ F', ofTree T' ∈ coassocSubalg (R := R) (α := α) :=
      fun T' hT' => h T' (Multiset.mem_cons_of_mem hT')
    have ih' := ih hF'
    rw [show ((T ::ₘ F') : Forest (Nonplanar α)) = ({T} + F') from rfl, of'_add, of'_singleton]
    exact mul_mem hT ih'

/-- Every Nonplanar tree's `ofTree` lies in `coassocSubalg`. By strong
    induction on tree depth: leaves are `B+_a 1` (closed under `B+_a` from `1`);
    nodes are `B+_a (of' F)` where `of' F` is a product of `ofTree` of smaller-depth
    trees. -/
theorem ofTree_mem_coassocSubalg (T : Nonplanar α) :
    ofTree T ∈ coassocSubalg (R := R) (α := α) := by
  -- Strong induction on T.depth.
  suffices aux : ∀ n : ℕ, ∀ T : Nonplanar α, T.depth = n →
      ofTree T ∈ coassocSubalg (R := R) (α := α) by
    exact aux T.depth T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hT
    -- Pick a planar rep T = mk (RoseTree.node a children).
    obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
      ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
    obtain ⟨a, children⟩ := T₀
    -- T = mk (.node a children) = Nonplanar.node a (Multiset.ofList (children.map mk))
    rw [show (Nonplanar.mk (RoseTree.node a children) : Nonplanar α) =
        Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))
        from (Nonplanar.node_mk_tree_list a children).symm]
    -- ofTree (Nonplanar.node a F) = bPlusLin a (of' F) by bPlusLin_of'.
    rw [show ofTree (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk)))
            = bPlusLin (R := R) a (of' (Multiset.ofList (children.map Nonplanar.mk)))
            from (bPlusLin_of' a _).symm]
    apply bPlus_mem_coassocSubalg
    -- of' F ∈ coassocSubalg, where F = Multiset.ofList (children.map mk).
    apply of'_mem_coassocSubalg_of_trees
    intro T' hT'
    -- T' ∈ Multiset.ofList (children.map mk). Use IH on T'.depth < (mk (.node a children)).depth.
    have hT'_depth : T'.depth < (Nonplanar.mk (RoseTree.node a children)).depth := by
      have := Nonplanar.depth_lt_of_mem T'
        (Multiset.ofList (children.map Nonplanar.mk)) hT' a
      rw [show (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk)) : Nonplanar α) =
          Nonplanar.mk (RoseTree.node a children) from
          Nonplanar.node_mk_tree_list a children] at this
      exact this
    rw [hT] at hT'_depth
    exact IH T'.depth hT'_depth T' rfl

/-! ### `coassocSubalg = ⊤`

Since `H` is generated as an algebra by `{ofTree T | T : Nonplanar α}` and
each generator is in `coassocSubalg`, the subalgebra is the whole thing. -/

theorem coassocSubalg_eq_top :
    coassocSubalg (R := R) (α := α) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  -- Induct on x; each piece is in coassocSubalg.
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
  · exact zero_mem _
  · intro f g hf hg
    exact add_mem hf hg
  · intro F r
    -- ConnesKreimer.single F r = r • of' F ∈ coassocSubalg via algebraMap.
    show (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) ∈ _
    rw [show (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) = r • of' F from
        ConnesKreimer.smul_single_one F r]
    exact Subalgebra.smul_mem _ (of'_mem_coassocSubalg_of_trees F
      (fun T _ => ofTree_mem_coassocSubalg T)) r

/-! ### Coassociativity at the algebra-hom level

Direct corollary: `coassocLHS = coassocRHS` as algebra homs. The
`Bialgebra.ofAlgHom` constructor takes this in its unfolded form
(without going through the `coassocLHS`/`coassocRHS` named bundles),
so we expose both. -/

theorem coassocLHS_eq_coassocRHS :
    coassocLHS (R := R) (α := α) = coassocRHS := by
  ext x
  have h : x ∈ coassocSubalg (R := R) (α := α) := by
    rw [coassocSubalg_eq_top]; trivial
  exact (mem_coassocSubalg x).mp h

theorem comulAlgHomN_coassoc_algHom :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α)) (ConnesKreimer R (Nonplanar α))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
        (AlgHom.id R _)).comp comulAlgHomN) =
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (comulAlgHomN (R := R) (α := α))).comp comulAlgHomN :=
  coassocLHS_eq_coassocRHS

/-- Coassociativity of Δ^ρ (LinearMap form). -/
theorem comulRhoN_coassoc :
    (TensorProduct.assoc R
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))).toLinearMap ∘ₗ
      (comulAlgHomN (R := R) (α := α)).toLinearMap.rTensor _ ∘ₗ
      (comulAlgHomN (R := R) (α := α)).toLinearMap =
    (comulAlgHomN (R := R) (α := α)).toLinearMap.lTensor _ ∘ₗ
      (comulAlgHomN (R := R) (α := α)).toLinearMap :=
  congrArg AlgHom.toLinearMap comulAlgHomN_coassoc_algHom

end CoassocFoissy

/-- The Δ^ρ **`Bialgebra`** on `ConnesKreimer R (Nonplanar α)`
    ([marcolli-chomsky-berwick-2025] Lemma 1.2.11), over any `CommSemiring`. -/
noncomputable instance instBialgebraRho :
    Bialgebra R (ConnesKreimer R (Nonplanar α)) :=
  Bialgebra.ofAlgHom (A := ConnesKreimer R (Nonplanar α)) comulAlgHomN counit
    comulAlgHomN_coassoc_algHom
    counit_rTensor_comulAlgHomN
    counit_lTensor_comulAlgHomN

/-- The coproduct of `instBialgebraRho` is `comulAlgHomN`. -/
theorem coalgebra_comul_apply (x : ConnesKreimer R (Nonplanar α)) :
    Coalgebra.comul (R := R) x = comulAlgHomN x := rfl

/-- The counit of `instBialgebraRho` is `ConnesKreimer.counit`. -/
theorem coalgebra_counit_apply (x : ConnesKreimer R (Nonplanar α)) :
    CoalgebraStruct.counit (R := R) x = counit x := rfl

/-! ### GL/CK duality: downstream

The GL/CK duality theorem (`pairing_gl_eq_pairing_coproduct_Rho`) lives in
`Coproduct/PruningDuality.lean`, downstream of `BMinus.lean` (whose B⁻
calculus drives its proof). -/

end ConnesKreimer
