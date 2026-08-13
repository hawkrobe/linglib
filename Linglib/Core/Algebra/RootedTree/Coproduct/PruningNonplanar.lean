import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
import Linglib.Core.Combinatorics.RootedTree.Cut
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.LinearAlgebra.Finsupp.LSum
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
(`Coproduct/TraceNonplanar.lean`), which leaves marker leaves.

## Main definitions

* `ConnesKreimer.comulTreeN`, `ConnesKreimer.comulForestN`,
  `ConnesKreimer.comulAlgHomN` — the Δ^ρ coproduct, as the generic
  admissible-cut coproduct (`Coproduct/WithCuts.lean`) at the
  enumeration `cutSummandsN`.
* `ConnesKreimer.comulTreeNFiltered` — the phase-restricted variant
  ([marcolli-chomsky-berwick-2025] §1.14).
* `ConnesKreimer.bPlus`, `ConnesKreimer.bPlusLin` — grafting `B+_a` as
  smart constructor and linear map.

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

/-- A **filtered nonplanar tree-level Δ^ρ**: the `T ⊗ 1` primitive term plus
    the cut-summand sum restricted to summands satisfying `pred`. Generalizes
    `comulTreeN` (the `pred = always-true` case); used to carve phase-restricted
    sub-coproducts (e.g. the phase coproduct Δ^c_Φ of
    [marcolli-chomsky-berwick-2025] §1.14). -/
noncomputable def comulTreeNFiltered (T : Nonplanar α)
    (pred : Forest (Nonplanar α) × Nonplanar α → Prop) [DecidablePred pred] :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
  + (((cutSummandsN T).filter pred).map
      (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-- The filter drops nothing when every cut summand satisfies `pred`, recovering
    the full `comulTreeN`. -/
theorem comulTreeNFiltered_eq_comulTreeN (T : Nonplanar α)
    (pred : Forest (Nonplanar α) × Nonplanar α → Prop) [DecidablePred pred]
    (hAll : ∀ p ∈ cutSummandsN T, pred p) :
    comulTreeNFiltered (R := R) T pred = comulTreeN (R := R) T := by
  unfold comulTreeNFiltered comulTreeN comulTreeNG
  rw [Multiset.filter_eq_self.mpr hAll]

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

/-- Forest-level Δ^ρ as a `MonoidHom` from `Multiplicative (Forest ...)`. -/
noncomputable def comulMonoidHomN :
    Multiplicative (Forest (Nonplanar α)) →*
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :=
  comulMonoidHomNG cutSummandsN

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

/-! ### B+_a as a function, smart constructor, and linear map -/

/-- The **B+_a** operator: graft an unordered forest of Nonplanar trees
    under a new root labeled `a`. Identical to the smart constructor. -/
noncomputable def bPlus (a : α) (F : Forest (Nonplanar α)) :
    Nonplanar α :=
  Nonplanar.node a F

@[simp] theorem bPlus_def (a : α) (F : Forest (Nonplanar α)) :
    bPlus a F = Nonplanar.node a F := rfl

/-- The **B+_a linear map**: linearly extend the smart constructor `bPlus a`
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

/-! ### Tensor-algebra and multiset distributivity helpers -/

/-- The fundamental distributivity in `H ⊗ H` for basis-vector tensors:
    `(of' a ⊗ of' b) * (of' c ⊗ of' d) = of' (a + c) ⊗ of' (b + d)`.
    Combines `Algebra.TensorProduct.tmul_mul_tmul` with `of'_add` on
    both channels. -/
private theorem of'_tmul_mul_of'_tmul (a b c d : Forest (Nonplanar α)) :
    (of' (R := R) a ⊗ₜ[R] of' (R := R) b) * (of' (R := R) c ⊗ₜ[R] of' (R := R) d) =
      of' (R := R) (a + c) ⊗ₜ[R] of' (R := R) (b + d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← of'_add, ← of'_add]

/-- Cartesian product distributes the head map: `(s.map f) ×ˢ t = s.bind (a ↦ t.map (Prod.mk (f a)))`.
    Pure `Multiset.product`/`Multiset.bind_map` algebra; included locally because mathlib
    doesn't ship this exact form. -/
private theorem map_first_product {β γ δ : Type*}
    (f : β → γ) (s : Multiset β) (t : Multiset δ) :
    (s.map f) ×ˢ t = s.bind (fun a => t.map (Prod.mk (f a))) :=
  Multiset.bind_map s _ f

/-! ### Public API

The two structural facts that drive the cocycle: cuts of a node
decompose along `cutForestSummandsN`, and `comulForestN` expands as the
multiset sum over `cutForestSummandsN`. Both are pure Nonplanar-level
statements; tree-level substrate is invisible to consumers. -/

/-- Cuts of `Nonplanar.node a F` decompose along the per-tree decisions
    of `F`: each pair `(cf, rem) ∈ cutForestSummandsN F` gives a cut
    summand `(cf, Nonplanar.node a rem)`. The Nonplanar-level form. -/
@[simp] theorem cutSummandsN_node (a : α) (F : Forest (Nonplanar α)) :
    cutSummandsN (Nonplanar.node a F) =
      (cutForestSummandsN F).map (fun pf => (pf.1, Nonplanar.node a pf.2)) := by
  obtain ⟨ps, hps⟩ := exists_planar_list_rep F
  subst hps
  rw [cutSummandsN_node_planar_list, ← cutForestSummandsN_via_planar_list]

/-- Extract-branch of the `comulForestN_eq_sum` cons step: `(ofTree T ⊗ 1)`
    times the forest-cuts sum collapses into the "extract T whole"
    summand of `cutForestSummandsN_cons` (the `({T}, none)` decision). -/
private theorem comulForestN_cons_extract_branch (T : Nonplanar α)
    (P : Multiset (Forest (Nonplanar α) × Forest (Nonplanar α))) :
    (ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))) *
        (P.map (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum =
      (((P.map (Prod.mk
          (({T}, Option.none) : Forest (Nonplanar α) × Option (Nonplanar α)))).map
        innerCombinerProj).map
        (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum := by
  rw [← of'_singleton, ← of'_zero (R := R) (T := Nonplanar α),
      ← Multiset.sum_map_mul_left]
  simp only [Multiset.map_map]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl (fun p _ => ?_))
  show (of' (R := R) ({T} : Forest (Nonplanar α)) ⊗ₜ[R] of' (R := R) 0) *
        (of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2) =
       ((fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2) ∘ innerCombinerProj ∘
          Prod.mk (({T}, Option.none) :
            Forest (Nonplanar α) × Option (Nonplanar α))) p
  rw [of'_tmul_mul_of'_tmul, zero_add]
  rfl

/-- Recurse-branch of the `comulForestN_eq_sum` cons step: the
    `cutSummandsN T`-indexed sum part of `comulTreeN T` times the
    forest-cuts sum collapses into the cartesian product of
    "recurse-with-cut" decisions on `T` against the rest. -/
private theorem comulForestN_cons_recurse_branch (T : Nonplanar α)
    (P : Multiset (Forest (Nonplanar α) × Forest (Nonplanar α))) :
    (((cutSummandsN T).map (fun s => of' (R := R) s.1 ⊗ₜ[R] ofTree s.2)).sum) *
        (P.map (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum =
      (((((cutSummandsN T).map (fun s => (s.1, Option.some s.2))) ×ˢ P).map
        innerCombinerProj).map
        (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum := by
  rw [← Multiset.sum_map_mul_right,
      show (cutSummandsN T).map (fun s =>
        (of' (R := R) s.1 ⊗ₜ[R] ofTree s.2) *
        (P.map (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum) =
      (cutSummandsN T).map (fun s =>
        (P.map (fun p => of' (R := R) (s.1 + p.1) ⊗ₜ[R]
          of' (R := R) (s.2 ::ₘ p.2))).sum) from
        Multiset.map_congr rfl (fun s _ => by
          rw [← of'_singleton (R := R) s.2, ← Multiset.sum_map_mul_left]
          refine congr_arg Multiset.sum
            (Multiset.map_congr rfl (fun p _ => ?_))
          rw [of'_tmul_mul_of'_tmul, Multiset.singleton_add]),
      ← Multiset.sum_bind, map_first_product]
  simp only [Multiset.map_bind, Multiset.map_map]
  refine congr_arg Multiset.sum (Multiset.bind_congr (fun s _ => ?_))
  apply Multiset.map_congr rfl
  intro p _
  rfl

/-- The forest coproduct `comulForestN F` expands as a multiset sum of
    `of' cf ⊗ of' rem` over `(cf, rem) ∈ cutForestSummandsN F`. -/
theorem comulForestN_eq_sum (F : Forest (Nonplanar α)) :
    comulForestN (R := R) F = ((cutForestSummandsN F).map
      (fun pf => of' (R := R) pf.1 ⊗ₜ[R] of' (R := R) pf.2)).sum := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestN_zero, cutForestSummandsN_zero,
        Multiset.map_singleton, Multiset.sum_singleton, of'_zero]
    rfl
  | cons T F' ih =>
    rw [comulForestN_cons, ih, cutForestSummandsN_cons]
    unfold comulTreeN comulTreeNG augActionN
    rw [add_mul, Multiset.cons_product, Multiset.map_add, Multiset.map_add, Multiset.sum_add,
        comulForestN_cons_extract_branch, comulForestN_cons_recurse_branch]

/-! ### The cocycle theorem (basis-level) -/

/-- For the empty forest: `Nonplanar.node a 0 = Nonplanar.leaf a`. -/
@[simp] theorem node_zero_eq_leaf (a : α) :
    (Nonplanar.node a (0 : Multiset (Nonplanar α)) : Nonplanar α) =
      Nonplanar.leaf a := rfl

/-- The cut summands of a leaf: only one summand `(0, leaf a)`,
    corresponding to the empty cut. -/
theorem cutSummandsN_leaf (a : α) :
    cutSummandsN (Nonplanar.leaf a : Nonplanar α) =
      ({((0 : Forest (Nonplanar α)), Nonplanar.leaf a)} : Multiset _) := by
  show (cutSummandsP (RoseTree.leaf a)).map (projSummand (α := α)) = _
  rw [show RoseTree.leaf a = RoseTree.node a [] from rfl, cutSummandsP_node,
      cutListSummandsP_nil, Multiset.map_singleton, Multiset.map_singleton]
  rfl

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

Counit laws follow by reducing to the tree case via
`ConnesKreimer.algHom_ext` + multiplicativity (the empty-cut summand
contributes `1 ⊗ of' F`; all others are killed by `counit`).

Coassociativity (`comulRhoN_coassoc`, from the GL/CK duality
`pairing_gl_eq_pairing_coproduct_Rho` + `GrossmanLarson.mul_assoc` via
`pairing₃_unique`) and the `Bialgebra` instance live downstream in
`Coproduct/PruningDuality.lean`. -/

/-! ### Tree-depth induction substrate -/

/-- A tree's depth is strictly less than the depth of any node containing
    it as a child. -/
theorem _root_.RoseTree.Nonplanar.depth_lt_of_mem (T : Nonplanar α) (F : Forest (Nonplanar α))
    (hT : T ∈ F) (a : α) : T.depth < (Nonplanar.node a F).depth := by
  obtain ⟨ps, hps⟩ := exists_planar_list_rep F
  subst hps
  rw [Nonplanar.node_mk_tree_list]
  show T.depth < (RoseTree.node a ps).depth
  rw [RoseTree.depth_node]
  rw [show (Multiset.ofList (ps.map Nonplanar.mk) : Forest (Nonplanar α)) =
        ((ps.map Nonplanar.mk : List (Nonplanar α)) : Multiset _) from rfl,
      Multiset.mem_coe, List.mem_map] at hT
  obtain ⟨c, hc, rfl⟩ := hT
  show (Nonplanar.mk c).depth < 1 + (ps.map RoseTree.depth).foldr max 0
  rw [Nonplanar.depth_mk, Nat.add_comm]
  exact Nat.lt_succ_of_le (RoseTree.depth_le_foldr_max hc)

/-! ### Counit ⊗ id commutation with `lTensor (bPlusLin a)`

The factor-wise commutation `(counit ⊗ id) ∘ (id ⊗ B+_a) = (id ⊗ B+_a) ∘ (counit ⊗ id)`
(where the right `id` is on different domains: `H` on the left, `R` on the right).
Pure `TensorProduct.induction_on` calculation; both sides reduce to
`counit x ⊗ B+_a y` on simple tensors. Used in the tree-level counit law and
in the bPlus closure proof. -/

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

/-! ### Symmetric: id ⊗ counit commutation with `lTensor (bPlusLin a)`

Mirror of `counit_rTensor_lTensor_bPlus_apply`. Acting on the right factor with
counit and on the left factor with B+_a — they don't interact. -/

private theorem counit_lTensor_lTensor_bPlus_apply (a : α)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R)))
      ((LinearMap.rTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.rTensor R (bPlusLin (R := R) a))
      ((Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        LinearMap.rTensor_tmul]
  | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

/-! ### Tree-level counit law (depth induction)

`(counit ⊗ id)(Δ T) = 1 ⊗ T` for every nonplanar tree `T`. Strong induction
on `T.depth`: leaves close directly via `comulTreeN_leaf`; nodes use the
cocycle `comulTreeN_node_cocycle`, the commutation
`counit_rTensor_lTensor_bPlus_apply`, and the forest law on the children. -/

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
  -- Strong induction on T.depth.
  suffices aux : ∀ n : ℕ, ∀ T : Nonplanar α, T.depth = n →
      (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
          (counit (R := R)))
        (comulTreeN T) = ofTree T ⊗ₜ (1 : R) by
    exact aux T.depth T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n _IH =>
    intro T _hT
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

Strategy: reduce to `of' F` via `ConnesKreimer.algHom_ext`. For each `F`, expand
`comulAlgHomN (of' F) = comulForestN F` via `comulForestN_eq_sum`, then identify
the unique cut summand `(0, F) ∈ cutForestSummandsN F` (the "all empty cuts"
tuple). Other summands have `pf.1.card > 0`, so `counit (of' pf.1) = 0` and
`(counit ⊗ id)` kills them. The surviving `(0, F)` summand contributes
`1 ⊗ of' F = (lid).symm (of' F)`.

Helper lemmas needed (substantive):
* `mem_cutSummandsN_zero (T : Nonplanar α) : (0, T) ∈ cutSummandsN T` — the empty
  cut exists at every tree.
* `cutForestSummandsN_zero_mem (F : Forest (Nonplanar α)) : (0, F) ∈ cutForestSummandsN F`.
* `cutForestSummandsN_pos_pi : ∀ pf ∈ cutForestSummandsN F, pf ≠ (0, F) → pf.1.card > 0`. -/

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

