import Linglib.Core.Algebra.ConnesKreimer.AugmentedCut
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Double Cuts on Decorated Trees @cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

The cuts-of-cuts coassociativity proof for `comul_coassoc_tree` (M-C-B
Lemma 1.2.10 / @cite{foissy-2002} §2) needs a uniform indexing for the
two iterated coproducts:

  (Δ^c ⊗ id) ∘ Δ^c (forestToHc {T})    -- "LHS"
  (id ⊗ Δ^c) ∘ Δ^c (forestToHc {T})    -- "RHS"

Both expand into sums of triple-tensors `(BOT ⊗ MID ⊗ TOP)` indexed by
"double cuts" of `T` — equivalently, 3-level partitions of T's vertices
where each root-to-leaf path is monotone (`Top ≤ Mid ≤ Bot`).

This file uses the **right-iterated form** (which directly matches the
RHS structure):

  DoubleCut T := (Σ C : CutShape T, AugCutShape (remainder C)) ⊕ Unit

- `Sum.inl ⟨C, ac₂⟩` (`DoubleCut.real`): outer cut `C` (separating
  `BOT` from `MID + TOP`), then augmented inner cut `ac₂` on
  `remainder C` (separating `MID` from `TOP`).
- `Sum.inr ()` (`DoubleCut.extractWhole`): the trivial double cut where
  the entire tree T is at `BOT` (mirroring `AugCutShape.extractWhole`
  at the outer level).

The bijection with the LHS-style indexing (the substantive Foissy
content) is deferred to a subsequent file.

## Layer status

`[UPSTREAM]` candidate, paired with `AugmentedCut.lean` and
`Bialgebra.lean`. Future home is something like
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.DoubleCut`.
-/

namespace ConnesKreimer

open scoped TensorProduct
open Finsupp

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## §1: `DoubleCut T` — right-iterated cut data -/

/-- A double cut on a tree `T`: either an outer real cut `C` together
    with an augmented inner cut on `remainder C`, or the trivial
    "extract whole" double cut at the outer level.

    `abbrev` so mathlib's `Sum.fintype` and `Sigma.fintype` (via
    `instFintypeSigma`) apply automatically. -/
abbrev DoubleCut (T : DecoratedTree α) : Type _ :=
  (Σ C : CutShape T, AugCutShape (CutShape.remainder C)) ⊕ Unit

namespace DoubleCut

/-- An outer real cut `C` paired with an augmented inner cut on
    `remainder C`. The triple-tensor is
    `(cutForest C) ⊗ (extracted by ac₂) ⊗ (remainder of ac₂)`. -/
abbrev real {T : DecoratedTree α} (C : CutShape T)
    (ac₂ : AugCutShape (CutShape.remainder C)) : DoubleCut T :=
  Sum.inl ⟨C, ac₂⟩

/-- The trivial double cut: the entire tree at `BOT`. The triple-tensor
    is `forestToHc {T} ⊗ 1 ⊗ 1` (mirroring `AugCutShape.extractWhole`
    at the outer level). -/
abbrev extractWhole {T : DecoratedTree α} : DoubleCut T := Sum.inr ()

/-- The triple-tensor associated with a double cut, in the right-iterated
    form `(Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))`. Mirrors the structure
    of `(id ⊗ Δ^c) ∘ Δ^c (forestToHc {T})`:
    - LEFT slot: `forestToHc (cutForest C)` (the outer extracted forest)
    - MIDDLE slot: `forestToHc (cutForest_aug ac₂)` (the inner extracted)
    - RIGHT slot: `forestToHc (remainderForest ac₂)` (the final remainder)

    For `extractWhole`: triple is `forestToHc {T} ⊗ 1 ⊗ 1` (with both `1`s
    being `forestToHc 0`). -/
noncomputable def tripleTensor (R : Type*) [CommSemiring R]
    {T : DecoratedTree α} : DoubleCut T → (Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))
  | .inl ⟨C, ac₂⟩ =>
      forestToHc (R := R) (CutShape.cutForest C)
        ⊗ₜ[R] (forestToHc (R := R) (AugCutShape.cutForest_aug ac₂)
                ⊗ₜ[R] forestToHc (R := R) (AugCutShape.remainderForest ac₂))
  | .inr _ =>
      forestToHc (R := R) ({T} : Forest α)
        ⊗ₜ[R] (forestToHc (R := R) (0 : Forest α)
                ⊗ₜ[R] forestToHc (R := R) (0 : Forest α))

@[simp] lemma tripleTensor_real {T : DecoratedTree α} (C : CutShape T)
    (ac₂ : AugCutShape (CutShape.remainder C)) :
    tripleTensor R (real C ac₂)
      = forestToHc (R := R) (CutShape.cutForest C)
          ⊗ₜ[R] (forestToHc (R := R) (AugCutShape.cutForest_aug ac₂)
                  ⊗ₜ[R] forestToHc (R := R) (AugCutShape.remainderForest ac₂)) := rfl

@[simp] lemma tripleTensor_extractWhole {T : DecoratedTree α} :
    tripleTensor R (extractWhole : DoubleCut T)
      = forestToHc (R := R) ({T} : Forest α)
          ⊗ₜ[R] (forestToHc (R := R) (0 : Forest α)
                  ⊗ₜ[R] forestToHc (R := R) (0 : Forest α)) := rfl

end DoubleCut

/-! ## §2: RHS expansion as sum over `DoubleCut T`

The "easier direction" of the cuts-of-cuts bijection: the right-iterated
coproduct `(id ⊗ Δ^c) ∘ Δ^c (forestToHc {T})` reorganizes term-by-term
into a sum over `DoubleCut T`.

This direction is straightforward because `DoubleCut T` is **defined**
to mirror the RHS structure. The substantive content is the LHS direction
(deferred), where we'll need to expand `comulForest (cutForest_aug ac₁)`
as a multi-tree product. -/

/-- The RHS of `comul_coassoc_tree` reorganized as a single sum over
    double cuts. -/
theorem rhs_eq_sum_DoubleCut (T : DecoratedTree α) :
    (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom)
        (comulTree T : Hc R α ⊗[R] Hc R α)
      = ∑ dc : DoubleCut T, dc.tripleTensor R := by
  -- Step 1: expand comulTree T as a sum over AugCutShape T
  rw [comulTree_eq_sum_AugCutShape T]
  -- Step 2: distribute (map id Δ) over the sum
  rw [map_sum]
  -- Step 3: each summand becomes (id ⊗ Δ)(forestToHc x ⊗ forestToHc y)
  --       = forestToHc x ⊗ Δ(forestToHc y)
  --       = forestToHc x ⊗ comulForest y
  -- Step 4: split over Sum (real vs extractWhole), then identify with DoubleCut
  -- Right side: ∑ dc, dc.tripleTensor R, split via Fintype.sum_sum_type
  -- and Fintype.sum_sigma to break apart Sum + Sigma structure.
  rw [Fintype.sum_sum_type]
  -- RHS now has 2 parts: (∑_(p : Σ C, AugCutShape (rem C)), ...) + (∑_(_ : Unit), ...)
  -- LHS still has 1 sum over AugCutShape T = (CutShape T) ⊕ Unit
  rw [Fintype.sum_sum_type]
  -- LHS now has 2 parts: (∑_(C : CutShape T), ...) + (∑_(_ : Unit), ...)
  congr 1
  · -- Real-cut part: ∑_C (id ⊗ Δ)(forestToHc (cutForest C) ⊗ forestToHc {remainder C})
    -- = ∑_C forestToHc (cutForest C) ⊗ comulForest {remainder C}
    -- = ∑_C forestToHc (cutForest C) ⊗ comulTree (remainder C)
    -- = ∑_C forestToHc (cutForest C) ⊗ (∑_(ac2 : AugCutShape (rem C)) ...)
    -- vs RHS: ∑_(p : Σ C, AugCutShape (rem C)) tripleTensor (real p.1 p.2)
    --       = ∑_C ∑_(ac2 : AugCutShape (rem C)) tripleTensor (real C ac2)
    -- Use Fintype.sum_sigma (additive) to split RHS Σ-sum.
    rw [show (∑ p : Σ C : CutShape T, AugCutShape (CutShape.remainder C),
              DoubleCut.tripleTensor R (DoubleCut.real p.1 p.2))
            = ∑ C : CutShape T, ∑ ac2 : AugCutShape (CutShape.remainder C),
                DoubleCut.tripleTensor R (DoubleCut.real C ac2) from
          Fintype.sum_sigma _]
    -- Each LHS summand: (id ⊗ Δ)(forestToHc (cutForest C) ⊗ forestToHc {remainder C})
    --                 = forestToHc (cutForest C) ⊗ comulForest {remainder C}
    refine Finset.sum_congr rfl (fun C _ => ?_)
    -- Goal: (map id Δ)(forestToHc (cutForest C) ⊗ forestToHc {remainder C})
    --     = ∑ ac2, tripleTensor R (real C ac2)
    show (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom)
            ((forestToHc (R := R) (CutShape.cutForest C)
              ⊗ₜ[R] forestToHc (R := R) ({CutShape.remainder C} : Forest α))
              : Hc R α ⊗[R] Hc R α)
        = ∑ ac2 : AugCutShape (CutShape.remainder C),
            DoubleCut.tripleTensor R (DoubleCut.real C ac2)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    -- Goal: forestToHc (cutForest C) ⊗ Δ(forestToHc {remainder C})
    --     = ∑ ac2, ...
    -- comulAlgHom (forestToHc {remainder C}) = comulForest {remainder C} = comulTree (remainder C)
    have hΔ : comulAlgHom (forestToHc (R := R) ({CutShape.remainder C} : Forest α))
            = comulTree (CutShape.remainder C) := by
      show comulAlgHom (Finsupp.single ({CutShape.remainder C} : Forest α) (1 : R))
         = comulTree (CutShape.remainder C)
      rw [comulAlgHom_apply_single]
      -- comulForest {x} = comulTree x via Multiset.map_singleton + prod_singleton
      unfold comulForest
      simp only [Multiset.map_singleton, Multiset.prod_singleton]
    rw [hΔ, comulTree_eq_sum_AugCutShape]
    -- Goal: forestToHc (cutForest C) ⊗ (∑ ac2, forestToHc (cutForest_aug ac2) ⊗ forestToHc (remainderForest ac2))
    --     = ∑ ac2, forestToHc (cutForest C) ⊗ forestToHc (cutForest_aug ac2) ⊗ forestToHc (remainderForest ac2)
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun ac2 _ => ?_)
    rfl
  · -- Unit (extractWhole) part:
    -- LHS: ∑ () : Unit, (id ⊗ Δ)(forestToHc {T} ⊗ forestToHc 0)
    -- RHS: ∑ () : Unit, tripleTensor R (extractWhole) = forestToHc {T} ⊗ (forestToHc 0 ⊗ forestToHc 0)
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    -- Compute LHS at the unique unit point:
    show (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom)
            ((forestToHc (R := R) (AugCutShape.cutForest_aug
                (Sum.inr () : AugCutShape T))
              ⊗ₜ[R] forestToHc (R := R) (AugCutShape.remainderForest
                (Sum.inr () : AugCutShape T)))
              : Hc R α ⊗[R] Hc R α)
        = DoubleCut.tripleTensor R (DoubleCut.extractWhole : DoubleCut T)
    simp only [AugCutShape.cutForest_aug_extractWhole,
               AugCutShape.remainderForest_extractWhole,
               DoubleCut.tripleTensor_extractWhole]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    -- Goal: forestToHc {T} ⊗ Δ(forestToHc 0) = forestToHc {T} ⊗ (forestToHc 0 ⊗ forestToHc 0)
    -- Δ(forestToHc 0) = Δ(1) = 1 = forestToHc 0 ⊗ forestToHc 0
    have h1 : (forestToHc (R := R) (0 : Forest α) : Hc R α) = 1 := by
      show (Finsupp.single (0 : Forest α) (1 : R) : AddMonoidAlgebra R (Forest α))
         = (1 : AddMonoidAlgebra R (Forest α))
      exact AddMonoidAlgebra.one_def.symm
    rw [h1, map_one, Algebra.TensorProduct.one_def]

/-! ## §3: LHS expansion as sum over `DoubleCut T`

The "harder direction" of the cuts-of-cuts bijection: the left-iterated
coproduct `assoc ∘ (Δ^c ⊗ id) ∘ Δ^c (forestToHc {T})` reorganizes
term-by-term into the same sum over `DoubleCut T` as the RHS.

A "double cut" admits two natural enumerations (right-iterated and
left-iterated); the bijection identifies them with the same triple-tensor.

**Status**:
- Generic primitive coassoc: ✅ `comul_coassoc_of_primitive`.
- Wrapper for primitive trees (leaf, trace): ✅ `lhs_eq_sum_DoubleCut_of_primitive_tree`.
- Leaf and trace cases of `lhs_eq_sum_DoubleCut`: ✅.
- Node case of `lhs_eq_sum_DoubleCut`: ⏳ sorry. The substantive Foissy
  content; uses `comulForest_eq_sum_sections` + the `AugCutShape (.node l r) ≅
  AugCutShape l × AugCutShape r ⊎ Unit` decomposition. Estimated 200-300 LOC. -/

/-! ### Generic primitive coassoc

For any `y : Hc R α` whose comul has the **primitive form**
`Δ y = y ⊗ 1 + 1 ⊗ y`, coassoc holds automatically by direct computation.
This handles the leaf and trace cases of `lhs_eq_sum_DoubleCut`. -/

/-- If `comulAlgHom y = y ⊗ 1 + 1 ⊗ y` (primitive form), then iterated
    coproduct coassoc holds for `y`. The classical "primitive elements
    satisfy coassoc" fact, applied to our `Hc R α` coalgebra. -/
lemma comul_coassoc_of_primitive (y : Hc R α)
    (hPrim : comulAlgHom (R := R) (α := α) y = y ⊗ₜ[R] 1 + 1 ⊗ₜ[R] y) :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
          (AlgHom.id R (Hc R α))) (comulAlgHom y))
      = (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom)
          (comulAlgHom y) := by
  rw [hPrim]
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one]
  rw [hPrim]
  simp only [Algebra.TensorProduct.one_def, TensorProduct.add_tmul,
             TensorProduct.tmul_add, map_add]
  abel

/-- If `comulTree T` has the primitive form `forestToHc {T} ⊗ 1 + 1 ⊗ forestToHc {T}`
    (as for leaf and trace trees), then the LHS direction of the cuts-of-cuts
    bijection holds for `T`. Composes `comul_coassoc_of_primitive` with the
    `comulAlgHom (forestToHc {T}) = comulTree T` bridge and `rhs_eq_sum_DoubleCut`. -/
lemma lhs_eq_sum_DoubleCut_of_primitive_tree (T : DecoratedTree α)
    (hPrim : (comulTree (R := R) T : Hc R α ⊗[R] Hc R α)
           = forestToHc (R := R) ({T} : Forest α) ⊗ₜ[R] (1 : Hc R α)
             + (1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T} : Forest α)) :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
          (AlgHom.id R (Hc R α))) (comulTree T : Hc R α ⊗[R] Hc R α))
      = ∑ dc : DoubleCut T, dc.tripleTensor R := by
  rw [← rhs_eq_sum_DoubleCut]
  -- Bridge: comulTree T = comulAlgHom (forestToHc {T})
  have hbridge : (comulTree (R := R) T : Hc R α ⊗[R] Hc R α)
               = comulAlgHom (forestToHc (R := R) ({T} : Forest α)) := by
    show (comulTree T : Hc R α ⊗[R] Hc R α)
       = comulAlgHom (Finsupp.single ({T} : Forest α) (1 : R))
    rw [comulAlgHom_apply_single]
    show comulTree T = ((({T} : Forest α).map (comulTree (R := R))).prod : Hc R α ⊗[R] Hc R α)
    rw [Multiset.map_singleton, Multiset.prod_singleton]
  rw [hbridge]
  apply comul_coassoc_of_primitive
  rw [← hbridge]
  exact hPrim

/-! ### LHS direction of the cuts-of-cuts bijection -/

/-- LHS direction of the cuts-of-cuts bijection: the left-iterated
    coproduct on a single-tree workspace, after the canonical associator,
    reorganizes as a sum over `DoubleCut T`.

    Cases on `T`:
    - `.leaf`: primitive (only the trivial cut) → apply
      `lhs_eq_sum_DoubleCut_of_primitive_tree`.
    - `.trace`: same as leaf (also only the trivial cut).
    - `.node l r`: substantive Foissy "cut-commutation" bijection;
      currently sorry.

    Plan for the deferred `.node` case (a "less clunky" version of the
    legacy 1500-LOC list-based proof):
    Use the multiplicative AugCutShape decomposition
    `AugCutShape (.node l r) ≅ AugCutShape l × AugCutShape r ⊎ Unit`
    and `Multiset.Sections` for multi-tree expansion (already in place).
    The bijection between LHS-natural data `(ac₁, section)` and `DoubleCut T`
    is the cut-commutation core: a "double cut" admits two enumerations
    (outer-then-sub-on-extracted vs outer-then-sub-on-remainder), and the
    bijection identifies them. Estimated 200-300 LOC. -/
theorem lhs_eq_sum_DoubleCut (T : DecoratedTree α) :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
          (AlgHom.id R (Hc R α))) (comulTree T : Hc R α ⊗[R] Hc R α))
      = ∑ dc : DoubleCut T, dc.tripleTensor R := by
  match T with
  | .leaf a =>
    apply lhs_eq_sum_DoubleCut_of_primitive_tree
    rw [comulTree_eq_sum_AugCutShape, Fintype.sum_sum_type,
        show (Finset.univ : Finset (CutShape (.leaf a))) = {CutShape.atLeaf} from rfl,
        Finset.sum_singleton, Fintype.sum_unique]
    simp only [AugCutShape.cutForest_aug_real, AugCutShape.remainderForest_real,
               CutShape.cutForest_atLeaf, CutShape.remainder_atLeaf, forestToHc_zero]
    abel
  | .trace t =>
    apply lhs_eq_sum_DoubleCut_of_primitive_tree
    rw [comulTree_eq_sum_AugCutShape, Fintype.sum_sum_type,
        show (Finset.univ : Finset (CutShape (.trace t))) = {CutShape.atTrace} from rfl,
        Finset.sum_singleton, Fintype.sum_unique]
    simp only [AugCutShape.cutForest_aug_real, AugCutShape.remainderForest_real,
               CutShape.cutForest_atTrace, CutShape.remainder_atTrace, forestToHc_zero]
    abel
  | .node l r =>
    sorry

end ConnesKreimer
