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
where each root-to-leaf path is monotone in the **child ≤ parent** sense:
`bot ≤ mid ≤ top`, with the root at `top` and BOT vertices deepest.

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

The leaf and trace cases dispatch via `comul_coassoc_of_primitive`. The
substantive `.node` case is `lhsMultiset_eq_rhsMultiset_node` (currently
`sorry` — the @cite{foissy-2002} cut-commutation content). -/

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

/-! ### §3a: `lhsMultiset` — the LHS as a `Multiset.sum`

For the substantive `.node` case of `lhs_eq_sum_DoubleCut`, we re-express the LHS
as a sum over `(ac, section)` pairs via `comulForest_eq_sum_sections`. Each pair
indexes a triple-tensor in `Hc ⊗ (Hc ⊗ Hc)`. The cuts-of-cuts bijection
(future sub-sessions) will identify this multiset with the `DoubleCut`-indexed
multiset on the RHS. -/

/-- The LHS-side multiset of triple-tensors. Each element is
    `assoc(s.prod ⊗ forestToHc(remainderForest ac))` for some
    `(ac : AugCutShape T, s ∈ Sections((cutForest_aug ac).map comulTreeMS))`.
    Outer bind iterates over `ac`; inner map iterates over the multiset of
    sections. Multiplicity matters — same as `Sections` produces. -/
noncomputable def lhsMultiset (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (AugCutShape T)).val.bind fun ac =>
    (Multiset.Sections ((AugCutShape.cutForest_aug ac).map (comulTreeMS R))).map fun s =>
      (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        (s.prod ⊗ₜ[R] forestToHc (R := R) (AugCutShape.remainderForest ac))

/-- `(Multiset.sum) ⊗ y = Multiset.sum (map (· ⊗ y))`. Tensor product on the
    left distributes over a multiset sum.

    Generic helper; mathlib-PR-able. Lives in `_root_.TensorProduct` (not
    `ConnesKreimer.TensorProduct`) so the namespace matches mathlib's. -/
theorem _root_.TensorProduct.sum_tmul_multiset {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (s : Multiset M) (y : N) :
    (s.sum : M) ⊗ₜ[R] y = (s.map (fun x => x ⊗ₜ[R] y)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [_root_.TensorProduct.zero_tmul]
  | cons x xs ih => simp [Multiset.sum_cons, _root_.TensorProduct.add_tmul, ih]

/-- LHS reduction: `assoc((map Δ id)(comulTree T)) = (lhsMultiset T).sum`.

    The proof distributes the algebra-hom maps `(map Δ id)` and `assoc` over
    the `AugCutShape`-indexed sum from `comulTree_eq_sum_AugCutShape`, then
    applies `comulForest_eq_sum_sections` per outer cut to expand into
    `Sections`. Combines via `Multiset.sum_bind`. -/
theorem lhs_eq_sum_lhsMultiset (T : DecoratedTree α) :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
          (AlgHom.id R (Hc R α))) (comulTree T : Hc R α ⊗[R] Hc R α))
      = (lhsMultiset T).sum := by
  rw [comulTree_eq_sum_AugCutShape T]
  rw [map_sum, map_sum]
  unfold lhsMultiset
  rw [Multiset.sum_bind, ← Finset.sum_eq_multiset_sum]
  refine Finset.sum_congr rfl fun ac _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  have hcomul : comulAlgHom (forestToHc (R := R) (AugCutShape.cutForest_aug ac))
              = comulForest (R := R) (AugCutShape.cutForest_aug ac) := by
    show comulAlgHom (Finsupp.single _ (1 : R)) = _
    rw [comulAlgHom_apply_single]
  rw [hcomul, comulForest_eq_sum_sections, TensorProduct.sum_tmul_multiset]
  -- Now: assoc((Sections.map prod).map (·⊗ y)).sum = (Sections.map (...)).sum
  rw [map_multiset_sum]
  simp only [Multiset.map_map, Function.comp_def]

/-! ### §3b: `lhsMultiset` decomposition by AugCutShape ctor

`AugCutShape T = CutShape T ⊕ Unit`. Splitting the bind by ctor isolates the
`extractWhole_T` contribution (a single `ac` summand whose section is over `{T}`)
from the `real C` contributions (a bind over `CutShape T`). -/

/-- The "extract whole T" contribution to `lhsMultiset`: sections over the
    singleton workspace `{T}.map comulTreeMS`. Each section is a singleton
    `{x}` for `x ∈ comulTreeMS T`, so this multiset has `|AugCutShape T|`
    elements. -/
noncomputable def lhsExtractWhole (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Multiset.Sections (({T} : Forest α).map (comulTreeMS R))).map fun s =>
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
      (s.prod ⊗ₜ[R] forestToHc (R := R) (0 : Forest α))

/-- The "real cuts" contributions to `lhsMultiset`: for each `C : CutShape T`,
    sections over the multi-tree forest `(cutForest C).map comulTreeMS`.
    Outer bind iterates over `C`. -/
noncomputable def lhsRealCuts (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (CutShape T)).val.bind fun C =>
    (Multiset.Sections ((CutShape.cutForest C).map (comulTreeMS R))).map fun s =>
      (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        (s.prod ⊗ₜ[R] forestToHc (R := R) ({CutShape.remainder C} : Forest α))

/-- `lhsMultiset T = lhsRealCuts T + lhsExtractWhole T`. Decomposes the bind
    over `AugCutShape T = CutShape T ⊕ Unit` into its two halves. -/
theorem lhsMultiset_decomp (T : DecoratedTree α) :
    (lhsMultiset T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = lhsRealCuts T + lhsExtractWhole T := by
  unfold lhsMultiset lhsRealCuts lhsExtractWhole
  -- AugCutShape T = CutShape T ⊕ Unit, so univ.val = (univ_CutShape).val.map Sum.inl + {Sum.inr ()}
  rw [show ((Finset.univ : Finset (CutShape T ⊕ Unit)).val)
        = (Finset.univ : Finset (CutShape T)).val.map Sum.inl
          + (Finset.univ : Finset Unit).val.map Sum.inr from rfl]
  rw [Multiset.add_bind]
  congr 1
  · rw [Multiset.bind_map]
    rfl
  · -- (univ : Finset Unit).val.map Sum.inr = {Sum.inr ()}
    show (({()} : Multiset Unit).map Sum.inr).bind _ = _
    rw [Multiset.map_singleton, Multiset.singleton_bind]
    rfl

/-- Closed form for `lhsExtractWhole T`: the sections over `{T}.map comulTreeMS`
    are precisely the singletons indexed by `AugCutShape T`, so the resulting
    multiset is `(univ : Finset (AugCutShape T)).val.map (fun ac' => ...)`.

    The shape of each element matches the `tripleTensor` of either
    `DoubleCut.extractWhole` (when ac' = extractWhole) or
    `DoubleCut.real C extractWhole_(remainder C)` (when ac' = real C). -/
theorem lhsExtractWhole_eq (T : DecoratedTree α) :
    (lhsExtractWhole T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = (Finset.univ : Finset (AugCutShape T)).val.map fun ac' =>
          forestToHc (R := R) (AugCutShape.cutForest_aug ac')
            ⊗ₜ[R] (forestToHc (R := R) (AugCutShape.remainderForest ac')
              ⊗ₜ[R] forestToHc (R := R) (0 : Forest α)) := by
  unfold lhsExtractWhole
  rw [Multiset.map_singleton]
  -- Sections of a singleton list of multisets = bind structure.
  show (Multiset.Sections ((comulTreeMS R T) ::ₘ (0 : Multiset (Multiset _)))).map _ = _
  rw [Multiset.sections_cons, Multiset.sections_zero]
  show ((comulTreeMS R T).bind fun a => (({(0 : Multiset _)} : Multiset _).map (Multiset.cons a))).map _ = _
  -- {0}.map (cons a) = {a ::ₘ 0} = {{a}}
  simp only [Multiset.map_singleton]
  -- Now we have `(comulTreeMS R T).bind (fun a => {a ::ₘ 0})` ↦ map ↦ ...
  -- By Multiset.bind_singleton: bind a => {f a} = map f
  rw [Multiset.bind_singleton]
  -- Now: (comulTreeMS R T).map (fun a => a ::ₘ 0)).map (...)
  rw [Multiset.map_map]
  -- Now one combined map: (comulTreeMS R T).map (fun a => assoc((a ::ₘ 0).prod ⊗ ...))
  unfold comulTreeMS pairsMS
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun ac' _ => ?_
  -- Compute the composition
  simp only [Function.comp_apply, Multiset.prod_cons, Multiset.prod_zero, mul_one]
  rfl

/-! ### §3c: `rhsMultiset` — the RHS as a `Multiset` of `tripleTensor`s

The RHS sum `∑ dc, dc.tripleTensor R` is itself a `Multiset.sum` (via
`Finset.sum_eq_multiset_sum`). Naming the underlying multiset makes the
substantive bijection lemma `lhsMultiset = rhsMultiset` cleanly statable. -/

/-- The RHS-side multiset of triple-tensors: enumerate `DoubleCut T` and project
    each to its `tripleTensor`. -/
noncomputable def rhsMultiset (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (DoubleCut T)).val.map (·.tripleTensor R)

/-- The RHS Finset.sum equals the `rhsMultiset` Multiset.sum. -/
theorem rhs_eq_sum_rhsMultiset (T : DecoratedTree α) :
    (∑ dc : DoubleCut T, dc.tripleTensor R) = (rhsMultiset T).sum := by
  rw [Finset.sum_eq_multiset_sum]
  rfl

/-! ### §3d: `rhsMultiset` pieces by `DoubleCut` ctor

`DoubleCut T = (Σ C : CutShape T, AugCutShape (remainder C)) ⊕ Unit`. The Sigma
splits further by `ac₂ : AugCutShape (remainder C) = CutShape (remainder C) ⊕ Unit`,
giving 3 pieces:
- `rhsExtractWhole T`: from `DoubleCut.extractWhole`. Single element.
- `rhsRealExtractInner T`: from `DoubleCut.real C extractWhole` (ac₂ = extractWhole).
  One element per `C : CutShape T`.
- `rhsRealRealInner T`: from `DoubleCut.real C (real C₂)` (ac₂ = real C₂).
  Bind over `(C, C₂)`. -/

/-- The "outer extractWhole" contribution to rhsMultiset: a singleton for
    `DoubleCut.extractWhole`, with triple `forestToHc{T} ⊗ (1 ⊗ 1)`. -/
noncomputable def rhsExtractWhole (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  ({(DoubleCut.extractWhole : DoubleCut T).tripleTensor R} : Multiset _)

/-- The "outer real C, inner extractWhole" contribution: one triple per
    `C : CutShape T`. -/
noncomputable def rhsRealExtractInner (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (CutShape T)).val.map fun C =>
    (DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R

/-- The "outer real C, inner real C₂" contribution: bind over `(C, C₂)`. -/
noncomputable def rhsRealRealInner (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (CutShape T)).val.bind fun C =>
    (Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map fun C₂ =>
      (DoubleCut.real C (AugCutShape.real C₂)).tripleTensor R

/-! ### §3e: The "easy half" of the cuts-of-cuts bijection

The `extractWhole_T` outer cut on the LHS contributes one element per
`AugCutShape T` choice for the inner section. These exactly match the
`DoubleCut.extractWhole` (one element) plus `DoubleCut.real C extractWhole_(remainder C)`
(one element per `C : CutShape T`) entries on the RHS.

This is the "structural" half — no cut commutation needed; just `AugCutShape T`
splitting into `CutShape T ⊕ Unit`. -/

/-- **Easy half of the cuts-of-cuts bijection**: the LHS extractWhole-outer
    contribution matches the RHS extractWhole + (real C, extractWhole_inner)
    contributions. -/
theorem lhsExtractWhole_eq_rhsExtractWhole_add_realExtractInner (T : DecoratedTree α) :
    (lhsExtractWhole T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = rhsExtractWhole T + rhsRealExtractInner T := by
  rw [lhsExtractWhole_eq]
  unfold rhsExtractWhole rhsRealExtractInner
  -- AugCutShape T = CutShape T ⊕ Unit; split univ.val on Sum, then split the map.
  rw [show ((Finset.univ : Finset (AugCutShape T)).val)
        = (Finset.univ : Finset (CutShape T)).val.map Sum.inl
          + (Finset.univ : Finset Unit).val.map Sum.inr from rfl]
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  -- After splitting: `map (...) ∘ Sum.inl + map (...) ∘ Sum.inr = singleton + map ...`
  -- The maps reduce by rfl; just need to swap order.
  rw [add_comm]
  rfl

/-! The "substantive half" `lhsRealCuts T = rhsRealRealInner T` is proven via the
GeoCut chain: `(lhsRealCuts_eq_geoMultiset).trans (rhsRealRealInner_eq_geoMultiset).symm`.
That proof requires the GeoCut substrate (defined later); see the theorem in §3g
below (`lhsRealCuts_eq_rhsRealRealInner`). -/

/-- Helper: `rhsMultiset T` split by outer `DoubleCut = Σ ⊕ Unit` ctor. -/
private theorem rhsMultiset_split_outer (T : DecoratedTree α) :
    (rhsMultiset T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = ((Finset.univ : Finset (Σ C : CutShape T,
          AugCutShape (CutShape.remainder C))).val.map fun ⟨C, ac₂⟩ =>
            (DoubleCut.real C ac₂).tripleTensor R)
        + rhsExtractWhole T := by
  unfold rhsMultiset rhsExtractWhole
  rw [show ((Finset.univ : Finset (DoubleCut T)).val)
        = (Finset.univ : Finset (Σ C : CutShape T,
            AugCutShape (CutShape.remainder C))).val.map Sum.inl
          + (Finset.univ : Finset Unit).val.map Sum.inr from rfl]
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  rfl

/-- Helper: the per-`(C, ac₂)` Sigma sum, split by inner `AugCutShape = CutShape ⊕ Unit`. -/
private theorem rhsRealSigma_split_inner (T : DecoratedTree α) :
    ((Finset.univ : Finset (Σ C : CutShape T,
        AugCutShape (CutShape.remainder C))).val.map fun ⟨C, ac₂⟩ =>
          (DoubleCut.real C ac₂).tripleTensor R)
      = rhsRealRealInner T + rhsRealExtractInner T := by
  unfold rhsRealRealInner rhsRealExtractInner
  -- Step 1: re-express the Sigma univ as a bind over CutShape T.
  rw [show ((Finset.univ : Finset (Σ C : CutShape T,
              AugCutShape (CutShape.remainder C))).val)
        = (Finset.univ : Finset (CutShape T)).val.bind fun C =>
            (Finset.univ : Finset (AugCutShape (CutShape.remainder C))).val.map
              fun ac₂ => (⟨C, ac₂⟩ : Σ C : CutShape T,
                AugCutShape (CutShape.remainder C)) from rfl]
  -- Step 2: distribute outer map over the bind.
  rw [Multiset.map_bind]
  -- Step 3: per-C, split the inner univ (AugCutShape = CutShape ⊕ Unit) and distribute.
  -- Use Multiset.bind_congr to apply per-C transformations.
  rw [show (fun C : CutShape T =>
              ((Finset.univ : Finset (AugCutShape (CutShape.remainder C))).val.map
                (fun ac₂ => (⟨C, ac₂⟩ : Σ C : CutShape T,
                  AugCutShape (CutShape.remainder C)))).map
                (fun x => match x with | ⟨C, ac₂⟩ => (DoubleCut.real C ac₂).tripleTensor R))
          = fun C : CutShape T =>
              ((Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map fun C₂ =>
                (DoubleCut.real C (AugCutShape.real C₂)).tripleTensor R)
              + ({(DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R}
                : Multiset _) from ?_]
  · -- Now bind over `f + g` distributes via `Multiset.bind_add`.
    rw [show (fun C : CutShape T =>
              ((Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map fun C₂ =>
                (DoubleCut.real C (AugCutShape.real C₂)).tripleTensor R)
              + ({(DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R}
                : Multiset _))
            = fun C : CutShape T =>
              (((Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map fun C₂ =>
                (DoubleCut.real C (AugCutShape.real C₂)).tripleTensor R)
              + ({(DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R}
                : Multiset _)) from rfl]
    -- bind over `f + g` = bind f + bind g
    rw [show (Finset.univ : Finset (CutShape T)).val.bind
            (fun C => (((Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map fun C₂ =>
                  (DoubleCut.real C (AugCutShape.real C₂)).tripleTensor R)
                + ({(DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R}
                  : Multiset _)))
          = ((Finset.univ : Finset (CutShape T)).val.bind fun C =>
              (Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map fun C₂ =>
                (DoubleCut.real C (AugCutShape.real C₂)).tripleTensor R)
            + ((Finset.univ : Finset (CutShape T)).val.bind fun C =>
              ({(DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R}
                : Multiset _)) from Multiset.bind_add _ _ _]
    -- Second bind is bind over singletons = map.
    rw [show ((Finset.univ : Finset (CutShape T)).val.bind fun C =>
              ({(DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R}
                : Multiset _))
          = (Finset.univ : Finset (CutShape T)).val.map fun C =>
              (DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R from
        Multiset.bind_singleton _ _]
  · -- Per-C: (univ_AcS.map ⟨C,·⟩).map (match...) = univ_AcS.map (DoubleCut.real C ·).tripleTensor
    -- Then split AugCutShape (rem C) = CutShape (rem C) ⊕ Unit.
    funext C
    rw [Multiset.map_map]
    rw [show ((Finset.univ : Finset (AugCutShape (CutShape.remainder C))).val)
          = (Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map Sum.inl
            + (Finset.univ : Finset Unit).val.map Sum.inr from rfl]
    rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl

/-- `rhsMultiset` decomposition: the 3-way split by `DoubleCut` ctor structure.
    `DoubleCut T = (Σ C, AugCutShape (rem C)) ⊕ Unit`; the Sigma further splits
    via `ac₂ : AugCutShape (rem C) = CutShape (rem C) ⊕ Unit`. -/
theorem rhsMultiset_decomp (T : DecoratedTree α) :
    (rhsMultiset T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = rhsExtractWhole T + rhsRealExtractInner T + rhsRealRealInner T := by
  rw [rhsMultiset_split_outer, rhsRealSigma_split_inner]
  abel

/-! `lhsMultiset_eq_rhsMultiset_node` is also moved to §3g (after the GeoCut
substrate), so the chain `lhsExtractWhole_eq_rhsExtractWhole_add_realExtractInner +
lhsRealCuts_eq_rhsRealRealInner + rhsMultiset_decomp` can complete via the
GeoCut bijections. -/

/-! ### §3f: `Layer` and `GeoCut` — the canonical "geometric double cut" type

`GeoCut T myL` represents a **monotone 3-coloring** of `T`'s vertices:
each vertex gets one of three layers (`top`, `mid`, `bot`), with the constraint
that child layers are `≤` their parent's layer. The root of `T` is colored
with `myL`.

The substantive cut-commutation lemma `lhsRealCuts T = rhsRealRealInner T`
then collapses to: both sides enumerate the same multiset of triple-tensors
indexed by `GeoCut T Layer.top` with `myL = Layer.top` (the "root in TOP"
subset, since `lhsRealCuts` excludes the outer-extractWhole case). -/

/-- Three layers for a "geometric double cut": `bot` (extracted at inner cut),
    `mid` (extracted at outer cut, kept by inner), `top` (kept in trunk).
    Carries `LinearOrder` via the order embedding into `Fin 3` —
    `bot < mid < top` matches the monotone child-`≤`-parent constraint. -/
inductive Layer
  | bot
  | mid
  | top
  deriving DecidableEq, Repr

namespace Layer

instance : Fintype Layer where
  elems := {Layer.bot, Layer.mid, Layer.top}
  complete := fun a => by cases a <;> decide

/-- Order-preserving embedding into `Fin 3`. Used to derive `LinearOrder`. -/
def toFin : Layer → Fin 3
  | .bot => 0
  | .mid => 1
  | .top => 2

theorem toFin_injective : Function.Injective toFin := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [toFin] at h)

instance : LinearOrder Layer := LinearOrder.lift' toFin toFin_injective

end Layer

/-- A geometric double cut on `T`: a monotone 3-coloring of `T`'s vertices.
    Indexed by the root vertex's layer `myL`. Children's layers must be `≤ myL`.

    **`.trace` constraint** (matches `IsNotTrace` in `CutShape`'s extracting
    constructors): when a child is a `.trace t` marker, its layer must EQUAL
    the parent's layer (not just `≤`). Reason: cuts can never separate a
    `.trace` from its enclosing maximal extracted subtree (per the substrate
    refactor 0.230.680), so in the GeoCut interpretation `.trace`'s layer
    is forced to match its surrounding context.

    For T = .leaf or .trace, only the root layer matters.
    For T = .node l r, the root has layer `myL`, and `l`, `r` have GeoCuts
    with their own root layers `lL`, `rL` satisfying `lL ≤ myL`, `rL ≤ myL`,
    plus the `.trace` constraint above. -/
inductive GeoCut : DecoratedTree α → Layer → Type _
  | leaf {a : α} (myL : Layer) : GeoCut (.leaf a) myL
  | trace {t : DecoratedTree α} (myL : Layer) : GeoCut (.trace t) myL
  | node {l r : DecoratedTree α} {myL lL rL : Layer}
      (hl : lL ≤ myL) (hr : rL ≤ myL)
      (hlNT : DecoratedTree.IsNotTrace l ∨ lL = myL)
      (hrNT : DecoratedTree.IsNotTrace r ∨ rL = myL)
      (gl : GeoCut l lL) (gr : GeoCut r rL) : GeoCut (.node l r) myL

/-! ### `Fintype (GeoCut T myL)`

Structural recursion on `T`:
- `.leaf` / `.trace`: `GeoCut` has a unique element (root layer is `myL`).
- `.node l r`: `GeoCut (.node l r) myL` is in bijection with
  `Σ (lL : {x // x ≤ myL}) (rL : {x // x ≤ myL}), GeoCut l lL.1 × GeoCut r rL.1`,
  which has `Fintype` via mathlib's `Sigma` / `Prod` / `Subtype` instances combined
  with the recursive `Fintype (GeoCut subtree _)`. -/

/-! ### `GeoCut.node` Sigma decomposition

The `GeoCut.node` constructor's data is exactly a Σ over (constrained) child layers
× per-child GeoCuts. Naming this Equiv lets us both derive `Fintype (GeoCut T myL)`
recursively (via `Fintype.ofEquiv`) AND decompose `Finset.univ : Finset (GeoCut .node ...)`
via `Finset.map_univ_equiv` downstream. -/

/-- Equivalence: `GeoCut (.node l r) myL ≃ Σ (lL, rL) constrained, GeoCut l × GeoCut r`.
    The constraint Subtype combines `lL ≤ myL` with the `IsNotTrace l ∨ lL = myL`
    `.trace`-layer match (and symmetrically for `rL`). -/
def nodeGeoCutEquiv (l r : DecoratedTree α) (myL : Layer) :
    (Σ (lL : {x : Layer // x ≤ myL ∧ (DecoratedTree.IsNotTrace l ∨ x = myL)})
       (rL : {x : Layer // x ≤ myL ∧ (DecoratedTree.IsNotTrace r ∨ x = myL)}),
      GeoCut l lL.1 × GeoCut r rL.1)
    ≃ GeoCut (.node l r) myL where
  toFun := fun ⟨lL, rL, gl, gr⟩ =>
    GeoCut.node lL.2.1 rL.2.1 lL.2.2 rL.2.2 gl gr
  invFun := fun g => match g with
    | .node hl hr hlNT hrNT gl gr =>
        ⟨⟨_, hl, hlNT⟩, ⟨_, hr, hrNT⟩, gl, gr⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun g => by cases g; rfl

/-- Recursive `Fintype` instance for `GeoCut T myL`. Mathlib pattern: declare
    as recursive `instance` directly (no `private def + wrapper`).
    - `.leaf` / `.trace`: 1 element via `Fintype.ofEquiv Unit`.
    - `.node l r`: `Fintype.ofEquiv` via `nodeGeoCutEquiv` (above), where the
      source's `Fintype` follows from the recursive IHs `Fintype (GeoCut l _)`,
      `Fintype (GeoCut r _)`. -/
instance instFintypeGeoCut : ∀ (T : DecoratedTree α) (myL : Layer),
    Fintype (GeoCut T myL)
  | .leaf _, myL =>
      Fintype.ofEquiv Unit
        { toFun := fun _ => GeoCut.leaf myL
          invFun := fun _ => ()
          left_inv := fun _ => rfl
          right_inv := fun g => by cases g; rfl }
  | .trace _, myL =>
      Fintype.ofEquiv Unit
        { toFun := fun _ => GeoCut.trace myL
          invFun := fun _ => ()
          left_inv := fun _ => rfl
          right_inv := fun g => by cases g; rfl }
  | .node l r, myL =>
      letI _ihl : ∀ lL, Fintype (GeoCut l lL) := instFintypeGeoCut l
      letI _ihr : ∀ rL, Fintype (GeoCut r rL) := instFintypeGeoCut r
      Fintype.ofEquiv _ (nodeGeoCutEquiv l r myL)

/-! ### `GeoCut` semantics — projecting to the triple-tensor

For each `g : GeoCut T myL` we extract three pieces:
- `geoBotForest g`: the BOT subtrees (extracted at the OUTER cut).
- `geoMidForest g`: the MID subtrees (extracted at the INNER cut, each represented as
  its outer-remainder skeleton — i.e., with its own BOT subtrees as `.trace` markers).
- `geoStackItem g`: the contribution this subtree makes to the **parent's** TOP slot.
  - `myL = .bot`: `.trace T` (the whole subtree is BOT-extracted; appears as a trace).
  - `myL = .mid`: `.trace T` (the whole subtree appears as a trace whose data is the
    original `T` — slot 3 only sees the outer cut, and the outer cut extracts T as
    a unit; T's MID-vs-BOT internal split is orthogonal).
  - `myL = .top`: recursive — for `.node l r`, becomes `.node (geoStackItem gl) (geoStackItem gr)`.

The triple is then `(geoBotForest g, geoMidForest g, {geoStackItem g})` — assembled
into `Hc ⊗ (Hc ⊗ Hc)` via `forestToHc` and `⊗ₜ`. For a top-rooted GeoCut on `T`
this matches the LHS-style triple from `lhsRealCuts T` (and the RHS-style from
`rhsRealRealInner T` after the substantive Foissy bijection). -/

/-- `T` with each BOT subtree replaced by a `.trace` marker carrying the cut
    subtree as data. (For `myL = .bot`, the whole `T` is BOT, becomes `.trace T`.) -/
def geoOuterSkeleton {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) :
    DecoratedTree α :=
  match myL, g with
  | .bot, _ => .trace T
  | .mid, .leaf _ => T
  | .mid, .trace _ => T
  | .mid, .node _ _ _ _ gl gr => .node (geoOuterSkeleton gl) (geoOuterSkeleton gr)
  | .top, .leaf _ => T
  | .top, .trace _ => T
  | .top, .node _ _ _ _ gl gr => .node (geoOuterSkeleton gl) (geoOuterSkeleton gr)

/-- The contribution this subtree makes to its **parent's** TOP slot — i.e., what
    appears at this subtree's position in the parent's slot-3 (outer-remainder) tree.
    - `myL ∈ {.bot, .mid}`: `.trace T` — the **whole** original subtree T as trace
      data. This matches the LHS-reading semantics: the outer cut extracts T as a
      unit (whether T's MID structure goes through inner-cut decomposition is
      orthogonal — slot 3 only sees the outer cut).
    - `myL = .top`: recursive — vertices kept at top form the structure; deeper
      BOT/MID positions become `.trace` via `geoStackItem` on subtrees. -/
def geoStackItem {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) :
    DecoratedTree α :=
  match myL, g with
  | .bot, _ => .trace T
  | .mid, _ => .trace T
  | .top, .leaf _ => T
  | .top, .trace _ => T
  | .top, .node _ _ _ _ gl gr => .node (geoStackItem gl) (geoStackItem gr)

/-- The BOT-slot forest contributed by this GeoCut: subtrees rooted at BOT vertices. -/
def geoBotForest {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) : Forest α :=
  match myL, g with
  | .bot, _ => ({T} : Forest α)
  | .mid, .leaf _ => 0
  | .mid, .trace _ => 0
  | .mid, .node _ _ _ _ gl gr => geoBotForest gl + geoBotForest gr
  | .top, .leaf _ => 0
  | .top, .trace _ => 0
  | .top, .node _ _ _ _ gl gr => geoBotForest gl + geoBotForest gr

/-- The MID-slot forest contributed by this GeoCut: each MID-rooted subtree
    contributes its outer-remainder skeleton (BOT positions become traces). -/
def geoMidForest {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) : Forest α :=
  match myL, g with
  | .bot, _ => 0
  | .mid, _ => ({geoOuterSkeleton g} : Forest α)
  | .top, .leaf _ => 0
  | .top, .trace _ => 0
  | .top, .node _ _ _ _ gl gr => geoMidForest gl + geoMidForest gr

/-- The triple-tensor extracted from a GeoCut. For a top-rooted GeoCut on `T`,
    this equals both the LHS-style triple from `lhsRealCuts` and the RHS-style
    triple from `rhsRealRealInner` (the substantive cuts-of-cuts identity). -/
noncomputable def geoCutToTriple (R : Type*) [CommSemiring R]
    {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) :
    (Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α)) :=
  forestToHc (R := R) (geoBotForest g) ⊗ₜ[R]
    (forestToHc (R := R) (geoMidForest g) ⊗ₜ[R]
      forestToHc (R := R) ({geoStackItem g} : Forest α))

/-- The "GeoCut multiset" on `T`: enumerate `GeoCut T Layer.top` and project each
    to its triple-tensor via `geoCutToTriple`. This is the canonical 3-coloring
    enumeration that both `lhsRealCuts T` and `rhsRealRealInner T` will be shown
    to factor through. -/
noncomputable def geoMultiset (T : DecoratedTree α) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (GeoCut T Layer.top)).val.map (geoCutToTriple R)

/-! ### Per-subtree "child slots": substrate for the .node bijection

A `ChildSlots α` triple `⟨BOT, MID, stack⟩` represents one subtree's contribution
to a parent's triple-tensor:
- `bot : Forest α` — subtrees of T that go to the BOT slot.
- `mid : Forest α` — subtrees of T (each as outer-skeleton) that go to the MID slot.
- `stack : DecoratedTree α` — what appears at T's position in the parent's slot-3 tree.

The triple-tensor for a subtree equals `forestToHc(bot) ⊗ (forestToHc(mid) ⊗ forestToHc({stack}))`.

For the .node l r bijection, both the LHS and the (any-layer) GeoCut enumerate
the SAME multiset of `ChildSlots` per subtree — this is the key inductive
hypothesis. -/

/-- Per-subtree child-slot data: the `(BOT, MID, stack)` triple in named-field form.
    `BOT`/`MID` are forests; `stack` is the single tree at this subtree's position
    in the parent's slot-3 tree. -/
structure ChildSlots (α : Type*) where
  bot   : Forest α
  mid   : Forest α
  stack : DecoratedTree α

/-- Project a GeoCut to its child-slot triple. -/
def geoToChildSlots {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) :
    ChildSlots α :=
  ⟨geoBotForest g, geoMidForest g, geoStackItem g⟩

/-- Convert a child-slot triple to its triple-tensor. -/
noncomputable def ChildSlots.toTriple (R : Type*) [CommSemiring R]
    (cs : ChildSlots α) : (Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α)) :=
  forestToHc (R := R) cs.bot ⊗ₜ[R]
    (forestToHc (R := R) cs.mid ⊗ₜ[R] forestToHc (R := R) ({cs.stack} : Forest α))

/-- `geoCutToTriple` factors as `ChildSlots.toTriple ∘ geoToChildSlots`. -/
theorem geoCutToTriple_eq {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) :
    geoCutToTriple R g = (geoToChildSlots g).toTriple R := rfl

/-- The "any-layer GeoCut child contribution" multiset on `T`: enumerate all
    `(myL, g : GeoCut T myL)` pairs and project each to its child slots. -/
noncomputable def geoCutAnyChildContrib (T : DecoratedTree α) :
    Multiset (ChildSlots α) :=
  (Finset.univ : Finset (Σ myL : Layer, GeoCut T myL)).val.map
    fun ⟨_, g⟩ => geoToChildSlots g

/-! ### Per-layer formulation of LHS child contribution

Following the mathlib-audit recommendation, the LHS-side child contribution on
`T` is split per-layer rather than per-case. The trichotomy "parent-extracts-with-extractWhole"
/ "parent-extracts-with-real-cl_inner" / "parent-recurses" IS the trichotomy
`Layer = bot/mid/top`. -/

/-- Per-layer LHS contribution at the subtree level.
- `.bot`: parent extracts T whole + inner = extractWhole. Single ChildSlots
  `⟨{T}, 0, .trace T⟩`.
- `.mid`: parent extracts T whole + inner = real cl_inner. One ChildSlots per
  `cl_inner ∈ CutShape T`: `⟨cutForest cl_inner, {remainder cl_inner}, .trace T⟩`.
- `.top`: parent recurses with `cl_outer ∈ CutShape T` + per-tree inner section.
  `⟨recursive BOT, recursive MID, remainder cl_outer⟩`. -/
noncomputable def perLayerContrib (T : DecoratedTree α) :
    Layer → Multiset (ChildSlots α)
  | .bot =>
      ({⟨({T} : Forest α), 0, .trace T⟩} : Multiset (ChildSlots α))
  | .mid =>
      (Finset.univ : Finset (CutShape T)).val.map fun cl_inner =>
        ⟨CutShape.cutForest cl_inner,
         ({CutShape.remainder cl_inner} : Forest α),
         .trace T⟩
  | .top =>
      (Finset.univ : Finset (CutShape T)).val.bind fun cl_outer =>
        (Multiset.Sections ((CutShape.cutForest cl_outer).map fun T' =>
          (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
            ((AugCutShape.cutForest_aug ac' : Forest α),
             (AugCutShape.remainderForest ac' : Forest α)))).map fun s =>
          ⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
           CutShape.remainder cl_outer⟩

/-- The LHS-side child contribution multiset on `T` (any-layer): bind of
    `perLayerContrib T` over `Layer`. Equals `geoCutAnyChildContrib T` (key IH). -/
noncomputable def lhsAnyChildContrib (T : DecoratedTree α) :
    Multiset (ChildSlots α) :=
  (Finset.univ : Finset Layer).val.bind (perLayerContrib T)

/-! ### Per-layer bijection sub-lemmas

Following the audit, split `lhsAnyChildContrib_eq_geoCutAny` into three smaller
per-layer equalities. The `.bot` and `.mid` cases reduce to direct multiset
computation; `.top` is the substantive recursive content. -/

omit [DecidableEq α] in
/-- All `g : GeoCut T .bot` give the same `ChildSlots`: `⟨{T}, 0, .trace T⟩`.
    Because for `myL = .bot` all the geo* helpers return the constant value
    determined by `T` alone. -/
theorem geoToChildSlots_bot {T : DecoratedTree α} (g : GeoCut T Layer.bot) :
    geoToChildSlots g = ⟨({T} : Forest α), 0, .trace T⟩ := by
  unfold geoToChildSlots geoBotForest geoMidForest geoStackItem
  rfl

/-- For `myL = .bot`, the layer constraint `lL ≤ .bot` forces `lL = .bot`. -/
private theorem Layer.le_bot_iff (lL : Layer) : lL ≤ Layer.bot ↔ lL = Layer.bot := by
  constructor
  · intro h; cases lL <;> first | rfl | (exact absurd h (by decide))
  · intro h; subst h; exact le_refl _

/-- The canonical "all-bot" GeoCut on T. -/
def botGeoCut : ∀ (T : DecoratedTree α), GeoCut T Layer.bot
  | .leaf _ => GeoCut.leaf Layer.bot
  | .trace _ => GeoCut.trace Layer.bot
  | .node l r =>
      GeoCut.node (le_refl _) (le_refl _) (Or.inr rfl) (Or.inr rfl)
        (botGeoCut l) (botGeoCut r)

omit [DecidableEq α] in
/-- Every `g : GeoCut T .bot` equals `botGeoCut T`. Combined with `Inhabited` via
    `botGeoCut`, gives `Unique (GeoCut T .bot)`. -/
theorem botGeoCut_unique : ∀ {T : DecoratedTree α} (g : GeoCut T Layer.bot),
    g = botGeoCut T
  | .leaf _, .leaf _ => rfl
  | .trace _, .trace _ => rfl
  | .node l r, .node hl hr _ _ gl gr => by
      have hlEq : (_ : Layer) = Layer.bot := (Layer.le_bot_iff _).mp hl
      have hrEq : (_ : Layer) = Layer.bot := (Layer.le_bot_iff _).mp hr
      subst hlEq; subst hrEq
      have el := botGeoCut_unique gl
      have er := botGeoCut_unique gr
      subst el; subst er
      rfl

instance instUniqueGeoCutBot (T : DecoratedTree α) : Unique (GeoCut T Layer.bot) where
  default := botGeoCut T
  uniq := botGeoCut_unique

/-- The `.bot` case: a single `ChildSlots ⟨{T}, 0, .trace T⟩`. -/
theorem perLayerContrib_bot (T : DecoratedTree α) :
    perLayerContrib (α := α) T .bot
      = (Finset.univ : Finset (GeoCut T Layer.bot)).val.map
          (fun g => geoToChildSlots g) := by
  -- LHS unfolds to {⟨{T}, 0, .trace T⟩}.
  -- RHS: univ has a unique element (botGeoCut T) via `instUniqueGeoCutBot`,
  -- so univ.val = {botGeoCut T}, mapped via geoToChildSlots → {⟨{T}, 0, .trace T⟩}.
  rw [show (Finset.univ : Finset (GeoCut T Layer.bot)).val
        = ({botGeoCut T} : Multiset _) by
       rw [show (Finset.univ : Finset (GeoCut T Layer.bot))
             = ({botGeoCut T} : Finset _) from
           Finset.eq_singleton_iff_unique_mem.mpr
             ⟨Finset.mem_univ _, fun g _ => botGeoCut_unique g⟩]
       rfl]
  rw [Multiset.map_singleton, geoToChildSlots_bot]
  rfl

/-! #### `midGeoCut`: bijection `CutShape T ≃ GeoCut T Layer.mid`

For each `cl_inner : CutShape T`, the corresponding `GeoCut T Layer.mid` represents
"T at MID with `cl_inner` determining the BOT-extraction within T". The bijection
preserves the (BOT, MID, stack) data: extracted subtrees → BOT, kept subtrees →
MID structure, T-vertex → MID. -/

/-- Forward: convert `cl_inner : CutShape T` to the corresponding `GeoCut T .mid`. -/
def midGeoCut : ∀ (T : DecoratedTree α), CutShape T → GeoCut T Layer.mid
  | .leaf _, .atLeaf => GeoCut.leaf Layer.mid
  | .trace _, .atTrace => GeoCut.trace Layer.mid
  | .node l r, .bothCut hl hr =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.mid)
        (by decide : Layer.bot ≤ Layer.mid)
        (Or.inl hl) (Or.inl hr) (botGeoCut l) (botGeoCut r)
  | .node l r, .onlyLeftCut hl cr_in =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.mid) (le_refl _)
        (Or.inl hl) (Or.inr rfl) (botGeoCut l) (midGeoCut r cr_in)
  | .node l r, .onlyRightCut hr cl_in =>
      GeoCut.node (le_refl _) (by decide : Layer.bot ≤ Layer.mid)
        (Or.inr rfl) (Or.inl hr) (midGeoCut l cl_in) (botGeoCut r)
  | .node l r, .bothRecurse cl_in cr_in =>
      GeoCut.node (le_refl _) (le_refl _) (Or.inr rfl) (Or.inr rfl)
        (midGeoCut l cl_in) (midGeoCut r cr_in)

/-- Inverse: convert `g : GeoCut T .mid` to the corresponding `CutShape T`. -/
def fromMidGeoCut : ∀ {T : DecoratedTree α}, GeoCut T Layer.mid → CutShape T
  | _, .leaf _ => CutShape.atLeaf
  | _, .trace _ => CutShape.atTrace
  | .node l r, .node hl hr hlNT hrNT gl gr => by
      -- Layer constraint: lL ≤ mid ⇒ lL ∈ {bot, mid}. Trace constraint: IsNotTrace l ∨ lL = mid.
      -- For each combination, dispatch to appropriate ctor.
      -- (lL=bot, rL=bot): bothCut. Requires IsNotTrace l, IsNotTrace r — extracted from hlNT/hrNT.
      -- (lL=bot, rL=mid): onlyLeftCut. Requires IsNotTrace l.
      -- (lL=mid, rL=bot): onlyRightCut. Requires IsNotTrace r.
      -- (lL=mid, rL=mid): bothRecurse.
      rename_i lL rL
      cases lL with
      | bot =>
        cases rL with
        | bot =>
          -- hlNT : IsNotTrace l ∨ bot = mid → IsNotTrace l (since bot ≠ mid).
          have hLT : DecoratedTree.IsNotTrace l := hlNT.resolve_right (by decide)
          have hRT : DecoratedTree.IsNotTrace r := hrNT.resolve_right (by decide)
          exact CutShape.bothCut hLT hRT
        | mid =>
          have hLT : DecoratedTree.IsNotTrace l := hlNT.resolve_right (by decide)
          exact CutShape.onlyLeftCut hLT (fromMidGeoCut gr)
        | top => exact absurd hr (by decide)
      | mid =>
        cases rL with
        | bot =>
          have hRT : DecoratedTree.IsNotTrace r := hrNT.resolve_right (by decide)
          exact CutShape.onlyRightCut hRT (fromMidGeoCut gl)
        | mid => exact CutShape.bothRecurse (fromMidGeoCut gl) (fromMidGeoCut gr)
        | top => exact absurd hr (by decide)
      | top => exact absurd hl (by decide)

/-! #### Helper lemmas: `geoToChildSlots ∘ midGeoCut` matches `(cutForest, {remainder}, .trace T)`. -/

omit [DecidableEq α] in
/-- For `myL = .mid`, `geoBotForest (midGeoCut T cl) = cutForest cl`. -/
theorem geoBotForest_midGeoCut : ∀ (T : DecoratedTree α) (cl : CutShape T),
    geoBotForest (midGeoCut T cl) = CutShape.cutForest cl
  | _, .atLeaf => rfl
  | _, .atTrace => rfl
  | .node _ _, .bothCut _ _ => by
      simp only [midGeoCut, geoBotForest, CutShape.cutForest]
      rfl
  | .node _ _, .onlyLeftCut _ cr_in => by
      have ih := geoBotForest_midGeoCut _ cr_in
      simp only [midGeoCut, geoBotForest, CutShape.cutForest, ih]
  | .node _ _, .onlyRightCut _ cl_in => by
      have ih := geoBotForest_midGeoCut _ cl_in
      simp only [midGeoCut, geoBotForest, CutShape.cutForest, ih]
  | .node _ _, .bothRecurse cl_in cr_in => by
      have ihl := geoBotForest_midGeoCut _ cl_in
      have ihr := geoBotForest_midGeoCut _ cr_in
      simp only [midGeoCut, geoBotForest, CutShape.cutForest, ihl, ihr]

omit [DecidableEq α] in
/-- For `myL = .mid`, `geoOuterSkeleton (midGeoCut T cl) = remainder cl`. -/
theorem geoOuterSkeleton_midGeoCut : ∀ (T : DecoratedTree α) (cl : CutShape T),
    geoOuterSkeleton (midGeoCut T cl) = CutShape.remainder cl
  | _, .atLeaf => rfl
  | _, .atTrace => rfl
  | .node _ _, .bothCut _ _ => by
      simp only [midGeoCut, geoOuterSkeleton, CutShape.remainder]
  | .node _ _, .onlyLeftCut _ cr_in => by
      have ih := geoOuterSkeleton_midGeoCut _ cr_in
      simp only [midGeoCut, geoOuterSkeleton, CutShape.remainder, ih]
  | .node _ _, .onlyRightCut _ cl_in => by
      have ih := geoOuterSkeleton_midGeoCut _ cl_in
      simp only [midGeoCut, geoOuterSkeleton, CutShape.remainder, ih]
  | .node _ _, .bothRecurse cl_in cr_in => by
      have ihl := geoOuterSkeleton_midGeoCut _ cl_in
      have ihr := geoOuterSkeleton_midGeoCut _ cr_in
      simp only [midGeoCut, geoOuterSkeleton, CutShape.remainder, ihl, ihr]

omit [DecidableEq α] in
/-- For `myL = .mid`, `geoMidForest (midGeoCut T cl) = {remainder cl}`. -/
theorem geoMidForest_midGeoCut (T : DecoratedTree α) (cl : CutShape T) :
    geoMidForest (midGeoCut T cl) = ({CutShape.remainder cl} : Forest α) := by
  -- For myL = mid, geoMidForest = ({geoOuterSkeleton g} : Forest α).
  rw [show geoMidForest (midGeoCut T cl)
        = ({geoOuterSkeleton (midGeoCut T cl)} : Forest α) by
       cases cl <;> rfl,
      geoOuterSkeleton_midGeoCut]

omit [DecidableEq α] in
/-- For `myL = .mid`, `geoStackItem (midGeoCut T cl) = .trace T`. -/
theorem geoStackItem_midGeoCut (T : DecoratedTree α) (cl : CutShape T) :
    geoStackItem (midGeoCut T cl) = .trace T := by
  -- For myL = mid, geoStackItem = .trace T always.
  cases cl <;> rfl

omit [DecidableEq α] in
/-- The combined fact: `geoToChildSlots (midGeoCut T cl)` matches the LHS triple. -/
theorem geoToChildSlots_midGeoCut (T : DecoratedTree α) (cl : CutShape T) :
    geoToChildSlots (midGeoCut T cl)
      = ⟨CutShape.cutForest cl, ({CutShape.remainder cl} : Forest α), .trace T⟩ := by
  unfold geoToChildSlots
  rw [geoBotForest_midGeoCut, geoMidForest_midGeoCut, geoStackItem_midGeoCut]

/-! #### Bijection: midGeoCut ↔ fromMidGeoCut

The forward (`midGeoCut`) and backward (`fromMidGeoCut`) directions are mutually
inverse on `.node l r`. Proofs by case analysis on the constructor + IH on
recursive sub-CutShapes / sub-GeoCuts. -/

omit [DecidableEq α] in
/-- Roundtrip 1: `fromMidGeoCut ∘ midGeoCut = id`. -/
theorem fromMidGeoCut_midGeoCut : ∀ (T : DecoratedTree α) (cl : CutShape T),
    fromMidGeoCut (midGeoCut T cl) = cl
  | _, .atLeaf => rfl
  | _, .atTrace => rfl
  | .node l r, .bothCut _ _ => rfl
  | .node l r, .onlyLeftCut _ cr_in => by
      show CutShape.onlyLeftCut _ (fromMidGeoCut (midGeoCut r cr_in)) = _
      rw [fromMidGeoCut_midGeoCut r cr_in]
  | .node l r, .onlyRightCut _ cl_in => by
      show CutShape.onlyRightCut _ (fromMidGeoCut (midGeoCut l cl_in)) = _
      rw [fromMidGeoCut_midGeoCut l cl_in]
  | .node l r, .bothRecurse cl_in cr_in => by
      show CutShape.bothRecurse (fromMidGeoCut (midGeoCut l cl_in))
                                (fromMidGeoCut (midGeoCut r cr_in)) = _
      rw [fromMidGeoCut_midGeoCut l cl_in, fromMidGeoCut_midGeoCut r cr_in]

omit [DecidableEq α] in
/-- Helper: when the `IsNotTrace ∨ lL = myL` disjunction's right disjunct is
    impossible (`lL ≠ myL`), it must equal `Or.inl ...`. Eliminates copy-paste
    in the `midGeoCut_fromMidGeoCut` dispatch. -/
private theorem trace_nt_eq_inl {T : DecoratedTree α} {lL myL : Layer}
    (h : DecoratedTree.IsNotTrace T ∨ lL = myL) (hne : lL ≠ myL) :
    h = Or.inl (h.resolve_right hne) := by
  rcases h with _ | hne'
  · rfl
  · exact absurd hne' hne

omit [DecidableEq α] in
/-- Roundtrip 2: `midGeoCut ∘ fromMidGeoCut = id`. Uses `botGeoCut_unique`
    for `gl/gr` at layer `.bot`, IH for `gl/gr` at layer `.mid`. -/
theorem midGeoCut_fromMidGeoCut : ∀ {T : DecoratedTree α} (g : GeoCut T Layer.mid),
    midGeoCut T (fromMidGeoCut g) = g
  | _, .leaf .mid => rfl
  | _, .trace .mid => rfl
  | .node l r, .node (lL := lL) (rL := rL) hl hr hlNT hrNT gl gr => by
      -- Dispatch by (lL, rL).
      cases lL with
      | top => exact absurd hl (by decide)
      | bot =>
        cases rL with
        | top => exact absurd hr (by decide)
        | bot =>
          have hlEq : gl = botGeoCut l := botGeoCut_unique gl
          have hrEq : gr = botGeoCut r := botGeoCut_unique gr
          subst hlEq; subst hrEq
          rw [trace_nt_eq_inl hlNT (by decide), trace_nt_eq_inl hrNT (by decide)]
          rfl
        | mid =>
          have hlEq : gl = botGeoCut l := botGeoCut_unique gl
          subst hlEq
          rw [trace_nt_eq_inl hlNT (by decide)]
          have ihr := midGeoCut_fromMidGeoCut gr
          show GeoCut.node _ _ _ _ _ (midGeoCut r (fromMidGeoCut gr)) = _
          rw [ihr]
      | mid =>
        cases rL with
        | top => exact absurd hr (by decide)
        | bot =>
          have hrEq : gr = botGeoCut r := botGeoCut_unique gr
          subst hrEq
          rw [trace_nt_eq_inl hrNT (by decide)]
          have ihl := midGeoCut_fromMidGeoCut gl
          show GeoCut.node _ _ _ _ (midGeoCut l (fromMidGeoCut gl)) _ = _
          rw [ihl]
        | mid =>
          have ihl := midGeoCut_fromMidGeoCut gl
          have ihr := midGeoCut_fromMidGeoCut gr
          show GeoCut.node _ _ _ _ (midGeoCut l (fromMidGeoCut gl))
                                   (midGeoCut r (fromMidGeoCut gr)) = _
          rw [ihl, ihr]

/-- The Equivalence `CutShape T ≃ GeoCut T Layer.mid`. -/
def midGeoCutEquiv (T : DecoratedTree α) : CutShape T ≃ GeoCut T Layer.mid where
  toFun := midGeoCut T
  invFun := fromMidGeoCut
  left_inv := fromMidGeoCut_midGeoCut T
  right_inv := midGeoCut_fromMidGeoCut

/-- The `.mid` case: enumerate `CutShape T` for inner cuts. -/
theorem perLayerContrib_mid (T : DecoratedTree α) :
    perLayerContrib (α := α) T .mid
      = (Finset.univ : Finset (GeoCut T Layer.mid)).val.map
          (fun g => geoToChildSlots g) := by
  match T with
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r =>
    -- Use midGeoCutEquiv to rewrite univ_GeoCut_mid as univ_CutShape mapped.
    rw [show (Finset.univ : Finset (GeoCut (.node l r) Layer.mid)).val
          = (Finset.univ : Finset (CutShape (.node l r))).val.map
              (midGeoCut (.node l r)) by
         rw [show (Finset.univ : Finset (GeoCut (.node l r) Layer.mid))
               = (Finset.univ : Finset (CutShape (.node l r))).map
                   (midGeoCutEquiv (.node l r)).toEmbedding from
             (Finset.map_univ_equiv (midGeoCutEquiv (.node l r))).symm]
         rfl]
    rw [Multiset.map_map]
    -- Now: univ_CutShape.val.map (geoToChildSlots ∘ midGeoCut) = perLayerContrib mid.
    refine Multiset.map_congr rfl (fun cl _ => ?_)
    exact (geoToChildSlots_midGeoCut _ cl).symm

/-! ### `perLayerContrib_top` — the substantive Foissy `.node` case

Per the mathlib audit, the `.top` case is proven by **structural induction** on
`T`, NOT by another `Equiv` (the `(cl_outer, section)` data type is too dependent
to admit clean helper lemmas).

For `T = .node l r` at `.top`:
- LHS data: bind over `cl_outer : CutShape (.node l r)` of section choices
  per tree in `cutForest cl_outer`. Each section element corresponds to an
  `AugCutShape T'` choice.
- RHS data: `(univ : Finset (GeoCut (.node l r) .top)).val.map geoToChildSlots`.
  GeoCut `.node` ctor decomposes as `(lL, rL, gl, gr)` with constraints.

**Both sides** factor through per-l × per-r `ChildSlots` pairs combined via
`nodeChildSlots`. The key inductive hypothesis is `lhsAnyChildContrib_eq_geoCutAny l`
and `... r`, which gives the per-subtree any-layer matching.

The CutShape ctor's gating naturally implements the `.trace` constraint:
- `bothCut`/`onlyLeftCut` (require `IsNotTrace l`): per-l ∈ {bot, mid layers}.
- `onlyRightCut`/`bothRecurse`: per-l = top layer.

This gating matches the `hlNT : IsNotTrace l ∨ lL = .top` constraint on
`GeoCut.node`. -/

/-- Combine per-l and per-r ChildSlots into a `.node`-combined ChildSlots. -/
def nodeChildSlots (cs_l cs_r : ChildSlots α) : ChildSlots α :=
  ⟨cs_l.bot + cs_r.bot, cs_l.mid + cs_r.mid, .node cs_l.stack cs_r.stack⟩

omit [DecidableEq α] in
/-- For `myL = .top` on `.node`, `geoToChildSlots (.node ... gl gr) = nodeChildSlots ...`. -/
theorem geoToChildSlots_node_top {l r : DecoratedTree α} {lL rL : Layer}
    (hl : lL ≤ Layer.top) (hr : rL ≤ Layer.top)
    (hlNT : DecoratedTree.IsNotTrace l ∨ lL = Layer.top)
    (hrNT : DecoratedTree.IsNotTrace r ∨ rL = Layer.top)
    (gl : GeoCut l lL) (gr : GeoCut r rL) :
    geoToChildSlots (GeoCut.node hl hr hlNT hrNT gl gr)
      = nodeChildSlots (geoToChildSlots gl) (geoToChildSlots gr) := by
  simp only [geoToChildSlots, geoBotForest, geoMidForest, geoStackItem, nodeChildSlots]

/-! #### RHS Sigma factoring: `geoMultiset_node_factored`

The RHS `(univ : Finset (GeoCut (.node l r) .top)).val.map geoToChildSlots`
factors via `nodeGeoCutEquiv` + `geoToChildSlots_node_top` into a Sigma-bind
over `(lL, rL, gl, gr)` with `nodeChildSlots` combined per-pair. -/

omit [DecidableEq α] in
/-- The RHS for `.node l r` at `.top` factored via Sigma decomposition. -/
theorem geoMultiset_node_factored (l r : DecoratedTree α) :
    (Finset.univ : Finset (GeoCut (.node l r) Layer.top)).val.map
        (fun g => geoToChildSlots g)
      = (Finset.univ : Finset
            (Σ (lL : {x : Layer // x ≤ Layer.top ∧
                  (DecoratedTree.IsNotTrace l ∨ x = Layer.top)})
               (rL : {x : Layer // x ≤ Layer.top ∧
                  (DecoratedTree.IsNotTrace r ∨ x = Layer.top)}),
              GeoCut l lL.1 × GeoCut r rL.1)).val.map
          (fun ⟨_, _, gl, gr⟩ =>
            nodeChildSlots (geoToChildSlots gl) (geoToChildSlots gr)) := by
  rw [show (Finset.univ : Finset (GeoCut (.node l r) Layer.top))
        = (Finset.univ : Finset (Σ
            (lL : {x : Layer // x ≤ Layer.top ∧
                  (DecoratedTree.IsNotTrace l ∨ x = Layer.top)})
            (rL : {x : Layer // x ≤ Layer.top ∧
                  (DecoratedTree.IsNotTrace r ∨ x = Layer.top)}),
            GeoCut l lL.1 × GeoCut r rL.1)).map
            (nodeGeoCutEquiv l r Layer.top).toEmbedding from
       (Finset.map_univ_equiv (nodeGeoCutEquiv l r Layer.top)).symm]
  rw [Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl (fun ⟨_, _, gl, gr⟩ _ => ?_)
  exact geoToChildSlots_node_top _ _ _ _ gl gr

/-- "Decomposed" form for `perLayerContrib (.node l r) .top`: bind over
    `(lL, rL, cs_l, cs_r)` of `nodeChildSlots`-combined ChildSlots, with per-l/per-r
    data drawn from `perLayerContrib l lL` / `perLayerContrib r rL` respectively.
    The trace constraint is encoded in the Subtype on layers. -/
noncomputable def perLayerContribDecomposed (l r : DecoratedTree α) :
    Multiset (ChildSlots α) :=
  (Finset.univ : Finset {x : Layer // x ≤ Layer.top ∧
        (DecoratedTree.IsNotTrace l ∨ x = Layer.top)}).val.bind fun lL =>
    (Finset.univ : Finset {x : Layer // x ≤ Layer.top ∧
        (DecoratedTree.IsNotTrace r ∨ x = Layer.top)}).val.bind fun rL =>
      (perLayerContrib (α := α) l lL.1).bind fun cs_l =>
        (perLayerContrib (α := α) r rL.1).map fun cs_r =>
          nodeChildSlots cs_l cs_r

/-! #### `perLayerContrib_top` `.node` case sub-lemmas: per-CutShape-ctor contributions

Each CutShape ctor for `(.node l r)` contributes a specific (lL, rL) sub-bind to
`perLayerContrib (.node l r) .top`. Mathlib provides `Multiset.bind_bind` (Fubini
commutativity for nested binds) and `Multiset.bind_map` (`(s.map f).bind g = s.bind (g ∘ f)`)
which are the foundational tools. -/

/-! **Per-ctor proof outline** (each ~50-80 LOC, total ~200-300 LOC for full `.node` proof):

For `bothRecurse cl_in cr_in`:
  1. `Multiset.bind_map` → `univ_(l × r).bind ...`.
  2. `Finset.product` decomposes `univ_(l × r)` into nested `univ_l.bind univ_r`.
  3. `Multiset.bind_assoc` for nested structure.
  4. cutForest = cutForest cl_in + cutForest cr_in. Apply `Multiset.map_add` + `Multiset.sections_add`.
  5. Decompose into bind over (m_l, m_r) via `Multiset.map_bind` + `Multiset.bind_map`.
  6. `Multiset.bind_bind` (Fubini) to reorder `(cl_in cr_in m_l m_r)` → `(cl_in m_l cr_in m_r)`.
  7. Match to perLayerContrib via its definition. Match to `(lL=top, rL=top)` sub-bind.

For `bothCut hl hr`:
  cutForest = {l, r}. `Multiset.sections_cons` (twice) decomposes Sections.
  Per (a, b) pair: `(a.fst + b.fst, a.snd + b.snd, .node (.trace l) (.trace r))`.
  Match to `(lL ∈ {bot, mid}, rL ∈ {bot, mid})` via `comulPairs ↔ perLayerContrib .bot ⊕ .mid`.

For `onlyLeftCut hl cr_in`: hybrid. cutForest = {l} + cutForest cr_in. Match to
  `(lL ∈ {bot, mid}, rL = top)`.

For `onlyRightCut hr cl_in`: symmetric.

Sum of all 4 = full perLayerContribDecomposed. -/

/-! #### `bothRecurse` ctor case: closed.

The `bothRecurse cl cr` ctor of `CutShape (.node l r)` contributes to
`perLayerContrib (.node l r) .top` exactly the (lL = .top, rL = .top) cell of
`perLayerContribDecomposed l r`. Strategy: per-(cl, cr) split via `sections_add`,
then Fubini-swap the (cl, cr, s_l, s_r) bind. -/

/-- The bothRecurse ctor's contribution to `perLayerContrib (.node l r) .top`. -/
private noncomputable def perLayerContribTopBothRecurse (l r : DecoratedTree α) :
    Multiset (ChildSlots α) :=
  (Finset.univ : Finset (CutShape l)).val.bind fun cl =>
    (Finset.univ : Finset (CutShape r)).val.bind fun cr =>
      (Multiset.Sections ((CutShape.cutForest cl + CutShape.cutForest cr).map fun T' =>
        (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
          ((AugCutShape.cutForest_aug ac' : Forest α),
           (AugCutShape.remainderForest ac' : Forest α)))).map fun s =>
        ⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
         .node (CutShape.remainder cl) (CutShape.remainder cr)⟩

/-- Per-cl-cr Sections-add reorganization for the bothRecurse case. -/
private theorem perLayerContribTopBothRecurse_per_cl_cr (l r : DecoratedTree α)
    (cl : CutShape l) (cr : CutShape r) :
    (Multiset.Sections ((CutShape.cutForest cl + CutShape.cutForest cr).map fun T' =>
        (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
          ((AugCutShape.cutForest_aug ac' : Forest α),
           (AugCutShape.remainderForest ac' : Forest α)))).map (fun s =>
        (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
          .node (CutShape.remainder cl) (CutShape.remainder cr)⟩ : ChildSlots α))
    = (Multiset.Sections ((CutShape.cutForest cl).map fun T' =>
        (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
          ((AugCutShape.cutForest_aug ac' : Forest α),
           (AugCutShape.remainderForest ac' : Forest α)))).bind fun s_l =>
        (Multiset.Sections ((CutShape.cutForest cr).map fun T' =>
          (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
            ((AugCutShape.cutForest_aug ac' : Forest α),
             (AugCutShape.remainderForest ac' : Forest α)))).map fun s_r =>
          nodeChildSlots
            ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
            ⟨(s_r.map Prod.fst).sum, (s_r.map Prod.snd).sum, CutShape.remainder cr⟩ := by
  rw [Multiset.map_add, Multiset.sections_add, Multiset.map_bind]
  refine Multiset.bind_congr (fun s_l _ => ?_)
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun s_r _ => ?_)
  rw [Function.comp_apply, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add]
  rfl

/-- The bothRecurse contribution equals the (.top, .top) cell of perLayerContribDecomposed.
    Closed via per-cl-cr lemma + Fubini-swap of the (cl, cr, s_l, s_r) bind. -/
private theorem perLayerContribTopBothRecurse_eq (l r : DecoratedTree α) :
    perLayerContribTopBothRecurse (α := α) l r
      = (perLayerContrib (α := α) l .top).bind fun cs_l =>
          (perLayerContrib (α := α) r .top).map fun cs_r =>
            nodeChildSlots cs_l cs_r := by
  unfold perLayerContribTopBothRecurse
  -- Step 1: apply per-cl-cr lemma to split sections.
  conv_lhs =>
    rw [show ((Finset.univ : Finset (CutShape l)).val.bind fun cl =>
              (Finset.univ : Finset (CutShape r)).val.bind fun cr =>
                (Multiset.Sections ((CutShape.cutForest cl + CutShape.cutForest cr).map
                    fun T' => (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                      ((AugCutShape.cutForest_aug ac' : Forest α),
                       (AugCutShape.remainderForest ac' : Forest α)))).map fun s =>
                  (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
                    .node (CutShape.remainder cl) (CutShape.remainder cr)⟩ : ChildSlots α))
            = (Finset.univ : Finset (CutShape l)).val.bind fun cl =>
              (Finset.univ : Finset (CutShape r)).val.bind fun cr =>
                (Multiset.Sections ((CutShape.cutForest cl).map fun T' =>
                  (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                    ((AugCutShape.cutForest_aug ac' : Forest α),
                     (AugCutShape.remainderForest ac' : Forest α)))).bind fun s_l =>
                  (Multiset.Sections ((CutShape.cutForest cr).map fun T' =>
                    (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                      ((AugCutShape.cutForest_aug ac' : Forest α),
                       (AugCutShape.remainderForest ac' : Forest α)))).map fun s_r =>
                    nodeChildSlots
                      ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
                      ⟨(s_r.map Prod.fst).sum, (s_r.map Prod.snd).sum, CutShape.remainder cr⟩ from
         Multiset.bind_congr (fun cl _ => Multiset.bind_congr (fun cr _ =>
           perLayerContribTopBothRecurse_per_cl_cr l r cl cr))]
  -- Step 2: Fubini-swap (cl, cr, s_l) → (cl, s_l, cr).
  rw [show ((Finset.univ : Finset (CutShape l)).val.bind fun cl =>
            (Finset.univ : Finset (CutShape r)).val.bind fun cr =>
              (Multiset.Sections ((CutShape.cutForest cl).map fun T' =>
                (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                  ((AugCutShape.cutForest_aug ac' : Forest α),
                   (AugCutShape.remainderForest ac' : Forest α)))).bind fun s_l =>
                (Multiset.Sections ((CutShape.cutForest cr).map fun T' =>
                  (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                    ((AugCutShape.cutForest_aug ac' : Forest α),
                     (AugCutShape.remainderForest ac' : Forest α)))).map fun s_r =>
                  nodeChildSlots
                    ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
                    ⟨(s_r.map Prod.fst).sum, (s_r.map Prod.snd).sum, CutShape.remainder cr⟩)
        = (Finset.univ : Finset (CutShape l)).val.bind fun cl =>
            (Multiset.Sections ((CutShape.cutForest cl).map fun T' =>
              (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                ((AugCutShape.cutForest_aug ac' : Forest α),
                 (AugCutShape.remainderForest ac' : Forest α)))).bind fun s_l =>
              (Finset.univ : Finset (CutShape r)).val.bind fun cr =>
                (Multiset.Sections ((CutShape.cutForest cr).map fun T' =>
                  (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                    ((AugCutShape.cutForest_aug ac' : Forest α),
                     (AugCutShape.remainderForest ac' : Forest α)))).map fun s_r =>
                  nodeChildSlots
                    ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
                    ⟨(s_r.map Prod.fst).sum, (s_r.map Prod.snd).sum, CutShape.remainder cr⟩ from by
       refine Multiset.bind_congr (fun cl _ => ?_)
       exact Multiset.bind_bind _ _]
  -- Step 3: Recognize bind cl (bind s_l ⟨..., rem cl⟩) = perLayerContrib l .top.
  show _ = ((Finset.univ : Finset (CutShape l)).val.bind fun cl_outer =>
              (Multiset.Sections ((CutShape.cutForest cl_outer).map fun T' =>
                (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                  ((AugCutShape.cutForest_aug ac' : Forest α),
                   (AugCutShape.remainderForest ac' : Forest α)))).map fun s =>
                (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum, CutShape.remainder cl_outer⟩
                  : ChildSlots α)).bind fun cs_l =>
            ((Finset.univ : Finset (CutShape r)).val.bind fun cl_outer =>
              (Multiset.Sections ((CutShape.cutForest cl_outer).map fun T' =>
                (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                  ((AugCutShape.cutForest_aug ac' : Forest α),
                   (AugCutShape.remainderForest ac' : Forest α)))).map fun s =>
                (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum, CutShape.remainder cl_outer⟩
                  : ChildSlots α)).map fun cs_r =>
              nodeChildSlots cs_l cs_r
  rw [Multiset.bind_assoc]
  refine Multiset.bind_congr (fun cl _ => ?_)
  conv_rhs => rw [Multiset.bind_map]
  refine Multiset.bind_congr (fun s_l _ => ?_)
  conv_rhs => rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun cr _ => ?_)
  rw [Multiset.map_map]
  rfl

/-! #### `bothCut`, `onlyLeftCut`, `onlyRightCut` ctor cases

The other 3 CutShape ctors of `(.node l r)` each produce a contribution to
`perLayerContrib (.node l r) .top` that matches a specific (lL, rL) sub-bind
of `perLayerContribDecomposed l r`. Following the pattern of `bothRecurse`,
these are proved by `Multiset.sections_add` + `Multiset.bind_singleton` +
per-(s_l, s_r) `nodeChildSlots`-recognition.

The `pairsMS l` reformulation collapses `AugCutShape l = CutShape l ⊕ Unit` into
a single Multiset of `(Forest, Forest)` pairs (used for the LHS bridge below). -/

/-- Per-layer .bot + .mid contribution = pairsMS wrapped as ChildSlots. -/
private theorem perLayerContrib_bot_add_mid_eq_pairsWrap (T : DecoratedTree α) :
    (perLayerContrib (α := α) T .bot) + (perLayerContrib (α := α) T .mid)
    = (pairsMS (α := α) T).map fun p => (⟨p.1, p.2, .trace T⟩ : ChildSlots α) := by
  show ((({⟨({T} : Forest α), 0, .trace T⟩} : Multiset (ChildSlots α))) +
        ((Finset.univ : Finset (CutShape T)).val.map fun cl =>
          (⟨CutShape.cutForest cl, ({CutShape.remainder cl} : Forest α), .trace T⟩
            : ChildSlots α)))
       = (pairsMS (α := α) T).map fun p => (⟨p.1, p.2, .trace T⟩ : ChildSlots α)
  unfold pairsMS
  rw [show ((Finset.univ : Finset (AugCutShape T)).val
            : Multiset (CutShape T ⊕ Unit))
        = (Finset.univ : Finset (CutShape T)).val.map Sum.inl
          + (Finset.univ : Finset Unit).val.map Sum.inr from rfl,
      Multiset.map_add, Multiset.map_add, Multiset.map_map, Multiset.map_map,
      Multiset.map_map, Multiset.map_map]
  rw [add_comm]
  rfl

/-- The bothCut ctor's contribution to perLayerContrib (.node l r) `.top` (raw form). -/
private noncomputable def perLayerContribTopBothCut (l r : DecoratedTree α) :
    Multiset (ChildSlots α) :=
  (Multiset.Sections (({l, r} : Forest α).map (pairsMS (α := α)))).map fun s =>
    ⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum, .node (.trace l) (.trace r)⟩

/-- The bothCut contribution equals the (.bot + .mid) × (.bot + .mid) cells of
    perLayerContribDecomposed. -/
private theorem perLayerContribTopBothCut_eq (l r : DecoratedTree α) :
    perLayerContribTopBothCut (α := α) l r
      = ((perLayerContrib (α := α) l .bot) + (perLayerContrib (α := α) l .mid)).bind fun cs_l =>
          ((perLayerContrib (α := α) r .bot) + (perLayerContrib (α := α) r .mid)).map fun cs_r =>
            nodeChildSlots cs_l cs_r := by
  rw [perLayerContrib_bot_add_mid_eq_pairsWrap, perLayerContrib_bot_add_mid_eq_pairsWrap]
  unfold perLayerContribTopBothCut
  rw [Multiset.bind_map]
  show (Multiset.Sections (((l ::ₘ r ::ₘ 0 : Multiset _)).map (pairsMS (α := α)))).map
        (fun s => (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
                    DecoratedTree.node (.trace l) (.trace r)⟩ : ChildSlots α))
      = (pairsMS (α := α) l).bind fun a_l =>
          ((pairsMS (α := α) r).map fun p => (⟨p.1, p.2, .trace r⟩ : ChildSlots α)).map fun cs_r =>
              nodeChildSlots ⟨a_l.1, a_l.2, .trace l⟩ cs_r
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_zero,
      Multiset.sections_cons, Multiset.sections_cons, Multiset.sections_zero]
  conv_lhs => rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun a_l _ => ?_)
  rw [Multiset.map_map, Multiset.map_bind]
  rw [show (fun a_r : Forest α × Forest α =>
            (({0} : Multiset (Multiset (Forest α × Forest α))).map (Multiset.cons a_r)).map
              ((fun s => (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
                          .node (DecoratedTree.trace l) (DecoratedTree.trace r)⟩ : ChildSlots α))
                ∘ Multiset.cons a_l))
          = fun a_r => ({(nodeChildSlots ⟨a_l.1, a_l.2, .trace l⟩
                          ⟨a_r.1, a_r.2, .trace r⟩ : ChildSlots α)} : Multiset _) from by
      funext a_r
      simp only [Multiset.map_singleton, Multiset.map_cons, Multiset.map_zero,
                 Multiset.sum_cons, Multiset.sum_zero, Function.comp_apply]
      unfold nodeChildSlots
      simp only [add_zero]]
  rw [Multiset.bind_singleton, Multiset.map_map]
  rfl

/-- The onlyLeftCut ctor's contribution: `cutForest = {l} + cutForest cr`. -/
private noncomputable def perLayerContribTopOnlyLeftCut (l r : DecoratedTree α) :
    Multiset (ChildSlots α) :=
  (Finset.univ : Finset (CutShape r)).val.bind fun cr =>
    (Multiset.Sections ((({l} + CutShape.cutForest cr : Forest α)).map (pairsMS (α := α)))).map
      fun s =>
        ⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
         .node (.trace l) (CutShape.remainder cr)⟩

/-- Per-cr lemma: section reorganization for onlyLeftCut. -/
private theorem perLayerContribTopOnlyLeftCut_per_cr (l r : DecoratedTree α)
    (cr : CutShape r) :
    (Multiset.Sections ((({l} + CutShape.cutForest cr : Forest α)).map
        (pairsMS (α := α)))).map (fun s =>
        (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
          .node (.trace l) (CutShape.remainder cr)⟩ : ChildSlots α))
    = (pairsMS (α := α) l).bind fun a_l =>
        (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α)))).map fun s_r =>
          nodeChildSlots ⟨a_l.1, a_l.2, .trace l⟩
            ⟨(s_r.map Prod.fst).sum, (s_r.map Prod.snd).sum, CutShape.remainder cr⟩ := by
  rw [Multiset.map_add, Multiset.sections_add]
  rw [show (({l} : Forest α).map (pairsMS (α := α)))
          = (pairsMS (α := α) l ::ₘ (0 : Multiset (Multiset (Forest α × Forest α)))) from rfl,
      Multiset.sections_cons, Multiset.sections_zero]
  rw [Multiset.bind_assoc, Multiset.map_bind]
  refine Multiset.bind_congr (fun a_l _ => ?_)
  rw [Multiset.map_singleton, Multiset.singleton_bind, Multiset.map_map]
  refine Multiset.map_congr rfl (fun s_r _ => ?_)
  show (⟨((a_l ::ₘ (0 : Multiset _) + s_r).map Prod.fst).sum,
         ((a_l ::ₘ (0 : Multiset _) + s_r).map Prod.snd).sum,
         .node (.trace l) (CutShape.remainder cr)⟩ : ChildSlots α)
       = nodeChildSlots ⟨a_l.1, a_l.2, .trace l⟩
            ⟨(s_r.map Prod.fst).sum, (s_r.map Prod.snd).sum, CutShape.remainder cr⟩
  rw [Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
      Multiset.map_cons, Multiset.map_zero, Multiset.map_cons, Multiset.map_zero,
      Multiset.sum_cons, Multiset.sum_zero, Multiset.sum_cons, Multiset.sum_zero,
      add_zero, add_zero]
  unfold nodeChildSlots
  rfl

/-- The onlyLeftCut contribution equals the (.bot + .mid, .top) sub-bind. -/
private theorem perLayerContribTopOnlyLeftCut_eq (l r : DecoratedTree α) :
    perLayerContribTopOnlyLeftCut (α := α) l r
      = ((perLayerContrib (α := α) l .bot) + (perLayerContrib (α := α) l .mid)).bind fun cs_l =>
          (perLayerContrib (α := α) r .top).map fun cs_r =>
            nodeChildSlots cs_l cs_r := by
  rw [perLayerContrib_bot_add_mid_eq_pairsWrap]
  unfold perLayerContribTopOnlyLeftCut
  conv_lhs =>
    rw [show ((Finset.univ : Finset (CutShape r)).val.bind fun cr =>
              (Multiset.Sections ((({l} + CutShape.cutForest cr : Forest α)).map
                  (pairsMS (α := α)))).map fun s =>
                (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
                  .node (.trace l) (CutShape.remainder cr)⟩ : ChildSlots α))
            = (Finset.univ : Finset (CutShape r)).val.bind fun cr =>
              (pairsMS (α := α) l).bind fun a_l =>
                (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α)))).map fun s_r =>
                  nodeChildSlots ⟨a_l.1, a_l.2, .trace l⟩
                    ⟨(s_r.map Prod.fst).sum, (s_r.map Prod.snd).sum, CutShape.remainder cr⟩ from
         Multiset.bind_congr (fun cr _ => perLayerContribTopOnlyLeftCut_per_cr l r cr)]
  rw [Multiset.bind_bind, Multiset.bind_map]
  refine Multiset.bind_congr (fun a_l _ => ?_)
  show _ = ((Finset.univ : Finset (CutShape r)).val.bind fun cl_outer =>
              (Multiset.Sections ((CutShape.cutForest cl_outer).map fun T' =>
                (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                  ((AugCutShape.cutForest_aug ac' : Forest α),
                   (AugCutShape.remainderForest ac' : Forest α)))).map fun s =>
                (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum, CutShape.remainder cl_outer⟩
                  : ChildSlots α)).map fun cs_r =>
              nodeChildSlots ⟨a_l.1, a_l.2, .trace l⟩ cs_r
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun cr _ => ?_)
  rw [Multiset.map_map]
  rfl

/-- The onlyRightCut ctor's contribution: `cutForest = cutForest cl + {r}`. -/
private noncomputable def perLayerContribTopOnlyRightCut (l r : DecoratedTree α) :
    Multiset (ChildSlots α) :=
  (Finset.univ : Finset (CutShape l)).val.bind fun cl =>
    (Multiset.Sections ((CutShape.cutForest cl + {r} : Forest α).map (pairsMS (α := α)))).map
      fun s =>
        ⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
         .node (CutShape.remainder cl) (.trace r)⟩

/-- Per-cl lemma: section reorganization for onlyRightCut. -/
private theorem perLayerContribTopOnlyRightCut_per_cl (l r : DecoratedTree α)
    (cl : CutShape l) :
    (Multiset.Sections (((CutShape.cutForest cl + {r} : Forest α)).map
        (pairsMS (α := α)))).map (fun s =>
        (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
          .node (CutShape.remainder cl) (.trace r)⟩ : ChildSlots α))
    = (Multiset.Sections ((CutShape.cutForest cl).map (pairsMS (α := α)))).bind fun s_l =>
        (pairsMS (α := α) r).map fun a_r =>
          nodeChildSlots
            ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
            ⟨a_r.1, a_r.2, .trace r⟩ := by
  rw [Multiset.map_add, Multiset.sections_add]
  rw [show (({r} : Forest α).map (pairsMS (α := α)))
          = (pairsMS (α := α) r ::ₘ (0 : Multiset (Multiset (Forest α × Forest α)))) from rfl,
      Multiset.sections_cons, Multiset.sections_zero]
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun s_l _ => ?_)
  rw [Multiset.map_bind, Multiset.map_bind]
  rw [show ((pairsMS (α := α) r).map fun a_r =>
              nodeChildSlots
                ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
                ⟨a_r.1, a_r.2, .trace r⟩)
          = (pairsMS (α := α) r).bind fun a_r =>
              ({nodeChildSlots
                ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
                ⟨a_r.1, a_r.2, .trace r⟩} : Multiset _) from
        (Multiset.bind_singleton _ _).symm]
  refine Multiset.bind_congr (fun a_r _ => ?_)
  rw [Multiset.map_singleton, Multiset.map_singleton, Multiset.map_singleton]
  show ({(_ : ChildSlots α)} : Multiset _) = _
  congr 1
  show (⟨((s_l + (a_r ::ₘ (0 : Multiset _))).map Prod.fst).sum,
         ((s_l + (a_r ::ₘ (0 : Multiset _))).map Prod.snd).sum,
         .node (CutShape.remainder cl) (.trace r)⟩ : ChildSlots α)
       = nodeChildSlots
          ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
          ⟨a_r.1, a_r.2, .trace r⟩
  rw [Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
      Multiset.map_cons, Multiset.map_zero, Multiset.map_cons, Multiset.map_zero,
      Multiset.sum_cons, Multiset.sum_zero, Multiset.sum_cons, Multiset.sum_zero,
      add_zero, add_zero]
  unfold nodeChildSlots
  rfl

/-- The onlyRightCut contribution equals the (.top, .bot + .mid) sub-bind. -/
private theorem perLayerContribTopOnlyRightCut_eq (l r : DecoratedTree α) :
    perLayerContribTopOnlyRightCut (α := α) l r
      = (perLayerContrib (α := α) l .top).bind fun cs_l =>
          ((perLayerContrib (α := α) r .bot) + (perLayerContrib (α := α) r .mid)).map fun cs_r =>
            nodeChildSlots cs_l cs_r := by
  rw [perLayerContrib_bot_add_mid_eq_pairsWrap]
  unfold perLayerContribTopOnlyRightCut
  conv_lhs =>
    rw [show ((Finset.univ : Finset (CutShape l)).val.bind fun cl =>
              (Multiset.Sections (((CutShape.cutForest cl + {r} : Forest α)).map
                  (pairsMS (α := α)))).map fun s =>
                (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
                  .node (CutShape.remainder cl) (.trace r)⟩ : ChildSlots α))
            = (Finset.univ : Finset (CutShape l)).val.bind fun cl =>
              (Multiset.Sections ((CutShape.cutForest cl).map (pairsMS (α := α)))).bind fun s_l =>
                (pairsMS (α := α) r).map fun a_r =>
                  nodeChildSlots
                    ⟨(s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum, CutShape.remainder cl⟩
                    ⟨a_r.1, a_r.2, .trace r⟩ from
         Multiset.bind_congr (fun cl _ => perLayerContribTopOnlyRightCut_per_cl l r cl)]
  unfold perLayerContrib
  rw [Multiset.bind_assoc]
  refine Multiset.bind_congr (fun cl _ => ?_)
  rw [Multiset.bind_map]
  refine Multiset.bind_congr (fun s_l _ => ?_)
  rw [Multiset.map_map]
  rfl

/-- The decomposed form equals the RHS Sigma-bind. -/
theorem geoMultiset_node_eq_decomposed (l r : DecoratedTree α)
    (ihl : ∀ layer, perLayerContrib (α := α) l layer
            = (Finset.univ : Finset (GeoCut l layer)).val.map (fun g => geoToChildSlots g))
    (ihr : ∀ layer, perLayerContrib (α := α) r layer
            = (Finset.univ : Finset (GeoCut r layer)).val.map (fun g => geoToChildSlots g)) :
    (Finset.univ : Finset (GeoCut (.node l r) Layer.top)).val.map
        (fun g => geoToChildSlots g)
      = perLayerContribDecomposed l r := by
  rw [geoMultiset_node_factored]
  unfold perLayerContribDecomposed
  -- RHS: Sigma over (lL, rL) of (gl × gr) → nodeChildSlots-combined.
  -- LHS: bind over (lL) (rL) (cs_l ∈ perLayerContrib l lL.1) (cs_r ∈ perLayerContrib r rL.1).
  -- Apply IH to convert perLayerContrib X layer → univ_GeoCut.map geoToChildSlots.
  rw [show ((Finset.univ : Finset (Σ (lL : {x : Layer // x ≤ Layer.top ∧
              (DecoratedTree.IsNotTrace l ∨ x = Layer.top)})
            (rL : {x : Layer // x ≤ Layer.top ∧
              (DecoratedTree.IsNotTrace r ∨ x = Layer.top)}),
            GeoCut l lL.1 × GeoCut r rL.1)).val
        : Multiset _)
      = (Finset.univ : Finset {x : Layer // x ≤ Layer.top ∧
              (DecoratedTree.IsNotTrace l ∨ x = Layer.top)}).val.bind fun lL =>
          ((Finset.univ : Finset (Σ (rL : {x : Layer // x ≤ Layer.top ∧
                (DecoratedTree.IsNotTrace r ∨ x = Layer.top)}),
                GeoCut l lL.1 × GeoCut r rL.1)).val).map (Sigma.mk lL) from rfl]
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun lL _ => ?_)
  simp only [Multiset.map_map, Function.comp_def]
  -- Now per-lL: rewrite the inner Sigma similarly.
  rw [show ((Finset.univ : Finset (Σ (rL : {x : Layer // x ≤ Layer.top ∧
              (DecoratedTree.IsNotTrace r ∨ x = Layer.top)}),
              GeoCut l lL.1 × GeoCut r rL.1)).val
        : Multiset _)
      = (Finset.univ : Finset {x : Layer // x ≤ Layer.top ∧
              (DecoratedTree.IsNotTrace r ∨ x = Layer.top)}).val.bind fun rL =>
          ((Finset.univ : Finset (GeoCut l lL.1 × GeoCut r rL.1)).val).map (Sigma.mk rL) from rfl]
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun rL _ => ?_)
  simp only [Multiset.map_map, Function.comp_def]
  -- Per (lL, rL): rewrite univ_(gl × gr) as univ_gl ×ˢ univ_gr → bind.
  rw [show ((Finset.univ : Finset (GeoCut l lL.1 × GeoCut r rL.1)).val
        : Multiset _)
      = (Finset.univ : Finset (GeoCut l lL.1)).val.bind fun gl =>
          ((Finset.univ : Finset (GeoCut r rL.1)).val).map (Prod.mk gl) from rfl]
  rw [Multiset.map_bind]
  rw [ihl lL.1]
  -- Now: ((univ_GeoCut_l_lL).map geoToChildSlots).bind ...
  rw [Multiset.bind_map]
  refine Multiset.bind_congr (fun gl _ => ?_)
  rw [Multiset.map_map]
  rw [ihr rL.1]
  rw [Multiset.map_map]
  rfl

/-- The `.top` case: substantive recursive content.

    **Status**: Step 1 done; Step 2 has 4 ctor case lemmas proven; final wiring is sorry.

    **Proof plan**:

    Step 1 (DONE): Apply `geoMultiset_node_eq_decomposed` to convert the RHS to
    `perLayerContribDecomposed l r` form, using `perLayerContrib_X` (for X ∈
    {bot, mid, top}) as IH on subtrees l and r.

    Step 2 (4 ctor lemmas DONE, final wiring TODO): Show `perLayerContrib (.node l r) .top
    = perLayerContribDecomposed l r`. Each CutShape ctor of `(.node l r)` has its own
    helper lemma that matches a specific (lL, rL) sub-bind of `perLayerContribDecomposed`:

    - `perLayerContribTopBothCut_eq`: bothCut → (.bot+.mid)×(.bot+.mid) cells.
    - `perLayerContribTopOnlyLeftCut_eq`: onlyLeftCut → (.bot+.mid, .top) cells.
    - `perLayerContribTopOnlyRightCut_eq`: onlyRightCut → (.top, .bot+.mid) cells.
    - `perLayerContribTopBothRecurse_eq`: bothRecurse → (.top, .top) cell.

    Final wiring TODO: 4-way ctor decomposition of `(Finset.univ : Finset (CutShape (.node
    l r))).val` (with conditional inclusion based on `IsNotTrace l, IsNotTrace r`),
    then case analysis on `IsNotTrace` to match the conditional ctor contributions to
    the conditional Subtype-bound (lL, rL) cells in `perLayerContribDecomposed`. -/
theorem perLayerContrib_top (T : DecoratedTree α) :
    perLayerContrib (α := α) T .top
      = (Finset.univ : Finset (GeoCut T Layer.top)).val.map
          (fun g => geoToChildSlots g) := by
  match T with
  | .leaf a => rfl
  | .trace t => rfl
  | .node l r =>
    -- Use IH on l, r to convert RHS to decomposed form.
    rw [geoMultiset_node_eq_decomposed l r
          (fun layer => match layer with
            | .bot => perLayerContrib_bot l
            | .mid => perLayerContrib_mid l
            | .top => perLayerContrib_top l)
          (fun layer => match layer with
            | .bot => perLayerContrib_bot r
            | .mid => perLayerContrib_mid r
            | .top => perLayerContrib_top r)]
    -- Goal: perLayerContrib (.node l r) .top = perLayerContribDecomposed l r.
    -- This is the substantive Foissy content:
    -- - LHS: bind over CutShape (.node l r) ctors with section data.
    -- - RHS (decomposed): bind over (lL, rL, cs_l, cs_r) with per-layer ChildSlots.
    -- The bijection: each CutShape ctor's contribution matches a specific (lL, rL)
    -- sub-bind. For each (lL, rL):
    --   (bot, bot): bothCut hl hr (requires IsNotTrace l, IsNotTrace r).
    --   (bot, mid): bothCut hl hr (per-r picks real cl_inner).
    --   (mid, bot): bothCut hl hr (per-l picks real cl_inner).
    --   (mid, mid): bothCut hl hr.
    --   (bot, top): onlyLeftCut hl cr_in.
    --   (mid, top): onlyLeftCut.
    --   (top, bot): onlyRightCut hr cl_in.
    --   (top, mid): onlyRightCut.
    --   (top, top): bothRecurse cl_in cr_in.
    sorry

/-- **Per-subtree IH** (any layer): combines the three per-layer sub-lemmas via
    Sigma decomposition + the per-layer bijections. -/
theorem lhsAnyChildContrib_eq_geoCutAny (T : DecoratedTree α) :
    lhsAnyChildContrib T = geoCutAnyChildContrib T := by
  unfold lhsAnyChildContrib geoCutAnyChildContrib
  -- Step 1: decompose `(univ : Finset (Σ myL, GeoCut T myL)).val` via `Multiset.sigma`,
  -- which by definition is `bind ... ∘ map (Sigma.mk _)`.
  rw [show ((Finset.univ : Finset (Σ myL : Layer, GeoCut T myL)).val
        : Multiset (Σ myL : Layer, GeoCut T myL))
      = (Finset.univ : Finset Layer).val.bind
          (fun myL => (Finset.univ : Finset (GeoCut T myL)).val.map (Sigma.mk myL)) from rfl]
  -- Step 2: the outer map distributes over the bind.
  rw [Multiset.map_bind]
  -- Step 3: per-layer, simplify (X.map (Sigma.mk myL)).map (fun ⟨_, g⟩ => geoToChildSlots g)
  -- = X.map geoToChildSlots.
  simp only [Multiset.map_map, Function.comp_def]
  -- Step 4: use the per-layer bijections to rewrite each layer.
  refine Multiset.bind_congr (fun layer _ => ?_)
  rcases layer with _ | _ | _
  · exact perLayerContrib_bot T
  · exact perLayerContrib_mid T
  · exact perLayerContrib_top T

/-! ### Bijection: `lhsRealCuts T = geoMultiset T = rhsRealRealInner T`

The substantive Foissy claim. Both sides factor through `geoMultiset T`,
so the equality follows by chaining two GeoCut bijections (LHS and RHS).

By induction on `T`:
- `.leaf` / `.trace`: definitional reduction (`rfl`).
- `.node l r`: substantive Foissy bijection. Sub-sessions 2.10b / 2.11. -/

/-! #### Algebraic identity bridge: `lhsRealCuts T = perLayerContrib T .top |>.map ChildSlots.toTriple`

This bridge holds at any T (independent of the Foissy bijection). Once proved,
`lhsRealCuts_eq_geoMultiset` follows from `perLayerContrib_top` via the chain:
`lhsRealCuts T = perLayerContrib T .top |>.map (ChildSlots.toTriple R)
   = (univ : Finset (GeoCut T .top)).val.map (ChildSlots.toTriple R ∘ geoToChildSlots)
   = (univ).val.map geoCutToTriple = geoMultiset T`. -/

/-- Product of pair-tensor map distributes through pair sums:
    `prod (s.map (forestToHc fst ⊗ forestToHc snd)) = forestToHc(sum fst) ⊗ forestToHc(sum snd)`.
    Combines `Algebra.TensorProduct.tmul_mul_tmul` and `forestToHc_add`. -/
private lemma forestToHc_pair_prod (s : Multiset (Forest α × Forest α)) :
    (s.map (fun p => (forestToHc (R := R) p.1) ⊗ₜ[R] (forestToHc (R := R) p.2))).prod
    = (forestToHc (R := R) (s.map Prod.fst).sum)
        ⊗ₜ[R] (forestToHc (R := R) (s.map Prod.snd).sum) := by
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero, forestToHc_zero,
               Algebra.TensorProduct.one_def]
  | cons p s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [ih, Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, ← forestToHc_add]

/-- Sections distribute through per-element map:
    `Sections (M.map (Multiset.map h)) = (Sections M).map (Multiset.map h)`.

    Mathlib gap: verified absent from `Mathlib/Data/Multiset/Sections.lean` as
    of this writing. PR candidate; lives in `_root_.Multiset` to match mathlib
    namespacing. -/
theorem _root_.Multiset.Sections_map_map {β γ : Type*} (h : β → γ)
    (M : Multiset (Multiset β)) :
    Multiset.Sections (M.map (Multiset.map h))
    = (Multiset.Sections M).map (Multiset.map h) := by
  induction M using Multiset.induction with
  | empty => simp
  | cons m M ih =>
    rw [Multiset.map_cons, Multiset.sections_cons, Multiset.sections_cons,
        Multiset.bind_map, ih, Multiset.map_bind]
    refine Multiset.bind_congr (fun a _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun s _ => ?_)
    rw [Function.comp_apply, Function.comp_apply, Multiset.map_cons]

/-- The algebraic bridge: the LHS triple-tensors equal the per-layer .top
    ChildSlots projected via `ChildSlots.toTriple`. Per-element identity holds
    by tensor-product associativity. -/
theorem lhsRealCuts_eq_perLayerContrib_top (T : DecoratedTree α) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = (perLayerContrib (α := α) T .top).map (ChildSlots.toTriple R) := by
  unfold lhsRealCuts perLayerContrib
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun cl_outer _ => ?_)
  -- LHS sections are over `(cutForest cl_outer).map comulTreeMS`; expand
  -- via `comulTreeMS = pairsMS.map tensorize`, then lift the per-element map
  -- through `Sections` via `Multiset.Sections_map_map`, and align with the RHS
  -- pair-section structure (which IS `pairsMS`).
  simp only [comulTreeMS_eq_pairsMS_map]
  rw [show ((CutShape.cutForest cl_outer).map fun T' =>
             (pairsMS T').map fun p =>
               (forestToHc (R := R) p.1) ⊗ₜ[R] (forestToHc (R := R) p.2))
        = ((CutShape.cutForest cl_outer).map (pairsMS (α := α))).map
            (Multiset.map (fun p =>
              (forestToHc (R := R) p.1) ⊗ₜ[R] (forestToHc (R := R) p.2))) from by
       rw [Multiset.map_map]; rfl]
  rw [Multiset.Sections_map_map, Multiset.map_map, Multiset.map_map]
  -- Per-section identity: apply forestToHc_pair_prod + assoc_tmul.
  refine Multiset.map_congr rfl (fun s _ => ?_)
  rw [Function.comp_apply, Function.comp_apply, forestToHc_pair_prod]
  rfl

/-- **LHS bijection**: `lhsRealCuts T` enumerates the same multiset of triples
    as `geoMultiset T`. Reduced to the algebraic bridge + `perLayerContrib_top`. -/
theorem lhsRealCuts_eq_geoMultiset (T : DecoratedTree α) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = geoMultiset T := by
  rw [lhsRealCuts_eq_perLayerContrib_top, perLayerContrib_top]
  unfold geoMultiset
  rw [Multiset.map_map]
  rfl

/-- The RHS algebraic bridge: `rhsRealRealInner T` triples equal the per-layer
    `.top` ChildSlots projected via `ChildSlots.toTriple`. -/
theorem rhsRealRealInner_eq_perLayerContrib_top (T : DecoratedTree α) :
    (rhsRealRealInner T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = (perLayerContrib (α := α) T .top).map (ChildSlots.toTriple R) := by
  -- RHS rhsRealRealInner is bind over (C₁, C₂) ∈ CutShape T × CutShape (rem C₁).
  -- The triple: forestToHc(cutForest C₁) ⊗ (forestToHc(cutForest C₂) ⊗ forestToHc({remainder C₂})).
  -- Per-layer .top maps cl_outer + section to similar structure.
  -- Pending — symmetric to lhsRealCuts_eq_perLayerContrib_top.
  sorry

/-- **RHS bijection**: `rhsRealRealInner T` enumerates the same multiset of
    triples as `geoMultiset T`. Reduced to the algebraic bridge + `perLayerContrib_top`. -/
theorem rhsRealRealInner_eq_geoMultiset (T : DecoratedTree α) :
    (rhsRealRealInner T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = geoMultiset T := by
  rw [rhsRealRealInner_eq_perLayerContrib_top, perLayerContrib_top]
  unfold geoMultiset
  rw [Multiset.map_map]
  rfl

/-! ### §3g: The substantive cuts-of-cuts identity (via GeoCut chain)

Now that both `lhsRealCuts_eq_geoMultiset` and `rhsRealRealInner_eq_geoMultiset`
are stated, we close the substantive identity by chaining them through `geoMultiset`. -/

/-- The substantive half: `lhsRealCuts T = rhsRealRealInner T`, proven via the
    GeoCut chain `(LHS).trans (RHS).symm`. For T = .leaf, .trace this is `rfl`
    via the leaf/trace cases of the bijection theorems; for T = .node l r this
    is the substantive Foissy content delegated to the GeoCut bijection. -/
theorem lhsRealCuts_eq_rhsRealRealInner (T : DecoratedTree α) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = rhsRealRealInner T :=
  (lhsRealCuts_eq_geoMultiset T).trans (rhsRealRealInner_eq_geoMultiset T).symm

/-- **The substantive cuts-of-cuts identity** (@cite{foissy-2002} §2 /
    @cite{connes-kreimer-1998}): for `T = .node l r`, the LHS-section multiset
    and the RHS-DoubleCut multiset are equal as multisets of triple-tensors.

    Composes the easy half + substantive half + `rhsMultiset_decomp`. -/
theorem lhsMultiset_eq_rhsMultiset_node (l r : DecoratedTree α) :
    (lhsMultiset (.node l r) : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = rhsMultiset (.node l r) := by
  rw [lhsMultiset_decomp,
      lhsExtractWhole_eq_rhsExtractWhole_add_realExtractInner,
      lhsRealCuts_eq_rhsRealRealInner,
      rhsMultiset_decomp]
  abel

/-! ### §3h: LHS direction of the cuts-of-cuts bijection -/

/-- LHS direction of the cuts-of-cuts bijection: the left-iterated
    coproduct on a single-tree workspace, after the canonical associator,
    reorganizes as a sum over `DoubleCut T`.

    - `.leaf`, `.trace`: primitive (only the trivial cut) → apply
      `lhs_eq_sum_DoubleCut_of_primitive_tree`.
    - `.node l r`: substantive Foissy "cut-commutation" bijection, reduces to
      `lhsMultiset_eq_rhsMultiset_node`. -/
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
    rw [lhs_eq_sum_lhsMultiset, rhs_eq_sum_rhsMultiset, lhsMultiset_eq_rhsMultiset_node]

end ConnesKreimer
