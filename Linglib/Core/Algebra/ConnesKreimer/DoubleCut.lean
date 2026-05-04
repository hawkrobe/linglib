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

    Generic helper; mathlib-PR-able. Public so future modules can reuse. -/
theorem TensorProduct.sum_tmul_multiset {M N : Type*}
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
  unfold comulTreeMS
  rw [Multiset.map_map]
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

/-- The substantive half: per-`C` matching of LHS sections vs RHS inner cuts.
    Both sides are `Multiset.bind` over `CutShape T`. The per-C contributions
    are different (LHS: sections of `cutForest C`; RHS: cuts of `remainder C`),
    but their TOTAL bind-sums match.

    For T = .leaf, .trace: trivial (both sides are singleton multisets matching).
    For T = .node l r: the substantive cut-commutation content. -/
theorem lhsRealCuts_eq_rhsRealRealInner (T : DecoratedTree α) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = rhsRealRealInner T := by
  match T with
  | .leaf a =>
    -- |CutShape (.leaf a)| = 1 (atLeaf); cutForest = 0, remainder = .leaf a.
    -- LHS: bind over {atLeaf}, inner = (Sections 0).map (assoc(1 ⊗ {leaf a})) = singleton.
    -- RHS: bind over {atLeaf}, inner = univ_CutShape (.leaf a).map (...) = singleton.
    unfold lhsRealCuts rhsRealRealInner
    rfl
  | .trace t =>
    unfold lhsRealCuts rhsRealRealInner
    rfl
  | .node l r =>
    -- The substantive cuts-of-cuts content: cut-commutation bijection.
    sorry

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

    For T = .leaf or .trace, only the root layer matters.
    For T = .node l r, the root has layer `myL`, and `l`, `r` have GeoCuts
    with their own root layers `lL`, `rL` satisfying `lL ≤ myL`, `rL ≤ myL`. -/
inductive GeoCut : DecoratedTree α → Layer → Type _
  | leaf {a : α} (myL : Layer) : GeoCut (.leaf a) myL
  | trace {t : DecoratedTree α} (myL : Layer) : GeoCut (.trace t) myL
  | node {l r : DecoratedTree α} {myL lL rL : Layer}
      (hl : lL ≤ myL) (hr : rL ≤ myL)
      (gl : GeoCut l lL) (gr : GeoCut r rL) : GeoCut (.node l r) myL

/-! ### `Fintype (GeoCut T myL)`

Structural recursion on `T`:
- `.leaf` / `.trace`: `GeoCut` has a unique element (root layer is `myL`).
- `.node l r`: `GeoCut (.node l r) myL` is in bijection with
  `Σ (lL : {x // x ≤ myL}) (rL : {x // x ≤ myL}), GeoCut l lL.1 × GeoCut r rL.1`,
  which has `Fintype` via mathlib's `Sigma` / `Prod` / `Subtype` instances combined
  with the recursive `Fintype (GeoCut subtree _)`. -/

@[reducible] private def geoCutFintype :
    ∀ (T : DecoratedTree α) (myL : Layer), Fintype (GeoCut T myL)
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
      letI _ihl : ∀ lL, Fintype (GeoCut l lL) := geoCutFintype l
      letI _ihr : ∀ rL, Fintype (GeoCut r rL) := geoCutFintype r
      Fintype.ofEquiv
        (Σ (lL : {x : Layer // x ≤ myL}) (rL : {x : Layer // x ≤ myL}),
          GeoCut l lL.1 × GeoCut r rL.1)
        { toFun := fun ⟨lL, rL, gl, gr⟩ => GeoCut.node lL.2 rL.2 gl gr
          invFun := fun g => match g with
            | .node hl hr gl gr => ⟨⟨_, hl⟩, ⟨_, hr⟩, gl, gr⟩
          left_inv := fun ⟨_, _, _, _⟩ => rfl
          right_inv := fun g => by cases g; rfl }

instance instFintypeGeoCut (T : DecoratedTree α) (myL : Layer) :
    Fintype (GeoCut T myL) :=
  geoCutFintype T myL

/-! ### `GeoCut` semantics — projecting to the triple-tensor

For each `g : GeoCut T myL` we extract three pieces:
- `geoBotForest g`: the BOT subtrees (extracted at the OUTER cut).
- `geoMidForest g`: the MID subtrees (extracted at the INNER cut, each represented as
  its outer-remainder skeleton — i.e., with its own BOT subtrees as `.trace` markers).
- `geoStackItem g`: the contribution this subtree makes to the **parent's** TOP slot.
  - `myL = .bot`: `.trace T` (the whole subtree is BOT-extracted; appears as a trace).
  - `myL = .mid`: `.trace (geoOuterSkeleton g)` (the subtree is MID-extracted; appears
    as a trace whose data is the outer-remainder skeleton).
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
  | .mid, .node _ _ gl gr => .node (geoOuterSkeleton gl) (geoOuterSkeleton gr)
  | .top, .leaf _ => T
  | .top, .trace _ => T
  | .top, .node _ _ gl gr => .node (geoOuterSkeleton gl) (geoOuterSkeleton gr)

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
  | .top, .node _ _ gl gr => .node (geoStackItem gl) (geoStackItem gr)

/-- The BOT-slot forest contributed by this GeoCut: subtrees rooted at BOT vertices. -/
def geoBotForest {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) : Forest α :=
  match myL, g with
  | .bot, _ => ({T} : Forest α)
  | .mid, .leaf _ => 0
  | .mid, .trace _ => 0
  | .mid, .node _ _ gl gr => geoBotForest gl + geoBotForest gr
  | .top, .leaf _ => 0
  | .top, .trace _ => 0
  | .top, .node _ _ gl gr => geoBotForest gl + geoBotForest gr

/-- The MID-slot forest contributed by this GeoCut: each MID-rooted subtree
    contributes its outer-remainder skeleton (BOT positions become traces). -/
def geoMidForest {T : DecoratedTree α} {myL : Layer} (g : GeoCut T myL) : Forest α :=
  match myL, g with
  | .bot, _ => 0
  | .mid, _ => ({geoOuterSkeleton g} : Forest α)
  | .top, .leaf _ => 0
  | .top, .trace _ => 0
  | .top, .node _ _ gl gr => geoMidForest gl + geoMidForest gr

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

/-! ### Bijection: `lhsRealCuts T = geoMultiset T = rhsRealRealInner T`

The substantive Foissy claim. Both sides factor through `geoMultiset T`,
so the equality follows by chaining two GeoCut bijections (LHS and RHS).

By induction on `T`:
- `.leaf` / `.trace`: definitional reduction (`rfl`).
- `.node l r`: substantive Foissy bijection. Sub-sessions 2.10b / 2.11. -/

/-- **LHS bijection**: `lhsRealCuts T` enumerates the same multiset of triples
    as `geoMultiset T`. Substantive content for `.node l r`; `.leaf` and `.trace`
    are by definitional reduction. -/
theorem lhsRealCuts_eq_geoMultiset (T : DecoratedTree α) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = geoMultiset T := by
  match T with
  | .leaf a =>
    -- |CutShape (.leaf a)| = 1 (atLeaf, with cutForest = 0).
    -- Sections of (0.map comulTreeMS) = singleton (one empty section).
    -- LHS: one triple = assoc(1 ⊗ {.leaf a}) = forestToHc 0 ⊗ (forestToHc 0 ⊗ {.leaf a}).
    -- RHS: |GeoCut .leaf a top| = 1 element = .leaf .top.
    -- geoCutToTriple (.leaf .top) = forestToHc 0 ⊗ (forestToHc 0 ⊗ forestToHc {.leaf a}).
    unfold lhsRealCuts geoMultiset
    rfl
  | .trace t =>
    unfold lhsRealCuts geoMultiset
    rfl
  | .node l r =>
    -- The substantive content: the per-(lL, rL, gl, gr) bijection between
    -- LHS data (CutShape (.node l r) ctors + sections) and GeoCut indexings.
    -- Forward map: outer extracting BOT subtrees + inner choices for each
    -- outer-extracted tree (extractWhole→BOT, real cl_inner→MID).
    -- Algebraic tools: `Multiset.sections_add`, `Multiset.map_add`, `Multiset.bind_map`.
    sorry

/-- **RHS bijection**: `rhsRealRealInner T` enumerates the same multiset of
    triples as `geoMultiset T`. Substantive content for `.node l r`. -/
theorem rhsRealRealInner_eq_geoMultiset (T : DecoratedTree α) :
    (rhsRealRealInner T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = geoMultiset T := by
  match T with
  | .leaf a =>
    -- |CutShape (.leaf a)| = 1 (atLeaf), |CutShape (rem atLeaf)| = |CutShape (.leaf a)| = 1.
    -- RHS-real-real: 1 triple. Triple: forestToHc 0 ⊗ (forestToHc 0 ⊗ forestToHc {.leaf a}).
    -- Matches geoMultiset (.leaf a) (singleton).
    unfold rhsRealRealInner geoMultiset
    rfl
  | .trace t =>
    unfold rhsRealRealInner geoMultiset
    rfl
  | .node l r =>
    -- The substantive RHS bijection. Outer C₁ extracts BOT, inner C₂ on remainder
    -- C₁ extracts MID. Each (C₁, C₂) corresponds to a unique GeoCut g with root=top.
    sorry

/-! ### §3g: LHS direction of the cuts-of-cuts bijection -/

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
