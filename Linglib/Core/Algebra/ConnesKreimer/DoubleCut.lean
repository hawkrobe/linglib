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
abbrev DoubleCut (T : TraceTree α Unit) : Type _ :=
  (Σ C : CutShape T, AugCutShape (CutShape.remainder C)) ⊕ Unit

namespace DoubleCut

/-- An outer real cut `C` paired with an augmented inner cut on
    `remainder C`. The triple-tensor is
    `(cutForest C) ⊗ (extracted by ac₂) ⊗ (remainder of ac₂)`. -/
abbrev real {T : TraceTree α Unit} (C : CutShape T)
    (ac₂ : AugCutShape (CutShape.remainder C)) : DoubleCut T :=
  Sum.inl ⟨C, ac₂⟩

/-- The trivial double cut: the entire tree at `BOT`. The triple-tensor
    is `forestToHc {T} ⊗ 1 ⊗ 1` (mirroring `AugCutShape.extractWhole`
    at the outer level). -/
abbrev extractWhole {T : TraceTree α Unit} : DoubleCut T := Sum.inr ()

/-- The triple-tensor associated with a double cut, in the right-iterated
    form `(Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))`. Mirrors the structure
    of `(id ⊗ Δ^c) ∘ Δ^c (forestToHc {T})`:
    - LEFT slot: `forestToHc (cutForest C)` (the outer extracted forest)
    - MIDDLE slot: `forestToHc (cutForest_aug ac₂)` (the inner extracted)
    - RIGHT slot: `forestToHc (remainderForest ac₂)` (the final remainder)

    For `extractWhole`: triple is `forestToHc {T} ⊗ 1 ⊗ 1` (with both `1`s
    being `forestToHc 0`). -/
noncomputable def tripleTensor (R : Type*) [CommSemiring R]
    {T : TraceTree α Unit} : DoubleCut T → (Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))
  | .inl ⟨C, ac₂⟩ =>
      forestToHc (R := R) (CutShape.cutForest C)
        ⊗ₜ[R] (forestToHc (R := R) (AugCutShape.cutForest_aug ac₂)
                ⊗ₜ[R] forestToHc (R := R) (AugCutShape.remainderForest ac₂))
  | .inr _ =>
      forestToHc (R := R) ({T} : TraceForest α Unit)
        ⊗ₜ[R] (forestToHc (R := R) (0 : TraceForest α Unit)
                ⊗ₜ[R] forestToHc (R := R) (0 : TraceForest α Unit))

@[simp] lemma tripleTensor_real {T : TraceTree α Unit} (C : CutShape T)
    (ac₂ : AugCutShape (CutShape.remainder C)) :
    tripleTensor R (real C ac₂)
      = forestToHc (R := R) (CutShape.cutForest C)
          ⊗ₜ[R] (forestToHc (R := R) (AugCutShape.cutForest_aug ac₂)
                  ⊗ₜ[R] forestToHc (R := R) (AugCutShape.remainderForest ac₂)) := rfl

@[simp] lemma tripleTensor_extractWhole {T : TraceTree α Unit} :
    tripleTensor R (extractWhole : DoubleCut T)
      = forestToHc (R := R) ({T} : TraceForest α Unit)
          ⊗ₜ[R] (forestToHc (R := R) (0 : TraceForest α Unit)
                  ⊗ₜ[R] forestToHc (R := R) (0 : TraceForest α Unit)) := rfl

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
theorem rhs_eq_sum_DoubleCut (T : TraceTree α Unit) :
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
              ⊗ₜ[R] forestToHc (R := R) ({CutShape.remainder C} : TraceForest α Unit))
              : Hc R α ⊗[R] Hc R α)
        = ∑ ac2 : AugCutShape (CutShape.remainder C),
            DoubleCut.tripleTensor R (DoubleCut.real C ac2)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    -- Goal: forestToHc (cutForest C) ⊗ Δ(forestToHc {remainder C})
    --     = ∑ ac2, ...
    -- comulAlgHom (forestToHc {remainder C}) = comulForest {remainder C} = comulTree (remainder C)
    have hΔ : comulAlgHom (forestToHc (R := R) ({CutShape.remainder C} : TraceForest α Unit))
            = comulTree (CutShape.remainder C) := by
      show comulAlgHom (Finsupp.single ({CutShape.remainder C} : TraceForest α Unit) (1 : R))
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
    have h1 : (forestToHc (R := R) (0 : TraceForest α Unit) : Hc R α) = 1 := by
      show (Finsupp.single (0 : TraceForest α Unit) (1 : R) : AddMonoidAlgebra R (TraceForest α Unit))
         = (1 : AddMonoidAlgebra R (TraceForest α Unit))
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
lemma lhs_eq_sum_DoubleCut_of_primitive_tree (T : TraceTree α Unit)
    (hPrim : (comulTree (R := R) T : Hc R α ⊗[R] Hc R α)
           = forestToHc (R := R) ({T} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)
             + (1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T} : TraceForest α Unit)) :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
          (AlgHom.id R (Hc R α))) (comulTree T : Hc R α ⊗[R] Hc R α))
      = ∑ dc : DoubleCut T, dc.tripleTensor R := by
  rw [← rhs_eq_sum_DoubleCut]
  -- Bridge: comulTree T = comulAlgHom (forestToHc {T})
  have hbridge : (comulTree (R := R) T : Hc R α ⊗[R] Hc R α)
               = comulAlgHom (forestToHc (R := R) ({T} : TraceForest α Unit)) := by
    show (comulTree T : Hc R α ⊗[R] Hc R α)
       = comulAlgHom (Finsupp.single ({T} : TraceForest α Unit) (1 : R))
    rw [comulAlgHom_apply_single]
    show comulTree T = ((({T} : TraceForest α Unit).map (comulTree (R := R))).prod : Hc R α ⊗[R] Hc R α)
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
noncomputable def lhsMultiset (T : TraceTree α Unit) :
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
theorem lhs_eq_sum_lhsMultiset (T : TraceTree α Unit) :
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
noncomputable def lhsExtractWhole (T : TraceTree α Unit) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Multiset.Sections (({T} : TraceForest α Unit).map (comulTreeMS R))).map fun s =>
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
      (s.prod ⊗ₜ[R] forestToHc (R := R) (0 : TraceForest α Unit))

/-- The "real cuts" contributions to `lhsMultiset`: for each `C : CutShape T`,
    sections over the multi-tree forest `(cutForest C).map comulTreeMS`.
    Outer bind iterates over `C`. -/
noncomputable def lhsRealCuts (T : TraceTree α Unit) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (CutShape T)).val.bind fun C =>
    (Multiset.Sections ((CutShape.cutForest C).map (comulTreeMS R))).map fun s =>
      (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        (s.prod ⊗ₜ[R] forestToHc (R := R) ({CutShape.remainder C} : TraceForest α Unit))

/-- `lhsMultiset T = lhsRealCuts T + lhsExtractWhole T`. Decomposes the bind
    over `AugCutShape T = CutShape T ⊕ Unit` into its two halves. -/
theorem lhsMultiset_decomp (T : TraceTree α Unit) :
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
theorem lhsExtractWhole_eq (T : TraceTree α Unit) :
    (lhsExtractWhole T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = (Finset.univ : Finset (AugCutShape T)).val.map fun ac' =>
          forestToHc (R := R) (AugCutShape.cutForest_aug ac')
            ⊗ₜ[R] (forestToHc (R := R) (AugCutShape.remainderForest ac')
              ⊗ₜ[R] forestToHc (R := R) (0 : TraceForest α Unit)) := by
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
noncomputable def rhsMultiset (T : TraceTree α Unit) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (DoubleCut T)).val.map (·.tripleTensor R)

/-- The RHS Finset.sum equals the `rhsMultiset` Multiset.sum. -/
theorem rhs_eq_sum_rhsMultiset (T : TraceTree α Unit) :
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
noncomputable def rhsExtractWhole (T : TraceTree α Unit) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  ({(DoubleCut.extractWhole : DoubleCut T).tripleTensor R} : Multiset _)

/-- The "outer real C, inner extractWhole" contribution: one triple per
    `C : CutShape T`. -/
noncomputable def rhsRealExtractInner (T : TraceTree α Unit) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (CutShape T)).val.map fun C =>
    (DoubleCut.real C (AugCutShape.extractWhole : AugCutShape _)).tripleTensor R

/-- The "outer real C, inner real C₂" contribution: bind over `(C, C₂)`. -/
noncomputable def rhsRealRealInner (T : TraceTree α Unit) :
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
theorem lhsExtractWhole_eq_rhsExtractWhole_add_realExtractInner (T : TraceTree α Unit) :
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
private theorem rhsMultiset_split_outer (T : TraceTree α Unit) :
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
private theorem rhsRealSigma_split_inner (T : TraceTree α Unit) :
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
theorem rhsMultiset_decomp (T : TraceTree α Unit) :
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
inductive GeoCut : TraceTree α Unit → Layer → Type _
  | leaf {a : α} (myL : Layer) : GeoCut (.leaf a) myL
  | trace {b : Unit} (myL : Layer) : GeoCut (.trace b) myL
  | node {l r : TraceTree α Unit} {myL lL rL : Layer}
      (hl : lL ≤ myL) (hr : rL ≤ myL)
      (hlNT : TraceTree.IsNotTrace l ∨ lL = myL)
      (hrNT : TraceTree.IsNotTrace r ∨ rL = myL)
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
def nodeGeoCutEquiv (l r : TraceTree α Unit) (myL : Layer) :
    (Σ (lL : {x : Layer // x ≤ myL ∧ (TraceTree.IsNotTrace l ∨ x = myL)})
       (rL : {x : Layer // x ≤ myL ∧ (TraceTree.IsNotTrace r ∨ x = myL)}),
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
instance instFintypeGeoCut : ∀ (T : TraceTree α Unit) (myL : Layer),
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
  - `myL = .bot`: `.trace ()` (the whole subtree is BOT-extracted; appears as a trace).
  - `myL = .mid`: `.trace ()` (the whole subtree appears as a trace whose data is the
    original `T` — slot 3 only sees the outer cut, and the outer cut extracts T as
    a unit; T's MID-vs-BOT internal split is orthogonal).
  - `myL = .top`: recursive — for `.node l r`, becomes `.node (geoStackItem gl) (geoStackItem gr)`.

The triple is then `(geoBotForest g, geoMidForest g, {geoStackItem g})` — assembled
into `Hc ⊗ (Hc ⊗ Hc)` via `forestToHc` and `⊗ₜ`. For a top-rooted GeoCut on `T`
this matches the LHS-style triple from `lhsRealCuts T` (and the RHS-style from
`rhsRealRealInner T` after the substantive Foissy bijection). -/

/-- `T` with each BOT subtree replaced by a `.trace` marker carrying the cut
    subtree as data. (For `myL = .bot`, the whole `T` is BOT, becomes `.trace ()`.) -/
def geoOuterSkeleton {T : TraceTree α Unit} {myL : Layer} (g : GeoCut T myL) :
    TraceTree α Unit :=
  match myL, g with
  | .bot, _ => .trace ()
  | .mid, .leaf _ => T
  | .mid, .trace _ => T
  | .mid, .node _ _ _ _ gl gr => .node (geoOuterSkeleton gl) (geoOuterSkeleton gr)
  | .top, .leaf _ => T
  | .top, .trace _ => T
  | .top, .node _ _ _ _ gl gr => .node (geoOuterSkeleton gl) (geoOuterSkeleton gr)

/-- The contribution this subtree makes to its **parent's** TOP slot — i.e., what
    appears at this subtree's position in the parent's slot-3 (outer-remainder) tree.
    - `myL ∈ {.bot, .mid}`: `.trace ()` — the **whole** original subtree T as trace
      data. This matches the LHS-reading semantics: the outer cut extracts T as a
      unit (whether T's MID structure goes through inner-cut decomposition is
      orthogonal — slot 3 only sees the outer cut).
    - `myL = .top`: recursive — vertices kept at top form the structure; deeper
      BOT/MID positions become `.trace` via `geoStackItem` on subtrees. -/
def geoStackItem {T : TraceTree α Unit} {myL : Layer} (g : GeoCut T myL) :
    TraceTree α Unit :=
  match myL, g with
  | .bot, _ => .trace ()
  | .mid, _ => .trace ()
  | .top, .leaf _ => T
  | .top, .trace _ => T
  | .top, .node _ _ _ _ gl gr => .node (geoStackItem gl) (geoStackItem gr)

/-- The BOT-slot forest contributed by this GeoCut: subtrees rooted at BOT vertices. -/
def geoBotForest {T : TraceTree α Unit} {myL : Layer} (g : GeoCut T myL) : TraceForest α Unit :=
  match myL, g with
  | .bot, _ => ({T} : TraceForest α Unit)
  | .mid, .leaf _ => 0
  | .mid, .trace _ => 0
  | .mid, .node _ _ _ _ gl gr => geoBotForest gl + geoBotForest gr
  | .top, .leaf _ => 0
  | .top, .trace _ => 0
  | .top, .node _ _ _ _ gl gr => geoBotForest gl + geoBotForest gr

/-- The MID-slot forest contributed by this GeoCut: each MID-rooted subtree
    contributes its outer-remainder skeleton (BOT positions become traces). -/
def geoMidForest {T : TraceTree α Unit} {myL : Layer} (g : GeoCut T myL) : TraceForest α Unit :=
  match myL, g with
  | .bot, _ => 0
  | .mid, _ => ({geoOuterSkeleton g} : TraceForest α Unit)
  | .top, .leaf _ => 0
  | .top, .trace _ => 0
  | .top, .node _ _ _ _ gl gr => geoMidForest gl + geoMidForest gr

/-- The triple-tensor extracted from a GeoCut. For a top-rooted GeoCut on `T`,
    this equals both the LHS-style triple from `lhsRealCuts` and the RHS-style
    triple from `rhsRealRealInner` (the substantive cuts-of-cuts identity). -/
noncomputable def geoCutToTriple (R : Type*) [CommSemiring R]
    {T : TraceTree α Unit} {myL : Layer} (g : GeoCut T myL) :
    (Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α)) :=
  forestToHc (R := R) (geoBotForest g) ⊗ₜ[R]
    (forestToHc (R := R) (geoMidForest g) ⊗ₜ[R]
      forestToHc (R := R) ({geoStackItem g} : TraceForest α Unit))

/-- The "GeoCut multiset" on `T`: enumerate `GeoCut T Layer.top` and project each
    to its triple-tensor via `geoCutToTriple`. This is the canonical 3-coloring
    enumeration that both `lhsRealCuts T` and `rhsRealRealInner T` will be shown
    to factor through. -/
noncomputable def geoMultiset (T : TraceTree α Unit) :
    Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))) :=
  (Finset.univ : Finset (GeoCut T Layer.top)).val.map (geoCutToTriple R)

/-! ### Per-subtree "child slots": substrate for the .node bijection

A `ChildSlots α` triple `⟨BOT, MID, stack⟩` represents one subtree's contribution
to a parent's triple-tensor:
- `bot : TraceForest α Unit` — subtrees of T that go to the BOT slot.
- `mid : TraceForest α Unit` — subtrees of T (each as outer-skeleton) that go to the MID slot.
- `stack : TraceTree α Unit` — what appears at T's position in the parent's slot-3 tree.

The triple-tensor for a subtree equals `forestToHc(bot) ⊗ (forestToHc(mid) ⊗ forestToHc({stack}))`.

For the .node l r bijection, both the LHS and the (any-layer) GeoCut enumerate
the SAME multiset of `ChildSlots` per subtree — this is the key inductive
hypothesis. -/

/-- Per-subtree child-slot data: the `(BOT, MID, stack)` triple in named-field form.
    `BOT`/`MID` are forests; `stack` is the single tree at this subtree's position
    in the parent's slot-3 tree. -/
structure ChildSlots (α : Type*) where
  bot   : TraceForest α Unit
  mid   : TraceForest α Unit
  stack : TraceTree α Unit

/-- Project a GeoCut to its child-slot triple. -/
def geoToChildSlots {T : TraceTree α Unit} {myL : Layer} (g : GeoCut T myL) :
    ChildSlots α :=
  ⟨geoBotForest g, geoMidForest g, geoStackItem g⟩

/-- Convert a child-slot triple to its triple-tensor. -/
noncomputable def ChildSlots.toTriple (R : Type*) [CommSemiring R]
    (cs : ChildSlots α) : (Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α)) :=
  forestToHc (R := R) cs.bot ⊗ₜ[R]
    (forestToHc (R := R) cs.mid ⊗ₜ[R] forestToHc (R := R) ({cs.stack} : TraceForest α Unit))

/-- `geoCutToTriple` factors as `ChildSlots.toTriple ∘ geoToChildSlots`. -/
theorem geoCutToTriple_eq {T : TraceTree α Unit} {myL : Layer} (g : GeoCut T myL) :
    geoCutToTriple R g = (geoToChildSlots g).toTriple R := rfl

/-! ### `perLayerContrib`: per-layer LHS contribution

Used by Session 2's `lhsRealCuts_eq_lhsIndexSum` (in `LhsBridge.lean`) via the
algebraic bridge `lhsRealCuts_eq_perLayerContrib_top` below. The substantive
GeoCut bijection lives in `LhsEquiv.lean` and bypasses this hub entirely. -/

/-- Per-layer LHS contribution at the subtree level.
- `.bot`: parent extracts T whole + inner = extractWhole. Single ChildSlots
  `⟨{T}, 0, .trace ()⟩`.
- `.mid`: parent extracts T whole + inner = real cl_inner. One ChildSlots per
  `cl_inner ∈ CutShape T`: `⟨cutForest cl_inner, {remainder cl_inner}, .trace ()⟩`.
- `.top`: parent recurses with `cl_outer ∈ CutShape T` + per-tree inner section.
  `⟨recursive BOT, recursive MID, remainder cl_outer⟩`. -/
noncomputable def perLayerContrib (T : TraceTree α Unit) :
    Layer → Multiset (ChildSlots α)
  | .bot =>
      ({⟨({T} : TraceForest α Unit), 0, .trace ()⟩} : Multiset (ChildSlots α))
  | .mid =>
      (Finset.univ : Finset (CutShape T)).val.map fun cl_inner =>
        ⟨CutShape.cutForest cl_inner,
         ({CutShape.remainder cl_inner} : TraceForest α Unit),
         .trace ()⟩
  | .top =>
      (Finset.univ : Finset (CutShape T)).val.bind fun cl_outer =>
        (Multiset.Sections ((CutShape.cutForest cl_outer).map fun T' =>
          (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
            ((AugCutShape.cutForest_aug ac' : TraceForest α Unit),
             (AugCutShape.remainderForest ac' : TraceForest α Unit)))).map fun s =>
          ⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
           CutShape.remainder cl_outer⟩

/-! #### `botGeoCut`: the canonical .bot-rooted GeoCut -/

/-- For `myL = .bot`, the layer constraint `lL ≤ .bot` forces `lL = .bot`. -/
private theorem Layer.le_bot_iff (lL : Layer) : lL ≤ Layer.bot ↔ lL = Layer.bot := by
  constructor
  · intro h; cases lL <;> first | rfl | (exact absurd h (by decide))
  · intro h; subst h; exact le_refl _

/-- The canonical "all-bot" GeoCut on T. -/
def botGeoCut : ∀ (T : TraceTree α Unit), GeoCut T Layer.bot
  | .leaf _ => GeoCut.leaf Layer.bot
  | .trace _ => GeoCut.trace Layer.bot
  | .node l r =>
      GeoCut.node (le_refl _) (le_refl _) (Or.inr rfl) (Or.inr rfl)
        (botGeoCut l) (botGeoCut r)

omit [DecidableEq α] in
/-- Every `g : GeoCut T .bot` equals `botGeoCut T`. Combined with `Inhabited` via
    `botGeoCut`, gives `Unique (GeoCut T .bot)`. -/
theorem botGeoCut_unique : ∀ {T : TraceTree α Unit} (g : GeoCut T Layer.bot),
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

instance instUniqueGeoCutBot (T : TraceTree α Unit) : Unique (GeoCut T Layer.bot) where
  default := botGeoCut T
  uniq := botGeoCut_unique

/-! #### `midGeoCut`: bijection `CutShape T ≃ GeoCut T Layer.mid`

For each `cl_inner : CutShape T`, the corresponding `GeoCut T Layer.mid` represents
"T at MID with `cl_inner` determining the BOT-extraction within T". The bijection
preserves the (BOT, MID, stack) data: extracted subtrees → BOT, kept subtrees →
MID structure, T-vertex → MID. -/

/-- Forward: convert `cl_inner : CutShape T` to the corresponding `GeoCut T .mid`. -/
def midGeoCut : ∀ (T : TraceTree α Unit), CutShape T → GeoCut T Layer.mid
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
def fromMidGeoCut : ∀ {T : TraceTree α Unit}, GeoCut T Layer.mid → CutShape T
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
          have hLT : TraceTree.IsNotTrace l := hlNT.resolve_right (by decide)
          have hRT : TraceTree.IsNotTrace r := hrNT.resolve_right (by decide)
          exact CutShape.bothCut hLT hRT
        | mid =>
          have hLT : TraceTree.IsNotTrace l := hlNT.resolve_right (by decide)
          exact CutShape.onlyLeftCut hLT (fromMidGeoCut gr)
        | top => exact absurd hr (by decide)
      | mid =>
        cases rL with
        | bot =>
          have hRT : TraceTree.IsNotTrace r := hrNT.resolve_right (by decide)
          exact CutShape.onlyRightCut hRT (fromMidGeoCut gl)
        | mid => exact CutShape.bothRecurse (fromMidGeoCut gl) (fromMidGeoCut gr)
        | top => exact absurd hr (by decide)
      | top => exact absurd hl (by decide)

/-! #### Helper lemmas: `geoToChildSlots ∘ midGeoCut` matches `(cutForest, {remainder}, .trace ())`. -/

omit [DecidableEq α] in
/-- For `myL = .mid`, `geoBotForest (midGeoCut T cl) = cutForest cl`. -/
theorem geoBotForest_midGeoCut : ∀ (T : TraceTree α Unit) (cl : CutShape T),
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
theorem geoOuterSkeleton_midGeoCut : ∀ (T : TraceTree α Unit) (cl : CutShape T),
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
theorem geoMidForest_midGeoCut (T : TraceTree α Unit) (cl : CutShape T) :
    geoMidForest (midGeoCut T cl) = ({CutShape.remainder cl} : TraceForest α Unit) := by
  -- For myL = mid, geoMidForest = ({geoOuterSkeleton g} : TraceForest α Unit).
  rw [show geoMidForest (midGeoCut T cl)
        = ({geoOuterSkeleton (midGeoCut T cl)} : TraceForest α Unit) by
       cases cl <;> rfl,
      geoOuterSkeleton_midGeoCut]

omit [DecidableEq α] in
/-- For `myL = .mid`, `geoStackItem (midGeoCut T cl) = .trace ()`. -/
theorem geoStackItem_midGeoCut (T : TraceTree α Unit) (cl : CutShape T) :
    geoStackItem (midGeoCut T cl) = .trace () := by
  -- For myL = mid, geoStackItem = .trace () always.
  cases cl <;> rfl

/-! #### Bijection: midGeoCut ↔ fromMidGeoCut

The forward (`midGeoCut`) and backward (`fromMidGeoCut`) directions are mutually
inverse on `.node l r`. Proofs by case analysis on the constructor + IH on
recursive sub-CutShapes / sub-GeoCuts. -/

omit [DecidableEq α] in
/-- Roundtrip 1: `fromMidGeoCut ∘ midGeoCut = id`. -/
theorem fromMidGeoCut_midGeoCut : ∀ (T : TraceTree α Unit) (cl : CutShape T),
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
private theorem trace_nt_eq_inl {T : TraceTree α Unit} {lL myL : Layer}
    (h : TraceTree.IsNotTrace T ∨ lL = myL) (hne : lL ≠ myL) :
    h = Or.inl (h.resolve_right hne) := by
  rcases h with _ | hne'
  · rfl
  · exact absurd hne' hne

omit [DecidableEq α] in
/-- Roundtrip 2: `midGeoCut ∘ fromMidGeoCut = id`. Uses `botGeoCut_unique`
    for `gl/gr` at layer `.bot`, IH for `gl/gr` at layer `.mid`. -/
theorem midGeoCut_fromMidGeoCut : ∀ {T : TraceTree α Unit} (g : GeoCut T Layer.mid),
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
def midGeoCutEquiv (T : TraceTree α Unit) : CutShape T ≃ GeoCut T Layer.mid where
  toFun := midGeoCut T
  invFun := fromMidGeoCut
  left_inv := fromMidGeoCut_midGeoCut T
  right_inv := midGeoCut_fromMidGeoCut

/-! ### `rhsToGeoCut` and `geoCutToRhs` — the RHS-side substantive Foissy bijection

The RHS-style "double cut" indexing `(C₁ : CutShape T, C₂ : CutShape (remainder C₁))`
bijections to `GeoCut T .top`. This IS the substantive Foissy cut-commutation content,
named honestly as a bijection of indexing types — not as an algebraic-bridge "equality".

By structural recursion on T with case analysis on C₁ and C₂'s ctors. The .node case
has 9 sub-cases (4 for `bothRecurse cl cr`, 2 for `onlyLeftCut`, 2 for `onlyRightCut`,
1 for `bothCut`), matching the 9 (lL, rL) cells of `GeoCut .node`. -/

/-- Forward: `(C₁, C₂)` double-cut to its `GeoCut` 3-coloring. -/
noncomputable def rhsToGeoCut : ∀ {T : TraceTree α Unit}
    (C₁ : CutShape T) (_C₂ : CutShape (CutShape.remainder C₁)),
    GeoCut T Layer.top
  | .leaf _, .atLeaf, c2 =>
      have : c2 = .atLeaf := match c2 with | .atLeaf => rfl
      GeoCut.leaf Layer.top
  | .trace _, .atTrace, c2 =>
      have : c2 = .atTrace := match c2 with | .atTrace => rfl
      GeoCut.trace Layer.top
  | .node l r, .bothCut hl hr, .bothRecurse .atTrace .atTrace =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.top)
        (by decide : Layer.bot ≤ Layer.top)
        (Or.inl hl) (Or.inl hr)
        (botGeoCut l) (botGeoCut r)
  | .node l r, .onlyLeftCut hl cr, .bothRecurse .atTrace cr2 =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.top) (le_refl _)
        (Or.inl hl) (Or.inr rfl)
        (botGeoCut l) (rhsToGeoCut (T := r) cr cr2)
  | .node l r, .onlyLeftCut hl cr, .onlyRightCut hr2 .atTrace =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.top)
        (by decide : Layer.mid ≤ Layer.top)
        (Or.inl hl) (Or.inl (CutShape.isNotTrace_of_isNotTrace_remainder cr hr2))
        (botGeoCut l) (midGeoCut r cr)
  | .node l r, .onlyRightCut hr cl, .bothRecurse cl2 .atTrace =>
      GeoCut.node (le_refl _) (by decide : Layer.bot ≤ Layer.top)
        (Or.inr rfl) (Or.inl hr)
        (rhsToGeoCut (T := l) cl cl2) (botGeoCut r)
  | .node l r, .onlyRightCut hr cl, .onlyLeftCut hl2 .atTrace =>
      GeoCut.node (by decide : Layer.mid ≤ Layer.top)
        (by decide : Layer.bot ≤ Layer.top)
        (Or.inl (CutShape.isNotTrace_of_isNotTrace_remainder cl hl2)) (Or.inl hr)
        (midGeoCut l cl) (botGeoCut r)
  | .node l r, .bothRecurse cl cr, .bothRecurse cl2 cr2 =>
      GeoCut.node (le_refl _) (le_refl _)
        (Or.inr rfl) (Or.inr rfl)
        (rhsToGeoCut (T := l) cl cl2) (rhsToGeoCut (T := r) cr cr2)
  | .node l r, .bothRecurse cl cr, .bothCut hl2 hr2 =>
      GeoCut.node (by decide : Layer.mid ≤ Layer.top)
        (by decide : Layer.mid ≤ Layer.top)
        (Or.inl (CutShape.isNotTrace_of_isNotTrace_remainder cl hl2))
        (Or.inl (CutShape.isNotTrace_of_isNotTrace_remainder cr hr2))
        (midGeoCut l cl) (midGeoCut r cr)
  | .node l r, .bothRecurse cl cr, .onlyLeftCut hl2 cr2 =>
      GeoCut.node (by decide : Layer.mid ≤ Layer.top) (le_refl _)
        (Or.inl (CutShape.isNotTrace_of_isNotTrace_remainder cl hl2))
        (Or.inr rfl)
        (midGeoCut l cl) (rhsToGeoCut (T := r) cr cr2)
  | .node l r, .bothRecurse cl cr, .onlyRightCut hr2 cl2 =>
      GeoCut.node (le_refl _) (by decide : Layer.mid ≤ Layer.top)
        (Or.inr rfl)
        (Or.inl (CutShape.isNotTrace_of_isNotTrace_remainder cr hr2))
        (rhsToGeoCut (T := l) cl cl2) (midGeoCut r cr)

/-- Inverse: `GeoCut T .top` to its `(C₁, C₂)` double-cut representation.
    Inverts `rhsToGeoCut` by case analysis on the GeoCut node's child layers `(lL, rL)`. -/
noncomputable def geoCutToRhs : ∀ {T : TraceTree α Unit} (_g : GeoCut T Layer.top),
    Σ C₁ : CutShape T, CutShape (CutShape.remainder C₁)
  | .leaf _, .leaf _ => ⟨.atLeaf, .atLeaf⟩
  | .trace _, .trace _ => ⟨.atTrace, .atTrace⟩
  | .node l r, .node (lL := lL) (rL := rL) _ _ hlNT hrNT gl gr =>
    match lL, rL, hlNT, hrNT, gl, gr with
    | .bot, .bot, hlNT, hrNT, _, _ =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        ⟨CutShape.bothCut hl_NT hr_NT, CutShape.bothRecurse .atTrace .atTrace⟩
    | .bot, .mid, hlNT, hrNT, _, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let cr := fromMidGeoCut gr
        ⟨CutShape.onlyLeftCut hl_NT cr,
         CutShape.onlyRightCut (CutShape.isNotTrace_remainder cr hr_NT) .atTrace⟩
    | .bot, .top, hlNT, _, _, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        let ⟨cr, cr2⟩ := geoCutToRhs (T := r) gr
        ⟨CutShape.onlyLeftCut hl_NT cr, CutShape.bothRecurse .atTrace cr2⟩
    | .mid, .bot, hlNT, hrNT, gl, _ =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        let cl := fromMidGeoCut gl
        ⟨CutShape.onlyRightCut hr_NT cl,
         CutShape.onlyLeftCut (CutShape.isNotTrace_remainder cl hl_NT) .atTrace⟩
    | .mid, .mid, hlNT, hrNT, gl, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let cl := fromMidGeoCut gl
        let cr := fromMidGeoCut gr
        ⟨CutShape.bothRecurse cl cr,
         CutShape.bothCut (CutShape.isNotTrace_remainder cl hl_NT)
           (CutShape.isNotTrace_remainder cr hr_NT)⟩
    | .mid, .top, hlNT, _, gl, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let cl := fromMidGeoCut gl
        let ⟨cr, cr2⟩ := geoCutToRhs (T := r) gr
        ⟨CutShape.bothRecurse cl cr,
         CutShape.onlyLeftCut (CutShape.isNotTrace_remainder cl hl_NT) cr2⟩
    | .top, .bot, _, hrNT, gl, _ =>
        let hr_NT := hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        let ⟨cl, cl2⟩ := geoCutToRhs (T := l) gl
        ⟨CutShape.onlyRightCut hr_NT cl, CutShape.bothRecurse cl2 .atTrace⟩
    | .top, .mid, _, hrNT, gl, gr =>
        let hr_NT := hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let ⟨cl, cl2⟩ := geoCutToRhs (T := l) gl
        let cr := fromMidGeoCut gr
        ⟨CutShape.bothRecurse cl cr,
         CutShape.onlyRightCut (CutShape.isNotTrace_remainder cr hr_NT) cl2⟩
    | .top, .top, _, _, gl, gr =>
        let ⟨cl, cl2⟩ := geoCutToRhs (T := l) gl
        let ⟨cr, cr2⟩ := geoCutToRhs (T := r) gr
        ⟨CutShape.bothRecurse cl cr, CutShape.bothRecurse cl2 cr2⟩

/-- `Or.inl ∘ resolve_right` collapses to the original disjunction when the
    right disjunct is impossible. Mathlib gap (parallel to `_root_.Multiset.Sections_map_map`
    below — both `[UPSTREAM]` candidates). -/
theorem _root_.Or.inl_resolve_right_eq
    {p q : Prop} (h : p ∨ q) (hne : ¬ q) :
    Or.inl (h.resolve_right hne) = h := by
  rcases h with h1 | h2
  · rfl
  · exact absurd h2 hne

omit [DecidableEq α] in
/-- Left inverse: `geoCutToRhs (rhsToGeoCut C₁ C₂) = ⟨C₁, C₂⟩`.
    By structural induction on T + case analysis on (C₁ ctor, C₂ ctor). For each of
    the 9 .node sub-cases, the roundtrip is `rfl` after `simp only` unfolding and
    application of IH on subtrees and `fromMidGeoCut_midGeoCut` on .mid GeoCuts. -/
theorem geoCutToRhs_rhsToGeoCut : ∀ {T : TraceTree α Unit}
    (C₁ : CutShape T) (C₂ : CutShape (CutShape.remainder C₁)),
    geoCutToRhs (rhsToGeoCut C₁ C₂) = ⟨C₁, C₂⟩
  | .leaf _, .atLeaf, c2 => by
      have hc : c2 = .atLeaf := match c2 with | .atLeaf => rfl
      subst hc; rfl
  | .trace _, .atTrace, c2 => by
      have hc : c2 = .atTrace := match c2 with | .atTrace => rfl
      subst hc; rfl
  | .node l r, .bothCut hl hr, .bothRecurse .atTrace .atTrace => rfl
  | .node l r, .onlyLeftCut hl cr, .bothRecurse .atTrace cr2 => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [geoCutToRhs_rhsToGeoCut cr cr2]
  | .node l r, .onlyLeftCut hl cr, .onlyRightCut hr2 .atTrace => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [fromMidGeoCut_midGeoCut r cr]
  | .node l r, .onlyRightCut hr cl, .bothRecurse cl2 .atTrace => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [geoCutToRhs_rhsToGeoCut cl cl2]
  | .node l r, .onlyRightCut hr cl, .onlyLeftCut hl2 .atTrace => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [fromMidGeoCut_midGeoCut l cl]
  | .node l r, .bothRecurse cl cr, .bothRecurse cl2 cr2 => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [geoCutToRhs_rhsToGeoCut cl cl2, geoCutToRhs_rhsToGeoCut cr cr2]
  | .node l r, .bothRecurse cl cr, .bothCut hl2 hr2 => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [fromMidGeoCut_midGeoCut l cl, fromMidGeoCut_midGeoCut r cr]
  | .node l r, .bothRecurse cl cr, .onlyLeftCut hl2 cr2 => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [fromMidGeoCut_midGeoCut l cl, geoCutToRhs_rhsToGeoCut cr cr2]
  | .node l r, .bothRecurse cl cr, .onlyRightCut hr2 cl2 => by
      simp only [rhsToGeoCut, geoCutToRhs]
      rw [geoCutToRhs_rhsToGeoCut cl cl2, fromMidGeoCut_midGeoCut r cr]

omit [DecidableEq α] in
/-- Right inverse: `rhsToGeoCut (geoCutToRhs g).fst (geoCutToRhs g).snd = g`.
    By structural induction on T + case analysis on the GeoCut.node `(lL, rL)`.
    For each of the 9 (lL, rL) cells: use `botGeoCut_unique` to fix `.bot`-layer
    children, `midGeoCut_fromMidGeoCut` to round-trip `.mid` layers, and IH for
    `.top` layers. The `Or.inl (resolve_right _)` reconstructions collapse via
    `Or.inl_resolve_right_eq`. -/
theorem rhsToGeoCut_geoCutToRhs : ∀ {T : TraceTree α Unit} (g : GeoCut T Layer.top),
    rhsToGeoCut (geoCutToRhs g).fst (geoCutToRhs g).snd = g
  | .leaf _, .leaf _ => rfl
  | .trace _, .trace _ => rfl
  | .node l r, .node (lL := lL) (rL := rL) hl hr hlNT hrNT gl gr => by
    cases lL with
    | bot =>
      have hglEq : gl = botGeoCut l := botGeoCut_unique gl
      subst hglEq
      cases rL with
      | bot =>
        have hgrEq : gr = botGeoCut r := botGeoCut_unique gr
        subst hgrEq
        show GeoCut.node _ _ (Or.inl (hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
                              (Or.inl (hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top))) _ _ = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.bot ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.bot ≠ Layer.top)]
      | mid =>
        show GeoCut.node _ _ (Or.inl (hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
                              (Or.inl (hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top))) _
                              (midGeoCut r (fromMidGeoCut gr)) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.bot ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.mid ≠ Layer.top),
            midGeoCut_fromMidGeoCut gr]
      | top =>
        have ihr := rhsToGeoCut_geoCutToRhs gr
        show GeoCut.node _ _ (Or.inl (hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
                              hrNT _
                              (rhsToGeoCut (geoCutToRhs gr).fst (geoCutToRhs gr).snd) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.bot ≠ Layer.top), ihr]
    | mid =>
      cases rL with
      | bot =>
        have hgrEq : gr = botGeoCut r := botGeoCut_unique gr
        subst hgrEq
        show GeoCut.node _ _ (Or.inl (hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
                              (Or.inl (hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
                              (midGeoCut l (fromMidGeoCut gl)) _ = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.mid ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.bot ≠ Layer.top),
            midGeoCut_fromMidGeoCut gl]
      | mid =>
        show GeoCut.node _ _ (Or.inl (hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
                              (Or.inl (hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
                              (midGeoCut l (fromMidGeoCut gl))
                              (midGeoCut r (fromMidGeoCut gr)) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.mid ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.mid ≠ Layer.top),
            midGeoCut_fromMidGeoCut gl, midGeoCut_fromMidGeoCut gr]
      | top =>
        have ihr := rhsToGeoCut_geoCutToRhs gr
        show GeoCut.node _ _ (Or.inl (hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
                              hrNT
                              (midGeoCut l (fromMidGeoCut gl))
                              (rhsToGeoCut (geoCutToRhs gr).fst (geoCutToRhs gr).snd) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.mid ≠ Layer.top),
            midGeoCut_fromMidGeoCut gl, ihr]
    | top =>
      cases rL with
      | bot =>
        have hgrEq : gr = botGeoCut r := botGeoCut_unique gr
        subst hgrEq
        have ihl := rhsToGeoCut_geoCutToRhs gl
        show GeoCut.node _ _ hlNT
                              (Or.inl (hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
                              (rhsToGeoCut (geoCutToRhs gl).fst (geoCutToRhs gl).snd) _ = _
        rw [Or.inl_resolve_right_eq hrNT (by decide : Layer.bot ≠ Layer.top), ihl]
      | mid =>
        have ihl := rhsToGeoCut_geoCutToRhs gl
        show GeoCut.node _ _ hlNT
                              (Or.inl (hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
                              (rhsToGeoCut (geoCutToRhs gl).fst (geoCutToRhs gl).snd)
                              (midGeoCut r (fromMidGeoCut gr)) = _
        rw [Or.inl_resolve_right_eq hrNT (by decide : Layer.mid ≠ Layer.top),
            ihl, midGeoCut_fromMidGeoCut gr]
      | top =>
        have ihl := rhsToGeoCut_geoCutToRhs gl
        have ihr := rhsToGeoCut_geoCutToRhs gr
        show GeoCut.node _ _ hlNT hrNT
                              (rhsToGeoCut (geoCutToRhs gl).fst (geoCutToRhs gl).snd)
                              (rhsToGeoCut (geoCutToRhs gr).fst (geoCutToRhs gr).snd) = _
        rw [ihl, ihr]

/-- The RHS-side substantive Foissy bijection as an `Equiv`. -/
noncomputable def rhsGeoCutEquiv (T : TraceTree α Unit) :
    (Σ C₁ : CutShape T, CutShape (CutShape.remainder C₁)) ≃ GeoCut T Layer.top where
  toFun := fun ⟨C₁, C₂⟩ => rhsToGeoCut C₁ C₂
  invFun := geoCutToRhs
  left_inv := fun ⟨C₁, C₂⟩ => geoCutToRhs_rhsToGeoCut C₁ C₂
  right_inv := rhsToGeoCut_geoCutToRhs

/-! ### Per-element forest agreement under `rhsToGeoCut`

The Equiv `rhsGeoCutEquiv` between `(C₁, C₂)`-pairs and `GeoCut T .top`
preserves the triple-tensor data, which means the substantive Foissy
identity reduces to per-element agreement on each forest projection. -/

omit [DecidableEq α] in
/-- `geoBotForest (rhsToGeoCut C₁ C₂) = cutForest C₁`. By structural
    induction on T with case analysis on the (C₁, C₂) constructor pair. -/
theorem geoBotForest_rhsToGeoCut :
    ∀ {T : TraceTree α Unit} (C₁ : CutShape T)
      (C₂ : CutShape (CutShape.remainder C₁)),
    geoBotForest (rhsToGeoCut C₁ C₂) = CutShape.cutForest C₁
  | .leaf _, .atLeaf, c2 => by
      have hc : c2 = .atLeaf := match c2 with | .atLeaf => rfl
      subst hc; rfl
  | .trace _, .atTrace, c2 => by
      have hc : c2 = .atTrace := match c2 with | .atTrace => rfl
      subst hc; rfl
  | .node l r, .bothCut hl hr, .bothRecurse .atTrace .atTrace => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rfl
  | .node l r, .onlyLeftCut hl cr, .bothRecurse .atTrace cr2 => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_rhsToGeoCut cr cr2]
  | .node l r, .onlyLeftCut hl cr, .onlyRightCut hr2 .atTrace => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_midGeoCut r cr]
  | .node l r, .onlyRightCut hr cl, .bothRecurse cl2 .atTrace => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_rhsToGeoCut cl cl2]
  | .node l r, .onlyRightCut hr cl, .onlyLeftCut hl2 .atTrace => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_midGeoCut l cl]
  | .node l r, .bothRecurse cl cr, .bothRecurse cl2 cr2 => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_rhsToGeoCut cl cl2, geoBotForest_rhsToGeoCut cr cr2]
  | .node l r, .bothRecurse cl cr, .bothCut hl2 hr2 => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_midGeoCut l cl, geoBotForest_midGeoCut r cr]
  | .node l r, .bothRecurse cl cr, .onlyLeftCut hl2 cr2 => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_midGeoCut l cl, geoBotForest_rhsToGeoCut cr cr2]
  | .node l r, .bothRecurse cl cr, .onlyRightCut hr2 cl2 => by
      simp only [rhsToGeoCut, geoBotForest, CutShape.cutForest]
      rw [geoBotForest_rhsToGeoCut cl cl2, geoBotForest_midGeoCut r cr]

omit [DecidableEq α] in
/-- `geoMidForest (rhsToGeoCut C₁ C₂) = cutForest C₂`. -/
theorem geoMidForest_rhsToGeoCut :
    ∀ {T : TraceTree α Unit} (C₁ : CutShape T)
      (C₂ : CutShape (CutShape.remainder C₁)),
    geoMidForest (rhsToGeoCut C₁ C₂) = CutShape.cutForest C₂
  | .leaf _, .atLeaf, c2 => by
      have hc : c2 = .atLeaf := match c2 with | .atLeaf => rfl
      subst hc; rfl
  | .trace _, .atTrace, c2 => by
      have hc : c2 = .atTrace := match c2 with | .atTrace => rfl
      subst hc; rfl
  | .node l r, .bothCut hl hr, .bothRecurse .atTrace .atTrace => by
      simp only [rhsToGeoCut, geoMidForest, CutShape.cutForest]
      rfl
  | .node l r, .onlyLeftCut hl cr, .bothRecurse .atTrace cr2 => by
      simp only [rhsToGeoCut, geoMidForest, CutShape.cutForest]
      rw [geoMidForest_rhsToGeoCut cr cr2]
      rfl
  | .node l r, .onlyLeftCut hl cr, .onlyRightCut hr2 .atTrace => by
      simp only [rhsToGeoCut, CutShape.cutForest]
      show geoMidForest (.node _ _ _ _ _ _) = _
      simp only [geoMidForest]
      rw [geoOuterSkeleton_midGeoCut r cr]
      rfl
  | .node l r, .onlyRightCut hr cl, .bothRecurse cl2 .atTrace => by
      simp only [rhsToGeoCut, geoMidForest, CutShape.cutForest]
      rw [geoMidForest_rhsToGeoCut cl cl2]
      rfl
  | .node l r, .onlyRightCut hr cl, .onlyLeftCut hl2 .atTrace => by
      simp only [rhsToGeoCut, CutShape.cutForest]
      show geoMidForest (.node _ _ _ _ _ _) = _
      simp only [geoMidForest]
      rw [geoOuterSkeleton_midGeoCut l cl]
      rfl
  | .node l r, .bothRecurse cl cr, .bothRecurse cl2 cr2 => by
      simp only [rhsToGeoCut, geoMidForest, CutShape.cutForest]
      rw [geoMidForest_rhsToGeoCut cl cl2, geoMidForest_rhsToGeoCut cr cr2]
      rfl
  | .node l r, .bothRecurse cl cr, .bothCut hl2 hr2 => by
      simp only [rhsToGeoCut, CutShape.cutForest]
      show geoMidForest (.node _ _ _ _ _ _) = _
      simp only [geoMidForest]
      rw [geoOuterSkeleton_midGeoCut l cl, geoOuterSkeleton_midGeoCut r cr]
      rfl
  | .node l r, .bothRecurse cl cr, .onlyLeftCut hl2 cr2 => by
      simp only [rhsToGeoCut, CutShape.cutForest]
      show geoMidForest (.node _ _ _ _ _ _) = _
      simp only [geoMidForest]
      rw [geoOuterSkeleton_midGeoCut l cl, geoMidForest_rhsToGeoCut cr cr2]
      rfl
  | .node l r, .bothRecurse cl cr, .onlyRightCut hr2 cl2 => by
      simp only [rhsToGeoCut, CutShape.cutForest]
      show geoMidForest (.node _ _ _ _ _ _) = _
      simp only [geoMidForest]
      rw [geoMidForest_rhsToGeoCut cl cl2, geoOuterSkeleton_midGeoCut r cr]
      rfl

omit [DecidableEq α] in
/-- `geoStackItem (rhsToGeoCut C₁ C₂) = remainder C₂`.

    Now provable post-migration: with `β = Unit`, both sides only produce
    `.trace ()` markers (no recursive trace data), so the structural shapes
    match. Pre-migration this failed because LHS had `.trace T` (whole
    subtree) while RHS had `.trace (remainder cr)` (cut-remainder of
    subtree). The trace-data anonymization restores the bijection. -/
theorem geoStackItem_rhsToGeoCut :
    ∀ {T : TraceTree α Unit} (C₁ : CutShape T)
      (C₂ : CutShape (CutShape.remainder C₁)),
    geoStackItem (rhsToGeoCut C₁ C₂) = CutShape.remainder C₂
  | .leaf _, .atLeaf, c2 => by
      have hc : c2 = .atLeaf := match c2 with | .atLeaf => rfl
      subst hc; rfl
  | .trace _, .atTrace, c2 => by
      have hc : c2 = .atTrace := match c2 with | .atTrace => rfl
      subst hc; rfl
  | .node l r, .bothCut hl hr, .bothRecurse .atTrace .atTrace => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder]
  | .node l r, .onlyLeftCut hl cr, .bothRecurse .atTrace cr2 => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder]
      rw [geoStackItem_rhsToGeoCut cr cr2]
  | .node l r, .onlyLeftCut hl cr, .onlyRightCut hr2 .atTrace => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder, geoStackItem_midGeoCut]
  | .node l r, .onlyRightCut hr cl, .bothRecurse cl2 .atTrace => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder]
      rw [geoStackItem_rhsToGeoCut cl cl2]
  | .node l r, .onlyRightCut hr cl, .onlyLeftCut hl2 .atTrace => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder, geoStackItem_midGeoCut]
  | .node l r, .bothRecurse cl cr, .bothRecurse cl2 cr2 => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder]
      rw [geoStackItem_rhsToGeoCut cl cl2, geoStackItem_rhsToGeoCut cr cr2]
  | .node l r, .bothRecurse cl cr, .bothCut hl2 hr2 => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder, geoStackItem_midGeoCut]
  | .node l r, .bothRecurse cl cr, .onlyLeftCut hl2 cr2 => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder, geoStackItem_midGeoCut]
      rw [geoStackItem_rhsToGeoCut cr cr2]
  | .node l r, .bothRecurse cl cr, .onlyRightCut hr2 cl2 => by
      simp only [rhsToGeoCut, geoStackItem, CutShape.remainder, geoStackItem_midGeoCut]
      rw [geoStackItem_rhsToGeoCut cl cl2]

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
private lemma forestToHc_pair_prod (s : Multiset (TraceForest α Unit × TraceForest α Unit)) :
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
  | empty => simp only [Multiset.map_zero, Multiset.sections_zero, Multiset.map_singleton,
                        Multiset.map_zero]
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
theorem lhsRealCuts_eq_perLayerContrib_top (T : TraceTree α Unit) :
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

/-- Per-element triple agreement: for each `(C₁, C₂)`, the RHS double-cut's
    triple-tensor equals the GeoCut triple-tensor of the corresponding
    `rhsToGeoCut C₁ C₂`. Combines the three forest-agreement lemmas. -/
theorem tripleTensor_real_real_eq_geoCutToTriple {T : TraceTree α Unit}
    (C₁ : CutShape T) (C₂ : CutShape (CutShape.remainder C₁)) :
    (DoubleCut.real C₁ (AugCutShape.real C₂)).tripleTensor R
      = geoCutToTriple R (rhsToGeoCut C₁ C₂) := by
  unfold DoubleCut.tripleTensor geoCutToTriple
  simp only [AugCutShape.cutForest_aug_real, AugCutShape.remainderForest_real]
  rw [geoBotForest_rhsToGeoCut, geoMidForest_rhsToGeoCut,
      geoStackItem_rhsToGeoCut]

/-- **RHS bijection**: `rhsRealRealInner T` enumerates the same multiset of
    triples as `geoMultiset T`. Direct via `rhsGeoCutEquiv` and the per-element
    triple agreement, bypassing the `perLayerContrib` hub. -/
theorem rhsRealRealInner_eq_geoMultiset (T : TraceTree α Unit) :
    (rhsRealRealInner T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = geoMultiset T := by
  unfold rhsRealRealInner geoMultiset
  -- Step 1: rewrite the bind over CutShape T as a map over Sigma.
  rw [show ((Finset.univ : Finset (CutShape T)).val.bind fun C =>
            (Finset.univ : Finset (CutShape (CutShape.remainder C))).val.map fun C₂ =>
              (DoubleCut.real C (AugCutShape.real C₂)).tripleTensor R)
        = ((Finset.univ : Finset
              (Σ C₁ : CutShape T, CutShape (CutShape.remainder C₁))).val).map
            fun ⟨C₁, C₂⟩ =>
              (DoubleCut.real C₁ (AugCutShape.real C₂)).tripleTensor R from by
       rw [show ((Finset.univ : Finset
              (Σ C₁ : CutShape T, CutShape (CutShape.remainder C₁))).val)
             = (Finset.univ : Finset (CutShape T)).val.bind fun C₁ =>
                 (Finset.univ : Finset
                    (CutShape (CutShape.remainder C₁))).val.map
                   fun C₂ => (⟨C₁, C₂⟩ : Σ C, CutShape (CutShape.remainder C))
             from rfl]
       rw [Multiset.map_bind]
       refine Multiset.bind_congr (fun C _ => ?_)
       rw [Multiset.map_map]
       rfl]
  -- Step 2: convert univ Sigma to (univ GeoCut).map symm via rhsGeoCutEquiv.
  rw [show (Finset.univ : Finset
              (Σ C₁ : CutShape T, CutShape (CutShape.remainder C₁)))
        = (Finset.univ : Finset (GeoCut T Layer.top)).map
            (rhsGeoCutEquiv T).symm.toEmbedding from
       (Finset.map_univ_equiv (rhsGeoCutEquiv T).symm).symm]
  rw [Finset.map_val, Multiset.map_map]
  -- Step 3: per-element identity via tripleTensor_real_real_eq_geoCutToTriple.
  refine Multiset.map_congr rfl (fun g _ => ?_)
  rw [Function.comp_apply]
  -- (rhsGeoCutEquiv T).symm g destructures to (C₁, C₂). Apply the per-element
  -- identity, then use right_inv (rhsToGeoCut_geoCutToRhs) to collapse.
  show (DoubleCut.real (geoCutToRhs g).fst
            (AugCutShape.real (geoCutToRhs g).snd)).tripleTensor R = geoCutToTriple R g
  rw [tripleTensor_real_real_eq_geoCutToTriple, rhsToGeoCut_geoCutToRhs]

/-! Note: the LHS bijection (`lhsRealCuts_eq_geoMultiset`) and the cuts-of-cuts
identity theorems (`lhsRealCuts_eq_rhsRealRealInner`, `lhsMultiset_eq_rhsMultiset_node`,
`lhs_eq_sum_DoubleCut`) live in `LhsEquiv.lean`, where they are proven directly
via `lhsGeoCutEquiv` and the per-element forest agreement lemmas. -/

end ConnesKreimer
