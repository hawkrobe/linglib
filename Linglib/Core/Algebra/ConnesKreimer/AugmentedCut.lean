import Linglib.Core.Algebra.ConnesKreimer.Coproduct
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# Augmented Cuts on Trace-Anonymized Trees @cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

The `comulTree T` formula has two structurally distinct contributions:

  Δ^c(T) = forestToHc {T} ⊗ 1
         + ∑ C : CutShape T, forestToHc (cutForest C) ⊗ forestToHc {remainder C}

The first term (the "explicit" `T ⊗ 1`) corresponds to "extracting `T` whole"
— there is no admissible cut that produces this term (there is no edge above
the root to remove). The second sum ranges over real admissible cuts.

For the cuts-of-cuts coassociativity proof (M-C-B Lemma 1.2.10 /
@cite{foissy-2002} §2), it is convenient to **unify** these two cases as
"augmented cuts": a real admissible cut `C : CutShape T` *or* a virtual
"extract-whole" cut. The unified sum

  Δ^c(T) = ∑ ac : AugCutShape T,
    forestToHc (cutForest_aug ac) ⊗ forestToHc (remainderForest ac)

then admits a clean recursive treatment under iteration.

## Layout

This file provides the `AugCutShape` substrate; the actual coassoc proof
(double-cut bijection) lives in `Bialgebra.lean`'s `comul_coassoc_tree`.

## Carrier

Like `Coproduct.lean`, this file works on `TraceTree α Unit`. The bialgebra
basis carrier is `TraceForest α Unit`; trace labels are scalar (Unit) so the
`AugCutShape`-summed coproduct expression matches Connes-Kreimer's
Feynman-graph CK structure (see `Decorated.lean` rationale citing
@cite{marcolli-skigin-2025} §10.1).

## Layer status

`[UPSTREAM]` candidate, paired with `Bialgebra.lean`. Future home is
something like
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.AugmentedCut`.
-/

namespace ConnesKreimer

open scoped TensorProduct
open Finsupp

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## §1: `AugCutShape T` — augmented cut shapes

`AugCutShape T = CutShape T ⊕ Unit`, where
- `Sum.inl C` is a real admissible cut `C : CutShape T`
- `Sum.inr ()` is the virtual "extract-whole" cut

`abbrev` so that mathlib's `Fintype` and `DecidableEq` instances on `Sum`
apply automatically. -/

/-- An augmented cut on `T`: a real admissible cut, or the virtual
    "extract-whole" cut representing the explicit `T ⊗ 1` term in
    `comulTree T`. -/
abbrev AugCutShape (T : TraceTree α Unit) : Type _ := CutShape T ⊕ Unit

namespace AugCutShape

/-- The "extract-whole" virtual cut: extracts all of `T` as a singleton
    workspace, leaves no remainder. -/
abbrev extractWhole {T : TraceTree α Unit} : AugCutShape T := Sum.inr ()

/-- A real admissible cut, lifted to an augmented cut. -/
abbrev real {T : TraceTree α Unit} (C : CutShape T) : AugCutShape T := Sum.inl C

/-- The extracted forest of an augmented cut. For a real cut, this is
    `cutForest C`; for `extractWhole`, the singleton workspace `{T}`. -/
def cutForest_aug {T : TraceTree α Unit} : AugCutShape T → TraceForest α Unit
  | .inl C => CutShape.cutForest C
  | .inr _ => ({T} : TraceForest α Unit)

/-- The remainder forest (right-channel content) of an augmented cut.
    For a real cut `C`, the singleton workspace `{remainder C}`; for
    `extractWhole`, the empty workspace `0` (so that the right channel
    becomes `forestToHc 0 = 1`). -/
def remainderForest {T : TraceTree α Unit} : AugCutShape T → TraceForest α Unit
  | .inl C => ({CutShape.remainder C} : TraceForest α Unit)
  | .inr _ => 0

omit [DecidableEq α] in
@[simp] lemma cutForest_aug_real {T : TraceTree α Unit} (C : CutShape T) :
    cutForest_aug (real C) = CutShape.cutForest C := rfl

omit [DecidableEq α] in
@[simp] lemma cutForest_aug_extractWhole {T : TraceTree α Unit} :
    cutForest_aug (extractWhole : AugCutShape T) = ({T} : TraceForest α Unit) := rfl

omit [DecidableEq α] in
@[simp] lemma remainderForest_real {T : TraceTree α Unit} (C : CutShape T) :
    remainderForest (real C) = ({CutShape.remainder C} : TraceForest α Unit) := rfl

omit [DecidableEq α] in
@[simp] lemma remainderForest_extractWhole {T : TraceTree α Unit} :
    remainderForest (extractWhole : AugCutShape T) = 0 := rfl

end AugCutShape

/-! ## §2: `comulTree` as a unified sum over `AugCutShape`

The single key lemma making the augmented-cut substrate useful: the
existing two-piece formulation of `comulTree T` (explicit term + sum
over real cuts) coincides with a single sum over `AugCutShape T`. -/

/-- `comulTree T` as a unified sum over augmented cuts. The explicit
    `forestToHc {T} ⊗ 1` term in `comulTree`'s definition becomes the
    summand at `AugCutShape.extractWhole`; each real cut `C` becomes
    the summand at `AugCutShape.real C`. -/
theorem comulTree_eq_sum_AugCutShape (T : TraceTree α Unit) :
    (comulTree T : Hc R α ⊗[R] Hc R α)
      = ∑ ac : AugCutShape T,
          forestToHc (R := R) (AugCutShape.cutForest_aug ac)
            ⊗ₜ[R] forestToHc (R := R) (AugCutShape.remainderForest ac) := by
  -- Split the AugCutShape sum into Sum.inl (real cuts) and Sum.inr (extractWhole).
  rw [Fintype.sum_sum_type]
  -- Use the `_eq_prim_add_sum` form of comulTree to expose primitive + cut-sum.
  rw [comulTree_eq_prim_add_sum]
  -- LHS: forestToHc {T} ⊗ 1 + ∑ C : CutShape T, ...
  -- RHS: ∑ C : CutShape T, ... + ∑ () : Unit, forestToHc {T} ⊗ forestToHc 0
  --    = ∑ C, ... + (forestToHc {T} ⊗ 1)  (one unit term; forestToHc 0 = 1)
  rw [add_comm]
  -- Both halves now agree definitionally (same as previous proof structure).
  rfl

/-! ## §3: `pairsMS` and `comulTreeMS` for multi-tree sections

For the LHS direction of `comul_coassoc_tree` we need to expand
`comulForest F = (F.map comulTree).prod` (a product of sums) as a sum
of products. Mathlib provides exactly this via `Multiset.prod_map_sum`
and `Multiset.Sections`:

  `prod (s.map sum) = sum ((Sections s).map prod)`

We separate the data into two layers:

- `pairsMS T : Multiset (TraceForest α Unit × TraceForest α Unit)` is the
  **Forest-pair primitive**: enumerate `ac : AugCutShape T` and project to
  `(cutForest_aug ac, remainderForest ac)`. Pure combinatorial data, no algebra.
- `comulTreeMS R T : Multiset ((Hc R α) ⊗[R] (Hc R α))` is the algebraic image:
  `(pairsMS T).map (forestToHc tensorize)`. The form needed by
  `Multiset.prod_map_sum` for the multi-tree expansion.

Both `Sections (F.map (pairsMS · ))` (Forest-pair sections) and
`Sections (F.map (comulTreeMS R · ))` (Hc-tensor sections) are useful — the
former for `ChildSlots`-style downstream consumers (see `DoubleCut.lean`), the
latter for direct `Multiset.prod` aggregation in the algebra. The two are related
via `Sections.map_map_pair` (in `DoubleCut.lean`). -/

/-- The `(cutForest_aug, remainderForest)` pair multiset for `AugCutShape T`:
    enumerate all augmented cuts and project to the `(left-channel, right-channel)`
    Forest pair. The Forest-pair primitive that `comulTreeMS R T` builds upon. -/
def pairsMS (T : TraceTree α Unit) :
    Multiset (TraceForest α Unit × TraceForest α Unit) :=
  (Finset.univ : Finset (AugCutShape T)).val.map fun ac =>
    (AugCutShape.cutForest_aug ac, AugCutShape.remainderForest ac)

/-- `comulTree T` reformulated as the **sum** of an explicit multiset of
    pure tensors. Equivalent to `comulTree_eq_sum_AugCutShape T` but
    using `Multiset.sum` instead of `Finset.sum` — the form needed by
    mathlib's `Multiset.prod_map_sum`. Built from `pairsMS T` by tensorizing
    each Forest-pair via `forestToHc`. -/
noncomputable def comulTreeMS (R : Type*) [CommSemiring R]
    (T : TraceTree α Unit) : Multiset ((Hc R α) ⊗[R] (Hc R α)) :=
  (pairsMS T).map fun p => forestToHc (R := R) p.1 ⊗ₜ[R] forestToHc (R := R) p.2

/-- The factoring lemma `comulTreeMS = pairsMS.map tensorize` made explicit.
    Holds by `rfl` because of the new `comulTreeMS` definition; kept as a named
    lemma so downstream callers don't need to know it's definitional. -/
@[simp] lemma comulTreeMS_eq_pairsMS_map (T : TraceTree α Unit) :
    (comulTreeMS R T : Multiset ((Hc R α) ⊗[R] (Hc R α)))
      = (pairsMS T).map fun p => forestToHc (R := R) p.1 ⊗ₜ[R] forestToHc (R := R) p.2 := rfl

/-- `comulTree T = (comulTreeMS R T).sum`. Direct from
    `comulTree_eq_sum_AugCutShape` and `Finset.sum_eq_multiset_sum`. -/
theorem comulTree_eq_sum_comulTreeMS (T : TraceTree α Unit) :
    (comulTree T : Hc R α ⊗[R] Hc R α) = (comulTreeMS R T).sum := by
  rw [comulTree_eq_sum_AugCutShape T]
  unfold comulTreeMS pairsMS
  rw [Multiset.map_map]
  rfl

/-- **Multi-tree expansion**: `comulForest F` as a sum over multi-tree
    cut sections. Each "section" in `Multiset.Sections (F.map (comulTreeMS R))`
    represents a choice, for each tree `T'` in `F`, of an augmented cut
    on `T'`. The product of the section's tensors gives a single
    `forestToHc (sum of left-channels) ⊗ forestToHc (sum of right-channels)`
    contribution; their sum over all sections is `comulForest F`.

    Direct application of `Multiset.prod_map_sum`. -/
theorem comulForest_eq_sum_sections (F : TraceForest α Unit) :
    (comulForest F : Hc R α ⊗[R] Hc R α)
      = ((Multiset.Sections (F.map (comulTreeMS R))).map Multiset.prod).sum := by
  -- Step 1: comulForest F = (F.map comulTree).prod by definition
  unfold comulForest
  -- Step 2: rewrite each comulTree as sum-of-comulTreeMS
  rw [show F.map (comulTree (R := R))
        = (F.map (comulTreeMS R)).map Multiset.sum from by
       rw [Multiset.map_map]
       refine Multiset.map_congr rfl (fun T _ => ?_)
       exact comulTree_eq_sum_comulTreeMS T]
  -- Step 3: apply Multiset.prod_map_sum
  exact Multiset.prod_map_sum

end ConnesKreimer
