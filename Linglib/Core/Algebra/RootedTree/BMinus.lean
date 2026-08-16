/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Pairing
import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionNodeDecomp
import Linglib.Core.Data.Multiset.Antidiagonal
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.Ring

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# The B- operator and the B+/B- pairing adjoint

The `B-_a` operator on `ConnesKreimer R (Nonplanar α)`
([foissy-typed-decorated-rooted-trees-2018]'s B⁻ on decorated trees) is the
transpose of the grafting operator `B+_a` (`Coproduct/Pruning.lean`) under
the symmetry-weighted pairing (`GrossmanLarson/Pairing.lean`). On basis
elements:

```
B-_a (of' F) = if F = {Nonplanar.node a F'} for some F' then of' F' else 0
```

i.e., `B-_a` projects a singleton forest with an `a`-labeled root tree to
that tree's children forest, and vanishes otherwise.

## Main definitions

* `GrossmanLarson.bMinusTree`, `GrossmanLarson.bMinusBasis`,
  `GrossmanLarson.bMinusLin` — B-_a per tree, per basis forest, and as a
  linear endomorphism.

## Main results

* `GrossmanLarson.isAdjointPair_bMinusLin_bPlusLin`,
  `GrossmanLarson.bMinusLin_pairing_adjoint` — the transpose property
  `⟨B-_a x, y⟩ = ⟨x, B+_a y⟩` ([oudom-guin-2008] Prop 3.2 substrate).
* `GrossmanLarson.bMinusLin_gl_mul` — the derivation identity
  `B-(A ∗ B) = ε(A) B-(B) + B-(A) ∗ B` ([oudom-guin-2008] §3.2), whose
  duality argument the transpose property anchors.
-/


namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### `bMinusTree` and `bMinusBasis` -/

/-- Per-tree B-_a: the children forest when the root is labeled `a`,
    else `0` — Foissy's B⁻ on trees
    ([foissy-typed-decorated-rooted-trees-2018]). -/
noncomputable def bMinusTree (a : α) (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) :=
  if T.rootValue = a then of' (R := R) T.rootChildren else 0

@[simp] theorem bMinusTree_node (a : α) (F : Forest (Nonplanar α)) :
    bMinusTree (R := R) a (Nonplanar.node a F) = of' F := by
  rw [bMinusTree, Nonplanar.rootValue_node, if_pos rfl,
      Nonplanar.rootChildren_node]

/-- The B-_a operator on basis forests: `bMinusTree` on singletons, `0`
    otherwise. Stated via `card`/`map`/`sum`, which carry the descent to
    the `Multiset` quotient. -/
noncomputable def bMinusBasis (a : α) (F : Forest (Nonplanar α)) :
    ConnesKreimer R (Nonplanar α) :=
  if F.card = 1 then (F.map (bMinusTree (R := R) a)).sum else 0

@[simp] theorem bMinusBasis_zero (a : α) :
    bMinusBasis (R := R) a (0 : Forest (Nonplanar α)) = 0 := by
  simp [bMinusBasis]

@[simp] theorem bMinusBasis_singleton_node (a : α) (F : Forest (Nonplanar α)) :
    bMinusBasis (R := R) a ({Nonplanar.node a F} : Forest (Nonplanar α)) =
      of' F := by
  simp [bMinusBasis]

/-- `bMinusBasis a` vanishes on basis forests that are not
    singleton-`a`-rooted. -/
theorem bMinusBasis_eq_zero_of_not_singleton_a (a : α)
    (F : Forest (Nonplanar α))
    (h : ¬ ∃ G' : Forest (Nonplanar α), F = ({Nonplanar.node a G'} : Forest _)) :
    bMinusBasis (R := R) a F = 0 := by
  rw [bMinusBasis]
  split_ifs with hcard
  · obtain ⟨T, rfl⟩ := Multiset.card_eq_one.mp hcard
    rw [Multiset.map_singleton, Multiset.sum_singleton, bMinusTree, if_neg]
    intro hlab
    exact h ⟨T.rootChildren, by rw [← hlab, Nonplanar.node_eta]⟩
  · rfl

/-! ### `bMinusLin a` — linear extension -/

/-- The B-_a linear map: linear extension of `bMinusBasis` via `Finsupp.lift`. -/
noncomputable def bMinusLin (a : α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.linearLift (bMinusBasis (R := R) a)

@[simp] theorem bMinusLin_of' (a : α) (F : Forest (Nonplanar α)) :
    bMinusLin (R := R) a (of' F) = bMinusBasis (R := R) a F := by
  show ConnesKreimer.linearLift (bMinusBasis (R := R) a) (ConnesKreimer.of' F) = _
  rw [ConnesKreimer.linearLift_of']

/-! ### B+/B- pairing adjoint -/

/-- **Adjoint** of `bPlusLin a` w.r.t. the symmetry-weighted pairing, on
    basis elements: both sides are `[F = {node a G}] · forestAutCard F`. -/
theorem bMinusLin_pairing_adjoint_basis (a : α)
    (F G : Forest (Nonplanar α)) :
    pairing (R := R) (bMinusLin (R := R) a (of' F)) (of' G) =
    pairing (R := R) (of' F) (bPlusLin (R := R) a (of' G)) := by
  rw [bMinusLin_of',
      show bPlusLin (R := R) a (of' G) =
        of' ({Nonplanar.node a G} : Forest (Nonplanar α)) from
        ConnesKreimer.bPlusLin_of' a G,
      show pairing (R := R) (of' F)
          (of' ({Nonplanar.node a G} : Forest (Nonplanar α))) =
        (if F = ({Nonplanar.node a G} : Forest (Nonplanar α)) then
          (forestAutCard F : R) else 0) from pairing_of'_of' F _]
  by_cases hF : ∃ G' : Forest (Nonplanar α), F = {Nonplanar.node a G'}
  · obtain ⟨G', rfl⟩ := hF
    rw [bMinusBasis_singleton_node,
        show pairing (R := R) (of' G') (of' G) =
          (if G' = G then (forestAutCard G' : R) else 0) from
          pairing_of'_of' G' G]
    by_cases hG : G' = G
    · subst hG
      rw [if_pos rfl, if_pos rfl, Nonplanar.forestAutCard_singleton,
          Nonplanar.autCard_node]
    · rw [if_neg hG, if_neg fun h => hG (by
        simpa using congrArg Nonplanar.rootChildren (Multiset.singleton_inj.mp h))]
  · rw [bMinusBasis_eq_zero_of_not_singleton_a a F hF,
        if_neg fun h => hF ⟨G, h⟩, pairing_zero_left]

/-- **B+/B- adjointness** under the symmetry-weighted pairing, in mathlib's
    `LinearMap.IsAdjointPair` packaging. -/
theorem isAdjointPair_bMinusLin_bPlusLin (a : α) :
    LinearMap.IsAdjointPair (pairing (R := R)) (pairing (R := R))
      (bMinusLin (R := R) a) (ConnesKreimer.bPlusLin (R := R) a) := by
  rw [LinearMap.isAdjointPair_iff_comp_eq_compl₂]
  refine ConnesKreimer.lhom_ext' fun F => ?_
  refine ConnesKreimer.lhom_ext' fun G => ?_
  exact bMinusLin_pairing_adjoint_basis a F G

/-- **B+/B- adjoint** under the symmetry-weighted pairing, pointwise:
    `⟨B-_a x, y⟩ = ⟨x, B+_a y⟩` for all `a, x, y`. -/
theorem bMinusLin_pairing_adjoint (a : α)
    (x y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (bMinusLin (R := R) a x) y =
    pairing (R := R) x (bPlusLin (R := R) a y) :=
  isAdjointPair_bMinusLin_bPlusLin a x y

/-! ## The OG derivation identity `B-_a(x *_GL y) = ε(x) • B-_a y + B-_a x *_GL y`

OG paper [oudom-guin-2008] §3.2 proves this identity on the S(L)
side; on the CK carrier it is the direct identity
`bMinusLin a (x *_GL y) = counit(x) • bMinusLin a y +
bMinusLin a x *_GL y`.

This identity says `bMinusLin a` is a "1-cocycle" with respect to `*_GL`
in the sense `B-(xy) = ε(x) B-(y) + B-(x) y`.

The proof reduces to the basis case `x = of' A, y = of' B` and
case-analyzes on `A`:
* `A = 0`: counit = 1, B-_a (of' 0) = 0; identity reduces to `B-_a (of' B) = B-_a (of' B)`.
* `|A| ≥ 2`: both sides 0 by length grading (B-_a vanishes on non-singletons).
* `|A| = 1` with root label ≠ a: both sides 0 (B-_a kills non-a-rooted singletons).
* `|A| = 1` with root label = a (A = {node a A'}): the combinatorial heart.

The hard case reduces to the substrate lemma:
  `insertion (of' {node a A'}) (of' B) = bPlusLin a (of' A' *_GL of' B)`

(grafting B into the only tree of {node a A'} = a-rooting the GL
product). This is `singleton_node_a_insertion_eq_bPlus_gl_mul` below.
-/

/-- **Key combinatorial substrate**: grafting `of' B` into the
    singleton-a-rooted host `{node a A'}` equals the a-rooting (via
    `bPlusLin a`) of the **GL product** `of' A' *_GL of' B`.

    Intuition: a result tree `T' = node a (children of node a A' with B grafted)`
    has root label `a` (preserved by NIM) and children formed by either
    (i) a B-tree prepended at root, or (ii) a B-tree grafted into an A'
    subtree. The partition of B's grafting positions exactly matches
    the powerset decomposition of `of' A' *_GL of' B = Σ_{B₁ ⊆ B}
    (insertion (of' A') (of' B₁)) *_CK of'(B - B₁)`. Each summand of
    the GL sum, a-rooted via `bPlusLin a`, yields a corresponding tree
    in the NIM enumeration.

    Proved from the NIM-level decomposition
    `Nonplanar.insertionMultiset_singleton_node`
    (`PreLie/InsertionNonplanar.lean`). -/
theorem singleton_node_a_insertion_eq_bPlus_gl_mul
    (a : α) (A' B : Forest (Nonplanar α)) :
    insertion (R := R)
        (GrossmanLarson.of' ({Nonplanar.node a A'} : Forest (Nonplanar α)))
        (GrossmanLarson.of' B) =
      ConnesKreimer.bPlusLin (R := R) a
        (unop
          ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
            GrossmanLarson.of' B)) := by
  -- Common form: (B.powerset.map (fun B₁ =>
  --   ((NIM A' B₁).map (fun F' => of' {node a (F' + (B - B₁))})).sum)).sum
  set common : ConnesKreimer R (Nonplanar α) :=
    (B.powerset.map fun B₁ =>
      ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
        ConnesKreimer.of' (R := R)
          ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))).sum).sum
    with h_common
  -- Step 1: LHS = common.
  have hLHS : (insertion (R := R)
      (GrossmanLarson.of' ({Nonplanar.node a A'} : Forest (Nonplanar α)))
      (GrossmanLarson.of' B) : GrossmanLarson R α) = common := by
    rw [insertion_of'_of']
    unfold insertionBasis
    rw [Nonplanar.insertionMultiset_singleton_node a A' B]
    rw [Multiset.map_bind, Multiset.sum_bind, h_common]
    congr 1
    apply Multiset.map_congr rfl
    intro B₁ _
    rw [Multiset.map_map]
    rfl
  -- Step 2: RHS = common.
  have hRHS : ConnesKreimer.bPlusLin (R := R) a
      (unop
        ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
          GrossmanLarson.of' B)) = common := by
    -- Per-summand identity:
    have h_summand : ∀ B₁ : Forest (Nonplanar α),
        ConnesKreimer.bPlusLin (R := R) a
          ((unop
            (insertion (R := R)
              (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
              ConnesKreimer R (Nonplanar α)) *
            (unop (GrossmanLarson.of' (R := R) (B - B₁)))) =
        ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
          ConnesKreimer.of' (R := R)
            ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))).sum := by
      intro B₁
      -- insertion (of' A') (of' B₁) = insertionBasis A' B₁ = (NIM ...).map of').sum.
      rw [insertion_of'_of']
      unfold insertionBasis
      -- Goal: bPlusLin a ((NIM A' B₁).map of').sum.unop * of'(B - B₁).unop) = ...
      -- unop on basis sum is the same sum on CK side.
      show ConnesKreimer.bPlusLin (R := R) a
          ((((Nonplanar.insertionMultiset A' B₁).map fun F' =>
              ConnesKreimer.of' (R := R) F').sum) *
            (ConnesKreimer.of' (R := R) (B - B₁))) =
        ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
          ConnesKreimer.of' (R := R)
            ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))).sum
      -- Push * over sum (right-distributive): (Σ X_i) * Y = Σ (X_i * Y).
      rw [← Multiset.sum_map_mul_right]
      -- Now: bPlusLin a ((NIM A' B₁).map (fun F' => of' F' * of' (B - B₁))).sum
      -- For each F': of' F' * of' (B - B₁) = of' (F' + (B - B₁)) [of'_add].
      rw [show ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
              (ConnesKreimer.of' (R := R) F' : ConnesKreimer R (Nonplanar α)) *
                ConnesKreimer.of' (R := R) (B - B₁)) =
            ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
              ConnesKreimer.of' (R := R) (F' + (B - B₁)))
          from by
        apply Multiset.map_congr rfl
        intro F' _
        rw [ConnesKreimer.of'_add]]
      -- bPlusLin a is linear, distributes over Multiset.sum.
      rw [show ConnesKreimer.bPlusLin (R := R) a
              ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
                ConnesKreimer.of' (R := R) (F' + (B - B₁))).sum =
            ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
              ConnesKreimer.bPlusLin (R := R) a
                (ConnesKreimer.of' (R := R) (F' + (B - B₁)))).sum from ?_]
      swap
      · -- Push bPlusLin a through Multiset.sum via linearity.
        induction Nonplanar.insertionMultiset A' B₁ using Multiset.induction with
        | empty => simp
        | cons F' rest ih =>
          simp only [Multiset.map_cons, Multiset.sum_cons, map_add, ih]
      -- bPlusLin a (of' G) = ofTree (node a G) = of' {node a G}.
      congr 1
      apply Multiset.map_congr rfl
      intro F' _
      show ConnesKreimer.bPlusLin (R := R) a
          (ConnesKreimer.of' (F' + (B - B₁))) =
        ConnesKreimer.of' ({Nonplanar.node a (F' + (B - B₁))} : Forest _)
      rw [ConnesKreimer.bPlusLin_of']
      rfl
    -- Apply per-summand identity to RHS structure.
    -- RHS = bPlusLin a (unop (productForest powerset sum)).
    rw [GrossmanLarson.of'_mul_of']
    unfold productForest
    rw [h_common]
    -- Define the per-B₁ summand function and use linearity.
    -- For each B₁, the summand is op (unop (insertion ...) * unop (of' ...)),
    -- so unop'd it's just unop (insertion ...) * unop (of' ...).
    -- bPlusLin a (Σ ...) = Σ bPlusLin a (...).
    -- Use h_summand B₁ for each.
    -- Push unop through Multiset.sum (it's linear) — define a helper.
    have h_unop_sum : ∀ (s : Multiset (Forest (Nonplanar α))),
        unop
            (s.map fun B₁ =>
              op
                (unop
                    (insertion (R := R)
                      (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) *
                  unop (GrossmanLarson.of' (B - B₁)))).sum =
          (s.map fun B₁ =>
            (unop
                (insertion (R := R)
                  (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
              ConnesKreimer R (Nonplanar α)) *
              unop (GrossmanLarson.of' (B - B₁))).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => rfl
      | cons B₁ rest ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        show (unop
              ((op _ : GrossmanLarson R α) + (rest.map _).sum)) =
          _ + (rest.map _).sum
        rfl
    rw [h_unop_sum B.powerset]
    -- Now push bPlusLin a through Multiset.sum.
    have h_bPlus_sum : ∀ (s : Multiset (Forest (Nonplanar α))),
        ConnesKreimer.bPlusLin (R := R) a
            (s.map fun B₁ =>
              (unop
                  (insertion (R := R)
                    (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
                ConnesKreimer R (Nonplanar α)) *
                unop (GrossmanLarson.of' (B - B₁))).sum =
          (s.map fun B₁ =>
            ConnesKreimer.bPlusLin (R := R) a
              ((unop
                  (insertion (R := R)
                    (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
                ConnesKreimer R (Nonplanar α)) *
                unop (GrossmanLarson.of' (B - B₁)))).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => simp
      | cons B₁ rest ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, map_add, ih]
    rw [h_bPlus_sum B.powerset]
    -- Apply h_summand per B₁.
    congr 1
    apply Multiset.map_congr rfl
    intro B₁ _
    exact h_summand B₁
  rw [hLHS, hRHS]

/-! ### The derivation identity -/

/-- Counit of `of' F`: `1` if `F = 0`, else `0`. Re-expressed via `Decidable`. -/
private theorem counit_of'_eq (F : Forest (Nonplanar α)) :
    (ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
      (ConnesKreimer.of' F) =
      (if F = 0 then (1 : R) else 0) := by
  rw [ConnesKreimer.counit_of']
  by_cases h : F = 0
  · subst h; simp
  · have hne : F.card ≠ 0 := fun hc => h (Multiset.card_eq_zero.mp hc)
    rw [if_neg hne, if_neg h]

/-! ### Helpers for `bMinusLin_gl_mul_basis` -/

/-- `bMinusBasis a ({node a F} + G) = if G = 0 then of' F else 0`.
    When `G = 0`, the forest is the singleton `{node a F}` so
    `bMinusBasis = of' F`. When `G ≠ 0`, the forest has cardinality
    `1 + |G| ≥ 2`, so it's not a singleton and `bMinusBasis = 0` via
    `bMinusBasis_eq_zero_of_not_singleton_a`. -/
private theorem bMinusBasis_singleton_node_add (a : α)
    (F G : Forest (Nonplanar α)) :
    bMinusBasis (R := R) a ({Nonplanar.node a F} + G) =
      (if G = 0 then (ConnesKreimer.of' (R := R) F : ConnesKreimer R (Nonplanar α))
       else 0) := by
  by_cases hG : G = 0
  · subst hG
    rw [add_zero, if_pos rfl, bMinusBasis_singleton_node]
    rfl
  · rw [if_neg hG]
    apply bMinusBasis_eq_zero_of_not_singleton_a
    rintro ⟨G', hG'⟩
    have hcard : ({Nonplanar.node a F} + G : Forest (Nonplanar α)).card =
        ({Nonplanar.node a G'} : Forest (Nonplanar α)).card := by rw [hG']
    rw [Multiset.card_add, Multiset.card_singleton, Multiset.card_singleton] at hcard
    have hGcard : G.card = 0 := by omega
    exact hG (Multiset.card_eq_zero.mp hGcard)

/-- **Helper**: `bMinusLin a (bPlusLin a Y * of' G)` equals `Y`
    if `G = 0` (the `bMinusLin ∘ bPlusLin = id` identity on basis elements
    extends linearly to all `Y`), and `0` otherwise (the product has each
    basis summand of cardinality `≥ 2`, so `bMinusLin` kills it).

    Reduces by `ConnesKreimer.induction_linear` on `Y` to the basis case via
    `bMinusBasis_singleton_node_add`. -/
private theorem bMinusLin_bPlusLin_mul_of' (a : α)
    (Y : ConnesKreimer R (Nonplanar α)) (G : Forest (Nonplanar α)) :
    bMinusLin (R := R) a
      (ConnesKreimer.bPlusLin (R := R) a Y *
        ConnesKreimer.of' (R := R) G) =
      (if G = 0 then Y else 0) := by
  refine ConnesKreimer.induction_linear Y ?_ ?_ ?_
  · -- Y = 0
    show bMinusLin (R := R) a
        (ConnesKreimer.bPlusLin (R := R) a (0 : ConnesKreimer R (Nonplanar α)) *
          ConnesKreimer.of' (R := R) G) = _
    rw [(ConnesKreimer.bPlusLin (R := R) a).map_zero, zero_mul,
        (bMinusLin (R := R) a).map_zero]
    split_ifs <;> rfl
  · -- Y = Y₁ + Y₂
    intro Y₁ Y₂ ih₁ ih₂
    let Y₁' : ConnesKreimer R (Nonplanar α) := Y₁
    let Y₂' : ConnesKreimer R (Nonplanar α) := Y₂
    show bMinusLin (R := R) a
        (ConnesKreimer.bPlusLin (R := R) a (Y₁' + Y₂') *
          ConnesKreimer.of' (R := R) G) = _
    rw [(ConnesKreimer.bPlusLin (R := R) a).map_add, add_mul,
        (bMinusLin (R := R) a).map_add, ih₁, ih₂]
    split_ifs <;> first | rfl | simp
  · -- Y = single F r = r • of' F
    intro F r
    -- Compute bPlusLin a (single F r) = r • of' {node a F}.
    have h_bPlus : ConnesKreimer.bPlusLin (R := R) a (ConnesKreimer.single F r) =
        r • ConnesKreimer.of' (R := R) ({Nonplanar.node a F} : Forest _) := by
      show ConnesKreimer.linearLift (fun F => ConnesKreimer.ofTree (Nonplanar.node a F))
            (ConnesKreimer.single F r) = _
      rw [ConnesKreimer.linearLift_single]
      rfl
    show bMinusLin (R := R) a
        (ConnesKreimer.bPlusLin (R := R) a (ConnesKreimer.single F r) *
          ConnesKreimer.of' (R := R) G) = _
    rw [h_bPlus, smul_mul_assoc, ← of'_add, (bMinusLin (R := R) a).map_smul]
    -- Now: r • bMinusLin a (of' ({node a F} + G)) = if G = 0 then single F r else 0
    rw [show bMinusLin (R := R) a
            (ConnesKreimer.of' (R := R) ({Nonplanar.node a F} + G) :
              ConnesKreimer R (Nonplanar α)) =
          bMinusBasis (R := R) a ({Nonplanar.node a F} + G) from
        bMinusLin_of' a _]
    rw [bMinusBasis_singleton_node_add]
    split_ifs with hG
    · -- G = 0: r • of' F = single F r
      subst hG
      show r • ConnesKreimer.of' (R := R) F =
        (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α))
      exact (ConnesKreimer.smul_single_one F r).symm
    · rw [smul_zero]

/-- Combinatorial helper: summing a `B - B₁ = 0` indicator over `B.powerset`
    picks out exactly the `B₁ = B` summand. Used in
    `bMinusLin_gl_mul_basis`'s singleton-a sub-case to collapse the GL
    product expansion (only the `B₁ = B` term survives `bMinusLin_bPlusLin_mul_of'`).

    Proof: induction on `B`. Base `B = 0` is `Multiset.zero_sub`.
    Inductive `B = T ::ₘ B'`: the first half `B'.powerset` summands all
    vanish (`T ::ₘ B' - B₁ = T ::ₘ (B' - B₁) ≠ 0` for `B₁ ≤ B'`), and
    the second half reduces to the IH via `T ::ₘ B' - (T ::ₘ B₁') = B' - B₁'`
    (`Multiset.sub_cons` + `Multiset.erase_cons_head`). -/
private lemma sum_powerset_diff_zero_indicator
    {β : Type*} [AddCommMonoid β]
    (B : Forest (Nonplanar α)) (f : Forest (Nonplanar α) → β) :
    (B.powerset.map fun B₁ =>
      if B - B₁ = (0 : Forest (Nonplanar α)) then f B₁ else (0 : β)).sum = f B := by
  induction B using Multiset.induction generalizing f with
  | empty =>
    rw [Multiset.powerset_zero, Multiset.map_singleton, Multiset.sum_singleton]
    rw [show (0 - (0 : Forest (Nonplanar α))) = 0 from Multiset.sub_zero _, if_pos rfl]
  | cons T B' ih =>
    rw [Multiset.powerset_cons, Multiset.map_add, Multiset.sum_add]
    have h_first_zero : (B'.powerset.map fun B₁ =>
          if T ::ₘ B' - B₁ = (0 : Forest (Nonplanar α)) then f B₁
          else (0 : β)).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨B₁, hB₁, hx_eq⟩ := hx
      have hB₁le : B₁ ≤ B' := Multiset.mem_powerset.mp hB₁
      have hne : T ::ₘ B' - B₁ ≠ (0 : Forest (Nonplanar α)) := by
        rw [Multiset.cons_sub_of_le T hB₁le]
        exact Multiset.cons_ne_zero
      rw [← hx_eq, if_neg hne]
    rw [h_first_zero, zero_add, Multiset.map_map]
    have h_cond_eq : (B'.powerset.map ((fun B₁ =>
            if T ::ₘ B' - B₁ = (0 : Forest (Nonplanar α)) then f B₁
            else (0 : β)) ∘ (T ::ₘ ·))) =
        B'.powerset.map (fun B₁' =>
          if B' - B₁' = (0 : Forest (Nonplanar α)) then f (T ::ₘ B₁')
          else (0 : β)) := by
      apply Multiset.map_congr rfl
      intro B₁ _
      show (if T ::ₘ B' - (T ::ₘ B₁) = (0 : Forest (Nonplanar α))
              then f (T ::ₘ B₁) else (0 : β)) =
        (if B' - B₁ = (0 : Forest (Nonplanar α)) then f (T ::ₘ B₁)
          else (0 : β))
      rw [Multiset.sub_cons, Multiset.erase_cons_head]
    rw [h_cond_eq]
    exact ih (fun B₁' => f (T ::ₘ B₁'))

/-- **Helper for the non-singleton-a sub-case**: when `A` is not of the
    form `{node a A'}` and `A ≠ 0`, every forest of the form
    `F' + (B - B₁)` (for `F' ∈ NIM A B₁`, `B₁ ⊆ B`) is also not of the
    form `{node a G}`, so `bMinusBasis a (F' + (B - B₁)) = 0`.

    Cardinality of `F' + (B - B₁)` is `|A| + |B - B₁|` (since
    `F'.card = A.card` via `insertionMultiset_card_eq`).
    * If `|A| ≥ 2`: total ≥ 2, not a singleton.
    * If `|A| + |B - B₁| ≥ 2`: not a singleton.
    * If `|A| = 1, |B - B₁| = 0`: `F'` is a singleton, but its root label
      equals `A`'s root label (which is ≠ a since `A` is not singleton-a-rooted),
      so still not of form `{node a G}`. Uses
      `Nonplanar.insertionMultiset_singleton_rootValue`. -/
private theorem bMinusBasis_nim_add_eq_zero (a : α)
    (A B₁ B' F' : Forest (Nonplanar α))
    (hA_ne : A ≠ 0)
    (hA : ¬ ∃ G' : Forest (Nonplanar α), A = ({Nonplanar.node a G'} : Forest _))
    (hF' : F' ∈ Nonplanar.insertionMultiset A B₁) :
    bMinusBasis (R := R) a (F' + B') = 0 := by
  apply bMinusBasis_eq_zero_of_not_singleton_a
  rintro ⟨G, hG⟩
  -- (F' + B').card = |A| + |B'|; must equal 1.
  have hcard_F' : F'.card = A.card :=
    Nonplanar.insertionMultiset_card_eq A B₁ hF'
  have h_total_card : (F' + B').card = 1 := by
    rw [hG]; exact Multiset.card_singleton _
  rw [Multiset.card_add, hcard_F'] at h_total_card
  -- A.card ≥ 1 since A ≠ 0.
  have hA_card_pos : 1 ≤ A.card := by
    have : A.card ≠ 0 := fun h => hA_ne (Multiset.card_eq_zero.mp h)
    omega
  -- So A.card = 1 and B'.card = 0.
  have hA_card : A.card = 1 := by omega
  have hB'_card : B'.card = 0 := by omega
  have hB' : B' = 0 := Multiset.card_eq_zero.mp hB'_card
  subst hB'
  -- F' + 0 = F', and F' has card 1, F' = {T'} with T' = node a G.
  rw [add_zero] at hG
  -- Now F' ∈ NIM A B₁ with A.card = 1; A = {T} for some T with T.rootValue ≠ a.
  -- Goal: derive contradiction from F' = {node a G} via root preservation.
  have hF'_card : F'.card = 1 := by rw [hcard_F', hA_card]
  -- A is a singleton (card 1): A = {T_A} for some T_A.
  obtain ⟨T_A, hT_A⟩ : ∃ T_A : Nonplanar α, A = {T_A} := by
    rcases Multiset.card_eq_one.mp hA_card with ⟨T_A, hT_A⟩
    exact ⟨T_A, hT_A⟩
  -- T_A.rootValue ≠ a (otherwise A = {node a (rootChildren T_A)} via node_eta).
  have hT_A_lab : T_A.rootValue ≠ a := by
    intro h_lab
    apply hA
    refine ⟨Nonplanar.rootChildren T_A, ?_⟩
    rw [hT_A]
    congr 1
    rw [← h_lab, Nonplanar.node_eta]
  -- Apply NIM singleton root preservation.
  subst hT_A
  obtain ⟨T', hF'_eq, hT'_lab⟩ :=
    Nonplanar.insertionMultiset_singleton_rootValue T_A B₁ hF'
  -- F' = {T'} with T'.rootValue = T_A.rootValue ≠ a.
  -- But hG says F' = {node a G}, so T' = node a G.
  rw [hF'_eq] at hG
  have hT'_eq_node : T' = Nonplanar.node a G := Multiset.singleton_inj.mp hG
  -- Then T'.rootValue = a, contradicting hT'_lab + hT_A_lab.
  have hT'_lab_a : T'.rootValue = a := by
    rw [hT'_eq_node, Nonplanar.rootValue_node]
  rw [hT'_lab_a] at hT'_lab
  exact hT_A_lab hT'_lab.symm

/-- **Basis case of the derivation identity**: for basis `x = of' A, y = of' B`, the OG
    identity holds. Case-analyzes on `A`:
    * `A = 0`: counit = 1, both sides equal `bMinusLin a (of' B)`.
    * `|A| ≥ 2`: both sides 0 (B-_a vanishes on non-singletons).
    * `|A| = 1` with non-a root: both sides 0.
    * `|A| = 1` with `a`-root: reduces to `singleton_node_a_insertion_eq_bPlus_gl_mul`. -/
private theorem bMinusLin_gl_mul_basis (a : α) (A B : Forest (Nonplanar α)) :
    bMinusLin (R := R) a
      ((GrossmanLarson.of' (R := R) A : GrossmanLarson R α) *
        GrossmanLarson.of' B) =
      ((ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' A)) •
        bMinusLin (R := R) a (ConnesKreimer.of' B) +
      unop
        ((op (bMinusLin (R := R) a (ConnesKreimer.of' A))) *
          GrossmanLarson.of' B) := by
  by_cases hA : ∃ A' : Forest (Nonplanar α), A = ({Nonplanar.node a A'} : Forest _)
  · -- Hard case: A = {node a A'}. Uses singleton_node_a_insertion_eq_bPlus_gl_mul.
    obtain ⟨A', hAA'⟩ := hA
    subst hAA'
    -- Simplify counit and bMinusLin a on of' {node a A'}.
    have h_counit : (ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (ConnesKreimer.of' ({Nonplanar.node a A'} : Forest (Nonplanar α))) = 0 := by
      rw [ConnesKreimer.counit_of', Multiset.card_singleton, if_neg one_ne_zero]
    have h_bmin : bMinusLin (R := R) a
          (ConnesKreimer.of' ({Nonplanar.node a A'} : Forest (Nonplanar α))) =
        ConnesKreimer.of' A' := by
      -- Use show to bridge namespace difference for bMinusLin_of'.
      rw [show bMinusLin (R := R) a
            (ConnesKreimer.of' (R := R) ({Nonplanar.node a A'} : Forest _) :
              ConnesKreimer R (Nonplanar α)) =
          bMinusBasis (R := R) a ({Nonplanar.node a A'} : Forest _) from
        bMinusLin_of' a _]
      rw [bMinusBasis_singleton_node]
      rfl
    rw [h_counit, zero_smul, zero_add, h_bmin]
    -- Goal: bMinusLin a ((of'{node a A'} : GL) * of' B) = unop(op(of' A') * of' B).
    -- Both sides equal unop(of' A' *_GL of' B) (op/unop are identity coercions).
    -- Convert * to productForest using show (mul_def is rfl) + of'_mul_of'.
    show bMinusLin (R := R) a
        (product
          (GrossmanLarson.of' (R := R)
            ({Nonplanar.node a A'} : Forest (Nonplanar α)))
          (GrossmanLarson.of' B)) = _
    rw [show product
            (GrossmanLarson.of' (R := R)
              ({Nonplanar.node a A'} : Forest (Nonplanar α)))
            (GrossmanLarson.of' B) =
          productForest
            (GrossmanLarson.of' (R := R)
              ({Nonplanar.node a A'} : Forest (Nonplanar α))) B from
        GrossmanLarson.of'_mul_of' _ _]
    unfold productForest
    -- Push bMinusLin a through Multiset.sum.
    have h_push_sum : bMinusLin (R := R) a
          ((B.powerset.map fun B₁ =>
            op
              (unop
                  (insertion (R := R)
                    (GrossmanLarson.of'
                      ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                    (GrossmanLarson.of' B₁)) *
                unop (GrossmanLarson.of' (B - B₁)))).sum) =
        (B.powerset.map fun B₁ =>
          bMinusLin (R := R) a
            (op
              (unop
                  (insertion (R := R)
                    (GrossmanLarson.of'
                      ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                    (GrossmanLarson.of' B₁)) *
                unop (GrossmanLarson.of' (B - B₁))))).sum := by
      rw [map_multiset_sum (bMinusLin (R := R) a), Multiset.map_map]
      rfl
    rw [h_push_sum]
    -- Per-summand: apply singleton bridge then helper 2.
    have h_summand : ∀ B₁ : Forest (Nonplanar α),
        bMinusLin (R := R) a
          (op
            (unop
                (insertion (R := R)
                  (GrossmanLarson.of'
                    ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                  (GrossmanLarson.of' B₁)) *
              unop (GrossmanLarson.of' (B - B₁)))) =
        (if B - B₁ = (0 : Forest (Nonplanar α)) then
           unop
             ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
               GrossmanLarson.of' B₁)
         else 0) := by
      intro B₁
      rw [singleton_node_a_insertion_eq_bPlus_gl_mul]
      -- Now: bMinusLin a (op (unop (bPlusLin a (unop(of' A' * of' B₁))) * unop(of' (B - B₁))))
      -- = bMinusLin a (bPlusLin a (unop(of' A' * of' B₁)) * of'(B - B₁))   [op, unop are id]
      show bMinusLin (R := R) a
          ((ConnesKreimer.bPlusLin (R := R) a
              (unop
                ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
                  GrossmanLarson.of' B₁))) *
            ConnesKreimer.of' (R := R) (B - B₁)) = _
      rw [bMinusLin_bPlusLin_mul_of']
    have h_map_eq : (B.powerset.map fun B₁ =>
          bMinusLin (R := R) a
            (op
              (unop
                  (insertion (R := R)
                    (GrossmanLarson.of'
                      ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                    (GrossmanLarson.of' B₁)) *
                unop (GrossmanLarson.of' (B - B₁))))) =
        B.powerset.map (fun B₁ =>
          if B - B₁ = (0 : Forest (Nonplanar α)) then
            unop
              ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
                GrossmanLarson.of' B₁)
          else 0) := by
      apply Multiset.map_congr rfl
      intro B₁ _
      exact h_summand B₁
    rw [h_map_eq]
    -- Collapse via helper 3.
    have h_collapse := sum_powerset_diff_zero_indicator B (fun B₁ =>
        unop
          ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
            GrossmanLarson.of' B₁))
    convert h_collapse using 4
    · rfl
  · -- A is not singleton-a-rooted. bMinusLin a (of' A) = 0 and counit (of' A) handled by sub-cases.
    have hBmin : bMinusLin (R := R) a (ConnesKreimer.of' A) = 0 := by
      show bMinusLin (R := R) a (of' A) = 0
      rw [bMinusLin_of', bMinusBasis_eq_zero_of_not_singleton_a a A hA]
    rw [hBmin]
    show bMinusLin (R := R) a
          ((GrossmanLarson.of' (R := R) A : GrossmanLarson R α) *
            GrossmanLarson.of' B) =
        ((ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (ConnesKreimer.of' A)) •
          bMinusLin (R := R) a (ConnesKreimer.of' B) +
        unop
          ((op (0 : ConnesKreimer R (Nonplanar α))) *
            GrossmanLarson.of' B)
    -- Simplify `(op 0 * of' B).unop = 0` using `product`'s linearity.
    have hZero : (op (0 : ConnesKreimer R (Nonplanar α)) :
        GrossmanLarson R α) * GrossmanLarson.of' B =
      (0 : GrossmanLarson R α) := by
      show product (0 : GrossmanLarson R α)
            (GrossmanLarson.of' B) = 0
      rw [LinearMap.map_zero, LinearMap.zero_apply]
    rw [hZero, show unop (0 : GrossmanLarson R α) =
                  (0 : ConnesKreimer R (Nonplanar α)) from rfl,
        add_zero]
    -- Goal: bMinusLin a (of' A *_GL of' B) = counit (of' A) • bMinusLin a (of' B).
    -- Case-on A = 0 (counit = 1, of' A *_GL of' B = of' B *_GL 1 = of' B → bMinusLin a (of' B))
    -- vs A ≠ 0 (counit = 0, RHS = 0; need to show LHS = 0).
    by_cases hA0 : A = 0
    · subst hA0
      rw [counit_of'_eq, if_pos rfl, one_smul]
      -- LHS: bMinusLin a (of' 0 *_GL of' B) = bMinusLin a (1 *_GL of' B) = bMinusLin a (of' B).
      show bMinusLin (R := R) a
          ((GrossmanLarson.of' (R := R) (0 : Forest (Nonplanar α)) :
            GrossmanLarson R α) *
            GrossmanLarson.of' B) =
        bMinusLin (R := R) a (ConnesKreimer.of' B)
      congr 1
      show (GrossmanLarson.of' (R := R) (0 : Forest (Nonplanar α)) :
          GrossmanLarson R α) * GrossmanLarson.of' B =
        ConnesKreimer.of' B
      rw [show (GrossmanLarson.of' (R := R) (0 : Forest (Nonplanar α)) :
              GrossmanLarson R α) = 1 from GrossmanLarson.of'_zero]
      exact one_mul _
    · rw [counit_of'_eq, if_neg hA0, zero_smul]
      -- LHS = 0; A ≠ 0 and A is not singleton-a-rooted.
      -- Expand of' A *_GL of' B via productForest = powerset-sum.
      change bMinusLin (R := R) a
          (product
            (GrossmanLarson.of' (R := R) A)
            (GrossmanLarson.of' B)) = 0
      rw [show product
              (GrossmanLarson.of' (R := R) A) (GrossmanLarson.of' B) =
            productForest (GrossmanLarson.of' (R := R) A) B from
          GrossmanLarson.of'_mul_of' _ _]
      unfold productForest
      -- Push bMinusLin a through Multiset.sum
      -- (treating the GrossmanLarson-typed sum as a CK-typed sum, defeq).
      have h_push : bMinusLin (R := R) a
          (B.powerset.map fun B₁ =>
            op
              (unop
                  (insertion (R := R)
                    (GrossmanLarson.of' A) (GrossmanLarson.of' B₁)) *
                unop (GrossmanLarson.of' (B - B₁)))).sum =
          (B.powerset.map fun B₁ =>
            bMinusLin (R := R) a
              (op
                (unop
                    (insertion (R := R)
                      (GrossmanLarson.of' A) (GrossmanLarson.of' B₁)) *
                  unop
                    (GrossmanLarson.of' (B - B₁))) :
                ConnesKreimer R (Nonplanar α))).sum := by
        rw [map_multiset_sum (bMinusLin (R := R) a), Multiset.map_map]
        rfl
      rw [h_push]
      -- Now: (B.powerset.map (bMinusLin a ∘ (B₁ => op (unop (insertion ...) * of'(B-B₁))))).sum
      -- Each summand: bMinusLin a (op (unop X * unop Y)) = bMinusLin a (X * Y) (op/unop are id).
      -- where X = insertion (of' A) (of' B₁) = Σ_{F' ∈ NIM A B₁} of' F'
      --       Y = of' (B - B₁)
      -- So X * Y = Σ of' F' * of' (B-B₁) = Σ of' (F' + (B-B₁))
      -- and bMinusLin a of that sum = Σ bMinusBasis a (F' + (B-B₁)) = 0 by helper.
      -- Reduce each summand to 0.
      apply Multiset.sum_eq_zero
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨B₁, _hB₁_mem, hx_eq⟩ := hx
      subst hx_eq
      -- Per-B₁ closure: bMinusLin a (op (unop (insertion (of' A) (of' B₁)) * unop (of' (B-B₁)))) = 0
      -- op/unop are identity; reduce to CK level. The `op` outer is a
      -- no-op on the underlying carrier; the goal already has CK as the
      -- ambient bMinusLin argument.
      have h_step : bMinusLin (R := R) a
          (((unop
              (insertion (R := R)
                (GrossmanLarson.of' A) (GrossmanLarson.of' B₁)) :
              ConnesKreimer R (Nonplanar α)) *
            unop (GrossmanLarson.of' (B - B₁)))) = 0 := by
        -- Unfold insertion (of' A) (of' B₁) = insertionBasis A B₁.
        rw [show (unop
              (insertion (R := R)
                (GrossmanLarson.of' A) (GrossmanLarson.of' B₁)) :
              ConnesKreimer R (Nonplanar α)) =
            insertionBasis A B₁ from by
          rw [insertion_of'_of']; rfl]
        unfold insertionBasis
        -- Now: bMinusLin a (((NIM A B₁).map of').sum * unop (of' (B-B₁))) = 0.
        show bMinusLin (R := R) a
            ((((Nonplanar.insertionMultiset A B₁).map fun F' =>
                ConnesKreimer.of' (R := R) F').sum :
              ConnesKreimer R (Nonplanar α)) *
              ConnesKreimer.of' (R := R) (B - B₁)) = 0
        -- Distribute * over the sum (right distributivity).
        rw [← Multiset.sum_map_mul_right]
        -- Push bMinusLin a through Multiset.sum.
        rw [map_multiset_sum (bMinusLin (R := R) a), Multiset.map_map]
        -- Show every summand is 0.
        apply Multiset.sum_eq_zero
        intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨F', hF'_mem, hy_eq⟩ := hy
        subst hy_eq
        -- of' F' * of' (B - B₁) = of' (F' + (B - B₁)), then bMinusLin a (of' ...) = bMinusBasis a ...
        show bMinusLin (R := R) a
            ((ConnesKreimer.of' (R := R) F' : ConnesKreimer R (Nonplanar α)) *
              ConnesKreimer.of' (R := R) (B - B₁)) = 0
        rw [← ConnesKreimer.of'_add]
        rw [show bMinusLin (R := R) a
              (ConnesKreimer.of' (R := R) (F' + (B - B₁)) :
                ConnesKreimer R (Nonplanar α)) =
            bMinusBasis (R := R) a (F' + (B - B₁)) from
          bMinusLin_of' a _]
        exact bMinusBasis_nim_add_eq_zero a A B₁ (B - B₁) F' hA0 hA hF'_mem
      exact h_step

/-- **The OG derivation identity**: `bMinusLin a` is a 1-cocycle
    with respect to the GL product:
    `B-_a (x *_GL y) = ε(x) • B-_a y + B-_a x *_GL y`.

    Both sides are bilinear in `(x, y)` (`product` is bundled bilinear), so
    basis extensionality reduces to `bMinusLin_gl_mul_basis`. -/
theorem bMinusLin_gl_mul (a : α)
    (x y : ConnesKreimer R (Nonplanar α)) :
    bMinusLin (R := R) a (product (R := R) x y) =
      ((ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x) •
        bMinusLin (R := R) a y +
      unop (product (R := R) (bMinusLin (R := R) a x) y) := by
  let mulCK : ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
    product (R := R) (α := α)
  have h : mulCK.compr₂ (bMinusLin (R := R) a) =
      LinearMap.smulRight
          (ConnesKreimer.counit :
            ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap
          (bMinusLin (R := R) a) +
        mulCK.comp (bMinusLin (R := R) a) :=
    ConnesKreimer.lhom_ext' fun A => ConnesKreimer.lhom_ext' fun B =>
      bMinusLin_gl_mul_basis a A B
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y


/-! ### Duality recurrences

The base and step cases of the GL/CK duality induction
(`Coproduct/PruningDuality.lean`): ε is multiplicative for the GL
product, and pairing against `B⁺ₐ z` unfolds through the B⁺/B⁻ adjoint
and the derivation identity `bMinusLin_gl_mul`. -/

/-! ### ε is multiplicative for the GL product

The cardinality preservation lemma `Nonplanar.insertionMultiset_card_eq`
(every `F' ∈ NIM(A, B)` has `|F'| = |A|`) and its planar substrate
`RoseTree.Pathed.insertionForest_length` now live in
`Linglib.Core.Algebra.RootedTree.PreLie.InsertionNonplanar`. -/

/-- `counit` of `insertionBasis A B` equals `if A = 0 ∧ B = 0 then 1 else 0`.
    For non-zero host A: every NIM output has cardinality |A| ≥ 1, so ε = 0.
    For host A = 0: NIM(0, B) = {0} iff B = 0, else empty. -/
private theorem counit_insertionBasis (A B : Forest (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (unop
          (insertionBasis (R := R) A B)) =
      (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
        (counit (ConnesKreimer.of' B : ConnesKreimer R (Nonplanar α))) := by
  -- Unfold insertionBasis: sum over NIM(A, B) of of' F'.
  -- ε of sum = sum of ε. ε(of' F') = if F'.card = 0 then 1 else 0.
  -- Case on A:
  -- * A = 0: NIM(0, B) handled by insertionMultiset_zero_left / _zero_right.
  -- * A ≠ 0: every F' has |F'| = |A| ≥ 1, so ε(of' F') = 0, sum = 0.
  unfold insertionBasis
  -- Goal: counit (unop ((NIM A B).map (fun F' => of' F')).sum) =
  --        counit (of' A) * counit (of' B)
  show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
      ((Nonplanar.insertionMultiset A B).map
        fun F' => ConnesKreimer.of' (R := R) F').sum =
    _
  -- counit (Σ ...) = Σ counit (...).
  rw [show ((Nonplanar.insertionMultiset A B).map
        fun F' => ConnesKreimer.of' (R := R) F').sum =
      ((Nonplanar.insertionMultiset A B).map
        fun F' => ConnesKreimer.of' (R := R) F').sum from rfl]
  -- Use additivity of counit through Multiset.sum.
  rw [show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        ((Nonplanar.insertionMultiset A B).map
          (fun F' => ConnesKreimer.of' (R := R) F')).sum =
      ((Nonplanar.insertionMultiset A B).map
        (fun F' => (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' (R := R) F'))).sum from ?_]
  swap
  · -- counit preserves Multiset.sum via additivity.
    induction Nonplanar.insertionMultiset A B using Multiset.induction with
    | empty => simp
    | cons F' rest ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, map_add, ih]
  -- Now: (NIM(A, B).map (fun F' => counit (of' F'))).sum = counit (of' A) * counit (of' B).
  -- ε(of' F') = if F'.card = 0 then 1 else 0.
  simp only [ConnesKreimer.counit_of']
  -- Now: (NIM(A,B).map (fun F' => if F'.card = 0 then 1 else 0)).sum =
  --       (if A.card = 0 then 1 else 0) * (if B.card = 0 then 1 else 0)
  by_cases hA : A = 0
  · subst hA
    -- Case A = 0: NIM(0, B) = {0} if B = 0 else 0.
    by_cases hB : B = 0
    · subst hB
      -- NIM(0, 0) = {0}.
      rw [Nonplanar.insertionMultiset_zero_right]
      simp
    · -- NIM(0, B) = 0 for B ≠ 0 (no host vertices).
      rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero B hB]
      simp [hB]
  · -- Case A ≠ 0: every F' ∈ NIM(A, B) has cardinality |A| ≥ 1, so F' ≠ 0.
    -- So ε(of' F') = 0 for every F'; sum = 0.
    -- And ε(of' A) = 0 (since A.card ≠ 0).
    have hAcard : A.card ≠ 0 := fun hc => hA (Multiset.card_eq_zero.mp hc)
    rw [if_neg hAcard, zero_mul]
    -- Need: (NIM(A,B).map (fun F' => if F'.card = 0 then 1 else 0)).sum = 0.
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨F', hF', hF'_eq⟩ := hx
    rw [← hF'_eq]
    -- |F'| = |A| ≠ 0.
    have hF'card : F'.card = A.card :=
      Nonplanar.insertionMultiset_card_eq A B hF'
    rw [hF'card, if_neg hAcard]

/-- The counit `ε` on CK is multiplicative for the GL product on basis.
    `ε(of' A *_GL of' B) = ε(of' A) · ε(of' B)`.

    Proof by case on `B`:
    * `B = 0`: GL product reduces to `of' A` (right unit); `ε(of' A) = ε(of' A) · 1`.
    * `B ≠ 0`: `ε(of' B) = 0`, RHS = 0. Expand LHS via `mul_of'_sum_form`;
      each summand has `ε(of'(B - B₁))` factor, non-zero only when `B - B₁ = 0`
      i.e. `B₁ = B`; then `ε(unop(insertion(of' A)(of' B))) = ε(of' A) · ε(of' B) = 0`
      via `counit_insertionBasis`. -/
private theorem counit_gl_mul_basis (A B : Forest (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (unop
          ((GrossmanLarson.of' (R := R) A : GrossmanLarson R α) *
            GrossmanLarson.of' B)) =
      (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
        (counit (ConnesKreimer.of' B : ConnesKreimer R (Nonplanar α))) := by
  by_cases hB : B = 0
  · subst hB
    -- of' A *_GL of' 0 = of' A *_GL 1 = of' A.
    have h_of_zero : (GrossmanLarson.of' (R := R) (0 : Forest (Nonplanar α)) :
          GrossmanLarson R α) = 1 := GrossmanLarson.of'_zero
    rw [h_of_zero, mul_one]
    show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (ConnesKreimer.of' A) =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' A) *
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' (0 : Forest (Nonplanar α)))
    rw [show (ConnesKreimer.of' (0 : Forest (Nonplanar α)) :
            ConnesKreimer R (Nonplanar α)) = 1 from
        ConnesKreimer.of'_zero, map_one]
    ring
  · -- B ≠ 0: counit(of' B) = 0, RHS = counit(of' A) * 0 = 0.
    have hBcard : B.card ≠ 0 := fun hc => hB (Multiset.card_eq_zero.mp hc)
    have hCBzero : (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (ConnesKreimer.of' B) = 0 := by
      rw [ConnesKreimer.counit_of', if_neg hBcard]
    rw [hCBzero, mul_zero]
    -- Strategy: expand of' A * of' B via productForest formula, push counit through
    -- the Multiset.sum, show each summand reduces to counit(of' A) * counit(of' B) = 0,
    -- so the sum is 0.
    -- Helper: per-summand (CK product after unop) identity.
    have h_summand : ∀ B₁ : Forest (Nonplanar α),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            ConnesKreimer.of' (R := R) (B - B₁)) =
        (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
          (counit (ConnesKreimer.of' (R := R) (B₁ + (B - B₁)) :
            ConnesKreimer R (Nonplanar α))) := by
      intro B₁
      -- counit (X *_CK Y) = counit X * counit Y (algebra hom).
      rw [map_mul]
      -- Convert insertion (of' A) (of' B₁) → insertionBasis A B₁ (def via insertion_of'_of').
      rw [insertion_of'_of']
      -- counit (unop (insertionBasis A B₁)) = counit (of' A) * counit (of' B₁).
      rw [counit_insertionBasis A B₁]
      -- counit (of' (B₁ + (B - B₁))) = counit (of' B₁ * of'(B - B₁))
      --                              = counit (of' B₁) * counit (of'(B - B₁)).
      rw [show (ConnesKreimer.of' (R := R) (B₁ + (B - B₁)) :
              ConnesKreimer R (Nonplanar α)) =
            ConnesKreimer.of' (R := R) B₁ * ConnesKreimer.of' (R := R) (B - B₁) from
          ConnesKreimer.of'_add B₁ (B - B₁)]
      rw [map_mul]
      ring
    -- Outer: expand (of' A) * (of' B) via productForest, push counit through sum.
    -- Generic helper: push counit (algebra hom) ∘ unop through Multiset.sum.
    -- (unop is identity coercion, so this reduces to map_multiset_sum on counit.)
    have h_push_counit_unop_sum : ∀ s : Multiset (GrossmanLarson R α),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (unop s.sum) =
          (s.map (fun x =>
            (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (unop x))).sum :=
      fun s => map_multiset_sum (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) s
    -- Each summand of the productForest sum reduces to 0 after counit ∘ unop:
    -- op (unop(insertion (of' A) (of' B₁)) * unop(of'(B-B₁))) — after unop on the outer,
    -- becomes the inner CK product. counit applied via h_summand: = 0 for B₁ ⊆ B.
    have h_each_zero : ∀ x ∈ B.powerset.map (fun B₁ =>
        op
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            unop (GrossmanLarson.of' (B - B₁)))),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (unop x) = 0 := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨B₁, hB₁, hx_eq⟩ := hx
      have hB₁le : B₁ ≤ B := Multiset.mem_powerset.mp hB₁
      have hB₁add : B₁ + (B - B₁) = B := by
        rw [add_comm]; exact Multiset.sub_add_cancel hB₁le
      rw [← hx_eq]
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            unop (GrossmanLarson.of' (B - B₁))) = 0
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            ConnesKreimer.of' (R := R) (B - B₁)) = 0
      rw [h_summand B₁, hB₁add, hCBzero, mul_zero]
    -- Now compute LHS via productForest expansion.
    rw [GrossmanLarson.of'_mul_of']
    unfold productForest
    -- Goal: counit (unop ((B.powerset.map ...).sum)) = 0
    rw [h_push_counit_unop_sum]
    -- Goal: ((B.powerset.map ...).map (fun x => counit (unop x))).sum = 0
    apply Multiset.sum_eq_zero
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨x, hx, hy_eq⟩ := hy
    rw [← hy_eq]
    exact h_each_zero x hx

/-- The counit `ε` on CK is multiplicative for the GL product: both sides
    of `ε (x ⋆ y) = ε x · ε y` are bilinear (`product` is bundled), so basis
    extensionality reduces to `counit_gl_mul_basis`. -/
theorem counit_gl_mul (x y : ConnesKreimer R (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (product (R := R) x y) =
      (counit x) * (counit y) := by
  let mulCK : ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
    product (R := R) (α := α)
  have h : mulCK.compr₂
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap =
      LinearMap.smulRight
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap :=
    ConnesKreimer.lhom_ext' fun A => ConnesKreimer.lhom_ext' fun B =>
      counit_gl_mul_basis A B
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y


/-! ### Phase D's pairing-side recurrence -/

/-- The pairing-side recurrence: `⟨X ⋆ Y, B+_a z⟩` unfolds via the B+/B-
    adjoint + the derivation identity:
    `⟨X ⋆ Y, B+_a z⟩ = ε(X) · ⟨B-_a Y, z⟩ + ⟨B-_a X ⋆ Y, z⟩`. -/
theorem pairing_apply_bPlus_gl_mul (a : α)
    (X Y z : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (product (R := R) X Y)
      (ConnesKreimer.bPlusLin (R := R) a z) =
      (counit X) * pairing (R := R) (bMinusLin (R := R) a Y) z +
      pairing (R := R) (product (R := R) (bMinusLin (R := R) a X) Y) z := by
  rw [← bMinusLin_pairing_adjoint a (product (R := R) X Y) z,
      bMinusLin_gl_mul, LinearMap.map_add, LinearMap.add_apply,
      show pairing (R := R)
          (((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) X) •
            bMinusLin (R := R) a Y) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) X) •
          pairing (R := R) (bMinusLin a Y) from
        LinearMap.map_smul (pairing : ConnesKreimer R _ →ₗ[R] _) _ _,
      LinearMap.smul_apply, smul_eq_mul]
  rfl

end GrossmanLarson

