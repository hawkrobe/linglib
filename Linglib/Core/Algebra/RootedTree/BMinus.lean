/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# B- operator on `ConnesKreimer R (Nonplanar α)` and the B+/B- pairing adjoint
[oudom-guin-2008] [foissy-typed-decorated-rooted-trees-2018]

The `B-_a` operator is the transpose of `B+_a` (defined in
`Coproduct/PruningNonplanar.lean`) under the symmetry-weighted pairing
(defined in `GrossmanLarsonPairing.lean`). On basis elements:

```
B-_a (of' F) = if F = {Nonplanar.node a F'} for some F' then of' F' else 0
```

i.e., `B-_a` projects a singleton-forest containing an `a`-labeled root
tree to the children-forest of that tree, and gives `0` otherwise (on
multi-tree forests, empty forest, or singletons with a different root
label).

## Headline result

* `bMinusLin_pairing_adjoint`:
  `⟨B-_a x, y⟩ = ⟨x, B+_a y⟩`
  for all `a : α`, `x y : ConnesKreimer R (Nonplanar α)`.

This is the OG Prop 3.2 substrate: the transpose property anchors
the duality argument for `B-(A ∗ B) = ε(A) B-(B) + B-(A) ∗ B`
([oudom-guin-2008] §3.2; deferred to a sibling file).

## Why this file (OG-faithful Q5c route)

Per `[[feedback-substrate2-not-og]]`, Q5c's substrate 2 was a
linglib-invented identity that embeds A3.3 difficulty. OG's actual
route in Prop 3.2 uses B+/B- duality with Δ^ρ instead. This file
provides the B+/B- adjoint property — the foundation of that route.
-/

namespace RootedTree

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### `bMinusBasis` via per-list branching with perm-invariance -/

/-- Per-list branching for `bMinusBasis`. Reads the list as a planar
    representative of the basis forest, returns `of' (rootChildren T)`
    when the list is `[T]` and `T` has root label `a`. -/
private noncomputable def bMinusList (a : α) :
    List (Nonplanar α) → ConnesKreimer R (Nonplanar α)
  | [T] =>
      letI : Decidable (Nonplanar.rootLabel T = a) := Classical.dec _
      if Nonplanar.rootLabel T = a then
        of' (R := R) (Nonplanar.rootChildren T)
      else 0
  | _ => 0

/-- `bMinusList` is `List.Perm`-invariant: lists differing by a
    permutation give the same `bMinusList` output. Case analysis on
    list length (Perm preserves length): length 1 lists are equal
    pointwise; other lengths both give `0`. -/
private theorem bMinusList_perm (a : α) :
    ∀ {lst₁ lst₂ : List (Nonplanar α)}, lst₁.Perm lst₂ →
    bMinusList (R := R) a lst₁ = bMinusList (R := R) a lst₂ := by
  intro lst₁ lst₂ hperm
  rcases lst₁ with _ | ⟨T₁, _ | ⟨T₁', rest⟩⟩
  · -- lst₁ = []
    have hlen : lst₂.length = 0 := by rw [← hperm.length_eq]; rfl
    rcases lst₂ with _ | _
    · rfl
    · simp at hlen
  · -- lst₁ = [T₁]
    have hlen : lst₂.length = 1 := by rw [← hperm.length_eq]; rfl
    rcases lst₂ with _ | ⟨T₂, _ | ⟨_, _⟩⟩
    · simp at hlen
    · have hT : T₁ = T₂ := by
        have := hperm.mem_iff (a := T₁)
        simp at this
        exact this
      show bMinusList a [T₁] = bMinusList a [T₂]
      rw [hT]
    · simp at hlen
  · -- lst₁ = T₁ :: T₁' :: rest, length ≥ 2
    have hlen : lst₂.length = rest.length + 2 := by
      rw [← hperm.length_eq]; rfl
    rcases lst₂ with _ | ⟨T₂, _ | ⟨T₂', rest₂⟩⟩
    · simp at hlen
    · simp at hlen
    · rfl

/-- The B-_a operator on basis-key forests. Defined via `Quotient.liftOn`
    from `bMinusList`, using `bMinusList_perm` for well-definedness. -/
noncomputable def bMinusBasis (a : α) (F : Forest (Nonplanar α)) :
    ConnesKreimer R (Nonplanar α) :=
  Quotient.liftOn F (bMinusList (R := R) a)
    (fun _ _ hperm => bMinusList_perm a hperm)

@[simp] theorem bMinusBasis_zero (a : α) :
    bMinusBasis (R := R) a (0 : Forest (Nonplanar α)) = 0 := by
  unfold bMinusBasis
  show Quotient.liftOn (↑([] : List (Nonplanar α)) : Multiset (Nonplanar α))
      (bMinusList (R := R) a) _ = 0
  show bMinusList (R := R) a [] = 0
  rfl

@[simp] theorem bMinusBasis_singleton_node (a : α) (F : Forest (Nonplanar α)) :
    bMinusBasis (R := R) a ({Nonplanar.node a F} : Forest (Nonplanar α)) =
      of' F := by
  unfold bMinusBasis
  show Quotient.liftOn (↑[Nonplanar.node a F] : Multiset (Nonplanar α))
      (bMinusList (R := R) a) _ = of' F
  show bMinusList (R := R) a [Nonplanar.node a F] = of' F
  show (letI : Decidable (Nonplanar.rootLabel (Nonplanar.node a F) = a) :=
            Classical.dec _
        if Nonplanar.rootLabel (Nonplanar.node a F) = a then
          of' (R := R) (Nonplanar.rootChildren (Nonplanar.node a F))
        else 0) = of' F
  rw [Nonplanar.rootLabel_node, if_pos rfl, Nonplanar.rootChildren_node]

/-! ### `bMinusLin a` — linear extension -/

/-- The B-_a linear map: linear extension of `bMinusBasis` via `Finsupp.lift`. -/
noncomputable def bMinusLin (a : α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  Finsupp.lift _ R (Forest (Nonplanar α)) (bMinusBasis (R := R) a)

@[simp] theorem bMinusLin_of' (a : α) (F : Forest (Nonplanar α)) :
    bMinusLin (R := R) a (of' F) = bMinusBasis (R := R) a F := by
  show Finsupp.lift _ R _ _ (Finsupp.single F 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

/-! ### B+/B- pairing adjoint -/

/-- **Adjoint** of `bPlusLin a` w.r.t. the symmetry-weighted pairing.
    On basis: `⟨B-_a (of' F), of' G⟩ = ⟨of' F, B+_a (of' G)⟩`. -/
theorem bMinusLin_pairing_adjoint_basis (a : α)
    (F G : Forest (Nonplanar α)) :
    pairing (R := R) (bMinusLin (R := R) a (of' F)) (of' G) =
    pairing (R := R) (of' F) (bPlusLin (R := R) a (of' G)) := by
  -- RHS: bPlusLin a (of' G) = ofTree (node a G) = of' {node a G}.
  -- pairing (of' F) (of' {node a G}) = if F = {node a G} then forestAutCard F else 0.
  have hBplus : ConnesKreimer.bPlusLin (R := R) a (of' G) =
      ofTree (Nonplanar.node a G) :=
    ConnesKreimer.bPlusLin_of' a G
  rw [hBplus]
  -- ofTree T = of' {T}.
  have hRHS : pairing (R := R) (of' F)
      (ofTree (Nonplanar.node a G) : ConnesKreimer R (Nonplanar α)) =
    (letI : Decidable (F = ({Nonplanar.node a G} : Forest (Nonplanar α))) :=
        Classical.dec _
      if F = ({Nonplanar.node a G} : Forest (Nonplanar α)) then
        (forestAutCard F : R) else 0) := by
    show pairing (R := R) (of' F)
        (of' ({Nonplanar.node a G} : Forest (Nonplanar α))) = _
    exact pairing_of'_of' F _
  rw [hRHS]
  -- LHS: bMinusLin a (of' F) = bMinusBasis a F.
  rw [bMinusLin_of']
  -- Case on whether F is a singleton-{node a-rooted} forest.
  -- F = {node a G'} for some G'? Or other?
  -- The basis pairing of bMinusBasis F with of' G:
  --   - If F = {node a G''}: bMinusBasis = of' G''; pair with of' G = [G'' = G] · forestAutCard G''.
  --   - Else: bMinusBasis = 0; pair = 0.
  -- RHS = [F = {node a G}] · forestAutCard F.
  -- Match: F = {node a G''} = {node a G} ↔ G'' = G; forestAutCard {node a G} = forestAutCard {node a G''}.
  -- So both sides are: [F = {node a G}] · forestAutCard F.
  letI : DecidableEq (Forest (Nonplanar α)) := Classical.decEq _
  by_cases hF : ∃ G' : Forest (Nonplanar α), F = {Nonplanar.node a G'}
  · obtain ⟨G', hFG'⟩ := hF
    subst hFG'
    rw [bMinusBasis_singleton_node]
    have hLHS : pairing (R := R) (of' G') (of' G) =
        (letI : Decidable (G' = G) := Classical.dec _
         if G' = G then (forestAutCard G' : R) else 0) :=
      pairing_of'_of' G' G
    rw [hLHS]
    by_cases hG : G' = G
    · subst hG
      rw [if_pos rfl, if_pos rfl]
      show ((Nonplanar.forestAutCard G' : R)) =
          ((Nonplanar.forestAutCard ({Nonplanar.node a G'} : Forest _) : R))
      congr 1
      -- forestAutCard {node a G'} = autCard (node a G') = forestAutCard G'.
      letI : DecidableEq (Nonplanar α) := Classical.decEq _
      show Nonplanar.forestAutCard G' =
        Nonplanar.forestAutCard ({Nonplanar.node a G'} : Forest _)
      conv_rhs => unfold Nonplanar.forestAutCard
      rw [show ({Nonplanar.node a G'} : Multiset (Nonplanar α)).toFinset =
            {Nonplanar.node a G'} from Multiset.toFinset_singleton _]
      rw [Finset.prod_singleton]
      simp [Nonplanar.autCard_node]
    · have hne : ({Nonplanar.node a G'} : Forest (Nonplanar α)) ≠
                 ({Nonplanar.node a G} : Forest (Nonplanar α)) := by
        intro heq; apply hG
        have := Multiset.singleton_inj.mp heq
        have := congrArg Nonplanar.rootChildren this
        rwa [Nonplanar.rootChildren_node, Nonplanar.rootChildren_node] at this
      rw [if_neg hG, if_neg hne]
  · -- F is not of form {node a G'}; bMinusBasis F = 0; RHS pairing also 0.
    have hF_ne : F ≠ {Nonplanar.node a G} :=
      fun h => hF ⟨G, h⟩
    rw [if_neg hF_ne]
    -- Show bMinusBasis a F = 0.
    have h_zero : bMinusBasis (R := R) a F = 0 := by
      -- Take list representative; case-analyze its length / head label.
      obtain ⟨lst, hlst⟩ : ∃ lst : List (Nonplanar α), F = ↑lst :=
        ⟨F.toList, F.coe_toList.symm⟩
      subst hlst
      unfold bMinusBasis
      show Quotient.liftOn (↑lst : Multiset (Nonplanar α))
          (bMinusList (R := R) a) _ = 0
      show bMinusList (R := R) a lst = 0
      rcases lst with _ | ⟨T, _ | ⟨T', rest⟩⟩
      · rfl
      · -- lst = [T]; F = ↑[T] = {T}. Need: T ≠ Nonplanar.node a (anything).
        show (letI : Decidable (Nonplanar.rootLabel T = a) := Classical.dec _
              if Nonplanar.rootLabel T = a then
                of' (R := R) (Nonplanar.rootChildren T)
              else 0) = 0
        rw [if_neg]
        intro hlab
        apply hF
        refine ⟨Nonplanar.rootChildren T, ?_⟩
        show (↑[T] : Multiset (Nonplanar α)) =
              {Nonplanar.node a (Nonplanar.rootChildren T)}
        congr 1
        -- T = node a (rootChildren T) when rootLabel T = a (by eta).
        rw [← hlab, Nonplanar.node_eta]
      · rfl
    rw [h_zero]
    show pairing (R := R) (0 : ConnesKreimer R (Nonplanar α)) (of' G) = 0
    rw [LinearMap.map_zero, LinearMap.zero_apply]

/-- **B+/B- adjoint** under the symmetry-weighted pairing:
    `⟨B-_a x, y⟩ = ⟨x, B+_a y⟩` for all `a, x, y`.
    Reduces to `bMinusLin_pairing_adjoint_basis` via bilinearity. -/
theorem bMinusLin_pairing_adjoint (a : α)
    (x y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (bMinusLin (R := R) a x) y =
    pairing (R := R) x (bPlusLin (R := R) a y) := by
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · -- x = 0
    show pairing (R := R) (bMinusLin (R := R) a
          (0 : ConnesKreimer R (Nonplanar α))) y =
        pairing (R := R) (0 : ConnesKreimer R (Nonplanar α))
          (bPlusLin (R := R) a y)
    rw [LinearMap.map_zero, LinearMap.map_zero,
        LinearMap.zero_apply, LinearMap.zero_apply]
  · -- x = x₁ + x₂
    intro x₁ x₂ ih₁ ih₂
    let x₁' : ConnesKreimer R (Nonplanar α) := x₁
    let x₂' : ConnesKreimer R (Nonplanar α) := x₂
    show pairing (R := R) (bMinusLin (R := R) a (x₁' + x₂')) y =
        pairing (R := R) (x₁' + x₂') (bPlusLin (R := R) a y)
    rw [LinearMap.map_add, LinearMap.map_add, LinearMap.add_apply, ih₁, ih₂]
    rw [show pairing (R := R) (x₁' + x₂') = pairing x₁' + pairing x₂' from
          pairing.map_add x₁' x₂']
    rfl
  · -- x = single F r
    intro F r
    refine Finsupp.induction_linear y ?_ ?_ ?_
    · -- y = 0
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      show pairing (R := R) (bMinusLin (R := R) a x_single)
            (0 : ConnesKreimer R (Nonplanar α)) =
          pairing (R := R) x_single (bPlusLin (R := R) a
            (0 : ConnesKreimer R (Nonplanar α)))
      rw [pairing_zero_right]
      rw [show ConnesKreimer.bPlusLin (R := R) a
              (0 : ConnesKreimer R (Nonplanar α)) = 0 from
          LinearMap.map_zero _]
      rw [pairing_zero_right]
    · -- y = y₁ + y₂
      intro y₁ y₂ ih₁ ih₂
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      let y₁' : ConnesKreimer R (Nonplanar α) := y₁
      let y₂' : ConnesKreimer R (Nonplanar α) := y₂
      show pairing (R := R) (bMinusLin (R := R) a x_single) (y₁' + y₂') =
          pairing (R := R) x_single (bPlusLin (R := R) a (y₁' + y₂'))
      rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ih₁, ih₂]
    · -- y = single G s
      intro G s
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      let y_single : ConnesKreimer R (Nonplanar α) := Finsupp.single G s
      show pairing (R := R) (bMinusLin (R := R) a x_single) y_single =
          pairing (R := R) x_single (bPlusLin (R := R) a y_single)
      have hx : x_single = r • (of' (R := R) F) := by
        show (Finsupp.single F r : ConnesKreimer R (Nonplanar α)) =
              r • (Finsupp.single F 1 : ConnesKreimer R (Nonplanar α))
        exact (Finsupp.smul_single_one F r).symm
      have hy : y_single = s • (of' (R := R) G) := by
        show (Finsupp.single G s : ConnesKreimer R (Nonplanar α)) =
              s • (Finsupp.single G 1 : ConnesKreimer R (Nonplanar α))
        exact (Finsupp.smul_single_one G s).symm
      rw [hx, hy]
      -- Goal: pairing (bMinusLin a (r • of' F)) (s • of' G) =
      --       pairing (r • of' F) (bPlusLin a (s • of' G))
      -- Pull scalars out via bilinearity helper, then apply basis adjoint.
      have h_factor : ∀ (u v : ConnesKreimer R (Nonplanar α)),
          pairing (R := R) (r • u) (s • v) = r * s * pairing (R := R) u v := by
        intro u v
        have step1 : pairing (R := R) (r • u) = r • pairing (R := R) u :=
          LinearMap.map_smul (pairing : ConnesKreimer R _ →ₗ[R] _) r u
        have step3 : (pairing (R := R) u) (s • v) =
            s • (pairing (R := R) u) v :=
          LinearMap.map_smul (pairing (R := R) u) s v
        calc pairing (R := R) (r • u) (s • v)
            = (r • pairing (R := R) u) (s • v) := by rw [step1]
          _ = r • (pairing (R := R) u) (s • v) := LinearMap.smul_apply _ _ _
          _ = r • s • (pairing (R := R) u) v := by rw [step3]
          _ = r * s * (pairing (R := R) u) v := by
                rw [smul_eq_mul, smul_eq_mul]; ring
      -- Apply h_bmin/h_bplus to pull scalars from the bMinusLin/bPlusLin LinearMaps.
      have h_bmin : bMinusLin (R := R) a (r • (of' (R := R) F)) =
          r • bMinusLin (R := R) a (of' F) :=
        LinearMap.map_smul (bMinusLin (R := R) a) r (of' F)
      have h_bplus : ConnesKreimer.bPlusLin (R := R) a (s • (of' (R := R) G)) =
          s • ConnesKreimer.bPlusLin (R := R) a (of' G) :=
        LinearMap.map_smul (ConnesKreimer.bPlusLin (R := R) a) s (of' G)
      -- Direct calc chain.
      calc pairing (R := R) (bMinusLin a (r • (of' F))) (s • (of' G))
          = pairing (R := R) (r • bMinusLin a (of' F)) (s • (of' G)) := by
              congr 2
        _ = r * s * pairing (R := R) (bMinusLin a (of' F)) (of' G) :=
              h_factor _ _
        _ = r * s * pairing (R := R) (of' F)
              (ConnesKreimer.bPlusLin a (of' G)) := by
              rw [bMinusLin_pairing_adjoint_basis]
        _ = pairing (R := R) (r • (of' F))
              (s • ConnesKreimer.bPlusLin a (of' G)) := (h_factor _ _).symm
        _ = pairing (R := R) (r • (of' F))
              (ConnesKreimer.bPlusLin a (s • (of' G))) := by
              congr 1
              exact h_bplus.symm

/-! ## Phase C: OG-style identity `B-_a(x *_GL y) = ε(x) • B-_a y + B-_a x *_GL y`

OG paper [oudom-guin-2008] §3.2 proves this identity on the S(L)
side. On the CK side (under the algebra iso ckIso), this becomes the
direct identity `bMinusLin a (x *_GL y) = counit(x) • bMinusLin a y +
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

/-- **NIM-level keystone**: at the Nonplanar multi-insertion level, grafting
    `B` into the singleton host `{node a A'}` decomposes by partitioning
    B's grafting positions into "at the root vertex" (becomes new
    children) vs "in A's subtrees" (recursive NIM).

    `(letI : DecidableEq (Nonplanar α) := Classical.decEq _`
    ` Nonplanar.insertionMultiset {Nonplanar.node a A'} B) =`
    `(B.powerset.bind (fun B₁ =>`
    `  (Nonplanar.insertionMultiset A' B₁).map`
    `    (fun F' => ({Nonplanar.node a (F' + (B - B₁))} : Forest _))))`

    Sorry-fenced — the planar-level partition (via
    `vertices_multiGraft_decomp` + assignment-bucketing) underlies
    this. Singleton-host-with-fixed-root-label case of A3.3-style
    reasoning. -/
private theorem nim_singleton_node_a_decomp
    (a : α) (A' B : Forest (Nonplanar α)) :
    Nonplanar.insertionMultiset
        ({Nonplanar.node a A'} : Forest (Nonplanar α)) B =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       B.powerset.bind fun B₁ =>
         (Nonplanar.insertionMultiset A' B₁).map fun F' =>
           ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))) := by
  sorry

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

    This is the singleton-a-rooted-host case of A3.3 keystone reasoning.
    Sorry-fenced; needed for Phase C / Sub-case B1. -/
private theorem singleton_node_a_insertion_eq_bPlus_gl_mul
    (a : α) (A' B : Forest (Nonplanar α)) :
    GrossmanLarson.insertion (R := R)
        (GrossmanLarson.of' ({Nonplanar.node a A'} : Forest (Nonplanar α)))
        (GrossmanLarson.of' B) =
      ConnesKreimer.bPlusLin (R := R) a
        (GrossmanLarson.unop
          ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
            GrossmanLarson.of' B)) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Common form: (B.powerset.map (fun B₁ =>
  --   ((NIM A' B₁).map (fun F' => of' {node a (F' + (B - B₁))})).sum)).sum
  set common : ConnesKreimer R (Nonplanar α) :=
    (B.powerset.map fun B₁ =>
      ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
        ConnesKreimer.of' (R := R)
          ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))).sum).sum
    with h_common
  -- Step 1: LHS = common.
  have hLHS : (GrossmanLarson.insertion (R := R)
      (GrossmanLarson.of' ({Nonplanar.node a A'} : Forest (Nonplanar α)))
      (GrossmanLarson.of' B) : GrossmanLarson R α) = common := by
    rw [GrossmanLarson.insertion_of'_of']
    unfold GrossmanLarson.insertionBasis
    rw [nim_singleton_node_a_decomp a A' B]
    rw [Multiset.map_bind, Multiset.sum_bind, h_common]
    congr 1
    apply Multiset.map_congr rfl
    intro B₁ _
    rw [Multiset.map_map]
    rfl
  -- Step 2: RHS = common.
  have hRHS : ConnesKreimer.bPlusLin (R := R) a
      (GrossmanLarson.unop
        ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
          GrossmanLarson.of' B)) = common := by
    -- Per-summand identity:
    have h_summand : ∀ B₁ : Forest (Nonplanar α),
        ConnesKreimer.bPlusLin (R := R) a
          ((GrossmanLarson.unop
            (GrossmanLarson.insertion (R := R)
              (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
              ConnesKreimer R (Nonplanar α)) *
            (GrossmanLarson.unop (GrossmanLarson.of' (R := R) (B - B₁)))) =
        ((Nonplanar.insertionMultiset A' B₁).map fun F' =>
          ConnesKreimer.of' (R := R)
            ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))).sum := by
      intro B₁
      -- insertion (of' A') (of' B₁) = insertionBasis A' B₁ = (NIM ...).map of').sum.
      rw [GrossmanLarson.insertion_of'_of']
      unfold GrossmanLarson.insertionBasis
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
    unfold GrossmanLarson.productForest
    rw [h_common]
    -- Define the per-B₁ summand function and use linearity.
    -- For each B₁, the summand is op (unop (insertion ...) * unop (of' ...)),
    -- so unop'd it's just unop (insertion ...) * unop (of' ...).
    -- bPlusLin a (Σ ...) = Σ bPlusLin a (...).
    -- Use h_summand B₁ for each.
    -- Push unop through Multiset.sum (it's linear) — define a helper.
    have h_unop_sum : ∀ (s : Multiset (Forest (Nonplanar α))),
        GrossmanLarson.unop
            (s.map fun B₁ =>
              GrossmanLarson.op
                (GrossmanLarson.unop
                    (GrossmanLarson.insertion (R := R)
                      (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) *
                  GrossmanLarson.unop (GrossmanLarson.of' (B - B₁)))).sum =
          (s.map fun B₁ =>
            (GrossmanLarson.unop
                (GrossmanLarson.insertion (R := R)
                  (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
              ConnesKreimer R (Nonplanar α)) *
              GrossmanLarson.unop (GrossmanLarson.of' (B - B₁))).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => rfl
      | cons B₁ rest ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        show (GrossmanLarson.unop
              ((GrossmanLarson.op _ : GrossmanLarson R α) + (rest.map _).sum)) =
          _ + (rest.map _).sum
        rfl
    rw [h_unop_sum B.powerset]
    -- Now push bPlusLin a through Multiset.sum.
    have h_bPlus_sum : ∀ (s : Multiset (Forest (Nonplanar α))),
        ConnesKreimer.bPlusLin (R := R) a
            (s.map fun B₁ =>
              (GrossmanLarson.unop
                  (GrossmanLarson.insertion (R := R)
                    (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
                ConnesKreimer R (Nonplanar α)) *
                GrossmanLarson.unop (GrossmanLarson.of' (B - B₁))).sum =
          (s.map fun B₁ =>
            ConnesKreimer.bPlusLin (R := R) a
              ((GrossmanLarson.unop
                  (GrossmanLarson.insertion (R := R)
                    (GrossmanLarson.of' A') (GrossmanLarson.of' B₁)) :
                ConnesKreimer R (Nonplanar α)) *
                GrossmanLarson.unop (GrossmanLarson.of' (B - B₁)))).sum := by
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

/-! ### Phase C main theorem -/

/-- `bMinusLin a` is the constant function `0` on basis forests that are
    not singleton-a-rooted. Helper for the easy cases of Phase C. -/
theorem bMinusBasis_eq_zero_of_not_singleton_a (a : α)
    (F : Forest (Nonplanar α))
    (h : ¬ ∃ G' : Forest (Nonplanar α), F = ({Nonplanar.node a G'} : Forest _)) :
    bMinusBasis (R := R) a F = 0 := by
  obtain ⟨lst, hlst⟩ : ∃ lst : List (Nonplanar α), F = ↑lst :=
    ⟨F.toList, F.coe_toList.symm⟩
  subst hlst
  unfold bMinusBasis
  show Quotient.liftOn (↑lst : Multiset (Nonplanar α))
      (bMinusList (R := R) a) _ = 0
  show bMinusList (R := R) a lst = 0
  rcases lst with _ | ⟨T, _ | ⟨T', rest⟩⟩
  · rfl
  · -- lst = [T]; F = ↑[T] = {T}. Need: T's root label ≠ a.
    show (letI : Decidable (Nonplanar.rootLabel T = a) := Classical.dec _
          if Nonplanar.rootLabel T = a then
            of' (R := R) (Nonplanar.rootChildren T) else 0) = 0
    rw [if_neg]
    intro hlab
    apply h
    refine ⟨Nonplanar.rootChildren T, ?_⟩
    show (↑[T] : Multiset (Nonplanar α)) =
          {Nonplanar.node a (Nonplanar.rootChildren T)}
    congr 1
    rw [← hlab, Nonplanar.node_eta]
  · rfl

/-- Counit of `of' F`: `1` if `F = 0`, else `0`. Re-expressed via `Decidable`. -/
private theorem counit_of'_eq (F : Forest (Nonplanar α)) :
    (ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
      (ConnesKreimer.of' F) =
      (letI : Decidable (F = 0) := Classical.dec _
       if F = 0 then (1 : R) else 0) := by
  rw [ConnesKreimer.counit_of']
  letI : Decidable (F = 0) := Classical.dec _
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
      (letI : Decidable (G = 0) := Classical.dec _
       if G = 0 then (ConnesKreimer.of' (R := R) F : ConnesKreimer R (Nonplanar α))
       else 0) := by
  letI : Decidable (G = 0) := Classical.dec _
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

/-- **Phase C helper**: `bMinusLin a (bPlusLin a Y * of' G)` equals `Y`
    if `G = 0` (the `bMinusLin ∘ bPlusLin = id` identity on basis elements
    extends linearly to all `Y`), and `0` otherwise (the product has each
    basis summand of cardinality `≥ 2`, so `bMinusLin` kills it).

    Reduces by `Finsupp.induction_linear` on `Y` to the basis case via
    `bMinusBasis_singleton_node_add`. -/
private theorem bMinusLin_bPlusLin_mul_of' (a : α)
    (Y : ConnesKreimer R (Nonplanar α)) (G : Forest (Nonplanar α)) :
    bMinusLin (R := R) a
      (ConnesKreimer.bPlusLin (R := R) a Y *
        ConnesKreimer.of' (R := R) G) =
      (letI : Decidable (G = 0) := Classical.dec _
       if G = 0 then Y else 0) := by
  letI : Decidable (G = 0) := Classical.dec _
  refine Finsupp.induction_linear Y ?_ ?_ ?_
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
    have h_bPlus : ConnesKreimer.bPlusLin (R := R) a (Finsupp.single F r) =
        r • ConnesKreimer.of' (R := R) ({Nonplanar.node a F} : Forest _) := by
      show Finsupp.lift _ R _ _ (Finsupp.single F r) = _
      rw [Finsupp.lift_apply, Finsupp.sum_single_index]
      · rfl
      · simp
    show bMinusLin (R := R) a
        (ConnesKreimer.bPlusLin (R := R) a (Finsupp.single F r) *
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
        (Finsupp.single F r : ConnesKreimer R (Nonplanar α))
      show r • Finsupp.single F (1 : R) =
        (Finsupp.single F r : ConnesKreimer R (Nonplanar α))
      rw [Finsupp.smul_single]
      simp
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
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    (B.powerset.map fun B₁ =>
      if B - B₁ = (0 : Forest (Nonplanar α)) then f B₁ else (0 : β)).sum = f B := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
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

/-- **Phase C basis case**: for basis `x = of' A, y = of' B`, the OG
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
      GrossmanLarson.unop
        ((GrossmanLarson.op (bMinusLin (R := R) a (ConnesKreimer.of' A))) *
          GrossmanLarson.of' B) := by
  letI : DecidableEq (Forest (Nonplanar α)) := Classical.decEq _
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
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
        (GrossmanLarson.product
          (GrossmanLarson.of' (R := R)
            ({Nonplanar.node a A'} : Forest (Nonplanar α)))
          (GrossmanLarson.of' B)) = _
    rw [show GrossmanLarson.product
            (GrossmanLarson.of' (R := R)
              ({Nonplanar.node a A'} : Forest (Nonplanar α)))
            (GrossmanLarson.of' B) =
          GrossmanLarson.productForest
            (GrossmanLarson.of' (R := R)
              ({Nonplanar.node a A'} : Forest (Nonplanar α))) B from
        GrossmanLarson.of'_mul_of' _ _]
    unfold GrossmanLarson.productForest
    -- Push bMinusLin a through Multiset.sum (generic lemma).
    have h_push_sum_generic : ∀ s : Multiset (ConnesKreimer R (Nonplanar α)),
        bMinusLin (R := R) a s.sum = (s.map (bMinusLin (R := R) a)).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => simp
      | cons head rest ih => simp [ih]
    have h_push_sum : bMinusLin (R := R) a
          ((B.powerset.map fun B₁ =>
            GrossmanLarson.op
              (GrossmanLarson.unop
                  (GrossmanLarson.insertion (R := R)
                    (GrossmanLarson.of'
                      ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                    (GrossmanLarson.of' B₁)) *
                GrossmanLarson.unop (GrossmanLarson.of' (B - B₁)))).sum) =
        (B.powerset.map fun B₁ =>
          bMinusLin (R := R) a
            (GrossmanLarson.op
              (GrossmanLarson.unop
                  (GrossmanLarson.insertion (R := R)
                    (GrossmanLarson.of'
                      ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                    (GrossmanLarson.of' B₁)) *
                GrossmanLarson.unop (GrossmanLarson.of' (B - B₁))))).sum := by
      have h := h_push_sum_generic (B.powerset.map fun B₁ =>
        GrossmanLarson.op
          (GrossmanLarson.unop
              (GrossmanLarson.insertion (R := R)
                (GrossmanLarson.of'
                  ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                (GrossmanLarson.of' B₁)) *
            GrossmanLarson.unop (GrossmanLarson.of' (B - B₁))))
      rw [Multiset.map_map] at h
      exact h
    rw [h_push_sum]
    -- Per-summand: apply singleton bridge then helper 2.
    have h_summand : ∀ B₁ : Forest (Nonplanar α),
        bMinusLin (R := R) a
          (GrossmanLarson.op
            (GrossmanLarson.unop
                (GrossmanLarson.insertion (R := R)
                  (GrossmanLarson.of'
                    ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                  (GrossmanLarson.of' B₁)) *
              GrossmanLarson.unop (GrossmanLarson.of' (B - B₁)))) =
        (if B - B₁ = (0 : Forest (Nonplanar α)) then
           GrossmanLarson.unop
             ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
               GrossmanLarson.of' B₁)
         else 0) := by
      intro B₁
      rw [singleton_node_a_insertion_eq_bPlus_gl_mul]
      -- Now: bMinusLin a (op (unop (bPlusLin a (unop(of' A' * of' B₁))) * unop(of' (B - B₁))))
      -- = bMinusLin a (bPlusLin a (unop(of' A' * of' B₁)) * of'(B - B₁))   [op, unop are id]
      show bMinusLin (R := R) a
          ((ConnesKreimer.bPlusLin (R := R) a
              (GrossmanLarson.unop
                ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
                  GrossmanLarson.of' B₁))) *
            ConnesKreimer.of' (R := R) (B - B₁)) = _
      rw [bMinusLin_bPlusLin_mul_of']
    have h_map_eq : (B.powerset.map fun B₁ =>
          bMinusLin (R := R) a
            (GrossmanLarson.op
              (GrossmanLarson.unop
                  (GrossmanLarson.insertion (R := R)
                    (GrossmanLarson.of'
                      ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                    (GrossmanLarson.of' B₁)) *
                GrossmanLarson.unop (GrossmanLarson.of' (B - B₁))))) =
        B.powerset.map (fun B₁ =>
          if B - B₁ = (0 : Forest (Nonplanar α)) then
            GrossmanLarson.unop
              ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
                GrossmanLarson.of' B₁)
          else 0) := by
      apply Multiset.map_congr rfl
      intro B₁ _
      exact h_summand B₁
    rw [h_map_eq]
    -- Collapse via helper 3.
    have h_collapse := sum_powerset_diff_zero_indicator B (fun B₁ =>
        GrossmanLarson.unop
          ((GrossmanLarson.of' (R := R) A' : GrossmanLarson R α) *
            GrossmanLarson.of' B₁))
    -- h_collapse uses Classical.decEq for the if-then-else; goal uses local instance.
    -- Decidable instances on the same proposition are subsingletons.
    convert h_collapse using 4
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
        GrossmanLarson.unop
          ((GrossmanLarson.op (0 : ConnesKreimer R (Nonplanar α))) *
            GrossmanLarson.of' B)
    -- Simplify `(op 0 * of' B).unop = 0` using `product`'s linearity.
    have hZero : (GrossmanLarson.op (0 : ConnesKreimer R (Nonplanar α)) :
        GrossmanLarson R α) * GrossmanLarson.of' B =
      (0 : GrossmanLarson R α) := by
      show GrossmanLarson.product (0 : GrossmanLarson R α)
            (GrossmanLarson.of' B) = 0
      rw [LinearMap.map_zero, LinearMap.zero_apply]
    rw [hZero, show GrossmanLarson.unop (0 : GrossmanLarson R α) =
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
      exact GrossmanLarson.one_mul _
    · rw [counit_of'_eq, if_neg hA0, zero_smul]
      -- LHS = 0; A ≠ 0 and A is not singleton-a-rooted.
      -- Approach: expand of' A *_GL of' B via mul_of'_sum_form; each
      -- summand has form `op (unop X * unop Y)` with X = insertion-output
      -- (whose support is forests of cardinality |A|), Y = of'(B - B₁).
      -- Applied to bMinusLin a, summands are 0 because output forests
      -- aren't singleton-a-rooted (cardinality = |A| + |B-B₁|).
      -- Wiring is non-trivial (unop push through Multiset.sum, bMinusLin
      -- push through Multiset.sum, then the per-summand analysis).
      -- Deferred — depends on substrate moves; sorry-fenced.
      sorry

/-- **Phase C main theorem (OG-style)**: `bMinusLin a` is a 1-cocycle
    with respect to the GL product:
    `B-_a (x *_GL y) = ε(x) • B-_a y + B-_a x *_GL y`.

    Reduces by `Finsupp.induction_linear` (twice) to the basis case
    `bMinusLin_gl_mul_basis`. Deferred — mechanical bilinearity wiring
    once the basis case is closed. -/
theorem bMinusLin_gl_mul (a : α)
    (x y : ConnesKreimer R (Nonplanar α)) :
    bMinusLin (R := R) a
      ((GrossmanLarson.op x : GrossmanLarson R α) * GrossmanLarson.op y) =
      ((ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x) •
        bMinusLin (R := R) a y +
      GrossmanLarson.unop
        ((GrossmanLarson.op (bMinusLin (R := R) a x)) *
          GrossmanLarson.op y) := by
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · -- x = 0
    change bMinusLin (R := R) a
        ((0 : GrossmanLarson R α) * GrossmanLarson.op y) =
      ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) 0) •
        bMinusLin (R := R) a y +
      GrossmanLarson.unop
        (((GrossmanLarson.op (bMinusLin (R := R) a 0)) : GrossmanLarson R α) *
          GrossmanLarson.op y)
    rw [GrossmanLarson.zero_mul_gl,
        show bMinusLin (R := R) a (0 : ConnesKreimer R (Nonplanar α)) =
            (0 : ConnesKreimer R (Nonplanar α)) from
          (bMinusLin (R := R) a).map_zero,
        map_zero, zero_smul]
    change (0 : ConnesKreimer R (Nonplanar α)) =
      0 +
      GrossmanLarson.unop
        (((0 : GrossmanLarson R α)) * GrossmanLarson.op y)
    rw [GrossmanLarson.zero_mul_gl,
        show GrossmanLarson.unop (0 : GrossmanLarson R α) =
            (0 : ConnesKreimer R (Nonplanar α)) from rfl,
        zero_add]
  · -- x = x₁ + x₂
    intro x₁ x₂ ih₁ ih₂
    let x₁' : ConnesKreimer R (Nonplanar α) := x₁
    let x₂' : ConnesKreimer R (Nonplanar α) := x₂
    show bMinusLin (R := R) a
        ((GrossmanLarson.op (x₁' + x₂') : GrossmanLarson R α) * GrossmanLarson.op y) =
      ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) (x₁' + x₂')) •
        bMinusLin (R := R) a y +
      GrossmanLarson.unop
        ((GrossmanLarson.op (bMinusLin (R := R) a (x₁' + x₂'))) * GrossmanLarson.op y)
    rw [show (GrossmanLarson.op (x₁' + x₂') : GrossmanLarson R α) =
          GrossmanLarson.op x₁' + GrossmanLarson.op x₂' from rfl,
        add_mul]
    -- Push bMinusLin a through + (using explicit map_add to bypass FunLike issue).
    rw [show bMinusLin (R := R) a
          ((GrossmanLarson.op x₁' : GrossmanLarson R α) * GrossmanLarson.op y +
            GrossmanLarson.op x₂' * GrossmanLarson.op y) =
        bMinusLin (R := R) a
            ((GrossmanLarson.op x₁' : GrossmanLarson R α) * GrossmanLarson.op y) +
          bMinusLin (R := R) a
            ((GrossmanLarson.op x₂' : GrossmanLarson R α) * GrossmanLarson.op y) from
        map_add _ _ _]
    rw [ih₁, ih₂,
        map_add (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x₁' x₂',
        add_smul,
        show bMinusLin (R := R) a (x₁' + x₂') =
            bMinusLin (R := R) a x₁' + bMinusLin (R := R) a x₂' from
          map_add _ _ _,
        show (GrossmanLarson.op (bMinusLin (R := R) a x₁' +
              bMinusLin (R := R) a x₂') : GrossmanLarson R α) =
            GrossmanLarson.op (bMinusLin (R := R) a x₁') +
            GrossmanLarson.op (bMinusLin (R := R) a x₂') from rfl,
        add_mul,
        show GrossmanLarson.unop
              ((GrossmanLarson.op (bMinusLin (R := R) a x₁') :
                GrossmanLarson R α) * GrossmanLarson.op y +
                GrossmanLarson.op (bMinusLin (R := R) a x₂') *
                  GrossmanLarson.op y) =
            GrossmanLarson.unop ((GrossmanLarson.op (bMinusLin (R := R) a x₁') :
                GrossmanLarson R α) * GrossmanLarson.op y) +
              GrossmanLarson.unop (GrossmanLarson.op (bMinusLin (R := R) a x₂') *
                GrossmanLarson.op y) from rfl]
    abel
  · -- x = single F r
    intro F r
    refine Finsupp.induction_linear y ?_ ?_ ?_
    · -- y = 0
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      show bMinusLin (R := R) a
          ((GrossmanLarson.op x_single : GrossmanLarson R α) *
            GrossmanLarson.op (0 : ConnesKreimer R (Nonplanar α))) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a 0 +
        GrossmanLarson.unop
          ((GrossmanLarson.op (bMinusLin (R := R) a x_single)) *
            GrossmanLarson.op (0 : ConnesKreimer R (Nonplanar α)))
      change bMinusLin (R := R) a
          ((GrossmanLarson.op x_single : GrossmanLarson R α) *
            (0 : GrossmanLarson R α)) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a 0 +
        GrossmanLarson.unop
          ((GrossmanLarson.op (bMinusLin (R := R) a x_single) : GrossmanLarson R α) *
            (0 : GrossmanLarson R α))
      rw [GrossmanLarson.mul_zero_gl, GrossmanLarson.mul_zero_gl,
          show bMinusLin (R := R) a (0 : ConnesKreimer R (Nonplanar α)) =
              (0 : ConnesKreimer R (Nonplanar α)) from
            (bMinusLin (R := R) a).map_zero,
          smul_zero,
          show GrossmanLarson.unop (0 : GrossmanLarson R α) =
              (0 : ConnesKreimer R (Nonplanar α)) from rfl, add_zero]
      exact (bMinusLin (R := R) a).map_zero
    · -- y = y₁ + y₂
      intro y₁ y₂ ih₁ ih₂
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      let y₁' : ConnesKreimer R (Nonplanar α) := y₁
      let y₂' : ConnesKreimer R (Nonplanar α) := y₂
      show bMinusLin (R := R) a
          ((GrossmanLarson.op x_single : GrossmanLarson R α) *
            GrossmanLarson.op (y₁' + y₂')) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a (y₁' + y₂') +
        GrossmanLarson.unop
          ((GrossmanLarson.op (bMinusLin (R := R) a x_single)) *
            GrossmanLarson.op (y₁' + y₂'))
      rw [show (GrossmanLarson.op (y₁' + y₂') : GrossmanLarson R α) =
            GrossmanLarson.op y₁' + GrossmanLarson.op y₂' from rfl,
          mul_add]
      rw [show bMinusLin (R := R) a
            ((GrossmanLarson.op x_single : GrossmanLarson R α) * GrossmanLarson.op y₁' +
              GrossmanLarson.op x_single * GrossmanLarson.op y₂') =
          bMinusLin (R := R) a
              ((GrossmanLarson.op x_single : GrossmanLarson R α) * GrossmanLarson.op y₁') +
            bMinusLin (R := R) a
              ((GrossmanLarson.op x_single : GrossmanLarson R α) * GrossmanLarson.op y₂') from
          map_add _ _ _]
      rw [ih₁, ih₂,
          show bMinusLin (R := R) a (y₁' + y₂') =
              bMinusLin (R := R) a y₁' + bMinusLin (R := R) a y₂' from
            map_add _ _ _,
          smul_add, mul_add,
          show GrossmanLarson.unop
                ((GrossmanLarson.op (bMinusLin (R := R) a x_single) :
                  GrossmanLarson R α) * GrossmanLarson.op y₁' +
                  GrossmanLarson.op (bMinusLin (R := R) a x_single) *
                    GrossmanLarson.op y₂') =
              GrossmanLarson.unop ((GrossmanLarson.op (bMinusLin (R := R) a x_single) :
                  GrossmanLarson R α) * GrossmanLarson.op y₁') +
                GrossmanLarson.unop (GrossmanLarson.op (bMinusLin (R := R) a x_single) *
                  GrossmanLarson.op y₂') from rfl]
      abel
    · -- y = single G s: factor out r, s, then apply bMinusLin_gl_mul_basis F G.
      intro G s
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      let y_single : ConnesKreimer R (Nonplanar α) := Finsupp.single G s
      show bMinusLin (R := R) a
          ((GrossmanLarson.op x_single : GrossmanLarson R α) *
            GrossmanLarson.op y_single) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a y_single +
        GrossmanLarson.unop
          ((GrossmanLarson.op (bMinusLin (R := R) a x_single)) *
            GrossmanLarson.op y_single)
      have hx : x_single = r • (ConnesKreimer.of' (R := R) F) := by
        show (Finsupp.single F r : ConnesKreimer R (Nonplanar α)) =
            r • (Finsupp.single F (1 : R) : ConnesKreimer R (Nonplanar α))
        exact (Finsupp.smul_single_one F r).symm
      have hy : y_single = s • (ConnesKreimer.of' (R := R) G) := by
        show (Finsupp.single G s : ConnesKreimer R (Nonplanar α)) =
            s • (Finsupp.single G (1 : R) : ConnesKreimer R (Nonplanar α))
        exact (Finsupp.smul_single_one G s).symm
      rw [hx, hy]
      -- Pull r, s through op (op is linear, rfl since op = id).
      rw [show (GrossmanLarson.op (r • ConnesKreimer.of' (R := R) F) :
            GrossmanLarson R α) =
          r • GrossmanLarson.op (ConnesKreimer.of' (R := R) F) from rfl,
          show (GrossmanLarson.op (s • ConnesKreimer.of' (R := R) G) :
            GrossmanLarson R α) =
          s • GrossmanLarson.op (ConnesKreimer.of' (R := R) G) from rfl]
      -- Pull r, s through * using smul_mul_gl/mul_smul_gl.
      rw [GrossmanLarson.smul_mul_gl,
          GrossmanLarson.mul_smul_gl]
      -- Push bMinusLin a through smul (explicit show to bypass FunLike).
      rw [show bMinusLin (R := R) a
              (r • s • ((GrossmanLarson.op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * GrossmanLarson.op
                  (ConnesKreimer.of' (R := R) G))) =
            r • bMinusLin (R := R) a
              (s • ((GrossmanLarson.op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * GrossmanLarson.op
                  (ConnesKreimer.of' (R := R) G))) from
          (bMinusLin (R := R) a).map_smul r _,
          show bMinusLin (R := R) a
              (s • ((GrossmanLarson.op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * GrossmanLarson.op
                  (ConnesKreimer.of' (R := R) G))) =
            s • bMinusLin (R := R) a
              ((GrossmanLarson.op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * GrossmanLarson.op
                  (ConnesKreimer.of' (R := R) G)) from
          (bMinusLin (R := R) a).map_smul s _]
      -- RHS side: factor r, s out.
      rw [show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (r • ConnesKreimer.of' (R := R) F) =
            r • (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (ConnesKreimer.of' (R := R) F) from
          map_smul _ _ _,
          show bMinusLin (R := R) a
              (s • ConnesKreimer.of' (R := R) G) =
            s • bMinusLin (R := R) a (ConnesKreimer.of' (R := R) G) from
          (bMinusLin (R := R) a).map_smul s _,
          show bMinusLin (R := R) a
              (r • ConnesKreimer.of' (R := R) F) =
            r • bMinusLin (R := R) a (ConnesKreimer.of' (R := R) F) from
          (bMinusLin (R := R) a).map_smul r _,
          show (GrossmanLarson.op (r • bMinusLin (R := R) a
              (ConnesKreimer.of' (R := R) F)) : GrossmanLarson R α) =
            r • GrossmanLarson.op (bMinusLin (R := R) a
              (ConnesKreimer.of' (R := R) F)) from rfl,
          GrossmanLarson.smul_mul_gl, GrossmanLarson.mul_smul_gl]
      -- Push unop through smul (unop is identity).
      rw [show GrossmanLarson.unop (r • s • ((GrossmanLarson.op
              (bMinusLin (R := R) a (ConnesKreimer.of' (R := R) F)) :
              GrossmanLarson R α) * GrossmanLarson.op
                (ConnesKreimer.of' (R := R) G))) =
            r • s • GrossmanLarson.unop ((GrossmanLarson.op
                (bMinusLin (R := R) a (ConnesKreimer.of' (R := R) F)) :
              GrossmanLarson R α) * GrossmanLarson.op
                (ConnesKreimer.of' (R := R) G)) from rfl]
      -- Apply bMinusLin_gl_mul_basis F G.
      -- Use `change` (isDefEq) to coerce `op (CK.of' _)` → `GL.of' _` so that
      -- `rw [bMinusLin_gl_mul_basis ...]` can match by head symbol.
      -- (The `show ... from rfl` chains don't suffice because `rw` indexes by
      -- head symbol via discrimination tree, which won't unfold opaque defs.)
      change r • s • bMinusLin (R := R) a
          ((GrossmanLarson.of' (R := R) F : GrossmanLarson R α) *
            GrossmanLarson.of' G) =
        (r • (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (ConnesKreimer.of' (R := R) F)) •
          s • bMinusLin (R := R) a (ConnesKreimer.of' (R := R) G) +
        r • s • GrossmanLarson.unop
          ((GrossmanLarson.op (bMinusLin (R := R) a
              (ConnesKreimer.of' (R := R) F)) : GrossmanLarson R α) *
            GrossmanLarson.of' G)
      rw [bMinusLin_gl_mul_basis a F G]
      -- Both sides now: r • s • (counit(of'F) • bMinusLin a (of'G) + unop(op(bMinusLin a (of'F)) * of'G))
      -- vs RHS: (r • counit (of'F)) • s • bMinusLin a (of'G) + r • s • unop(...)
      -- Distribute r •, s • through the sum and collapse smul-smul + smul-mul.
      simp only [smul_add, smul_smul, smul_eq_mul]
      -- Coefficient arithmetic: (r * (s * counit)) = (s * r * counit) by commutativity.
      congr 1
      congr 1
      ring

end GrossmanLarson

end RootedTree
