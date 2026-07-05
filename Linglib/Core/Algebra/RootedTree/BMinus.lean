/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionNodeDecomp
import Linglib.Core.Algebra.ConnesKreimer.Shuffle
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

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### `bMinusBasis` via per-list branching with perm-invariance -/

/-- Per-list branching for `bMinusBasis`. Reads the list as a planar
    representative of the basis forest, returns `of' (rootChildren T)`
    when the list is `[T]` and `T` has root label `a`. -/
private noncomputable def bMinusList (a : α) :
    List (Nonplanar α) → ConnesKreimer R (Nonplanar α)
  | [T] =>
      if Nonplanar.rootValue T = a then
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
  show (if Nonplanar.rootValue (Nonplanar.node a F) = a then
          of' (R := R) (Nonplanar.rootChildren (Nonplanar.node a F))
        else 0) = of' F
  rw [Nonplanar.rootValue_node, if_pos rfl, Nonplanar.rootChildren_node]

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
    (if F = ({Nonplanar.node a G} : Forest (Nonplanar α)) then
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
  by_cases hF : ∃ G' : Forest (Nonplanar α), F = {Nonplanar.node a G'}
  · obtain ⟨G', hFG'⟩ := hF
    subst hFG'
    rw [bMinusBasis_singleton_node]
    have hLHS : pairing (R := R) (of' G') (of' G) =
        (if G' = G then (forestAutCard G' : R) else 0) :=
      pairing_of'_of' G' G
    rw [hLHS]
    by_cases hG : G' = G
    · subst hG
      rw [if_pos rfl, if_pos rfl]
      show ((Nonplanar.forestAutCard G' : R)) =
          ((Nonplanar.forestAutCard ({Nonplanar.node a G'} : Forest _) : R))
      congr 1
      -- forestAutCard {node a G'} = autCard (node a G') = forestAutCard G'.
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
        show (if Nonplanar.rootValue T = a then
                of' (R := R) (Nonplanar.rootChildren T)
              else 0) = 0
        rw [if_neg]
        intro hlab
        apply hF
        refine ⟨Nonplanar.rootChildren T, ?_⟩
        show (↑[T] : Multiset (Nonplanar α)) =
              {Nonplanar.node a (Nonplanar.rootChildren T)}
        congr 1
        -- T = node a (rootChildren T) when rootValue T = a (by eta).
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
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
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
    refine ConnesKreimer.induction_linear y ?_ ?_ ?_
    · -- y = 0
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
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
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      let y₁' : ConnesKreimer R (Nonplanar α) := y₁
      let y₂' : ConnesKreimer R (Nonplanar α) := y₂
      show pairing (R := R) (bMinusLin (R := R) a x_single) (y₁' + y₂') =
          pairing (R := R) x_single (bPlusLin (R := R) a (y₁' + y₂'))
      rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ih₁, ih₂]
    · -- y = single G s
      intro G s
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      let y_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single G s
      show pairing (R := R) (bMinusLin (R := R) a x_single) y_single =
          pairing (R := R) x_single (bPlusLin (R := R) a y_single)
      have hx : x_single = r • (of' (R := R) F) := by
        show (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) =
              r • (ConnesKreimer.single F 1 : ConnesKreimer R (Nonplanar α))
        exact ConnesKreimer.smul_single_one F r
      have hy : y_single = s • (of' (R := R) G) := by
        show (ConnesKreimer.single G s : ConnesKreimer R (Nonplanar α)) =
              s • (ConnesKreimer.single G 1 : ConnesKreimer R (Nonplanar α))
        exact ConnesKreimer.smul_single_one G s
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

/-- `Multiset.bind` as a mapped sum (`join` is definitionally `sum`). -/
private theorem bind_eq_map_sum {γ δ : Type*} (s : Multiset γ)
    (f : γ → Multiset δ) : s.bind f = (s.map f).sum := rfl

omit [DecidableEq α] in
/-- The `true`-bucket of a zip over `Quotient.out` representatives has
    the nonplanar `true`-bucket as its `mk`-image. -/
private theorem filterMap_zip_out_mk_t (l : List (Nonplanar α)) (assn : List Bool) :
    (((l.map Quotient.out).zip assn).filterMap
        (fun p => if p.2 then some p.1 else none)).map Nonplanar.mk =
      (l.zip assn).filterMap (fun p => if p.2 then some p.1 else none) := by
  induction l generalizing assn with
  | nil => rfl
  | cons x l ih =>
    cases assn with
    | nil => rfl
    | cons b assn =>
      cases b with
      | true =>
        show Nonplanar.mk (Quotient.out x) ::
            ((((l.map Quotient.out).zip assn).filterMap _).map Nonplanar.mk) = _
        have hx : Nonplanar.mk (Quotient.out x) = x := Quotient.out_eq x
        rw [hx, ih]
        rfl
      | false => exact ih assn

omit [DecidableEq α] in
/-- The `false`-bucket analog of `filterMap_zip_out_mk_t`. -/
private theorem filterMap_zip_out_mk_f (l : List (Nonplanar α)) (assn : List Bool) :
    (((l.map Quotient.out).zip assn).filterMap
        (fun p => if p.2 then none else some p.1)).map Nonplanar.mk =
      (l.zip assn).filterMap (fun p => if p.2 then none else some p.1) := by
  induction l generalizing assn with
  | nil => rfl
  | cons x l ih =>
    cases assn with
    | nil => rfl
    | cons b assn =>
      cases b with
      | true => exact ih assn
      | false =>
        show Nonplanar.mk (Quotient.out x) ::
            ((((l.map Quotient.out).zip assn).filterMap _).map Nonplanar.mk) = _
        have hx : Nonplanar.mk (Quotient.out x) = x := Quotient.out_eq x
        rw [hx, ih]
        rfl

/-- **NIM-level keystone**: at the Nonplanar multi-insertion level, grafting
    `B` into the singleton host `{node a A'}` decomposes by partitioning
    B's grafting positions into "at the root vertex" (becomes new
    children) vs "in A's subtrees" (recursive NIM).

    Descent through the quotient: the singleton host's canonical planar
    representative is `Perm`-swapped for a visible planar node,
    `RoseTree.Pathed.insertion_node_split` provides the root-vs-subtree
    mask decomposition, and the mask enumeration is converted to the
    powerset bind via `listChoices_bridge_powerset_paired` plus the
    powerset partition involution (the mask convention has `true` =
    root guests, while the powerset bind runs over the subtree bucket). -/
private theorem nim_singleton_node_a_decomp
    (a : α) (A' B : Forest (Nonplanar α)) :
    Nonplanar.insertionMultiset
        ({Nonplanar.node a A'} : Forest (Nonplanar α)) B =
      (B.powerset.bind fun B₁ =>
         (Nonplanar.insertionMultiset A' B₁).map fun F' =>
           ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))) := by
  -- §1: the canonical planar representative of the host is equivalent to
  -- the visible node on A''s canonical children list.
  have h_mk2 : Nonplanar.mk (RoseTree.node a (A'.toList.map Quotient.out)) =
      Nonplanar.node a A' := by
    rw [← Nonplanar.node_mk_tree_list]
    congr 1
    rw [List.map_map,
        show A'.toList.map (Nonplanar.mk ∘ Quotient.out) = A'.toList from
          (List.map_congr_left fun x _ => Quotient.out_eq x).trans
            (List.map_id _)]
    exact A'.coe_toList
  have h_equiv : RoseTree.Perm
      (Quotient.out (Nonplanar.node a A'))
      (RoseTree.node a (A'.toList.map Quotient.out)) :=
    Nonplanar.mk_eq_mk_iff.mp
      (((Nonplanar.node a A').out_eq).trans h_mk2.symm)
  -- §2: unfold NIM; the host list is the singleton of the canonical rep.
  unfold Nonplanar.insertionMultiset
  rw [show (({Nonplanar.node a A'} : Forest (Nonplanar α)).toList.map
        Quotient.out : List (RoseTree α))
      = [Quotient.out (Nonplanar.node a A')] from by
    rw [Multiset.toList_singleton]
    rfl]
  -- §3: swap the host representative under the msform map.
  have h_host := RoseTree.Pathed.insertionForest_perm_host
    (B.toList.map Quotient.out) (List.Forall₂.cons h_equiv List.Forall₂.nil)
  have h_host' :
      (RoseTree.Pathed.insertionForest [Quotient.out (Nonplanar.node a A')]
          (B.toList.map Quotient.out)).map
        (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
          Multiset (Nonplanar α))) =
      (RoseTree.Pathed.insertionForest
          [RoseTree.node a (A'.toList.map Quotient.out)]
          (B.toList.map Quotient.out)).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
    have h2 := congrArg
      (Multiset.map (fun l : List (Nonplanar α) =>
        (Multiset.ofList l : Multiset (Nonplanar α)))) h_host
    rw [Multiset.map_map, Multiset.map_map] at h2
    exact h2
  rw [h_host']
  -- §4: singleton-forest reduction + the node-split engine.
  rw [RoseTree.Pathed.insertionForest_singleton, Multiset.map_map,
      RoseTree.Pathed.insertion_node_split, Multiset.map_bind]
  -- §5: convert the RHS powerset bind to the mask enumeration. The mask
  -- convention has `true` = root guests, so the powerset bind (over the
  -- subtree bucket B₁) is first flipped by the partition involution.
  have h_rhs : (B.powerset.bind fun B₁ =>
        (Nonplanar.insertionMultiset A' B₁).map fun F' =>
          ({Nonplanar.node a (F' + (B - B₁))} : Forest (Nonplanar α))) =
      (Multiset.ofList
          (RoseTree.Pathed.listChoices [true, false] B.toList.length)).bind
        (fun assn =>
          (Nonplanar.insertionMultiset A'
              (((B.toList.zip assn).filterMap
                fun p => if p.2 then none else some p.1 : List (Nonplanar α)) :
                Multiset (Nonplanar α))).map
            fun F' => ({Nonplanar.node a (F' +
              (((B.toList.zip assn).filterMap
                fun p => if p.2 then some p.1 else none : List (Nonplanar α)) :
                Multiset (Nonplanar α)))} : Forest (Nonplanar α))) := by
    -- Step A: flip the partition so the bind variable is the root bucket.
    rw [bind_eq_map_sum]
    rw [Multiset.powerset_partition_swap B
      (fun B₁ rest => (Nonplanar.insertionMultiset A' B₁).map fun F' =>
        ({Nonplanar.node a (F' + rest)} : Forest (Nonplanar α)))]
    -- Step B: pair form + the powerset↔mask bridge.
    rw [show (B.powerset.map fun s =>
          (Nonplanar.insertionMultiset A' (B - s)).map fun F' =>
            ({Nonplanar.node a (F' + s)} : Forest (Nonplanar α))) =
        ((B.powerset.map fun s => (s, B - s)).map
          fun pr => (Nonplanar.insertionMultiset A' pr.2).map fun F' =>
            ({Nonplanar.node a (F' + pr.1)} : Forest (Nonplanar α))) from by
      rw [Multiset.map_map]
      rfl]
    rw [show (B.powerset.map fun s => (s, B - s)) =
        (Multiset.ofList
            (RoseTree.Pathed.listChoices [true, false] B.toList.length)).map
          (fun assn =>
            ((((B.toList.zip assn).filterMap
                fun p => if p.2 then some p.1 else none : List (Nonplanar α)) :
                Multiset (Nonplanar α)),
             (((B.toList.zip assn).filterMap
                fun p => if p.2 then none else some p.1 : List (Nonplanar α)) :
                Multiset (Nonplanar α)))) from by
      conv_lhs => rw [show B = (↑(B.toList) : Multiset (Nonplanar α)) from
        B.coe_toList.symm]
      rw [← RoseTree.Pathed.listChoices_bridge_powerset_paired (l := B.toList)]]
    rw [Multiset.map_map, ← bind_eq_map_sum]
    rfl
  refine Eq.trans ?_ h_rhs.symm
  -- §6: per-mask congruence. Align mask lengths, then reduce each mask.
  rw [List.length_map]
  refine Multiset.bind_congr fun assn h_assn => ?_
  -- Named buckets: planar (out-rep) and nonplanar (canonical) per side.
  set gs_t : List (RoseTree α) := ((B.toList.map Quotient.out).zip assn).filterMap
    (fun p => if p.2 then some p.1 else none) with hgs_t
  set gs_f : List (RoseTree α) := ((B.toList.map Quotient.out).zip assn).filterMap
    (fun p => if p.2 then none else some p.1) with hgs_f
  set s_t : Multiset (Nonplanar α) := Multiset.ofList
    ((B.toList.zip assn).filterMap
      (fun p => if p.2 then some p.1 else none)) with hs_t
  set s_f : Multiset (Nonplanar α) := Multiset.ofList
    ((B.toList.zip assn).filterMap
      (fun p => if p.2 then none else some p.1)) with hs_f
  -- mk-image facts for the two planar buckets.
  have h_t_mk : Multiset.ofList (gs_t.map Nonplanar.mk) = s_t := by
    rw [hgs_t, filterMap_zip_out_mk_t, hs_t]
  have h_f_perm : (gs_f.map Nonplanar.mk).Perm
      ((s_f.toList.map Quotient.out).map Nonplanar.mk) := by
    apply Multiset.coe_eq_coe.mp
    rw [hgs_f, filterMap_zip_out_mk_f, List.map_map,
        show s_f.toList.map (Nonplanar.mk ∘ Quotient.out) = s_f.toList from
          (List.map_congr_left fun x _ => Quotient.out_eq x).trans
            (List.map_id _),
        Multiset.coe_toList, hs_f]
  have h_guests := RoseTree.Pathed.insertionForest_msform_invariance_guests
    (A'.toList.map Quotient.out) h_f_perm
  -- Assemble: fuse post-maps, factor through msform, swap guests, recombine.
  rw [Multiset.map_map]
  calc (RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out) gs_f).map
        ((((fun L => (Multiset.ofList (L.map Nonplanar.mk) :
            Multiset (Nonplanar α))) ∘ fun T' => [T']))
          ∘ (fun cs' => RoseTree.node a (gs_t ++ cs')))
      = ((RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out) gs_f).map
          (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
            Multiset (Nonplanar α)))).map
        (fun M => ({Nonplanar.node a (s_t + M)} : Forest (Nonplanar α))) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun cs' _ => ?_
        show ({Nonplanar.mk (RoseTree.node a (gs_t ++ cs'))} :
          Forest (Nonplanar α)) = _
        congr 1
        rw [← Nonplanar.node_mk_tree_list]
        congr 1
        rw [List.map_append, ← Multiset.coe_add, h_t_mk]
    _ = ((RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out)
            (s_f.toList.map Quotient.out)).map
          (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
            Multiset (Nonplanar α)))).map
        (fun M => ({Nonplanar.node a (s_t + M)} : Forest (Nonplanar α))) := by
        rw [h_guests]
    _ = (Nonplanar.insertionMultiset A' s_f).map
        (fun F' => ({Nonplanar.node a (F' + s_t)} : Forest (Nonplanar α))) := by
        unfold Nonplanar.insertionMultiset
        rw [Multiset.map_map, Multiset.map_map]
        refine Multiset.map_congr rfl fun L _ => ?_
        show ({Nonplanar.node a (s_t + Multiset.ofList (L.map Nonplanar.mk))} :
          Forest (Nonplanar α)) = _
        rw [add_comm]
        rfl

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

    This is the singleton-a-rooted-host case of A3.3 keystone reasoning,
    proved from the NIM-level decomposition `nim_singleton_node_a_decomp`. -/
private theorem singleton_node_a_insertion_eq_bPlus_gl_mul
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
    rw [nim_singleton_node_a_decomp a A' B]
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
    show (if Nonplanar.rootValue T = a then
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

/-- **Phase C helper**: `bMinusLin a (bPlusLin a Y * of' G)` equals `Y`
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
    -- Push bMinusLin a through Multiset.sum (generic lemma).
    have h_push_sum_generic : ∀ s : Multiset (ConnesKreimer R (Nonplanar α)),
        bMinusLin (R := R) a s.sum = (s.map (bMinusLin (R := R) a)).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => simp
      | cons head rest ih => simp [ih]
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
      have h := h_push_sum_generic (B.powerset.map fun B₁ =>
        op
          (unop
              (insertion (R := R)
                (GrossmanLarson.of'
                  ({Nonplanar.node a A'} : Forest (Nonplanar α)))
                (GrossmanLarson.of' B₁)) *
            unop (GrossmanLarson.of' (B - B₁))))
      rw [Multiset.map_map] at h
      exact h
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
      -- Push bMinusLin a through Multiset.sum.
      have h_push_sum : ∀ s : Multiset (ConnesKreimer R (Nonplanar α)),
          bMinusLin (R := R) a s.sum = (s.map (bMinusLin (R := R) a)).sum := by
        intro s
        induction s using Multiset.induction with
        | empty => simp
        | cons head rest ih => simp [ih]
      -- Treat the GrossmanLarson-typed sum as a CK-typed sum (defeq).
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
        have h := h_push_sum (B.powerset.map fun B₁ =>
            (op
              (unop
                  (insertion (R := R)
                    (GrossmanLarson.of' A) (GrossmanLarson.of' B₁)) *
                unop (GrossmanLarson.of' (B - B₁))) :
              ConnesKreimer R (Nonplanar α)))
        rw [Multiset.map_map] at h
        exact h
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
        rw [h_push_sum, Multiset.map_map]
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

/-- **Phase C main theorem (OG-style)**: `bMinusLin a` is a 1-cocycle
    with respect to the GL product:
    `B-_a (x *_GL y) = ε(x) • B-_a y + B-_a x *_GL y`.

    Reduces by `ConnesKreimer.induction_linear` (twice) to the basis case
    `bMinusLin_gl_mul_basis`. -/
theorem bMinusLin_gl_mul (a : α)
    (x y : ConnesKreimer R (Nonplanar α)) :
    bMinusLin (R := R) a
      ((op x : GrossmanLarson R α) * op y) =
      ((ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x) •
        bMinusLin (R := R) a y +
      unop
        ((op (bMinusLin (R := R) a x)) *
          op y) := by
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
  · -- x = 0
    change bMinusLin (R := R) a
        ((0 : GrossmanLarson R α) * op y) =
      ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) 0) •
        bMinusLin (R := R) a y +
      unop
        (((op (bMinusLin (R := R) a 0)) : GrossmanLarson R α) *
          op y)
    rw [zero_mul_gl,
        show bMinusLin (R := R) a (0 : ConnesKreimer R (Nonplanar α)) =
            (0 : ConnesKreimer R (Nonplanar α)) from
          (bMinusLin (R := R) a).map_zero,
        map_zero, zero_smul]
    change (0 : ConnesKreimer R (Nonplanar α)) =
      0 +
      unop
        (((0 : GrossmanLarson R α)) * op y)
    rw [zero_mul_gl,
        show unop (0 : GrossmanLarson R α) =
            (0 : ConnesKreimer R (Nonplanar α)) from rfl,
        zero_add]
  · -- x = x₁ + x₂
    intro x₁ x₂ ih₁ ih₂
    let x₁' : ConnesKreimer R (Nonplanar α) := x₁
    let x₂' : ConnesKreimer R (Nonplanar α) := x₂
    show bMinusLin (R := R) a
        ((op (x₁' + x₂') : GrossmanLarson R α) * op y) =
      ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) (x₁' + x₂')) •
        bMinusLin (R := R) a y +
      unop
        ((op (bMinusLin (R := R) a (x₁' + x₂'))) * op y)
    rw [show (op (x₁' + x₂') : GrossmanLarson R α) =
          op x₁' + op x₂' from rfl,
        add_mul]
    -- Push bMinusLin a through + (using explicit map_add to bypass FunLike issue).
    rw [show bMinusLin (R := R) a
          ((op x₁' : GrossmanLarson R α) * op y +
            op x₂' * op y) =
        bMinusLin (R := R) a
            ((op x₁' : GrossmanLarson R α) * op y) +
          bMinusLin (R := R) a
            ((op x₂' : GrossmanLarson R α) * op y) from
        map_add _ _ _]
    rw [ih₁, ih₂,
        map_add (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x₁' x₂',
        add_smul,
        show bMinusLin (R := R) a (x₁' + x₂') =
            bMinusLin (R := R) a x₁' + bMinusLin (R := R) a x₂' from
          map_add _ _ _,
        show (op (bMinusLin (R := R) a x₁' +
              bMinusLin (R := R) a x₂') : GrossmanLarson R α) =
            op (bMinusLin (R := R) a x₁') +
            op (bMinusLin (R := R) a x₂') from rfl,
        add_mul,
        show unop
              ((op (bMinusLin (R := R) a x₁') :
                GrossmanLarson R α) * op y +
                op (bMinusLin (R := R) a x₂') *
                  op y) =
            unop ((op (bMinusLin (R := R) a x₁') :
                GrossmanLarson R α) * op y) +
              unop (op (bMinusLin (R := R) a x₂') *
                op y) from rfl]
    abel
  · -- x = single F r
    intro F r
    refine ConnesKreimer.induction_linear y ?_ ?_ ?_
    · -- y = 0
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      show bMinusLin (R := R) a
          ((op x_single : GrossmanLarson R α) *
            op (0 : ConnesKreimer R (Nonplanar α))) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a 0 +
        unop
          ((op (bMinusLin (R := R) a x_single)) *
            op (0 : ConnesKreimer R (Nonplanar α)))
      change bMinusLin (R := R) a
          ((op x_single : GrossmanLarson R α) *
            (0 : GrossmanLarson R α)) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a 0 +
        unop
          ((op (bMinusLin (R := R) a x_single) : GrossmanLarson R α) *
            (0 : GrossmanLarson R α))
      rw [mul_zero_gl, mul_zero_gl,
          show bMinusLin (R := R) a (0 : ConnesKreimer R (Nonplanar α)) =
              (0 : ConnesKreimer R (Nonplanar α)) from
            (bMinusLin (R := R) a).map_zero,
          smul_zero,
          show unop (0 : GrossmanLarson R α) =
              (0 : ConnesKreimer R (Nonplanar α)) from rfl, add_zero]
      exact (bMinusLin (R := R) a).map_zero
    · -- y = y₁ + y₂
      intro y₁ y₂ ih₁ ih₂
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      let y₁' : ConnesKreimer R (Nonplanar α) := y₁
      let y₂' : ConnesKreimer R (Nonplanar α) := y₂
      show bMinusLin (R := R) a
          ((op x_single : GrossmanLarson R α) *
            op (y₁' + y₂')) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a (y₁' + y₂') +
        unop
          ((op (bMinusLin (R := R) a x_single)) *
            op (y₁' + y₂'))
      rw [show (op (y₁' + y₂') : GrossmanLarson R α) =
            op y₁' + op y₂' from rfl,
          mul_add]
      rw [show bMinusLin (R := R) a
            ((op x_single : GrossmanLarson R α) * op y₁' +
              op x_single * op y₂') =
          bMinusLin (R := R) a
              ((op x_single : GrossmanLarson R α) * op y₁') +
            bMinusLin (R := R) a
              ((op x_single : GrossmanLarson R α) * op y₂') from
          map_add _ _ _]
      rw [ih₁, ih₂,
          show bMinusLin (R := R) a (y₁' + y₂') =
              bMinusLin (R := R) a y₁' + bMinusLin (R := R) a y₂' from
            map_add _ _ _,
          smul_add, mul_add,
          show unop
                ((op (bMinusLin (R := R) a x_single) :
                  GrossmanLarson R α) * op y₁' +
                  op (bMinusLin (R := R) a x_single) *
                    op y₂') =
              unop ((op (bMinusLin (R := R) a x_single) :
                  GrossmanLarson R α) * op y₁') +
                unop (op (bMinusLin (R := R) a x_single) *
                  op y₂') from rfl]
      abel
    · -- y = single G s: factor out r, s, then apply bMinusLin_gl_mul_basis F G.
      intro G s
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      let y_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single G s
      show bMinusLin (R := R) a
          ((op x_single : GrossmanLarson R α) *
            op y_single) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single) •
          bMinusLin (R := R) a y_single +
        unop
          ((op (bMinusLin (R := R) a x_single)) *
            op y_single)
      have hx : x_single = r • (ConnesKreimer.of' (R := R) F) := by
        show (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) =
            r • (ConnesKreimer.single F (1 : R) : ConnesKreimer R (Nonplanar α))
        exact ConnesKreimer.smul_single_one F r
      have hy : y_single = s • (ConnesKreimer.of' (R := R) G) := by
        show (ConnesKreimer.single G s : ConnesKreimer R (Nonplanar α)) =
            s • (ConnesKreimer.single G (1 : R) : ConnesKreimer R (Nonplanar α))
        exact ConnesKreimer.smul_single_one G s
      rw [hx, hy]
      -- Pull r, s through op (op is linear, rfl since op = id).
      rw [show (op (r • ConnesKreimer.of' (R := R) F) :
            GrossmanLarson R α) =
          r • op (ConnesKreimer.of' (R := R) F) from rfl,
          show (op (s • ConnesKreimer.of' (R := R) G) :
            GrossmanLarson R α) =
          s • op (ConnesKreimer.of' (R := R) G) from rfl]
      -- Pull r, s through * using smul_mul_gl/mul_smul_gl.
      rw [smul_mul_gl,
          mul_smul_gl]
      -- Push bMinusLin a through smul (explicit show to bypass FunLike).
      rw [show bMinusLin (R := R) a
              (r • s • ((op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * op
                  (ConnesKreimer.of' (R := R) G))) =
            r • bMinusLin (R := R) a
              (s • ((op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * op
                  (ConnesKreimer.of' (R := R) G))) from
          (bMinusLin (R := R) a).map_smul r _,
          show bMinusLin (R := R) a
              (s • ((op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * op
                  (ConnesKreimer.of' (R := R) G))) =
            s • bMinusLin (R := R) a
              ((op (ConnesKreimer.of' (R := R) F) :
                GrossmanLarson R α) * op
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
          show (op (r • bMinusLin (R := R) a
              (ConnesKreimer.of' (R := R) F)) : GrossmanLarson R α) =
            r • op (bMinusLin (R := R) a
              (ConnesKreimer.of' (R := R) F)) from rfl,
          smul_mul_gl, mul_smul_gl]
      -- Push unop through smul (unop is identity).
      rw [show unop (r • s • ((op
              (bMinusLin (R := R) a (ConnesKreimer.of' (R := R) F)) :
              GrossmanLarson R α) * op
                (ConnesKreimer.of' (R := R) G))) =
            r • s • unop ((op
                (bMinusLin (R := R) a (ConnesKreimer.of' (R := R) F)) :
              GrossmanLarson R α) * op
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
        r • s • unop
          ((op (bMinusLin (R := R) a
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
