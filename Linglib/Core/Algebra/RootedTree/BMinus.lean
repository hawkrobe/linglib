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
@cite{oudom-guin-2008} @cite{foissy-typed-decorated-rooted-trees-2018}

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
(@cite{oudom-guin-2008} §3.2; deferred to a sibling file).

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

/-! ## Phase C helpers

The full Phase C theorem `bMinusLin_gl_mul` (OG-style identity
`B-_a(x *_GL y) = ε(x) • B-_a y + B-_a x *_GL y`) is now in
`OudomGuinBridgePairing.lean` as `bMinusLin_gl_mul_via_pbw`, derived
via Q5c (= pre-Lie PBW iso) + Piece B + Piece C. The previous
combinatorial proof via `nim_singleton_node_a_decomp` (an
A3.3-family sorry) was removed in favor of the abstract derivation.

The helper below remains: it discharges the easy cases of B-_a's
behavior on non-singleton-a-rooted basis forests, used elsewhere
on the S(L) side (`BMinusSL.lean`). -/

/-- `bMinusLin a` is the constant function `0` on basis forests that are
    not singleton-a-rooted. -/
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
end GrossmanLarson

end RootedTree
