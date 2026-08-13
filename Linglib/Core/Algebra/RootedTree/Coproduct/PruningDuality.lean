import Linglib.Core.Algebra.RootedTree.BMinus
import Linglib.Core.Algebra.RootedTree.Coproduct.Pairing
import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonMonoid
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonSplit
import Linglib.Core.Algebra.RootedTree.PreLie.OudomGuinBridgePairing

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false
-- Nested tensor squares `CK ⊗ (CK ⊗ CK)` need one extra pending step during
-- instance synthesis: the chain `Semiring (CK ⊗ (CK ⊗ CK)) → Algebra R (CK ⊗ CK)
-- → Semiring (CK ⊗ CK) → …` nests pending subgoals past the default limit
-- (verified still required with the full granular instance set on the wrapper).
set_option maxSynthPendingDepth 2

/-!
# GL/CK duality and coassociativity of the pruning coproduct

The Grossman-Larson product and the pruning coproduct Δ^ρ are adjoint
under the symmetry-weighted pairing ([foissy-2002]; the grafting
calculus of [oudom-guin-2008]), and Δ^ρ coassociativity plus the
`Bialgebra` instance of [marcolli-chomsky-berwick-2025] Lemma 1.2.11
transport from `mul_assoc` through that duality.

## Main results

* `ConnesKreimer.pairing_gl_eq_pairing_coproduct_Rho` — the duality
  `⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`.
* `ConnesKreimer.comulRhoN_coassoc`,
  `ConnesKreimer.comulAlgHomN_coassoc_algHom` — Δ^ρ coassociativity.
* `ConnesKreimer.instBialgebraRho` — the Δ^ρ `Bialgebra` on the plain
  Connes-Kreimer carrier, and the `IsAdmissibleCuts cutSummandsN` model
  instance for the `WithCuts` carrier.

## Implementation notes

The tensor slots of the duality are **crossed**: the GL product `x ⋆ y`
grafts `y`'s trees into the host `x` (so `x` carries the root
structure), while Δ^ρ puts the pruned crown in the first tensor slot
and the root trunk in the second. Hence `y` pairs against crowns and
`x` against trunks. The uncrossed orientation
`pairing₂ (x ⊗ y) (Δ^ρ z)` is **false** (e.g. `x = {•_p}`,
`y = {•_q}`, `z` the 2-chain `p–q`: LHS `1`, RHS `0`).

The duality is proved by strong induction on the total weight of a
basis forest `z = of' C`, with the single-tree step driven by the B⁺/B⁻
adjoint of `BMinus.lean` and the Hochschild cocycle, and the multi-tree
step by the pairing product rule over `antidiagonal`-indexed splits.
-/

namespace ConnesKreimer

open scoped TensorProduct
open GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### Adjoint through the second tensor slot -/

/-- `B⁺_a` on the second tensor factor dualizes to `B⁻_a` on the second
    pairing slot: `pairing₂ (u ⊗ v) ((id ⊗ B⁺_a) V) =
    pairing₂ (u ⊗ B⁻_a v) V`. `TensorProduct.induction_on` +
    `bMinusLin_pairing_adjoint`. -/
private lemma pairing₂_lTensor_bPlusLin (a : α)
    (u v : ConnesKreimer R (Nonplanar α))
    (V : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    pairing₂ (R := R) (u ⊗ₜ[R] v)
        ((LinearMap.lTensor _ (bPlusLin (R := R) a)) V) =
      pairing₂ (R := R) (u ⊗ₜ[R] (bMinusLin (R := R) a v)) V := by
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    rw [LinearMap.lTensor_tmul, pairing₂_tmul_tmul, pairing₂_tmul_tmul,
        ← bMinusLin_pairing_adjoint]
  | add V₁ V₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-! ### Pairing against the unit -/

/-- `⟨w, 1⟩ = ε(w)`: pairing against the empty forest extracts the
    counit (the coefficient of the empty forest). -/
private lemma pairing_apply_one (w : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) w (1 : ConnesKreimer R (Nonplanar α)) =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) w := by
  refine ConnesKreimer.induction_linear w ?_ ?_ ?_
  · show pairing (R := R)
        (0 : ConnesKreimer R (Nonplanar α)) 1 =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (0 : ConnesKreimer R (Nonplanar α))
    rw [pairing_zero_left, map_zero]
  · intro a b iha ihb
    let a' : ConnesKreimer R (Nonplanar α) := a
    let b' : ConnesKreimer R (Nonplanar α) := b
    show pairing (R := R) (a' + b') 1 =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) (a' + b')
    rw [map_add, LinearMap.add_apply, map_add]
    exact congrArg₂ (· + ·) iha ihb
  · intro F r
    let w' : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
    have hsingle : w' = r • (ConnesKreimer.of' (R := R) F) := by
      show (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) =
          r • (ConnesKreimer.single F 1 : ConnesKreimer R (Nonplanar α))
      exact ConnesKreimer.smul_single_one F r
    show pairing (R := R) w' 1 =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) w'
    rw [hsingle, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
        smul_eq_mul]
    congr 1
    show pairing (R := R) (ConnesKreimer.of' F)
        (ConnesKreimer.of' (0 : Forest (Nonplanar α))) = _
    rw [pairing_of'_of', ConnesKreimer.counit_of']
    by_cases h : F = (0 : Forest (Nonplanar α))
    · subst h
      rw [if_pos rfl, if_pos Multiset.card_zero]
      show ((Nonplanar.forestAutCard (0 : Forest (Nonplanar α)) : ℕ) : R) = 1
      rw [Nonplanar.forestAutCard_zero, Nat.cast_one]
    · rw [if_neg h, if_neg (by simpa [Multiset.card_eq_zero] using h)]

/-! ### Tensor-square of the pairing product rule -/

/-- The pairing product rule through both slots of `pairing₂`: for basis
    second components, multiplying the second argument decomposes over
    independent antidiagonal splits of the two basis forests. Tensor
    counterpart of `pairing_of'_mul`, aligned with the
    index order of `pairing_product_of'_mul_of'`. -/
private lemma pairing₂_of'_of'_mul (A B : Forest (Nonplanar α))
    (U V : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    pairing₂ (R := R) (ConnesKreimer.of' B ⊗ₜ[R] ConnesKreimer.of' A) (U * V) =
      ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
        pairing₂ (R := R)
            (ConnesKreimer.of' pq.2.1 ⊗ₜ[R] ConnesKreimer.of' pq.1.1) U *
        pairing₂ (R := R)
            (ConnesKreimer.of' pq.2.2 ⊗ₜ[R] ConnesKreimer.of' pq.1.2) V)).sum := by
  induction U using TensorProduct.induction_on with
  | zero =>
    rw [zero_mul, map_zero]
    symm
    refine Multiset.sum_eq_zero fun r hr => ?_
    obtain ⟨pq, _, rfl⟩ := Multiset.mem_map.mp hr
    rw [map_zero, zero_mul]
  | add U₁ U₂ ih₁ ih₂ =>
    rw [add_mul, map_add, ih₁, ih₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ => ?_)
    rw [map_add, add_mul]
  | tmul u₁ u₂ =>
    induction V using TensorProduct.induction_on with
    | zero =>
      rw [mul_zero, map_zero]
      symm
      refine Multiset.sum_eq_zero fun r hr => ?_
      obtain ⟨pq, _, rfl⟩ := Multiset.mem_map.mp hr
      rw [map_zero, mul_zero]
    | add V₁ V₂ ih₁ ih₂ =>
      rw [mul_add, map_add, ih₁, ih₂, ← Multiset.sum_map_add]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ => ?_)
      rw [map_add, mul_add]
    | tmul v₁ v₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairing₂_tmul_tmul,
          pairing_of'_mul B u₁ v₁,
          pairing_of'_mul A u₂ v₂]
      rw [show ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
            pairing₂ (R := R)
                (ConnesKreimer.of' pq.2.1 ⊗ₜ[R] ConnesKreimer.of' pq.1.1)
                (u₁ ⊗ₜ[R] u₂) *
            pairing₂ (R := R)
                (ConnesKreimer.of' pq.2.2 ⊗ₜ[R] ConnesKreimer.of' pq.1.2)
                (v₁ ⊗ₜ[R] v₂))) =
          ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
            (pairing (R := R)
                (ConnesKreimer.of' pq.1.1) u₂ *
             pairing (R := R)
                (ConnesKreimer.of' pq.1.2) v₂) *
            (pairing (R := R)
                (ConnesKreimer.of' pq.2.1) u₁ *
             pairing (R := R)
                (ConnesKreimer.of' pq.2.2) v₁))) from
        Multiset.map_congr rfl fun pq _ => by
          rw [pairing₂_tmul_tmul, pairing₂_tmul_tmul]; ring]
      rw [sum_map_product_mul (Multiset.antidiagonal A)
          (Multiset.antidiagonal B)
          (fun pa => pairing (R := R)
              (ConnesKreimer.of' pa.1) u₂ *
            pairing (R := R) (ConnesKreimer.of' pa.2) v₂)
          (fun pb => pairing (R := R)
              (ConnesKreimer.of' pb.1) u₁ *
            pairing (R := R) (ConnesKreimer.of' pb.2) v₁)]
      ring

/-! ### The duality theorem -/

/-- The GL/CK duality for Δ^ρ ([foissy-2002]): the GL `⋆` product and
    the pruning coproduct Δ^ρ are adjoint under the symmetry-weighted
    pairing, with crossed tensor slots (see module docstring):

    `⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`

    (`y` against pruned crowns, `x` against root trunks). -/
theorem pairing_gl_eq_pairing_coproduct_Rho
    (x y z : ConnesKreimer R (Nonplanar α)) :
    pairing
        (product x y) z =
      pairing₂ (R := R)
        (y ⊗ₜ[R] x)
        (comulAlgHomN (R := R) z) := by
  -- Core statement at basis `z = of' C`, strong induction on total weight.
  suffices core : ∀ (n : ℕ) (C : Forest (Nonplanar α)),
      (C.map Nonplanar.numNodes).sum = n →
      ∀ x y : ConnesKreimer R (Nonplanar α),
      pairing (R := R)
          (product x y) (ConnesKreimer.of' C) =
        pairing₂ (R := R) (y ⊗ₜ[R] x)
          (comulAlgHomN (R := R) (ConnesKreimer.of' C)) by
    refine ConnesKreimer.induction_linear z ?_ ?_ ?_
    · show pairing (R := R) (product x y)
          (0 : ConnesKreimer R (Nonplanar α)) =
        pairing₂ (R := R) (y ⊗ₜ[R] x)
          (comulAlgHomN (R := R) (0 : ConnesKreimer R (Nonplanar α)))
      rw [map_zero, map_zero, map_zero]
    · intro a b iha ihb
      let a' : ConnesKreimer R (Nonplanar α) := a
      let b' : ConnesKreimer R (Nonplanar α) := b
      show pairing (R := R) (product x y)
          (a' + b') =
        pairing₂ (R := R) (y ⊗ₜ[R] x) (comulAlgHomN (R := R) (a' + b'))
      rw [map_add, map_add, map_add]
      exact congrArg₂ (· + ·) iha ihb
    · intro C r
      let z' : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single C r
      have hsingle : z' = r • (ConnesKreimer.of' (R := R) C) := by
        show (ConnesKreimer.single C r : ConnesKreimer R (Nonplanar α)) =
            r • (ConnesKreimer.single C 1 : ConnesKreimer R (Nonplanar α))
        exact ConnesKreimer.smul_single_one C r
      show pairing (R := R) (product x y) z' =
        pairing₂ (R := R) (y ⊗ₜ[R] x) (comulAlgHomN (R := R) z')
      rw [hsingle, map_smul, map_smul, map_smul]
      exact congrArg (r • ·) (core _ C rfl x y)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro C hC x y
    rcases Multiset.empty_or_exists_mem C with hC0 | ⟨T, hT⟩
    · -- Base: C = 0, both sides are counits.
      subst hC0
      rw [ConnesKreimer.of'_zero,
          show comulAlgHomN (R := R) (1 : ConnesKreimer R (Nonplanar α)) = 1 from
            map_one _,
          show (1 : ConnesKreimer R (Nonplanar α) ⊗[R]
              ConnesKreimer R (Nonplanar α)) =
            (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
              (1 : ConnesKreimer R (Nonplanar α)) from
            Algebra.TensorProduct.one_def,
          pairing₂_tmul_tmul, pairing_apply_one, pairing_apply_one,
          pairing_apply_one]
      rw [show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (product x y) =
          (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (unop
              ((op x : GrossmanLarson R α) *
                op y)) from rfl,
          counit_gl_mul]
      exact mul_comm _ _
    · obtain ⟨C', rfl⟩ := Multiset.exists_cons_of_mem hT
      rcases Multiset.empty_or_exists_mem C' with hC'0 | ⟨T₂, hT₂⟩
      · -- Single tree: C = {T}, T = B⁺_a W; the B⁻ recurrences match.
        subst hC'0
        -- Weight bookkeeping: (rootChildren T) is one lighter than T.
        have hwT : ((T ::ₘ (0 : Forest (Nonplanar α))).map
            Nonplanar.numNodes).sum = T.numNodes := by
          rw [Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons,
              Multiset.sum_zero]
          omega
        have hTn : T.numNodes = n := by rw [← hwT, hC]
        have hwW : T.numNodes =
            1 + ((Nonplanar.rootChildren T).map Nonplanar.numNodes).sum := by
          conv_lhs => rw [← Nonplanar.node_eta T]
          rw [Nonplanar.numNodes_node]
        have hWlt : ((Nonplanar.rootChildren T).map Nonplanar.numNodes).sum < n := by
          omega
        -- Convert `of' {T}` to `B⁺_a (of' W)`.
        have hofT : (ConnesKreimer.of' (R := R) (T ::ₘ (0 : Forest (Nonplanar α))) :
            ConnesKreimer R (Nonplanar α)) =
            bPlusLin (R := R) (Nonplanar.rootValue T)
              (ConnesKreimer.of' (Nonplanar.rootChildren T)) := by
          rw [bPlusLin_of', Nonplanar.node_eta]
          rfl
        rw [hofT]
        -- LHS: the B⁺/B⁻ recurrence.
        rw [show pairing (R := R)
              (product x y)
              (bPlusLin (R := R) (Nonplanar.rootValue T)
                (ConnesKreimer.of' (Nonplanar.rootChildren T))) =
            pairing (R := R) (unop
              ((op x : GrossmanLarson R α) * op y))
              (bPlusLin (R := R) (Nonplanar.rootValue T)
                (ConnesKreimer.of' (Nonplanar.rootChildren T))) from rfl]
        rw [pairing_apply_bPlus_gl_mul]
        -- RHS: the Hochschild cocycle + adjoint.
        rw [show comulAlgHomN (R := R)
              (bPlusLin (R := R) (Nonplanar.rootValue T)
                (ConnesKreimer.of' (Nonplanar.rootChildren T))) =
            comulTreeN (R := R)
              (Nonplanar.node (Nonplanar.rootValue T)
                (Nonplanar.rootChildren T)) from by
          rw [bPlusLin_of', comulAlgHomN_apply_ofTree]]
        rw [comulTreeN_node_cocycle, map_add, pairing₂_tmul_tmul,
            pairing₂_lTensor_bPlusLin]
        -- Term 1: adjoint identity; Term 2: induction hypothesis.
        rw [show comulForestN (R := R) (Nonplanar.rootChildren T) =
            comulAlgHomN (R := R)
              (ConnesKreimer.of' (Nonplanar.rootChildren T)) from
          (comulAlgHomN_apply_of' _).symm]
        rw [← IH _ hWlt (Nonplanar.rootChildren T) rfl
            (bMinusLin (R := R) (Nonplanar.rootValue T) x) y]
        rw [show (ConnesKreimer.ofTree (R := R)
              (Nonplanar.node (Nonplanar.rootValue T)
                (Nonplanar.rootChildren T)) :
              ConnesKreimer R (Nonplanar α)) =
            bPlusLin (R := R) (Nonplanar.rootValue T)
              (ConnesKreimer.of' (Nonplanar.rootChildren T)) from
          (bPlusLin_of' _ _).symm]
        rw [← bMinusLin_pairing_adjoint, pairing_apply_one]
        rw [show pairing (R := R)
              (product
                (bMinusLin (R := R) (Nonplanar.rootValue T) x) y)
              (ConnesKreimer.of' (Nonplanar.rootChildren T)) =
            pairing (R := R) (unop
              ((op (bMinusLin (R := R)
                  (Nonplanar.rootValue T) x) : GrossmanLarson R α) *
                op y))
              (ConnesKreimer.of' (Nonplanar.rootChildren T)) from rfl]
        ring
      · -- Multi-tree: C = T ::ₘ C' with C' ≠ 0; split and use both
        -- product rules + the induction hypothesis at both factors.
        -- Weight bookkeeping.
        have hsum : T.numNodes + (C'.map Nonplanar.numNodes).sum = n := by
          rw [← hC, Multiset.map_cons, Multiset.sum_cons]
        have hT2pos : 0 < Nonplanar.numNodes T₂ := Nonplanar.numNodes_pos T₂
        have hC'ge : Nonplanar.numNodes T₂ ≤ (C'.map Nonplanar.numNodes).sum :=
          Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _
            (Multiset.mem_map_of_mem _ hT₂)
        have hTpos : 0 < T.numNodes := Nonplanar.numNodes_pos T
        have hTlt : ((({T} : Forest (Nonplanar α))).map Nonplanar.numNodes).sum < n := by
          rw [Multiset.map_singleton, Multiset.sum_singleton]
          omega
        have hC'lt : (C'.map Nonplanar.numNodes).sum < n := by omega
        -- Reduce x, y to basis vectors (both sides are bilinear in (x, y)).
        refine ConnesKreimer.induction_linear x ?_ ?_ ?_
        · show pairing (R := R)
              (product (0 : ConnesKreimer R (Nonplanar α)) y)
              (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
              (y ⊗ₜ[R] (0 : ConnesKreimer R (Nonplanar α)))
              (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
          simp only [TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]
        · intro a b iha ihb
          let a' : ConnesKreimer R (Nonplanar α) := a
          let b' : ConnesKreimer R (Nonplanar α) := b
          show pairing (R := R)
              (product (a' + b') y)
              (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
              (y ⊗ₜ[R] (a' + b'))
              (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
          simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) iha ihb
        · intro A rA
          let xA : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single A rA
          have hxA : xA = rA • (ConnesKreimer.of' (R := R) A) := by
            show (ConnesKreimer.single A rA : ConnesKreimer R (Nonplanar α)) =
                rA • (ConnesKreimer.single A 1 : ConnesKreimer R (Nonplanar α))
            exact ConnesKreimer.smul_single_one A rA
          show pairing (R := R)
              (product xA y)
              (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
              (y ⊗ₜ[R] xA)
              (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
          rw [hxA]
          simp only [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply]
          refine congrArg (rA • ·) ?_
          refine ConnesKreimer.induction_linear y ?_ ?_ ?_
          · show pairing (R := R)
                (product (ConnesKreimer.of' A)
                  (0 : ConnesKreimer R (Nonplanar α)))
                (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
                ((0 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ConnesKreimer.of' A)
                (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
            simp only [TensorProduct.zero_tmul, map_zero, LinearMap.zero_apply]
          · intro a b iha ihb
            let a' : ConnesKreimer R (Nonplanar α) := a
            let b' : ConnesKreimer R (Nonplanar α) := b
            show pairing (R := R)
                (product (ConnesKreimer.of' A) (a' + b'))
                (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
                ((a' + b') ⊗ₜ[R] ConnesKreimer.of' A)
                (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
            simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply]
            exact congrArg₂ (· + ·) iha ihb
          · intro B rB
            let yB : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single B rB
            have hyB : yB = rB • (ConnesKreimer.of' (R := R) B) := by
              show (ConnesKreimer.single B rB : ConnesKreimer R (Nonplanar α)) =
                  rB • (ConnesKreimer.single B 1 : ConnesKreimer R (Nonplanar α))
              exact ConnesKreimer.smul_single_one B rB
            show pairing (R := R)
                (product (ConnesKreimer.of' A) yB)
                (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
                (yB ⊗ₜ[R] ConnesKreimer.of' A)
                (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
            rw [hyB]
            simp only [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply]
            refine congrArg (rB • ·) ?_
            -- Basis case: split off the head tree and use both product rules.
            have hsplit : (ConnesKreimer.of' (R := R) (T ::ₘ C') :
                ConnesKreimer R (Nonplanar α)) =
                ConnesKreimer.of' ({T} : Forest (Nonplanar α)) *
                  ConnesKreimer.of' C' := by
              rw [← ConnesKreimer.of'_add, Multiset.singleton_add]
            rw [hsplit, pairing_product_of'_mul_of',
                map_mul, pairing₂_of'_of'_mul]
            refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ => ?_)
            rw [IH _ hTlt ({T} : Forest (Nonplanar α)) rfl
                  (ConnesKreimer.of' pq.1.1) (ConnesKreimer.of' pq.2.1),
                IH _ hC'lt C' rfl
                  (ConnesKreimer.of' pq.1.2) (ConnesKreimer.of' pq.2.2)]

/-! ### Coassoc LinearMaps + chain lemmas via the duality -/

/-- The LHS LinearMap of Δ^ρ coassoc:
    `assoc ∘ (Δ^ρ ⊗ id) ∘ Δ^ρ : CK →ₗ CK ⊗ (CK ⊗ CK)`. -/
private noncomputable def coassocLHSLinRho :
    ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R]
        (ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α)) :=
  (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
    (comulAlgHomN (R := R)).toLinearMap.rTensor _ ∘ₗ
    (comulAlgHomN (R := R)).toLinearMap

/-- The RHS LinearMap of Δ^ρ coassoc:
    `(id ⊗ Δ^ρ) ∘ Δ^ρ : CK →ₗ CK ⊗ (CK ⊗ CK)`. -/
private noncomputable def coassocRHSLinRho :
    ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R]
        (ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α)) :=
  (comulAlgHomN (R := R)).toLinearMap.lTensor _ ∘ₗ
    (comulAlgHomN (R := R)).toLinearMap

/-- Intermediate: `assoc + rTensor (Δ^ρ) + pairing₃` via one application
    of the duality. Note the crossed orientation: the inner coproduct
    expansion produces the GL product `y ⋆ x`. -/
private lemma pairing₃_assoc_rTensor_comul_rho
    (x y z' : ConnesKreimer R (Nonplanar α))
    (V : ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((TensorProduct.assoc R _ _ _)
          ((comulAlgHomN (R := R)).toLinearMap.rTensor _ V)) =
      pairing₂ (R := R) (product y x ⊗ₜ[R] z') V := by
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, pairing₃_assoc_tmul,
        ← pairing_gl_eq_pairing_coproduct_Rho y x a, pairing₂_tmul_tmul]
  | add V₁ V₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, ih₁, ih₂, map_add]

/-- Intermediate: `lTensor (Δ^ρ) + pairing₃` via one application of the
    duality (crossed orientation: produces `z' ⋆ y`). -/
private lemma pairing₃_lTensor_comul_rho
    (x y z' : ConnesKreimer R (Nonplanar α))
    (W : ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((comulAlgHomN (R := R)).toLinearMap.lTensor _ W) =
      pairing₂ (R := R) (x ⊗ₜ[R] product z' y) W := by
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, pairing₃_tmul_apply,
        ← pairing_gl_eq_pairing_coproduct_Rho z' y b, pairing₂_tmul_tmul]
  | add W₁ W₂ ih₁ ih₂ =>
    rw [map_add, map_add, ih₁, ih₂, map_add]

/-- LHS chain: pairing the LHS coassoc
    expression against a pure triple tensor reduces to pairing the
    GL product `z' ⋆ (y ⋆ x)` against `z`. -/
theorem pairing₃_coassocLHSLinRho
    (x y z' z : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z')) (coassocLHSLinRho (R := R) z) =
      pairing
        (product z' (product y x)) z := by
  show pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((TensorProduct.assoc R _ _ _)
          ((comulAlgHomN (R := R)).toLinearMap.rTensor _
            ((comulAlgHomN (R := R)).toLinearMap z))) = _
  rw [AlgHom.toLinearMap_apply, pairing₃_assoc_rTensor_comul_rho]
  exact (pairing_gl_eq_pairing_coproduct_Rho z'
          (product y x) z).symm

/-- RHS chain: pairing the RHS coassoc
    expression against a pure triple tensor reduces to pairing the
    GL product `(z' ⋆ y) ⋆ x` against `z`. -/
theorem pairing₃_coassocRHSLinRho
    (x y z' z : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z')) (coassocRHSLinRho (R := R) z) =
      pairing
        (product (product z' y) x) z := by
  show pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((comulAlgHomN (R := R)).toLinearMap.lTensor _
          ((comulAlgHomN (R := R)).toLinearMap z)) = _
  rw [AlgHom.toLinearMap_apply, pairing₃_lTensor_comul_rho]
  exact (pairing_gl_eq_pairing_coproduct_Rho
          (product z' y) x z).symm

/-! ### Coassociativity of Δ^ρ via GL/CK duality (LinearMap form)

Specialized to `[CommRing R]` (rather than `[CommSemiring R]`) since the
proof uses subtraction (via `sub_eq_zero` in `pairing₃_unique`), which
requires `R` to be a Ring (so `CK R T` has `AddCommGroup`). -/

section CoassocCommRingRho
variable {R' : Type*} [CommRing R'] {α' : Type*} [DecidableEq α']

/-- Coassociativity of Δ^ρ (LinearMap form): transported from
    `GrossmanLarson.mul_assoc` through the duality and the nondegeneracy
    of `pairing₃`. -/
theorem comulRhoN_coassoc [CharZero R'] [NoZeroDivisors R'] :
    (TensorProduct.assoc R'
        (ConnesKreimer R' (Nonplanar α'))
        (ConnesKreimer R' (Nonplanar α'))
        (ConnesKreimer R' (Nonplanar α'))).toLinearMap ∘ₗ
      (comulAlgHomN (R := R')).toLinearMap.rTensor _ ∘ₗ
      (comulAlgHomN (R := R')).toLinearMap =
    (comulAlgHomN (R := R')).toLinearMap.lTensor _ ∘ₗ
      (comulAlgHomN (R := R')).toLinearMap := by
  ext z
  apply pairing₃_unique
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x rest =>
    induction rest using TensorProduct.induction_on with
    | zero => simp
    | tmul y z' =>
      show pairing₃ (x ⊗ₜ[R'] (y ⊗ₜ[R'] z')) (coassocLHSLinRho z) =
           pairing₃ (x ⊗ₜ[R'] (y ⊗ₜ[R'] z')) (coassocRHSLinRho z)
      rw [pairing₃_coassocLHSLinRho, pairing₃_coassocRHSLinRho,
          ← mul_def, ← mul_def,
          ← mul_def, ← mul_def,
          GrossmanLarson.mul_assoc]
    | add a b iha ihb =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply,
                 iha, ihb]
  | add a b iha ihb =>
    simp only [map_add, LinearMap.add_apply, iha, ihb]

/-- The AlgHom form of Δ^ρ coassociativity. -/
theorem comulAlgHomN_coassoc_algHom [CharZero R'] [NoZeroDivisors R'] :
    (Algebra.TensorProduct.assoc R' R' R'
        (ConnesKreimer R' (Nonplanar α'))
        (ConnesKreimer R' (Nonplanar α'))
        (ConnesKreimer R' (Nonplanar α'))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHomN (R := R') (α := α'))
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar α')))).comp comulAlgHomN) =
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar α')))
      (comulAlgHomN (R := R') (α := α'))).comp comulAlgHomN := by
  apply AlgHom.toLinearMap_injective
  exact comulRhoN_coassoc

end CoassocCommRingRho

/-! ### `Bialgebra` instance

Built via `Bialgebra.ofAlgHom` from `comulAlgHomN_coassoc_algHom` (GL/CK
duality) and the two counit AlgHom laws. The duality-based coassoc proof
forces `[CommRing R] [CharZero R] [NoZeroDivisors R]`; the counit laws
hold over `[CommSemiring R]` and are automatically satisfied. -/

noncomputable instance instBialgebraRho
    {R' : Type*} [CommRing R'] [CharZero R'] [NoZeroDivisors R'] {α' : Type*}
    [DecidableEq α'] :
    Bialgebra R' (ConnesKreimer R' (Nonplanar α')) :=
  Bialgebra.ofAlgHom comulAlgHomN counit
    comulAlgHomN_coassoc_algHom
    counit_rTensor_comulAlgHomN
    counit_lTensor_comulAlgHomN

/-- Δ^ρ is the generic coproduct at `cuts := cutSummandsN` — definitional. -/
theorem comulAlgHomN_eq_G {R : Type*} [CommSemiring R] {α : Type*} :
    comulAlgHomN (R := R) (α := α) = comulAlgHomNG (R := R) cutSummandsN := rfl

/-- Δ^ρ is admissible: the GL/CK-duality coassociativity and the counit laws,
transported through the `rfl` bridge `comulAlgHomN_eq_G`. -/
instance {α : Type*} [DecidableEq α] : IsAdmissibleCuts (cutSummandsN (α := α)) where
  coassoc := by
    intro R _ _ _
    rw [← comulAlgHomN_eq_G]
    exact comulAlgHomN_coassoc_algHom
  counit_rTensor := by
    intro R _
    rw [← comulAlgHomN_eq_G]
    exact counit_rTensor_comulAlgHomN
  counit_lTensor := by
    intro R _
    rw [← comulAlgHomN_eq_G]
    exact counit_lTensor_comulAlgHomN

variable {R' : Type*} [CommRing R'] [CharZero R'] [NoZeroDivisors R'] {α' : Type*}
  [DecidableEq α']

/-- The coproduct of `instBialgebraRho` is `comulAlgHomN`. -/
theorem coalgebra_comul_apply (x : ConnesKreimer R' (Nonplanar α')) :
    Coalgebra.comul (R := R') x = comulAlgHomN x := rfl

/-- The counit of `instBialgebraRho` is `ConnesKreimer.counit`. -/
theorem coalgebraCounit_apply (x : ConnesKreimer R' (Nonplanar α')) :
    CoalgebraStruct.counit (R := R') x = counit x := rfl

end ConnesKreimer

