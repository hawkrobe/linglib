import Linglib.Core.Algebra.RootedTree.BMinus
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonSplit
import Linglib.Core.Algebra.RootedTree.PreLie.OudomGuinBridgePairing

set_option autoImplicit false
-- Nested tensor squares `CK ⊗ (CK ⊗ CK)` need one extra pending step during
-- instance synthesis: the chain `Semiring (CK ⊗ (CK ⊗ CK)) → Algebra R (CK ⊗ CK)
-- → Semiring (CK ⊗ CK) → …` nests pending subgoals past the default limit
-- (verified still required with the full granular instance set on the wrapper).
set_option maxSynthPendingDepth 2

/-!
# GL/CK duality for Δ^ρ and coassociativity of the pruning coproduct
[foissy-2002] [oudom-guin-2008] [marcolli-chomsky-berwick-2025]

The duality theorem `pairing_gl_eq_pairing_coproduct_Rho`:

  `⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`

pairing the Grossman-Larson product against the pruning coproduct
through the symmetry-weighted pairing, and its consequence: Δ^ρ
coassociativity (`comulRhoN_coassoc`) and the
`Bialgebra R (ConnesKreimer R (Nonplanar α))` instance
(`instBialgebraRho`), both transported from `GrossmanLarson.mul_assoc`.

## Orientation

The tensor slots are **crossed**: linglib's GL product `x ⋆ y` grafts
`y`'s trees into the host `x` (so `x` carries the root structure, cf.
`bMinusLin_gl_mul` placing `B⁻` on `x`), while `Δ^ρ` puts the pruned
crown in the first tensor slot and the root trunk in the second
(`comulTreeN`). Hence `y` pairs against crowns and `x` against trunks.
An earlier sorry-fenced statement of this theorem used the uncrossed
orientation `pairing₂ (x ⊗ y) (Δ^ρ z)`, which is **false** (e.g.
`x = {•_p}`, `y = {•_q}`, `z` the 2-chain `p–q`: LHS `1`, RHS `0`).
Both orientations were checked against the exhaustive planar simulation
battery in `scratch/validate_duality.lean` (V1): the crossed form holds
on all weight-matched triples of forests of weight ≤ 3 and on targeted
weight-4 duplicate-tree traps; the uncrossed form fails on 72 of them.

This file lives downstream of `BMinus.lean` (whose `B⁻` calculus drives
the single-tree induction step), so the duality theorem and its
consumers were moved here from `Coproduct/PruningNonplanar.lean`.

## Proof architecture (weight induction on `z`)

Reduce to basis forests `z = of' C` by linearity; strong induction on
total weight of `C`:

* `C = 0`: both sides are counits — `counit_gl_mul`.
* `C = {T}`, `T = B⁺_a W`: `⟨x ⋆ y, B⁺_a W⟩` unfolds via
  `pairing_apply_bPlus_gl_mul` (B⁺/B⁻ adjoint + the OG cocycle
  `bMinusLin_gl_mul`); `pairing₂ (y ⊗ x) (Δ^ρ B⁺_a W)` unfolds via the
  Hochschild cocycle `comulTreeN_node_cocycle` + the adjoint moved
  through the second tensor slot. The two recurrences match
  summand-wise; the `T ⊗ 1` term is the adjoint identity itself.
* `C = T ::ₘ C'` (`C' ≠ 0`): split `of' C = ofTree T * of' C'`; apply
  `pairing_product_of'_mul_of'` (LHS) and the tensor-square of
  `pairing_of'_mul` (RHS, via `Δ^ρ` multiplicativity); the two
  `antidiagonal`-indexed sums match termwise under the induction
  hypothesis at `ofTree T` and `of' C'`.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

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
      pairing₂ (R := R) (u ⊗ₜ[R] (GrossmanLarson.bMinusLin (R := R) a v)) V := by
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    rw [LinearMap.lTensor_tmul, pairing₂_tmul_tmul, pairing₂_tmul_tmul,
        ← GrossmanLarson.bMinusLin_pairing_adjoint]
  | add V₁ V₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-! ### Pairing against the unit -/

/-- `⟨w, 1⟩ = ε(w)`: pairing against the empty forest extracts the
    counit (the coefficient of the empty forest). -/
private lemma pairing_apply_one (w : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing (R := R) w (1 : ConnesKreimer R (Nonplanar α)) =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) w := by
  refine ConnesKreimer.induction_linear w ?_ ?_ ?_
  · show GrossmanLarson.pairing (R := R)
        (0 : ConnesKreimer R (Nonplanar α)) 1 =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (0 : ConnesKreimer R (Nonplanar α))
    rw [GrossmanLarson.pairing_zero_left, map_zero]
  · intro a b iha ihb
    let a' : ConnesKreimer R (Nonplanar α) := a
    let b' : ConnesKreimer R (Nonplanar α) := b
    show GrossmanLarson.pairing (R := R) (a' + b') 1 =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) (a' + b')
    rw [map_add, LinearMap.add_apply, map_add]
    exact congrArg₂ (· + ·) iha ihb
  · intro F r
    let w' : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
    have hsingle : w' = r • (ConnesKreimer.of' (R := R) F) := by
      show (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) =
          r • (ConnesKreimer.single F 1 : ConnesKreimer R (Nonplanar α))
      exact ConnesKreimer.smul_single_one F r
    show GrossmanLarson.pairing (R := R) w' 1 =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) w'
    rw [hsingle, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
        smul_eq_mul]
    congr 1
    show GrossmanLarson.pairing (R := R) (ConnesKreimer.of' F)
        (ConnesKreimer.of' (0 : Forest (Nonplanar α))) = _
    rw [GrossmanLarson.pairing_of'_of', ConnesKreimer.counit_of']
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
    counterpart of `GrossmanLarson.pairing_of'_mul`, aligned with the
    index order of `GrossmanLarson.pairing_product_of'_mul_of'`. -/
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
          GrossmanLarson.pairing_of'_mul B u₁ v₁,
          GrossmanLarson.pairing_of'_mul A u₂ v₂]
      rw [show ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
            pairing₂ (R := R)
                (ConnesKreimer.of' pq.2.1 ⊗ₜ[R] ConnesKreimer.of' pq.1.1)
                (u₁ ⊗ₜ[R] u₂) *
            pairing₂ (R := R)
                (ConnesKreimer.of' pq.2.2 ⊗ₜ[R] ConnesKreimer.of' pq.1.2)
                (v₁ ⊗ₜ[R] v₂))) =
          ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
            (GrossmanLarson.pairing (R := R)
                (ConnesKreimer.of' pq.1.1) u₂ *
             GrossmanLarson.pairing (R := R)
                (ConnesKreimer.of' pq.1.2) v₂) *
            (GrossmanLarson.pairing (R := R)
                (ConnesKreimer.of' pq.2.1) u₁ *
             GrossmanLarson.pairing (R := R)
                (ConnesKreimer.of' pq.2.2) v₁))) from
        Multiset.map_congr rfl fun pq _ => by
          rw [pairing₂_tmul_tmul, pairing₂_tmul_tmul]; ring]
      rw [GrossmanLarson.sum_map_product_mul (Multiset.antidiagonal A)
          (Multiset.antidiagonal B)
          (fun pa => GrossmanLarson.pairing (R := R)
              (ConnesKreimer.of' pa.1) u₂ *
            GrossmanLarson.pairing (R := R) (ConnesKreimer.of' pa.2) v₂)
          (fun pb => GrossmanLarson.pairing (R := R)
              (ConnesKreimer.of' pb.1) u₁ *
            GrossmanLarson.pairing (R := R) (ConnesKreimer.of' pb.2) v₁)]
      ring

/-! ### CK-typed linearity of the GL product in its first slot

`GrossmanLarson.product` is a `LinearMap` at the `GrossmanLarson` carrier;
these restate first-slot linearity with all terms ascribed at
`ConnesKreimer` (definitionally equal carriers, syntactically different
instances), so they can be used as rewrite rules in CK-typed goals. -/

private lemma pairing_product_zero_left (y w : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing (R := R)
      (GrossmanLarson.product (0 : ConnesKreimer R (Nonplanar α)) y) w = 0 := by
  have h1 : (GrossmanLarson.product (R := R) (α := α)
      (0 : ConnesKreimer R (Nonplanar α)) y :
      ConnesKreimer R (Nonplanar α)) = 0 :=
    LinearMap.map_zero₂ (GrossmanLarson.product (R := R) (α := α)) y
  exact (congrArg (fun u => GrossmanLarson.pairing (R := R) u w) h1).trans
    (GrossmanLarson.pairing_zero_left w)

private lemma pairing_product_add_left (a b y w : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing (R := R) (GrossmanLarson.product (a + b) y) w =
      GrossmanLarson.pairing (R := R) (GrossmanLarson.product a y) w +
      GrossmanLarson.pairing (R := R) (GrossmanLarson.product b y) w := by
  have h1 : (GrossmanLarson.product (R := R) (α := α) (a + b) y :
      ConnesKreimer R (Nonplanar α)) =
      ((GrossmanLarson.product a y : ConnesKreimer R (Nonplanar α)) +
       (GrossmanLarson.product b y : ConnesKreimer R (Nonplanar α)) :
        ConnesKreimer R (Nonplanar α)) :=
    LinearMap.map_add₂ (GrossmanLarson.product (R := R) (α := α)) a b y
  exact (congrArg (fun u => GrossmanLarson.pairing (R := R) u w) h1).trans
    (LinearMap.congr_fun
      (map_add (GrossmanLarson.pairing (R := R) (α := α)) _ _) w)

private lemma pairing_product_smul_left (r : R)
    (a y w : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing (R := R) (GrossmanLarson.product (r • a) y) w =
      r • GrossmanLarson.pairing (R := R) (GrossmanLarson.product a y) w := by
  have h1 : (GrossmanLarson.product (R := R) (α := α) (r • a) y :
      ConnesKreimer R (Nonplanar α)) =
      (r • (GrossmanLarson.product a y : ConnesKreimer R (Nonplanar α)) :
        ConnesKreimer R (Nonplanar α)) :=
    LinearMap.map_smul₂ (GrossmanLarson.product (R := R) (α := α)) r a y
  exact (congrArg (fun u => GrossmanLarson.pairing (R := R) u w) h1).trans
    (LinearMap.congr_fun
      (map_smul (GrossmanLarson.pairing (R := R) (α := α)) r _) w)

private lemma pairing_product_zero_right (x w : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing (R := R)
      (GrossmanLarson.product x (0 : ConnesKreimer R (Nonplanar α))) w = 0 := by
  have h1 : (GrossmanLarson.product (R := R) (α := α) x
      (0 : ConnesKreimer R (Nonplanar α)) :
      ConnesKreimer R (Nonplanar α)) = 0 :=
    map_zero (GrossmanLarson.product (R := R) (α := α) x)
  exact (congrArg (fun u => GrossmanLarson.pairing (R := R) u w) h1).trans
    (GrossmanLarson.pairing_zero_left w)

private lemma pairing_product_add_right (x a b w : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing (R := R) (GrossmanLarson.product x (a + b)) w =
      GrossmanLarson.pairing (R := R) (GrossmanLarson.product x a) w +
      GrossmanLarson.pairing (R := R) (GrossmanLarson.product x b) w := by
  have h1 : (GrossmanLarson.product (R := R) (α := α) x (a + b) :
      ConnesKreimer R (Nonplanar α)) =
      ((GrossmanLarson.product x a : ConnesKreimer R (Nonplanar α)) +
       (GrossmanLarson.product x b : ConnesKreimer R (Nonplanar α)) :
        ConnesKreimer R (Nonplanar α)) :=
    map_add (GrossmanLarson.product (R := R) (α := α) x) a b
  exact (congrArg (fun u => GrossmanLarson.pairing (R := R) u w) h1).trans
    (LinearMap.congr_fun
      (map_add (GrossmanLarson.pairing (R := R) (α := α)) _ _) w)

private lemma pairing_product_smul_right (r : R)
    (x a w : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing (R := R) (GrossmanLarson.product x (r • a)) w =
      r • GrossmanLarson.pairing (R := R) (GrossmanLarson.product x a) w := by
  have h1 : (GrossmanLarson.product (R := R) (α := α) x (r • a) :
      ConnesKreimer R (Nonplanar α)) =
      (r • (GrossmanLarson.product x a : ConnesKreimer R (Nonplanar α)) :
        ConnesKreimer R (Nonplanar α)) :=
    map_smul (GrossmanLarson.product (R := R) (α := α) x) r a
  exact (congrArg (fun u => GrossmanLarson.pairing (R := R) u w) h1).trans
    (LinearMap.congr_fun
      (map_smul (GrossmanLarson.pairing (R := R) (α := α)) r _) w)

/-! ### The duality theorem -/

/-- **GL/CK duality for Δ^ρ** ([foissy-2002]): the GL `⋆` product and
    the pruning coproduct Δ^ρ are adjoint under the symmetry-weighted
    pairing, with crossed tensor slots (see module docstring):

    `⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`

    (`y` against pruned crowns, `x` against root trunks). -/
theorem pairing_gl_eq_pairing_coproduct_Rho
    (x y z : ConnesKreimer R (Nonplanar α)) :
    GrossmanLarson.pairing
        (GrossmanLarson.product x y) z =
      pairing₂ (R := R)
        (y ⊗ₜ[R] x)
        (comulAlgHomN (R := R) z) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Core statement at basis `z = of' C`, strong induction on total weight.
  suffices core : ∀ (n : ℕ) (C : Forest (Nonplanar α)),
      (C.map Nonplanar.numNodes).sum = n →
      ∀ x y : ConnesKreimer R (Nonplanar α),
      GrossmanLarson.pairing (R := R)
          (GrossmanLarson.product x y) (ConnesKreimer.of' C) =
        pairing₂ (R := R) (y ⊗ₜ[R] x)
          (comulAlgHomN (R := R) (ConnesKreimer.of' C)) by
    refine ConnesKreimer.induction_linear z ?_ ?_ ?_
    · show GrossmanLarson.pairing (R := R) (GrossmanLarson.product x y)
          (0 : ConnesKreimer R (Nonplanar α)) =
        pairing₂ (R := R) (y ⊗ₜ[R] x)
          (comulAlgHomN (R := R) (0 : ConnesKreimer R (Nonplanar α)))
      rw [map_zero, map_zero, map_zero]
    · intro a b iha ihb
      let a' : ConnesKreimer R (Nonplanar α) := a
      let b' : ConnesKreimer R (Nonplanar α) := b
      show GrossmanLarson.pairing (R := R) (GrossmanLarson.product x y)
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
      show GrossmanLarson.pairing (R := R) (GrossmanLarson.product x y) z' =
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
            (GrossmanLarson.product x y) =
          (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (GrossmanLarson.unop
              ((GrossmanLarson.op x : GrossmanLarson R α) *
                GrossmanLarson.op y)) from rfl,
          GrossmanLarson.counit_gl_mul]
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
        rw [show GrossmanLarson.pairing (R := R)
              (GrossmanLarson.product x y)
              (bPlusLin (R := R) (Nonplanar.rootValue T)
                (ConnesKreimer.of' (Nonplanar.rootChildren T))) =
            GrossmanLarson.pairing (R := R) (GrossmanLarson.unop
              ((GrossmanLarson.op x : GrossmanLarson R α) * GrossmanLarson.op y))
              (bPlusLin (R := R) (Nonplanar.rootValue T)
                (ConnesKreimer.of' (Nonplanar.rootChildren T))) from rfl]
        rw [GrossmanLarson.pairing_apply_bPlus_gl_mul]
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
            (GrossmanLarson.bMinusLin (R := R) (Nonplanar.rootValue T) x) y]
        rw [show (ConnesKreimer.ofTree (R := R)
              (Nonplanar.node (Nonplanar.rootValue T)
                (Nonplanar.rootChildren T)) :
              ConnesKreimer R (Nonplanar α)) =
            bPlusLin (R := R) (Nonplanar.rootValue T)
              (ConnesKreimer.of' (Nonplanar.rootChildren T)) from
          (bPlusLin_of' _ _).symm]
        rw [← GrossmanLarson.bMinusLin_pairing_adjoint, pairing_apply_one]
        rw [show GrossmanLarson.pairing (R := R)
              (GrossmanLarson.product
                (GrossmanLarson.bMinusLin (R := R) (Nonplanar.rootValue T) x) y)
              (ConnesKreimer.of' (Nonplanar.rootChildren T)) =
            GrossmanLarson.pairing (R := R) (GrossmanLarson.unop
              ((GrossmanLarson.op (GrossmanLarson.bMinusLin (R := R)
                  (Nonplanar.rootValue T) x) : GrossmanLarson R α) *
                GrossmanLarson.op y))
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
        · show GrossmanLarson.pairing (R := R)
              (GrossmanLarson.product (0 : ConnesKreimer R (Nonplanar α)) y)
              (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
              (y ⊗ₜ[R] (0 : ConnesKreimer R (Nonplanar α)))
              (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
          simp only [pairing_product_zero_left, TensorProduct.tmul_zero,
              map_zero, LinearMap.zero_apply]
        · intro a b iha ihb
          let a' : ConnesKreimer R (Nonplanar α) := a
          let b' : ConnesKreimer R (Nonplanar α) := b
          show GrossmanLarson.pairing (R := R)
              (GrossmanLarson.product (a' + b') y)
              (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
              (y ⊗ₜ[R] (a' + b'))
              (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
          simp only [pairing_product_add_left, TensorProduct.tmul_add,
              map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) iha ihb
        · intro A rA
          let xA : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single A rA
          have hxA : xA = rA • (ConnesKreimer.of' (R := R) A) := by
            show (ConnesKreimer.single A rA : ConnesKreimer R (Nonplanar α)) =
                rA • (ConnesKreimer.single A 1 : ConnesKreimer R (Nonplanar α))
            exact ConnesKreimer.smul_single_one A rA
          show GrossmanLarson.pairing (R := R)
              (GrossmanLarson.product xA y)
              (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
              (y ⊗ₜ[R] xA)
              (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
          rw [hxA]
          simp only [pairing_product_smul_left, TensorProduct.tmul_smul,
              map_smul, LinearMap.smul_apply]
          refine congrArg (rA • ·) ?_
          refine ConnesKreimer.induction_linear y ?_ ?_ ?_
          · show GrossmanLarson.pairing (R := R)
                (GrossmanLarson.product (ConnesKreimer.of' A)
                  (0 : ConnesKreimer R (Nonplanar α)))
                (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
                ((0 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ConnesKreimer.of' A)
                (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
            simp only [pairing_product_zero_right, TensorProduct.zero_tmul,
                map_zero, LinearMap.zero_apply]
          · intro a b iha ihb
            let a' : ConnesKreimer R (Nonplanar α) := a
            let b' : ConnesKreimer R (Nonplanar α) := b
            show GrossmanLarson.pairing (R := R)
                (GrossmanLarson.product (ConnesKreimer.of' A) (a' + b'))
                (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
                ((a' + b') ⊗ₜ[R] ConnesKreimer.of' A)
                (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
            simp only [pairing_product_add_right, TensorProduct.add_tmul,
                map_add, LinearMap.add_apply]
            exact congrArg₂ (· + ·) iha ihb
          · intro B rB
            let yB : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single B rB
            have hyB : yB = rB • (ConnesKreimer.of' (R := R) B) := by
              show (ConnesKreimer.single B rB : ConnesKreimer R (Nonplanar α)) =
                  rB • (ConnesKreimer.single B 1 : ConnesKreimer R (Nonplanar α))
              exact ConnesKreimer.smul_single_one B rB
            show GrossmanLarson.pairing (R := R)
                (GrossmanLarson.product (ConnesKreimer.of' A) yB)
                (ConnesKreimer.of' (T ::ₘ C')) = pairing₂ (R := R)
                (yB ⊗ₜ[R] ConnesKreimer.of' A)
                (comulAlgHomN (R := R) (ConnesKreimer.of' (T ::ₘ C')))
            rw [hyB]
            simp only [pairing_product_smul_right, ← TensorProduct.smul_tmul',
                map_smul, LinearMap.smul_apply]
            refine congrArg (rB • ·) ?_
            -- Basis case: split off the head tree and use both product rules.
            have hsplit : (ConnesKreimer.of' (R := R) (T ::ₘ C') :
                ConnesKreimer R (Nonplanar α)) =
                ConnesKreimer.of' ({T} : Forest (Nonplanar α)) *
                  ConnesKreimer.of' C' := by
              rw [← ConnesKreimer.of'_add, Multiset.singleton_add]
            rw [hsplit, GrossmanLarson.pairing_product_of'_mul_of',
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
      pairing₂ (R := R) (GrossmanLarson.product y x ⊗ₜ[R] z') V := by
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
      pairing₂ (R := R) (x ⊗ₜ[R] GrossmanLarson.product z' y) W := by
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, pairing₃_tmul_apply,
        ← pairing_gl_eq_pairing_coproduct_Rho z' y b, pairing₂_tmul_tmul]
  | add W₁ W₂ ih₁ ih₂ =>
    rw [map_add, map_add, ih₁, ih₂, map_add]

/-- **LHS chain via the duality (twice)**: pairing the LHS coassoc
    expression against a pure triple tensor reduces to pairing the
    GL product `z' ⋆ (y ⋆ x)` against `z`. -/
theorem pairing₃_coassocLHSLinRho
    (x y z' z : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z')) (coassocLHSLinRho (R := R) z) =
      GrossmanLarson.pairing
        (GrossmanLarson.product z' (GrossmanLarson.product y x)) z := by
  show pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((TensorProduct.assoc R _ _ _)
          ((comulAlgHomN (R := R)).toLinearMap.rTensor _
            ((comulAlgHomN (R := R)).toLinearMap z))) = _
  rw [AlgHom.toLinearMap_apply, pairing₃_assoc_rTensor_comul_rho]
  exact (pairing_gl_eq_pairing_coproduct_Rho z'
          (GrossmanLarson.product y x) z).symm

/-- **RHS chain via the duality (twice)**: pairing the RHS coassoc
    expression against a pure triple tensor reduces to pairing the
    GL product `(z' ⋆ y) ⋆ x` against `z`. -/
theorem pairing₃_coassocRHSLinRho
    (x y z' z : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z')) (coassocRHSLinRho (R := R) z) =
      GrossmanLarson.pairing
        (GrossmanLarson.product (GrossmanLarson.product z' y) x) z := by
  show pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((comulAlgHomN (R := R)).toLinearMap.lTensor _
          ((comulAlgHomN (R := R)).toLinearMap z)) = _
  rw [AlgHom.toLinearMap_apply, pairing₃_lTensor_comul_rho]
  exact (pairing_gl_eq_pairing_coproduct_Rho
          (GrossmanLarson.product z' y) x z).symm

/-! ### Coassociativity of Δ^ρ via GL/CK duality (LinearMap form)

Specialized to `[CommRing R]` (rather than `[CommSemiring R]`) since the
proof uses subtraction (via `sub_eq_zero` in `pairing₃_unique`), which
requires `R` to be a Ring (so `CK R T` has `AddCommGroup`). -/

section CoassocCommRingRho
variable {R' : Type*} [CommRing R'] {α' : Type*}

/-- **Coassociativity of `comulAlgHomN`** (LinearMap form), via GL/CK
    duality. Parallel to `TraceNonplanar.comulCN_coassoc` for Δ^c.

    Derived via the chain:
    1. `ext z`: reduce to pointwise `LHS z = RHS z`.
    2. `pairing₃_unique`: reduce to `∀ t, pairing₃ t (LHS z) = pairing₃ t (RHS z)`.
    3. `TensorProduct.induction_on` thrice: reduce `t` to pure triple
       tensors `x ⊗ (y ⊗ z')`.
    4. `pairing₃_coassocLHSLinRho` / `pairing₃_coassocRHSLinRho`: reduce
       both sides to GL products against `z` (two duality applications
       each).
    5. `GrossmanLarson.mul_assoc z' y x` closes. -/
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
          ← GrossmanLarson.mul_def, ← GrossmanLarson.mul_def,
          ← GrossmanLarson.mul_def, ← GrossmanLarson.mul_def,
          GrossmanLarson.mul_assoc]
    | add a b iha ihb =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply,
                 iha, ihb]
  | add a b iha ihb =>
    simp only [map_add, LinearMap.add_apply, iha, ihb]

/-- **AlgHom-form coassociativity** of `comulAlgHomN`. Follows from
    `comulRhoN_coassoc` (LinearMap form) by AlgHom extensionality, the
    same one-liner pattern as `TraceNonplanar.comulCAlgHomN_coassoc_algHom`. -/
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
    {R' : Type*} [CommRing R'] [CharZero R'] [NoZeroDivisors R'] {α' : Type*} :
    Bialgebra R' (ConnesKreimer R' (Nonplanar α')) :=
  Bialgebra.ofAlgHom comulAlgHomN counit
    comulAlgHomN_coassoc_algHom
    counit_rTensor_comulAlgHomN
    counit_lTensor_comulAlgHomN

end ConnesKreimer

end RootedTree
