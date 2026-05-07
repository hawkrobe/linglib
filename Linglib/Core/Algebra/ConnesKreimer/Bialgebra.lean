import Linglib.Core.Algebra.ConnesKreimer.LhsEquiv
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Connes-Kreimer Bialgebra Instance on `Hc R α` @cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

Registers the Connes-Kreimer bialgebra structure on `Hc R α` via
`Bialgebra.ofAlgHom`. Stage 1a closed the counit laws; this commit
(Stage 1b prep) reduces `comul_coassoc` to a single-tree obligation
`comul_coassoc_tree` via `algHom_ext_tree` (algebra-hom multiplicativity).
The cuts-of-cuts bijection itself (@cite{foissy-2002} §2 for decorated
planar trees; @cite{connes-kreimer-1998} for Feynman graphs, the M-C-B
Lemma 1.2.10 reference) is closed via the `lhsGeoCutEquiv` direct
chain in `LhsEquiv.lean`.

## Status

- `comul_coassoc` — proved by reduction via `algHom_ext_tree` + `comul_coassoc_tree`.
- `comul_coassoc_tree` — proved via `lhs_eq_sum_DoubleCut + rhs_eq_sum_DoubleCut`
  (the LHS in `LhsEquiv.lean`, the RHS in `DoubleCut.lean`).
- `counit_rTensor` — proved (Stage 1a).
- `counit_lTensor` — proved (Stage 1a).

Stage 1 obligation chain is sorry-free as of 0.230.728. `instBialgebraHc`
is registered as an `instance` (promoted from `def` at 0.230.729).

## Why this works typeclass-wise

`Hc R α` is `def`-defined (not `abbrev`) in `Defs.lean`, giving us a
distinct typeclass slot from the underlying `AddMonoidAlgebra R (TraceForest α Unit)`.
mathlib's `AddMonoidAlgebra.instBialgebra` (group-like coproduct
Δ(F) = F ⊗ F) applies to the underlying type only; our
Connes-Kreimer instance applies to the wrapper. No conflict — this
is the mathlib `MonoidAlgebra` pattern.

## Proof summary for the closed counit laws

The proofs reduce via `AddMonoidAlgebra.algHom_ext` to checking on
basis vectors `Finsupp.single F 1`, then evaluate `comulAlgHom` on
that basis vector through `comulAlgHom_apply_single` (= `comulForest F`),
then induct on `F : TraceForest α Unit` (a `Multiset`). The cons step uses
multiplicativity of `comulForest` (`comulForest_add`) and reduces to
the singleton-tree case.

For `counit_rTensor` the singleton-tree case
`(ε ⊗ id) (Δ^c T) = 1 ⊗ {T}` requires that **only the empty cut**
contributes: the explicit `T ⊗ 1` term has `ε({T}) = 0` (since
`{T} ≠ 0`); each cut term `forestToHc (cutForest c) ⊗ {remainder c}`
has `ε(cutForest c) = 0` unless `cutForest c = 0`, and
`cutForest c = 0 ↔ c = empty T` (the helper `cutForest_eq_zero_imp_empty`,
proved by induction on `T`).

For `counit_lTensor` the singleton-tree case is symmetric and simpler:
`forestToHc {remainder c} = single {remainder c} 1` always has
`{remainder c} ≠ 0` (singleton), so the entire sum vanishes after
`(id ⊗ ε)` projection, leaving just the explicit `forestToHc {T} ⊗ 1`
term (where the right channel becomes `ε(1) = 1`).

## Proof strategy for the deferred `comul_coassoc_tree`

Both LHS and RHS of `comul_coassoc_tree` expand into sums of triple-tensors
indexed by "double cut" data on `T`. The cuts-of-cuts bijection
(@cite{foissy-2002} §2 / @cite{connes-kreimer-1998}) identifies the two
indexings:

- **LHS-style** `(Δ^c ⊗ id) ∘ Δ^c (forestToHc {T})`: outer cut
  `C₁ : CutShape T` (from the inner Δ^c on T), then for each tree
  `T' ∈ cutForest C₁`, an "augmented cut" on `T'` (real cut or "extract
  whole" via the explicit `T' ⊗ 1` term in `comulTree T'`). The product
  of all sub-cut data gives the inner Δ^c on the cutForest.
- **RHS-style** `(id ⊗ Δ^c) ∘ Δ^c (forestToHc {T})`: outer augmented cut
  `ac₁ : AugCutShape T`, then an inner augmented cut
  `ac₂ : AugCutShape (remainder ac₁)` (from the outer Δ^c on the
  right-channel forest of `ac₁`).

Both indexings enumerate the same set of "double cuts" on `T` —
equivalently, 3-level partitions of the vertices into `Top` (preserved
in remainder), `Mid` (between cuts), and `Bot` (extracted as deepest
forest). Each double cut contributes the same triple-tensor term to
both sums, so LHS = RHS.

Substrate progress:
1. ✅ `AugCutShape T := CutShape T ⊕ Unit` — defined in
   `AugmentedCut.lean`. Projections `cutForest_aug` and `remainderForest`,
   `Fintype` instance via `Sum.fintype`.
2. ✅ `comulTree_eq_sum_AugCutShape` — `AugmentedCut.lean` proves
   `comulTree T = ∑_(ac : AugCutShape T) ...`. Uniform sum form.
3. ✅ `comulForest_eq_sum_sections` — `AugmentedCut.lean` proves the
   multi-tree expansion via `Multiset.prod_map_sum` + `Multiset.Sections`.
4. ✅ `DoubleCut T := (Σ C : CutShape T, AugCutShape (remainder C)) ⊕ Unit`
   — defined in `DoubleCut.lean`. Right-iterated form. `tripleTensor`
   projection to `Hc ⊗ (Hc ⊗ Hc)`.
5. ✅ `rhs_eq_sum_DoubleCut` — proved in `DoubleCut.lean`.
6. ✅ `lhs_eq_sum_DoubleCut` — proved in `LhsEquiv.lean` via the
   `lhsGeoCutEquiv` direct chain (Sessions 2-5).
7. ✅ `comul_coassoc_tree` — proved via (5)+(6)+`comulAlgHom_apply_single`.
8. ✅ `comul_coassoc` — proved via `algHom_ext_tree` + (7).

Stage 1 obligation chain sorry-free as of 0.230.728.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## Helper lemma: how `counit` acts on basis vectors

(`comulAlgHom_apply_single` lives in `Coproduct.lean` next to the definition.) -/

/-- `counit` applied to the basis vector `Finsupp.single F 1` equals
    `1` if `F` is the empty forest, `0` otherwise. Not `@[simp]`: the
    `if F = 0` form requires F to be concrete or the equality to be
    in scope, so simp can't fire it on symbolic `F`. Callers split
    on `F = 0` then invoke this manually. -/
theorem counit_apply_single (F : TraceForest α Unit) :
    counit (R := R) (α := α) (Finsupp.single F 1)
      = if F = 0 then (1 : R) else 0 := by
  show AddMonoidAlgebra.lift R _ _ counitMonoidHom (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-! ## Helpers for the counit-law proofs -/

omit [DecidableEq α] in
/-- Structural fact about admissible cuts: `cutForest c = 0` iff `c`
    is the empty cut on `T`. Used to isolate the surviving term in
    the `(ε ⊗ id) ∘ Δ^c` sum (only the empty cut has cutForest = 0,
    so only that term has nonzero counit projection on the left
    channel). Inducts on `T : TraceTree α Unit`. -/
private lemma cutForest_eq_zero_imp_empty :
    ∀ {T : TraceTree α Unit} (c : CutShape T),
      CutShape.cutForest c = 0 → c = CutShape.empty T
  | .leaf _, .atLeaf, _ => rfl
  | .trace _, .atTrace, _ => rfl
  | .node l r, .bothCut _ _, h => by
      exfalso
      change ({l, r} : Multiset (TraceTree α Unit)) = 0 at h
      have hcard : Multiset.card ({l, r} : Multiset (TraceTree α Unit)) = 0 := by
        rw [h]; rfl
      rw [Multiset.card_pair] at hcard
      omega
  | .node _ _, .onlyLeftCut _ _, h => by
      exfalso
      exact Multiset.singleton_ne_zero _ (add_eq_zero.mp h).1
  | .node _ _, .onlyRightCut _ _, h => by
      exfalso
      exact Multiset.singleton_ne_zero _ (add_eq_zero.mp h).2
  | .node _ _, .bothRecurse cl cr, h => by
      obtain ⟨hl, hr⟩ := add_eq_zero.mp h
      have ihl := cutForest_eq_zero_imp_empty cl hl
      have ihr := cutForest_eq_zero_imp_empty cr hr
      subst ihl; subst ihr; rfl

/-- Singleton-tree case of `counit_rTensor`: `(ε ⊗ id) (Δ^c T) = 1 ⊗ {T}`.
    Only the empty cut contributes; explicit `T ⊗ 1` term and all
    nonempty cuts get killed by counit (= 0 on non-empty forests). -/
private lemma counit_rTensor_apply_comulTree (T : TraceTree α Unit) :
    (Algebra.TensorProduct.map (counit (R := R) (α := α))
        (AlgHom.id R (Hc R α))) (comulTree T)
      = (1 : R) ⊗ₜ[R] forestToHc (R := R) ({T} : TraceForest α Unit) := by
  rw [comulTree_eq_prim_add_sum]
  rw [map_add]
  unfold forestToHc
  rw [Algebra.TensorProduct.map_tmul]
  simp only [counit_apply_single, AlgHom.coe_id, id_eq]
  -- Explicit `forestToHc {T} ⊗ 1` term: counit({T}) = 0 since {T} ≠ 0.
  have hT : ({T} : TraceForest α Unit) ≠ 0 := Multiset.singleton_ne_zero _
  rw [if_neg hT, TensorProduct.zero_tmul, zero_add]
  -- Sum: only `c = empty T` contributes (others have cutForest c ≠ 0).
  rw [map_sum, Finset.sum_eq_single (CutShape.empty T)]
  · rw [Algebra.TensorProduct.map_tmul, counit_apply_single, AlgHom.coe_id, id_eq,
        CutShape.cutForest_empty, CutShape.remainder_empty]
    simp only [↓reduceIte]
  · intro c _ hne
    rw [Algebra.TensorProduct.map_tmul, counit_apply_single, AlgHom.coe_id, id_eq]
    have hc : CutShape.cutForest c ≠ 0 := fun h => hne (cutForest_eq_zero_imp_empty c h)
    rw [if_neg hc, TensorProduct.zero_tmul]
  · intro hempty
    exact absurd (Finset.mem_univ _) hempty

/-- Forest-level `counit_rTensor`: `(ε ⊗ id) (Δ^c F) = 1 ⊗ forestToHc F`.
    Multiset induction on `F`; cons case uses multiplicativity of
    `comulForest` and the singleton-tree lemma. -/
private lemma counit_rTensor_apply_comulForest (F : TraceForest α Unit) :
    (Algebra.TensorProduct.map (counit (R := R) (α := α))
        (AlgHom.id R (Hc R α))) (comulForest F)
      = (1 : R) ⊗ₜ[R] forestToHc (R := R) F := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForest_zero, map_one, Algebra.TensorProduct.one_def]
    rfl
  | cons T F' ih =>
    rw [show (T ::ₘ F' : TraceForest α Unit) = ({T} : TraceForest α Unit) + F' from rfl, comulForest_add]
    have h1 : comulForest (R := R) ({T} : TraceForest α Unit) = comulTree T := by
      unfold comulForest
      simp only [Multiset.map_singleton, Multiset.prod_singleton]
    rw [h1, map_mul, counit_rTensor_apply_comulTree, ih,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← forestToHc_add]

/-- Singleton-tree case of `counit_lTensor`: `(id ⊗ ε) (Δ^c T) = {T} ⊗ 1`.
    Only the explicit `T ⊗ 1` term survives; every cut term has
    `forestToHc {remainder c}` on the right channel, which is a
    singleton workspace and therefore non-zero, so counit kills it. -/
private lemma counit_lTensor_apply_comulTree (T : TraceTree α Unit) :
    (Algebra.TensorProduct.map (AlgHom.id R (Hc R α))
        (counit (R := R) (α := α))) (comulTree T)
      = forestToHc (R := R) ({T} : TraceForest α Unit) ⊗ₜ[R] (1 : R) := by
  rw [comulTree_eq_prim_add_sum]
  rw [map_add, Algebra.TensorProduct.map_tmul]
  simp only [AlgHom.coe_id, id_eq, map_one]
  rw [map_sum, Finset.sum_eq_zero, add_zero]
  intro c _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  unfold forestToHc
  rw [counit_apply_single]
  have hne : ({CutShape.remainder c} : TraceForest α Unit) ≠ 0 := Multiset.singleton_ne_zero _
  rw [if_neg hne, TensorProduct.tmul_zero]

/-- Forest-level `counit_lTensor`: `(id ⊗ ε) (Δ^c F) = forestToHc F ⊗ 1`. -/
private lemma counit_lTensor_apply_comulForest (F : TraceForest α Unit) :
    (Algebra.TensorProduct.map (AlgHom.id R (Hc R α))
        (counit (R := R) (α := α))) (comulForest F)
      = forestToHc (R := R) F ⊗ₜ[R] (1 : R) := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForest_zero, map_one, Algebra.TensorProduct.one_def]
    rfl
  | cons T F' ih =>
    rw [show (T ::ₘ F' : TraceForest α Unit) = ({T} : TraceForest α Unit) + F' from rfl, comulForest_add]
    have h1 : comulForest (R := R) ({T} : TraceForest α Unit) = comulTree T := by
      unfold comulForest
      simp only [Multiset.map_singleton, Multiset.prod_singleton]
    rw [h1, map_mul, counit_lTensor_apply_comulTree, ih,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← forestToHc_add]

/-! ## Reduction: AlgHom equality from agreement on tree-singleton workspaces

`Hc R α = AddMonoidAlgebra R (TraceForest α Unit)` is, as an algebra, the free
commutative algebra on `TraceTree α Unit` (since `TraceForest α Unit = Multiset
(TraceTree α Unit)` with multiset-addition as multiplication). So an
`AlgHom` from `Hc R α` is determined by its values on the single-tree
workspaces `forestToHc {T} = single {T} 1`, which are the multiplicative
generators.

This is the algebraic input that lets us reduce `comul_coassoc`
(Hc-level) to `comul_coassoc_tree` (single-tree level) — the only
remaining substantive obligation. -/

/-- Agreement of two `AlgHom`s out of `Hc R α` reduces to agreement on
    single-tree workspaces `forestToHc {T}`. The multiplicative generators
    of `Hc R α = AddMonoidAlgebra R (TraceForest α Unit)` are exactly the basis
    vectors `single {T} 1` for `T : TraceTree α Unit`; multiplicativity
    extends agreement on these to all `single F 1`, then
    `AddMonoidAlgebra.algHom_ext` extends to all of `Hc R α`. -/
lemma algHom_ext_tree {X : Type*} [Semiring X] [Algebra R X]
    {f g : Hc R α →ₐ[R] X}
    (h : ∀ T : TraceTree α Unit, f (forestToHc ({T} : TraceForest α Unit))
                              = g (forestToHc ({T} : TraceForest α Unit))) :
    f = g := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  show f (forestToHc (R := R) F) = g (forestToHc (R := R) F)
  induction F using Multiset.induction with
  | empty =>
    rw [forestToHc_zero, map_one, map_one]
  | cons T F' ih =>
    have heq : (T ::ₘ F' : TraceForest α Unit) = ({T} : TraceForest α Unit) + (F' : TraceForest α Unit) := rfl
    rw [heq, forestToHc_add, map_mul, map_mul, h T, ih]

/-! ## Bialgebra laws -/

/-- **Tree-level coassociativity** of Δ^c. Both sides reorganize as
    sums over `DoubleCut T` (right-iterated form), with the same
    triple-tensor terms. Reduces to:
    - `lhs_eq_sum_DoubleCut` (`LhsEquiv.lean` — the substantive Foissy
      bijection content, proved via `lhsGeoCutEquiv`)
    - `rhs_eq_sum_DoubleCut` (`DoubleCut.lean` — easier direction). -/
theorem comul_coassoc_tree (T : TraceTree α Unit) :
    ((Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
        (AlgHom.id R (Hc R α))).comp comulAlgHom))
       (forestToHc (R := R) ({T} : TraceForest α Unit))
    = ((Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom).comp comulAlgHom)
       (forestToHc (R := R) ({T} : TraceForest α Unit)) := by
  -- LHS: assoc ((map Δ id) (Δ (forestToHc {T}))) = assoc ((map Δ id) (comulTree T))
  -- RHS: (map id Δ) (Δ (forestToHc {T}))        = (map id Δ) (comulTree T)
  -- Both equal ∑ dc : DoubleCut T, dc.tripleTensor R.
  show (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _) (AlgHom.id R (Hc R α)))
          (comulAlgHom (forestToHc (R := R) ({T} : TraceForest α Unit))))
      = (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom)
          (comulAlgHom (forestToHc (R := R) ({T} : TraceForest α Unit)))
  -- comulAlgHom (forestToHc {T}) = comulForest {T} = comulTree T
  have hcomul : comulAlgHom (forestToHc (R := R) ({T} : TraceForest α Unit)) = comulTree T := by
    show comulAlgHom (Finsupp.single ({T} : TraceForest α Unit) (1 : R)) = comulTree T
    rw [comulAlgHom_apply_single]
    unfold comulForest
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [hcomul, lhs_eq_sum_DoubleCut, ← rhs_eq_sum_DoubleCut]

/-- Coassociativity of the Connes-Kreimer contraction coproduct Δ^c.
    @cite{marcolli-chomsky-berwick-2025} Lemma 1.2.10.

    Reduces via `algHom_ext_tree` (multiplicativity of AlgHoms +
    `AddMonoidAlgebra.algHom_ext`) to `comul_coassoc_tree`, the
    single-tree obligation containing the cuts-of-cuts bijection. -/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
        (AlgHom.id R (Hc R α))).comp comulAlgHom)
    = (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom).comp comulAlgHom := by
  apply algHom_ext_tree
  exact comul_coassoc_tree

/-- Right-tensor counit law: `(ε ⊗ id) ∘ Δ^c = lid.symm`.

    Only the term where the left tensor channel is the empty forest
    (i.e., the explicit empty cut, which has `cutForest = 0`) survives
    the counit projection. Reduces to `counit_rTensor_apply_comulForest`
    via `AddMonoidAlgebra.algHom_ext` + `comulAlgHom_apply_single`. -/
theorem counit_rTensor :
    (Algebra.TensorProduct.map (counit : Hc R α →ₐ[R] R)
      (AlgHom.id R (Hc R α))).comp comulAlgHom
    = (Algebra.TensorProduct.lid R (Hc R α)).symm.toAlgHom := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (counit : Hc R α →ₐ[R] R) (AlgHom.id R (Hc R α)))
        (comulAlgHom (Finsupp.single F 1))
      = (Algebra.TensorProduct.lid R (Hc R α)).symm.toAlgHom (Finsupp.single F 1)
  rw [comulAlgHom_apply_single, counit_rTensor_apply_comulForest]
  show (1 : R) ⊗ₜ[R] forestToHc (R := R) F
      = (Algebra.TensorProduct.lid R (Hc R α)).symm (Finsupp.single F 1)
  rw [Algebra.TensorProduct.lid_symm_apply]
  rfl

/-- Left-tensor counit law: `(id ⊗ ε) ∘ Δ^c = rid.symm`.

    Only the explicit `T ⊗ 1` term in `comulTree` survives the counit
    projection on the right channel (every cut term has
    `forestToHc {remainder c}`, a non-zero singleton, on the right).
    Reduces to `counit_lTensor_apply_comulForest`. -/
theorem counit_lTensor :
    (Algebra.TensorProduct.map (AlgHom.id R (Hc R α))
      (counit : Hc R α →ₐ[R] R)).comp comulAlgHom
    = (Algebra.TensorProduct.rid R R (Hc R α)).symm.toAlgHom := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) (counit : Hc R α →ₐ[R] R))
        (comulAlgHom (Finsupp.single F 1))
      = (Algebra.TensorProduct.rid R R (Hc R α)).symm.toAlgHom (Finsupp.single F 1)
  rw [comulAlgHom_apply_single, counit_lTensor_apply_comulForest]
  show forestToHc (R := R) F ⊗ₜ[R] (1 : R)
      = (Algebra.TensorProduct.rid R R (Hc R α)).symm (Finsupp.single F 1)
  rw [Algebra.TensorProduct.rid_symm_apply]
  rfl

/-- The Connes-Kreimer bialgebra structure on `Hc R α` using the **contraction**
    coproduct Δ^c (`comulAlgHom`).

    All Stage 1 obligations (`comul_coassoc`, `counit_rTensor`, `counit_lTensor`)
    are sorry-free, so this is registered as an `instance`. Typeclass resolution
    finds it on `Hc R α` because `Hc` is a `def` (not `abbrev`), giving a distinct
    typeclass slot from mathlib's `AddMonoidAlgebra.instBialgebra` on the underlying
    `AddMonoidAlgebra R (TraceForest α Unit)` (group-like coproduct Δ(F) = F ⊗ F).
    The two coexist without conflict — the wrapper pattern is the same as mathlib's
    `MonoidAlgebra`.

    **Δ^d vs Δ^c — the design choice.** Minimalism's `mergeOp` (M-C-B Def 1.3.4,
    p. 42) uses the **deletion** coproduct Δ^d (`comulDelAlgHom`), NOT Δ^c.
    Crucially, **Δ^d is NOT itself a coassociative coalgebra**: M-C-B Lemma 1.2.12
    (p. 39) only matches terms up to multiplicity (see Figure 1.3, p. 40), and
    Remark 1.2.9 (p. 34) labels it "a weaker version of the coassociativity
    relation". The proper algebraic structure for Δ^d is deferred by M-C-B to
    Marcolli-Walton ("Generalized Quasi-Hopf Algebras and Merge", in preparation,
    ref [146]).

    Hence the choice is **forced**, not a trade-off: only Δ^c is a bialgebra
    in the standard sense. M-C-B's own framing (§3.1.2.1, p. 206) treats
    `(V(F_SO_0), ⊔, Δ^c, S)` as THE Hopf algebra; Δ^d is "a form of the
    coproduct… when needed" for substructure comparisons. M-C-B p. 44 also
    gives the explicit derivation `Δ^d = (id ⊗ Π_{d,c}) ∘ Δ^c` where Π_{d,c}
    is the linear "remove-trace-and-edge-contract" projection.

    **TODO (future refactor):** Define `Π_{d,c} : Hc R α →ₗ[R] Hc R α` and
    derive `comulDelLin = (LinearMap.id ⊗ Π_{d,c}) ∘ comulAlgHom.toLinearMap`,
    matching M-C-B p. 44 — eliminates the parallel `comulDelAlgHom` def and
    expresses Δ^d as a *derivation* from the canonical Bialgebra structure.
    Loses the AlgHom shape on Δ^d (Π_{d,c} is only linear, not multiplicative)
    but matches M-C-B's structural framing.

    Direct access to operators stays available by name:
    `comulAlgHom` (Δ^c, Bialgebra-mediated), `comulDelAlgHom` (Δ^d,
    name-mediated), `counit`. -/
noncomputable instance instBialgebraHc : Bialgebra R (Hc R α) :=
  Bialgebra.ofAlgHom comulAlgHom counit comul_coassoc counit_rTensor counit_lTensor

end ConnesKreimer
