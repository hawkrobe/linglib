/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.PreLie.OudomGuinCirc
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonAssoc
import Linglib.Core.Algebra.RootedTree.PreLie.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.MonoidAlgebra.Basic

set_option autoImplicit false

/-!
# Bridge: GrossmanLarson product = Oudom-Guin ★ on basis
[oudom-guin-2008] [foissy-2021]

For the pre-Lie algebra `L = InsertionAlgebra α` (rooted trees with
vertex-insertion product), the Oudom-Guin construction gives an
associative product `★` on `S(L)`. This file bridges that abstract
construction to the concrete Grossman-Larson product on
`ConnesKreimer R (Nonplanar α)` via a canonical algebra isomorphism.

## Main definitions

* `ckIsoSymmetricAlgebra` : algebra equivalence
  `SymmetricAlgebra R (Nonplanar α →₀ R) ≃ₐ[R] ConnesKreimer R (Nonplanar α)`.
  Composed from mathlib equivalences:
    `SymmetricAlgebra.equivMvPolynomial` (with `Finsupp.basisSingleOne`) +
    `MvPolynomial σ R = AddMonoidAlgebra R (σ →₀ ℕ)` (definitional) +
    `AddMonoidAlgebra.domCongr` with `Multiset.toFinsupp.symm`.

## Main theorems

* `gl_product_eq_oudomGuinStar` (Q5c) : `★` transported via `ckIsoSymmetricAlgebra`
  equals the Grossman-Larson product. **Proved sorry-free** 2026-06-12.

* `mul_assoc_basis_via_oudom_guin_pbw` (Q6) : closure of
  `mul_assoc_basis` for `R = ℤ` using `oudomGuinStar_assoc` + Q5c.
  **Proved sorry-free** 2026-06-12 (Q3 + Q5c both closed).

## Status

Q3 + Q5c + Q6 chain fully proved. Grossman-Larson associativity over ℤ
is now established via the OG `★` bridge.
`#print axioms RootedTree.GrossmanLarson.mul_assoc_basis_via_oudom_guin_pbw`
yields `[propext, Classical.choice, Quot.sound]` (no sorryAx).
-/

open PreLie.OudomGuinCirc

namespace RootedTree

open GrossmanLarson

-- `α : Type*` since OG `oudomGuinStar` is now universe-polymorphic
-- (Phase 1 of the GL-associativity arc; `circT` is the only Type-0-pinned
-- exception, not used here).
variable {α : Type*} [DecidableEq α]

/-! ## §1: The carrier iso

`SymmetricAlgebra ℤ (Nonplanar α →₀ ℤ) ≃ₐ ConnesKreimer ℤ (Nonplanar α)`.

This is a direct composition of three mathlib equivalences. Lifts to
arbitrary `R` after `InsertionAlgebra` is generalized (deferred). -/

/-- The carrier iso from `SymmetricAlgebra ℤ (InsertionAlgebra α)` to
    `ConnesKreimer ℤ (Nonplanar α) = GrossmanLarson ℤ α`.

    `InsertionAlgebra α = Nonplanar α →₀ ℤ` has the canonical
    `Finsupp.basisSingleOne` indexed by `Nonplanar α`. Apply
    `SymmetricAlgebra.equivMvPolynomial` to get `MvPolynomial (Nonplanar α) ℤ`,
    which is definitionally `AddMonoidAlgebra ℤ (Nonplanar α →₀ ℕ)`. Then
    `AddMonoidAlgebra.domCongr` via the additive equiv
    `(Nonplanar α →₀ ℕ) ≃+ Multiset (Nonplanar α)` (= `Multiset.toFinsupp.symm`)
    lands in `AddMonoidAlgebra ℤ (Multiset (Nonplanar α))`; the final
    `ConnesKreimer.toFinsuppAlgEquiv.symm` wraps that bare carrier into the
    `ConnesKreimer` structure. -/
noncomputable def ckIsoSymmetricAlgebra :
    SymmetricAlgebra ℤ (InsertionAlgebra α) ≃ₐ[ℤ] ConnesKreimer ℤ (Nonplanar α) :=
  (SymmetricAlgebra.equivMvPolynomial
      (Finsupp.basisSingleOne (R := ℤ) (ι := Nonplanar α) :
        Module.Basis (Nonplanar α) ℤ (InsertionAlgebra α))).trans
    ((AddMonoidAlgebra.domCongr ℤ ℤ (Multiset.toFinsupp (α := Nonplanar α)).symm).trans
      ConnesKreimer.toFinsuppAlgEquiv.symm)

/-! ## §1b: Basis identification

The iso `ckIsoSymmetricAlgebra` sends `ι (single t 1)` to `of' (singleton t)`.
This is the basis-level fingerprint we use to translate proofs between
`SymAlg ℤ (InsertionAlgebra α)` and `ConnesKreimer ℤ (Nonplanar α)`. -/

/-- The iso sends `ι(single t 1)` (basis element of SymAlg) to
    `of'(singleton t)` (basis element of CK). -/
theorem ckIsoSymmetricAlgebra_ι_single (t : Nonplanar α) :
    ckIsoSymmetricAlgebra
        (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (Finsupp.single t (1 : ℤ))) =
      ConnesKreimer.of' (R := ℤ) ({t} : Multiset (Nonplanar α)) := by
  show ConnesKreimer.toFinsuppAlgEquiv.symm
        ((AddMonoidAlgebra.domCongr ℤ ℤ Multiset.toFinsupp.symm)
          ((SymmetricAlgebra.equivMvPolynomial
              (Finsupp.basisSingleOne (R := ℤ) (ι := Nonplanar α) :
                Module.Basis (Nonplanar α) ℤ (InsertionAlgebra α)))
            ((SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) (Finsupp.single t 1)))) = _
  -- Step 1: equivMvPolynomial sends ι (basisSingleOne t) to MvPolynomial.X t.
  have h1 : SymmetricAlgebra.equivMvPolynomial
      (Finsupp.basisSingleOne (R := ℤ) (ι := Nonplanar α) :
        Module.Basis (Nonplanar α) ℤ (InsertionAlgebra α))
      ((SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) (Finsupp.single t 1)) =
      MvPolynomial.X t := by
    rw [show (Finsupp.single t (1 : ℤ) : InsertionAlgebra α) =
          (Finsupp.basisSingleOne (R := ℤ) (ι := Nonplanar α) :
            Module.Basis (Nonplanar α) ℤ (InsertionAlgebra α)) t from rfl]
    exact SymmetricAlgebra.equivMvPolynomial_ι_apply _ t
  rw [h1]
  -- Step 2: MvPolynomial.X t = single (single t 1) 1.
  show ConnesKreimer.toFinsuppAlgEquiv.symm
      ((AddMonoidAlgebra.domCongr ℤ ℤ Multiset.toFinsupp.symm)
        (AddMonoidAlgebra.single (Finsupp.single t 1) 1 :
          AddMonoidAlgebra ℤ (Nonplanar α →₀ ℕ))) = _
  rw [AddMonoidAlgebra.domCongr_single]
  -- Multiset.toFinsupp.symm (single t 1) = {t}
  have h2 : (Multiset.toFinsupp (α := Nonplanar α)).symm (Finsupp.single t 1) =
        ({t} : Multiset (Nonplanar α)) := by
    rw [AddEquiv.symm_apply_eq]; exact (Multiset.toFinsupp_singleton t).symm
  rw [h2]
  rfl

/-! ## §2: Q5c — bridge `oudomGuinStar` ↔ `product`

The two products on `ConnesKreimer ℤ (Nonplanar α)`:

* Disjoint-union (the `CommSemiring` instance): `of' F * of' G = of' (F + G)`.
* Grossman-Larson (the custom `Mul` on `GrossmanLarson R α`):
  `of' F * of' G = Σ_{G₁ ⊆ G} of'(insertion F G₁) · (G - G₁)`.

The Oudom-Guin `★` on `SymmetricAlgebra ℤ (InsertionAlgebra α)`, transported
via `ckIsoSymmetricAlgebra`, equals the **Grossman-Larson** product (NOT the
disjoint-union one). This is the content of Q5c.

Proof strategy (mirrors Q3's per-tprod closure):

1. Lift Y via `algHomL_surjective` to `Y = algHomL(tprod m a)` and induct on m.
2. **m = 0**: Y = 1. LHS = ckIso X. RHS = (op (ckIso X)) * 1 = op (ckIso X)
   (via `mul_one`).
3. **m + 1**: Y = D · ι v where D = algHomL(tprod m init), v = a(last).
   - LHS via `oudomGuinStar_mul_ι_split`: ckIso(X ★ (D · ι v)) decomposes
     into 3 terms involving (X★D)○ιv, (X★D)·ιv, X★(D○ιv).
   - IH at D closes ckIso(X★D) → op(ckIso X) * op(ckIso D).
   - IH summand-wise at D○ιv (which is a sum of m-tprods via
     `oudomGuinCirc_algHomL_tprod_ι`) closes X★(D○ιv).
   - Intertwining substrate (`ckIso_circ_intertwine_insertion`) connects
     OG ○ to GL insertion.
   - RHS via `GL_product_split_mul_ι` (the GL Foissy split substrate)
     decomposes into matching 3 terms.

The proof structure is wired below; the two substrate lemmas
`ckIso_circ_intertwine_insertion` and `GL_product_split_mul_ι` are
both proved sorry-free below. -/

/-! ### Sub-substrates for Q5c's substrate 1

Three combinatorial bridges that substrate 1 (`ckIso_circ_intertwine_insertion`)
will use:

1. **`RoseTree`-level bridge**: `RoseTree.Pathed.insertion T [s] = RoseTree.insertSum T s`.
   Foissy's multi-graft on single-host-single-guest reduces to the simpler
   `insertSum`. Uses `multiGraft_singleton` + `listChoices xs 1 = xs.map [·]`
   + `insertSum_eq_coe_map_insertAt`.

2. **Nonplanar bridge**: `Nonplanar.insertionMultiset {t} {s} =
   (Nonplanar.insertSum t s).map (fun r => {r})`. Descends (1) through
   `Quotient.mk` using `insertionForest_singleton` + `mk_insertSum`.

3. **GL Leibniz substrate**: `insertion(op(A *_CK B))(op(of'({v}))) =
   op(unop(insertion(op A)(op(of'({v})))) *_CK B) + op(A *_CK
   unop(insertion(op B)(op(of'({v})))))`. Derived from existing
   `Nonplanar.insertionMultiset_add_host` (powerset of `{v}` collapses to
   the Leibniz split) + bilinear extension.

Each is a standalone combinatorial lemma; all three are proved below. -/

/-- Helper: `listChoices V 1 = V.map (fun v => [v])`. By induction on `V`. -/
private theorem listChoices_one {β : Type*} (V : List β) :
    RoseTree.Pathed.listChoices V 1 = V.map (fun v => [v]) := by
  induction V with
  | nil => rfl
  | cons head tail _ =>
    -- Both sides reduce to `[head] :: tail.map (fun v => [v])` definitionally.
    show ([head] :: tail.flatMap (fun v => [[v]])) =
        [head] :: tail.map (fun v => [v])
    congr 1

omit [DecidableEq α] in
/-- **Sub-substrate 1.1**: `RoseTree`-level Foissy multi-graft on single guest
    reduces to `insertSum`. Uses `listChoices V 1 = V.map [·]`,
    `multiGraft_singleton`, and `insertSum_eq_coe_map_insertAt`. -/
private theorem tree_insertion_singleton_guest_eq_insertSum
    (T s : RoseTree α) :
    RoseTree.Pathed.insertion T [s] = RoseTree.insertSum T s := by
  rw [RoseTree.Pathed.insertion_def]
  rw [RoseTree.insertSum_eq_coe_map_insertAt]
  simp only [List.length_singleton]
  rw [listChoices_one, List.map_map]
  -- Now: Multiset.ofList ((vertices T).map (fun v => multiGraft T ([v].zip [s])))
  --    = ((vertices T).map (fun p => insertAt p s T) : Multiset _)
  -- The two sides are `Multiset.ofList`/`coe` of two lists differing only by a funext.
  congr 1
  apply List.map_congr_left
  intro v _hv
  show RoseTree.Pathed.multiGraft T [(v, s)] = RoseTree.Pathed.insertAt v s T
  exact RoseTree.Pathed.multiGraft_singleton T v s

omit [DecidableEq α] in
/-- Helper: `insertionForest [T] [s'] = (insertion T [s']).map (fun T' => [T'])`.
    Reduces the bind over `[true, false]` assignments: `[true]` contributes
    `(insertion T [s']).map (fun T' => [T'])`, `[false]` contributes `0`
    (because `insertionForest [] [s'] = 0`). -/
private theorem insertionForest_singleton_singleton (T s' : RoseTree α) :
    RoseTree.Pathed.insertionForest [T] [s'] =
      (RoseTree.Pathed.insertion T [s']).map (fun T' => [T']) := by
  rw [RoseTree.Pathed.insertionForest_cons_cons]
  -- listChoices [true, false] 1 = [[true], [false]] by computation.
  show ((Multiset.ofList [[true], [false]]).bind fun assignment =>
        (RoseTree.Pathed.insertion T
          (([s'].zip assignment).filterMap fun p => if p.snd then some p.fst else none)).bind
          fun T' => (RoseTree.Pathed.insertionForest []
              (([s'].zip assignment).filterMap fun p => if p.snd then none else some p.fst)).map
            fun F' => T' :: F') =
      (RoseTree.Pathed.insertion T [s']).map (fun T' => [T'])
  rw [show (Multiset.ofList [[true], [false]] : Multiset (List Bool)) =
        ([true] ::ₘ {[false]}) from rfl]
  rw [Multiset.cons_bind, Multiset.singleton_bind]
  -- Branch true:
  --   zip [s'] [true] = [(s', true)]
  --   filterMap (snd → some fst) = [s']
  --   filterMap (¬snd → some fst) = []
  --   (insertion T [s']).bind (fun T' => (insertionForest [] []).map (fun F' => T' :: F'))
  -- Branch false:
  --   zip [s'] [false] = [(s', false)]
  --   filterMap (snd → some fst) = []
  --   filterMap (¬snd → some fst) = [s']
  --   (insertion T []).bind (fun T' => (insertionForest [] [s']).map (fun F' => T' :: F'))
  --   = 0  (since insertionForest [] [s'] = 0).
  show (RoseTree.Pathed.insertion T [s']).bind
        (fun T' => (RoseTree.Pathed.insertionForest [] []).map (fun F' => T' :: F'))
      + (RoseTree.Pathed.insertion T []).bind
        (fun T' => (RoseTree.Pathed.insertionForest [] [s']).map (fun F' => T' :: F')) =
      (RoseTree.Pathed.insertion T [s']).map (fun T' => [T'])
  rw [RoseTree.Pathed.insertionForest_nil_nil,
      RoseTree.Pathed.insertionForest_empty_host_nonempty_guests]
  simp only [Multiset.map_singleton, Multiset.bind_singleton, Multiset.map_zero,
             Multiset.bind_zero, add_zero]

omit [DecidableEq α] in
/-- **Sub-substrate 1.2**: Nonplanar multi-graft on singleton host/guest
    reduces to the singletonization of `insertSum`. Descends 1.1 through
    `Quotient.mk`. -/
private theorem nonplanar_insertionMultiset_singletons (t s : Nonplanar α) :
    Nonplanar.insertionMultiset ({t} : Multiset (Nonplanar α))
        ({s} : Multiset (Nonplanar α)) =
      (Nonplanar.insertSum t s).map fun r => ({r} : Multiset (Nonplanar α)) := by
  -- Step 1: Unfold insertionMultiset; reduce toList of singletons.
  unfold Nonplanar.insertionMultiset
  simp only [Multiset.toList_singleton]
  -- After simp: List.map Quotient.out [t] = [Quotient.out t] = [t.out]; same for s.
  show (RoseTree.Pathed.insertionForest [Quotient.out t] [Quotient.out s]).map
        (fun L => (Multiset.ofList (L.map Nonplanar.mk) : Multiset (Nonplanar α))) =
      (Nonplanar.insertSum t s).map fun r => ({r} : Multiset (Nonplanar α))
  -- Step 2: Reduce insertionForest [t.out] [s.out] via the helper.
  rw [insertionForest_singleton_singleton, Multiset.map_map]
  -- Step 3: Sub-substrate 1.1 reduces insertion to insertSum.
  rw [tree_insertion_singleton_guest_eq_insertSum]
  -- Goal:
  --   (RoseTree.insertSum t.out s.out).map
  --       (Function.comp (fun L => Multiset.ofList (L.map mk)) (fun T' => [T']))
  --   = (Nonplanar.insertSum t s).map (fun r => {r})
  -- Step 4: Reduce insertSum t s via Quotient.out_eq + Nonplanar.mk_insertSum.
  conv_rhs => rw [show t = Nonplanar.mk (Quotient.out t) from (Quotient.out_eq t).symm,
                  show s = Nonplanar.mk (Quotient.out s) from (Quotient.out_eq s).symm]
  rw [Nonplanar.mk_insertSum, Multiset.map_map]
  rfl

/-! ### Local op/unop simp lemmas

`op` and `unop` are identity coercions
between `ConnesKreimer ℤ (Nonplanar α)` and `GrossmanLarson ℤ α` (which
are definitionally equal). The forwarded `AddCommMonoid` and `Module ℤ`
instances make `op`/`unop` ℤ-linear; the lemmas below let `simp` cleanly
push `op`/`unop` through `+`, `0`, and `•`. -/

omit [DecidableEq α] in
@[local simp]
private theorem op_zero :
    op (0 : ConnesKreimer ℤ (Nonplanar α)) = (0 : GrossmanLarson ℤ α) := rfl

omit [DecidableEq α] in
@[local simp]
private theorem op_add (x y : ConnesKreimer ℤ (Nonplanar α)) :
    op (x + y) = op x + op y := rfl

omit [DecidableEq α] in
@[local simp]
private theorem op_smul (r : ℤ) (x : ConnesKreimer ℤ (Nonplanar α)) :
    op (r • x) = r • op x := rfl

omit [DecidableEq α] in
@[local simp]
private theorem unop_zero :
    unop (0 : GrossmanLarson ℤ α) = (0 : ConnesKreimer ℤ (Nonplanar α)) := rfl

omit [DecidableEq α] in
@[local simp]
private theorem unop_add (x y : GrossmanLarson ℤ α) :
    unop (x + y) = unop x + unop y := rfl

omit [DecidableEq α] in
@[local simp]
private theorem unop_smul (r : ℤ) (x : GrossmanLarson ℤ α) :
    unop (r • x) = r • unop x := rfl

omit [DecidableEq α] in
/-- **Basis form of sub-substrate 1.3**: GL Leibniz at basis level.

    For `F_A, F_B : Forest, v : Nonplanar α`:
    `insertion (of' (F_A + F_B)) (of' {v}) =
        op (of' F_A * unop (insertion (of' F_B) (of' {v})))
      + op (unop (insertion (of' F_A) (of' {v})) * of' F_B)`

    Follows from `insertion_mul_distrib` with `C := {v}`. Since
    `{v}.powerset = 0 ::ₘ {{v}}`, the sum has exactly 2 terms; each
    reduces via `of'_zero` + `insertion_one_right`. The `unop` on `of' F_A`
    and `of' F_B` collapses to the CK side by definitional equality
    (`unop` and `of'` are both identity wrt the underlying
    `ConnesKreimer.of'`). -/
private theorem GL_insertion_leibniz_basis_form [DecidableEq α]
    (F_A F_B : Forest (Nonplanar α)) (v : Nonplanar α) :
    insertion (R := ℤ)
        (of' (F_A + F_B))
        (of' ({v} : Multiset (Nonplanar α))) =
      op
        ((ConnesKreimer.of' F_A : ConnesKreimer ℤ (Nonplanar α)) *
          unop (insertion (R := ℤ)
            (of' F_B)
            (of' ({v} : Multiset _)))) +
      op
        (unop (insertion (R := ℤ)
            (of' F_A)
            (of' ({v} : Multiset _))) *
          (ConnesKreimer.of' F_B : ConnesKreimer ℤ (Nonplanar α))) := by
  rw [insertion_mul_distrib]
  -- LHS now: ({v}.powerset.map f).sum where
  --   f C₁ = op (unop (insertion (of' F_A) (of' C₁)) *
  --              unop (insertion (of' F_B) (of' ({v} - C₁))))
  -- Step 1: powerset {v} = 0 ::ₘ {{v}}.
  have h_powerset : (({v} : Multiset (Nonplanar α))).powerset =
        (0 : Multiset (Nonplanar α)) ::ₘ {({v} : Multiset (Nonplanar α))} := by
    show ((v ::ₘ (0 : Multiset (Nonplanar α)))).powerset = _
    rw [Multiset.powerset_cons, Multiset.powerset_zero]
    rfl
  rw [h_powerset]
  -- Step 2: distribute map + sum over 2-element multiset.
  rw [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
      Multiset.sum_singleton]
  -- Step 3: reduce {v} - 0 = {v} and {v} - {v} = 0.
  rw [tsub_zero, tsub_self]
  -- Step 4: of' 0 = 1, insertion X 1 = X (twice).
  rw [of'_zero,
      insertion_one_right,
      insertion_one_right]
  -- LHS: op (unop (of' F_A) * unop (insertion (of' F_B) (of' {v}))) +
  --      op (unop (insertion (of' F_A) (of' {v})) * unop (of' F_B))
  -- RHS: op (of' F_A * unop (insertion (of' F_B) (of' {v}))) +
  --      op (unop (insertion (of' F_A) (of' {v})) * of' F_B)
  -- unop (of' F_X) = of' F_X by definitional equality.
  rfl

/-- **Helper for 1.3**: Leibniz rule with right argument forced to be a
    Forest-basis element. Bilinear-in-A extension of the basis form via
    `ConnesKreimer.induction_linear` on A (following `insertion_mul_distrib_gen`'s
    pattern of explicit `show` casts to navigate type-alias unfolding). -/
private theorem GL_insertion_leibniz_basis_right
    (A : ConnesKreimer ℤ (Nonplanar α)) (F_B : Forest (Nonplanar α))
    (v : Nonplanar α) :
    insertion
        (op (A * (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
      op
        (unop (insertion (op A)
          (op (ConnesKreimer.of' ({v} : Multiset _)))) *
            (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
      op
        (A * unop (insertion
          (op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
          (op (ConnesKreimer.of' ({v} : Multiset _))))) := by
  refine ConnesKreimer.induction_linear A ?_ ?_ ?_
  · -- A = 0: every term has a `0 *` or `* 0` or `unop 0`/`op 0` that
    -- reduces to 0 of the appropriate type.
    show insertion
        (op ((0 : ConnesKreimer ℤ (Nonplanar α)) *
          (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
      op
        (unop (insertion
            (op (0 : ConnesKreimer ℤ (Nonplanar α)))
            (op (ConnesKreimer.of' ({v} : Multiset _)))) *
            (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
      op
        ((0 : ConnesKreimer ℤ (Nonplanar α)) *
          unop (insertion
            (op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
            (op (ConnesKreimer.of' ({v} : Multiset _)))))
    simp only [zero_mul, op_zero, unop_zero,
               (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_zero,
               LinearMap.zero_apply, add_zero]
  · -- additive
    intro A₁ A₂ ih₁ ih₂
    -- A₁, A₂ are `ConnesKreimer ℤ (Nonplanar α)` from `ConnesKreimer.induction_linear`.
    -- Alias each via `let` for the `show` below.
    let A₁' : ConnesKreimer ℤ (Nonplanar α) := A₁
    let A₂' : ConnesKreimer ℤ (Nonplanar α) := A₂
    show insertion
        (op ((A₁' + A₂') *
          (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
        op
          (unop (insertion
              (op (A₁' + A₂')) _) *
              (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
        op
          ((A₁' + A₂') *
            unop (insertion
              (op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
              (op (ConnesKreimer.of' ({v} : Multiset _)))))
    rw [add_mul, op_add,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, ih₁, ih₂]
    rw [op_add,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, unop_add, add_mul, add_mul]
    -- Now both sides are sums of `op (...)` expressions. Combine via op_add.
    simp only [← op_add]
    -- Goal: op(big CK expr) = op(big CK expr). Equate inside, then ring.
    congr 1
    ring
  · -- single F_A r
    intro F_A r
    -- Basis case: `A = ConnesKreimer.single F_A r`.
    let A_single : ConnesKreimer ℤ (Nonplanar α) := ConnesKreimer.single F_A r
    show insertion
        (op (A_single * (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
        op
          (unop (insertion (op A_single) _) *
              (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
        op
          (A_single * unop (insertion
            (op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
            (op (ConnesKreimer.of' ({v} : Multiset _)))))
    -- Unfold A_single = r • of' F_A.
    have hA : A_single = r • (ConnesKreimer.of' F_A : ConnesKreimer ℤ (Nonplanar α)) :=
      ConnesKreimer.smul_single_one F_A r
    rw [hA]
    rw [smul_mul_assoc, ← ConnesKreimer.of'_add, op_smul,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    -- Bridge `op (of' (F_A + F_B))` ≡ `of' (F_A + F_B)` so
    -- `GL_insertion_leibniz_basis_form` (stated with `of'`)
    -- applies.
    show r • insertion
        (of' (F_A + F_B)) (of' ({v} : Multiset _)) =
      _
    rw [GL_insertion_leibniz_basis_form, op_smul,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    simp only [smul_add, unop_smul, smul_mul_assoc, op_smul]
    rw [add_comm]
    rfl

/-- **Sub-substrate 1.3**: GL Leibniz rule for `insertion` w.r.t. CK product
    on first argument (single guest). Bilinear-in-B extension of
    `GL_insertion_leibniz_basis_right` (which already handles general A). -/
private theorem GL_insertion_leibniz_left_singleton_guest
    (A B : ConnesKreimer ℤ (Nonplanar α)) (v : Nonplanar α) :
    insertion (op (A * B))
        (op (ConnesKreimer.of' ({v} : Multiset (Nonplanar α)))) =
      op
        (unop (insertion (op A)
          (op (ConnesKreimer.of' ({v} : Multiset (Nonplanar α))))) * B) +
      op
        (A * unop (insertion (op B)
          (op (ConnesKreimer.of' ({v} : Multiset (Nonplanar α)))))) := by
  refine ConnesKreimer.induction_linear B ?_ ?_ ?_
  · -- B = 0
    show insertion
        (op (A * (0 : ConnesKreimer ℤ (Nonplanar α))))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
      op
        (unop (insertion (op A)
          (op (ConnesKreimer.of' ({v} : Multiset _)))) *
            (0 : ConnesKreimer ℤ (Nonplanar α))) +
      op
        (A * unop (insertion
          (op (0 : ConnesKreimer ℤ (Nonplanar α)))
          (op (ConnesKreimer.of' ({v} : Multiset _)))))
    simp only [mul_zero, op_zero,
               (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_zero,
               LinearMap.zero_apply, unop_zero, add_zero]
  · -- B = B₁ + B₂
    intro B₁ B₂ ih₁ ih₂
    let B₁' : ConnesKreimer ℤ (Nonplanar α) := B₁
    let B₂' : ConnesKreimer ℤ (Nonplanar α) := B₂
    show insertion
        (op (A * (B₁' + B₂')))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
      op
        (unop (insertion (op A)
          (op (ConnesKreimer.of' ({v} : Multiset _)))) * (B₁' + B₂')) +
      op
        (A * unop (insertion
          (op (B₁' + B₂'))
          (op (ConnesKreimer.of' ({v} : Multiset _)))))
    rw [mul_add, op_add,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, ih₁, ih₂]
    -- Distribute the (B₁' + B₂') on RHS: both via `mul_add` and via
    -- `op_add` then `insertion.map_add`.
    simp only [mul_add, op_add,
               (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
               LinearMap.add_apply, unop_add]
    simp only [← op_add]
    congr 1
    ring
  · -- B = single F_B r
    intro F_B r
    let B_single : ConnesKreimer ℤ (Nonplanar α) := ConnesKreimer.single F_B r
    show insertion
        (op (A * B_single))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
      op
        (unop (insertion (op A)
          (op (ConnesKreimer.of' ({v} : Multiset _)))) * B_single) +
      op
        (A * unop (insertion
          (op B_single)
          (op (ConnesKreimer.of' ({v} : Multiset _)))))
    have hB : B_single = r • (ConnesKreimer.of' F_B : ConnesKreimer ℤ (Nonplanar α)) :=
      ConnesKreimer.smul_single_one F_B r
    rw [hB]
    -- A * (r • of' F_B) = r • (A * of' F_B). Then op + insertion scale out.
    rw [mul_smul_comm, op_smul,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply, GL_insertion_leibniz_basis_right, op_smul,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    simp only [smul_add, unop_smul, mul_smul_comm, op_smul]

/-- **Helper**: `ckIso (ι (ofMultiset m)) = sum over m of of' {r}`. Used in
    the `ι w` case of `ckIso_circ_intertwine_basis_v`. -/
private theorem ckIso_ι_ofMultiset (m : Multiset (Nonplanar α)) :
    (ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofMultiset m)) :
      ConnesKreimer ℤ (Nonplanar α)) =
    (m.map (fun r => (ConnesKreimer.of' ({r} : Multiset _) : ConnesKreimer ℤ _))).sum := by
  induction m using Multiset.induction with
  | empty =>
    rw [InsertionAlgebra.ofMultiset_zero, map_zero, map_zero,
        Multiset.map_zero, Multiset.sum_zero]
  | cons a s ih =>
    rw [InsertionAlgebra.ofMultiset_cons, map_add, map_add, ih,
        Multiset.map_cons, Multiset.sum_cons]
    -- Need: ckIso (ι (ofTree a)) = of' {a}.
    congr 1
    show ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ _ (Finsupp.single a (1 : ℤ))) = _
    exact ckIsoSymmetricAlgebra_ι_single a

/-- **Helper for Substrate 1**: special case where `v` is a single basis
    tree `ofTree t` (so `ι v` corresponds to `of' {t}` on the GL side).

    Bilinearity-in-`v` extends this to the full substrate 1 via
    `Finsupp.induction_linear` on `v`.

    Proof by `SymmetricAlgebra.induction` on X, in 4 cases:
    * `algebraMap r`: `(r•1) ○ ι(ofTree t) = 0` (counit kills primitive);
      RHS: `insertion 1 (of' {t}) = 0`.
    * `ι w`: by Finsupp.induction_linear on w. Basis case `w = ofTree s`
      uses `circ_ι_ι` + `ofTree_mul_ofTree` + sub-substrate 1.2.
    * `mul X Y`: by `oudomGuinCirc_mul_ι` (Leibniz form) + IHs +
      sub-substrate 1.3 (`GL_insertion_leibniz_left_singleton_guest`).
    * `add X Y`: linearity. -/
private theorem ckIso_circ_intertwine_basis_v
    (X : SymmetricAlgebra ℤ (InsertionAlgebra α)) (t : Nonplanar α) :
    (ckIsoSymmetricAlgebra (oudomGuinCirc X
        (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) :
      ConnesKreimer ℤ (Nonplanar α)) =
    unop
      (insertion (op (ckIsoSymmetricAlgebra X))
        (op (ConnesKreimer.of' ({t} : Multiset _)))) := by
  induction X using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- LHS: (algebraMap r) ○ ι(ofTree t) = r • algebraMap (counit (ι(ofTree t)))
    --     = r • algebraMap 0 = 0 (since counit_ι = 0).
    rw [oudomGuinCirc_eq_ofConv, AlgHom.commutes,
        LinearMap.convAlgebraMap_apply, SymmetricAlgebra.counit_ι]
    -- Goal at this point: ckIso (r • algebraMap 0) = ...
    show ckIsoSymmetricAlgebra (r • (algebraMap ℤ
        (SymmetricAlgebra ℤ (InsertionAlgebra α)) 0)) = _
    rw [(algebraMap ℤ (SymmetricAlgebra ℤ (InsertionAlgebra α))).map_zero,
        smul_zero, map_zero]
    -- RHS: insertion (op (ckIso (algebraMap r))) (op (of' {t})) =
    --      insertion (r • op 1) (op (of' {t})) = r • insertion 1 (of' {t}) = r • 0 = 0.
    show (0 : ConnesKreimer ℤ (Nonplanar α)) =
      unop (insertion
        (op (ckIsoSymmetricAlgebra
          (algebraMap ℤ (SymmetricAlgebra ℤ (InsertionAlgebra α)) r)))
        (op (ConnesKreimer.of' ({t} : Multiset _))))
    rw [AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one]
    -- `op (r • 1)` and `r • (1 : GrossmanLarson)` are both `⟨r • 1⟩`; normalize
    -- the smul to the GL unit by defeq (avoids a `SMul ℤ` instance mismatch
    -- between `Algebra.toSMul` and the structural `SMul ℤ`).
    show (0 : ConnesKreimer ℤ (Nonplanar α)) =
      unop (insertion
        (r • (1 : GrossmanLarson ℤ α))
        (op (ConnesKreimer.of' ({t} : Multiset _))))
    rw [(insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    -- Goal: 0 = (r • insertion 1 (op (of' {t}))).unop
    rw [show op (ConnesKreimer.of' ({t} : Multiset (Nonplanar α))) =
            of' ({t} : Multiset _) from rfl]
    rw [insertion_one_of'_ne_zero ({t} : Multiset _)
          (Multiset.singleton_ne_zero t),
        smul_zero, unop_zero]
  | add X Y ih_X ih_Y =>
    -- LHS: ckIso ((X + Y) ○ ι(ofTree t)) = ckIso (X ○ ι _ + Y ○ ι _)
    --    = ckIso (X ○ ι _) + ckIso (Y ○ ι _).
    have h_add :
        oudomGuinCirc (R := ℤ) (X + Y)
            (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) =
          oudomGuinCirc (R := ℤ) X (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) +
          oudomGuinCirc (R := ℤ) Y (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) := by
      rw [oudomGuinCirc_eq_ofConv, map_add, WithConv.ofConv_add, LinearMap.add_apply,
          ← oudomGuinCirc_eq_ofConv, ← oudomGuinCirc_eq_ofConv]
    rw [h_add, map_add, ih_X, ih_Y]
    -- RHS: unop (insertion (op (ckIso (X + Y))) (op (of' {t}))).
    --    = unop (insertion (op (ckIso X + ckIso Y)) (op (of' {t})))   [ckIso preserves +]
    --    = unop (insertion (op (ckIso X) + op (ckIso Y)) (op (of' {t})))   [op preserves +]
    --    = unop (insertion (op (ckIso X)) _ + insertion (op (ckIso Y)) _)   [insertion linear]
    --    = unop (insertion (op (ckIso X)) _) + unop (insertion (op (ckIso Y)) _)   [unop preserves +]
    rw [show ckIsoSymmetricAlgebra (X + Y) =
            ckIsoSymmetricAlgebra X + ckIsoSymmetricAlgebra Y from map_add _ _ _,
        op_add,
        (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, unop_add]
  | ι w =>
    -- w : InsertionAlgebra α. Use Finsupp.induction_linear.
    refine Finsupp.induction_linear w ?_ ?_ ?_
    · -- w = 0: ι 0 = 0; both sides 0.
      show ckIsoSymmetricAlgebra ((oudomGuinCirc
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0))
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            unop ((insertion
              (op (ckIsoSymmetricAlgebra
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0))))
              (op (ConnesKreimer.of' ({t} : Multiset _))))
      rw [LinearMap.map_zero (SymmetricAlgebra.ι ℤ (InsertionAlgebra α))]
      rw [show oudomGuinCirc (R := ℤ) (0 : SymmetricAlgebra ℤ _)
                (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) = 0 by
            rw [oudomGuinCirc_eq_ofConv, map_zero, WithConv.ofConv_zero,
                LinearMap.zero_apply]]
      simp only [map_zero, op_zero,
                 (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_zero,
                 LinearMap.zero_apply, unop_zero]
    · -- w = w₁ + w₂: linearity in w.
      intro w₁ w₂ ih₁ ih₂
      let w₁' : InsertionAlgebra α := w₁
      let w₂' : InsertionAlgebra α := w₂
      show ckIsoSymmetricAlgebra ((oudomGuinCirc
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (w₁' + w₂')))
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            unop ((insertion
              (op (ckIsoSymmetricAlgebra
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (w₁' + w₂')))))
              (op (ConnesKreimer.of' ({t} : Multiset _))))
      rw [LinearMap.map_add (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) w₁' w₂']
      rw [show oudomGuinCirc (R := ℤ)
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w₁' +
                SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w₂')
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) =
            oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ _ w₁') _ +
            oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ _ w₂') _ from by
          rw [oudomGuinCirc_eq_ofConv, map_add, WithConv.ofConv_add,
              LinearMap.add_apply,
              ← oudomGuinCirc_eq_ofConv, ← oudomGuinCirc_eq_ofConv]]
      rw [map_add, ih₁, ih₂, map_add, op_add,
          (insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
          LinearMap.add_apply, unop_add]
    · -- w = single s r: scalar reduction via Algebra.smul_def detour.
      intro s r
      letI : SMulCommClass ℤ ℤ (SymmetricAlgebra ℤ (InsertionAlgebra α)) :=
        smulCommClass_self ℤ (SymmetricAlgebra ℤ (InsertionAlgebra α))
      let w_single : InsertionAlgebra α := Finsupp.single s r
      have hw : w_single = r • InsertionAlgebra.ofTree s := by
        show (Finsupp.single s r : InsertionAlgebra α) =
              r • (Finsupp.single s 1 : InsertionAlgebra α)
        exact (Finsupp.smul_single_one s r).symm
      show ckIsoSymmetricAlgebra ((oudomGuinCirc
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w_single))
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            unop ((insertion
              (op (ckIsoSymmetricAlgebra
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w_single))))
              (op (ConnesKreimer.of' ({t} : Multiset _))))
      have lhs_reduce : ckIsoSymmetricAlgebra ((oudomGuinCirc
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w_single))
                (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            r • ckIsoSymmetricAlgebra ((oudomGuinCirc
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                  (InsertionAlgebra.ofTree s)))
                (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) := by
        rw [hw]
        rw [(SymmetricAlgebra.ι ℤ (InsertionAlgebra α)).map_smul r _]
        rw [oudomGuinCirc_eq_ofConv]
        simp only [_root_.map_smul, WithConv.ofConv_smul]
        rw [← oudomGuinCirc_eq_ofConv]
        exact ckIsoSymmetricAlgebra.toLinearEquiv.map_smul r _
      have rhs_reduce : unop ((insertion
                (op (ckIsoSymmetricAlgebra
                  (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w_single))))
                (op (ConnesKreimer.of' ({t} : Multiset _)))) =
            r • unop ((insertion
                (op (ckIsoSymmetricAlgebra
                  (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                    (InsertionAlgebra.ofTree s)))))
                (op (ConnesKreimer.of' ({t} : Multiset _)))) := by
        rw [hw]
        simp only [_root_.map_smul, op_smul, unop_smul, LinearMap.smul_apply]
      rw [lhs_reduce, rhs_reduce]
      -- Reduce to basis-basis case.
      congr 1
      rw [circ_ι_ι, InsertionAlgebra.ofTree_mul_ofTree, ckIso_ι_ofMultiset]
      rw [show ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ _
              (InsertionAlgebra.ofTree s)) =
            ConnesKreimer.of' ({s} : Multiset _) from by
          show ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ _
                (Finsupp.single s (1 : ℤ))) = _
          exact ckIsoSymmetricAlgebra_ι_single s]
      rw [show op (ConnesKreimer.of' ({s} : Multiset (Nonplanar α))) =
              of' ({s} : Multiset _) from rfl,
          show op (ConnesKreimer.of' ({t} : Multiset (Nonplanar α))) =
              of' ({t} : Multiset _) from rfl,
          insertion_of'_of']
      show ((Nonplanar.insertSum s t).map fun r' =>
              (ConnesKreimer.of' ({r'} : Multiset (Nonplanar α)) :
                ConnesKreimer ℤ _)).sum =
          unop (insertionBasis ({s} : Multiset _)
              ({t} : Multiset _))
      rw [show insertionBasis ({s} : Multiset (Nonplanar α))
              ({t} : Multiset _) =
            ((Nonplanar.insertionMultiset ({s} : Multiset _) ({t} : Multiset _)).map
              fun F' => (of' (R := ℤ) F' :
                GrossmanLarson ℤ α)).sum from rfl,
          nonplanar_insertionMultiset_singletons s t,
          Multiset.map_map]
      rfl
  | mul X Y ih_X ih_Y =>
    -- LHS: `(X * Y) ○ ι(ofTree t) = (X ○ ι _) * Y + X * (Y ○ ι _)` (Leibniz)
    --      then ckIso preserves * and +, apply IHs.
    rw [oudomGuinCirc_mul_ι, map_add, map_mul, map_mul, ih_X, ih_Y]
    -- RHS: ckIso (X * Y) = ckIso X * ckIso Y, then apply sub-substrate 1.3
    -- and unop the result.
    rw [show ckIsoSymmetricAlgebra (X * Y) =
            ckIsoSymmetricAlgebra X * ckIsoSymmetricAlgebra Y from map_mul _ _ _]
    rw [GL_insertion_leibniz_left_singleton_guest]
    -- RHS after 1.3: unop (op (unop (insertion (op (ckIso X)) (op (of' {t}))) * ckIso Y) +
    --                       op (ckIso X * unop (insertion (op (ckIso Y)) (op (of' {t})))))
    -- = unop (op (unop_thing * ckIso Y) + op (ckIso X * unop_thing)) [unop_add]
    -- = unop_thing * ckIso Y + ckIso X * unop_thing [unop ∘ op = id]
    show unop (insertion (op (ckIsoSymmetricAlgebra X))
            (op (ConnesKreimer.of' ({t} : Multiset _)))) * ckIsoSymmetricAlgebra Y +
        ckIsoSymmetricAlgebra X *
          unop (insertion (op (ckIsoSymmetricAlgebra Y))
            (op (ConnesKreimer.of' ({t} : Multiset _)))) =
      unop (op
        (unop (insertion (op (ckIsoSymmetricAlgebra X))
          (op (ConnesKreimer.of' ({t} : Multiset _)))) * ckIsoSymmetricAlgebra Y) +
        op
          (ckIsoSymmetricAlgebra X *
            unop (insertion (op (ckIsoSymmetricAlgebra Y))
              (op (ConnesKreimer.of' ({t} : Multiset _))))))
    rw [unop_add]
    -- unop (op X) = X (unop ∘ op = id)
    rfl

/-- **Substrate 1 for Q5c**: `ckIso` intertwines OG ○ with GL insertion.

    For all X ∈ S(L), v ∈ L: `ckIso(X ○ ι v) = unop (insertion (op (ckIso X))
    (op (ckIso (ι v))))`.

    Proof structure (induction on X via `SymmetricAlgebra.induction`,
    generalizing v):

    * `algebraMap r`: trivial. `(r•1) ○ ι v = r • (ε(ιv) • 1) = 0` since
      `ε(ιv) = 0` for primitive `ιv`. RHS reduces to `r • 0 = 0` since
      `insertion (op (of' 0)) (of' {v}) = 0` (no original vertices to graft
      into for empty host).
    * `add`: linearity + IHs.
    * `ι w`: basis case. Uses `circ_ι_ι` (`ι w ○ ι w' = ι(w·w')`),
      `ofTree_mul_ofTree` (`w·w' = ofMultiset (Nonplanar.insertSum t_w t_{w'})`
      for basis w, w'), `ckIsoSymmetricAlgebra_ι_single` for the ckIso side,
      and **sub-substrate 1.2** to identify the multiset structure with
      `insertionMultiset` singletons. By v-linearity reduces to basis v.
    * `mul X_1 X_2`: uses Prop 2.7.iii (`circ_mul_distrib_via_comul`) on
      LHS to decompose `(X_1·X_2) ○ ιv = (X_1○ιv)·X_2 + X_1·(X_2○ιv)`
      (after `comul_ι` + `circ_one_right`); IHs at X_1 and X_2; then
      **sub-substrate 1.3** (GL Leibniz) on RHS.

    Uses sub-substrates 1.1, 1.2, 1.3 above. -/
private theorem ckIso_circ_intertwine_insertion
    (X : SymmetricAlgebra ℤ (InsertionAlgebra α))
    (v : InsertionAlgebra α) :
    (ckIsoSymmetricAlgebra (oudomGuinCirc X (SymmetricAlgebra.ι ℤ _ v)) :
      ConnesKreimer ℤ (Nonplanar α)) =
    unop
      (insertion (op (ckIsoSymmetricAlgebra X))
        (op (ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ _ v)))) := by
  -- v-induction: both sides linear in v.
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · -- v = 0: ι 0 = 0; both sides 0.
    show ckIsoSymmetricAlgebra (oudomGuinCirc X
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0)) =
        unop (insertion
          (op (ckIsoSymmetricAlgebra X))
          (op (ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0))))
    rw [LinearMap.map_zero (SymmetricAlgebra.ι ℤ (InsertionAlgebra α))]
    simp only [(oudomGuinCirc (R := ℤ) X).map_zero,
               map_zero, op_zero,
               ((insertion (R := ℤ) (α := α)
                 (op (ckIsoSymmetricAlgebra X))).map_zero),
               unop_zero]
  · -- v = v₁ + v₂: linearity in v.
    intro v₁ v₂ ih₁ ih₂
    let v₁' : InsertionAlgebra α := v₁
    let v₂' : InsertionAlgebra α := v₂
    show ckIsoSymmetricAlgebra (oudomGuinCirc X
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (v₁' + v₂'))) =
        unop (insertion
          (op (ckIsoSymmetricAlgebra X))
          (op (ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (v₁' + v₂')))))
    rw [LinearMap.map_add (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) v₁' v₂',
        (oudomGuinCirc (R := ℤ) X).map_add, map_add, ih₁, ih₂,
        map_add, op_add,
        ((insertion (R := ℤ) (α := α)
          (op (ckIsoSymmetricAlgebra X))).map_add _ _), unop_add]
  · -- v = single t r: scalar reduction to basis case; apply helper.
    intro t r
    let v_single : InsertionAlgebra α := Finsupp.single t r
    have hv : v_single = r • InsertionAlgebra.ofTree t := by
      show (Finsupp.single t r : InsertionAlgebra α) =
            r • (Finsupp.single t 1 : InsertionAlgebra α)
      exact (Finsupp.smul_single_one t r).symm
    -- Construct the LHS and RHS at v = ofTree t (helper case) and scale by r.
    have h_basis := ckIso_circ_intertwine_basis_v X t
    -- LHS at v_single: linear in v through ι, oudomGuinCirc X, ckIso.
    -- RHS at v_single: linear in v through ι, ckIso, op, insertion(..,·), unop.
    -- Both reduce to r • (helper LHS) = r • (helper RHS).
    show ckIsoSymmetricAlgebra ((oudomGuinCirc X)
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v_single)) =
        unop ((insertion
          (op (ckIsoSymmetricAlgebra X)))
          (op (ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v_single))))
    -- Reduce LHS to r • (helper LHS form) via linearity.
    have lhs_reduce : ckIsoSymmetricAlgebra ((oudomGuinCirc X)
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v_single)) =
          r • ckIsoSymmetricAlgebra ((oudomGuinCirc X)
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
              (InsertionAlgebra.ofTree t))) := by
      rw [hv]
      -- Carefully: factor out r through ι, oudomGuinCirc, ckIso.
      rw [show SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
              (r • InsertionAlgebra.ofTree t) =
            r • SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
              (InsertionAlgebra.ofTree t) from
          (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)).map_smul r _]
      rw [show (oudomGuinCirc (R := ℤ) X)
              (r • SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) =
            r • (oudomGuinCirc (R := ℤ) X)
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) from
          (oudomGuinCirc (R := ℤ) X).map_smul r _]
      exact ckIsoSymmetricAlgebra.toLinearEquiv.map_smul r _
    have rhs_reduce : unop ((insertion
            (op (ckIsoSymmetricAlgebra X)))
            (op (ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v_single)))) =
          r • unop ((insertion
            (op (ckIsoSymmetricAlgebra X)))
            (op (ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                (InsertionAlgebra.ofTree t))))) := by
      rw [hv]
      rw [show SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
              (r • InsertionAlgebra.ofTree t) =
            r • SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
              (InsertionAlgebra.ofTree t) from
          (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)).map_smul r _]
      rw [show ckIsoSymmetricAlgebra (r • SymmetricAlgebra.ι ℤ _
                (InsertionAlgebra.ofTree t)) =
            r • ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ _
                (InsertionAlgebra.ofTree t)) from
          ckIsoSymmetricAlgebra.toLinearEquiv.map_smul r _]
      rw [op_smul]
      rw [((insertion (R := ℤ) (α := α)
            (op (ckIsoSymmetricAlgebra X))).map_smul r _)]
      rw [unop_smul]
    rw [lhs_reduce, rhs_reduce, h_basis]
    -- Now: r • (insertion ... (op (of' {t}))).unop =
    --      r • (insertion ... (op (ckIso (ι (ofTree t))))).unop
    -- Equal since ckIso (ι (ofTree t)) = of' {t}.
    rw [show ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (InsertionAlgebra.ofTree t)) =
          ConnesKreimer.of' ({t} : Multiset _) from
        ckIsoSymmetricAlgebra_ι_single t]

/-! ### Substrate 2: GL guest-splitting identity (OG Prop 2.7(ii) GL side)

The four-term identity below is the GL-side analog of Oudom-Guin's
splitting lemma (Prop 2.7(ii)). It is the route for the per-tprod
`m+1` induction of `gl_product_eq_oudomGuinStar_tprod`, using the
singleton case `Nonplanar.insertionMultiset_singleton_assoc`. -/

/-- **Helper for substrate 2**: iterated single-guest insertion
    `ins (ins F (of' C)) (op of'{v})` splits into a "single-shot"
    `ins F (of' (C + {v}))` term plus a sum over `Y ∈ NIM C {v}`
    of `ins F (of' Y)`. The basis case `F = of' A` follows directly
    from `insertion_of'_of'` (twice) plus
    `Nonplanar.insertionMultiset_singleton_assoc`. -/
private theorem GL_iterated_insertion_singleton_v
    (F : GrossmanLarson ℤ α) (C : Forest (Nonplanar α)) (v : Nonplanar α) :
    insertion
        (insertion F (ConnesKreimer.of' C))
        (op (ConnesKreimer.of' ({v} : Multiset _))) =
      insertion F (ConnesKreimer.of' (C + {v})) +
      ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
        (fun Y => insertion F (ConnesKreimer.of' Y))).sum := by
  -- Define helper LinearMaps for cleaner manipulation.
  set ins : GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α :=
    insertion with hins
  -- Linearize F. Both sides are F-linear by bilinearity of `insertion`.
  refine ConnesKreimer.induction_linear F ?_ ?_ ?_
  · -- F = 0: both sides reduce to 0.
    show ins (ins 0 (ConnesKreimer.of' C))
          (op (ConnesKreimer.of' ({v} : Multiset _))) =
        ins 0 (ConnesKreimer.of' (C + {v})) +
        ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins 0 (ConnesKreimer.of' Y))).sum
    have h_ins_zero : ∀ Y : GrossmanLarson ℤ α, ins 0 Y = 0 := fun Y =>
      (ins.flip Y).map_zero
    rw [h_ins_zero, h_ins_zero, h_ins_zero, zero_add]
    symm
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨Y, _, hY_eq⟩ := hx
    rw [← hY_eq]
    exact h_ins_zero _
  · -- F = F₁ + F₂: by linearity in F on both sides.
    intro F₁ F₂ ih₁ ih₂
    let F₁' : GrossmanLarson ℤ α := F₁
    let F₂' : GrossmanLarson ℤ α := F₂
    show ins (ins (F₁' + F₂') (ConnesKreimer.of' C))
          (op (ConnesKreimer.of' ({v} : Multiset _))) =
        ins (F₁' + F₂') (ConnesKreimer.of' (C + {v})) +
        ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins (F₁' + F₂') (ConnesKreimer.of' Y))).sum
    -- Use a uniform "insertion respects + in first arg" helper:
    have hins_add_left : ∀ (X Y : GrossmanLarson ℤ α) (Z : GrossmanLarson ℤ α),
        ins (X + Y) Z = ins X Z + ins Y Z := fun X Y Z => by
      rw [show ins (X + Y) = ins X + ins Y from ins.map_add X Y]
      rfl
    have hinner : ins (F₁' + F₂') (ConnesKreimer.of' C : GrossmanLarson ℤ α) =
        ins F₁' (ConnesKreimer.of' C : GrossmanLarson ℤ α) +
        ins F₂' (ConnesKreimer.of' C : GrossmanLarson ℤ α) :=
      hins_add_left F₁' F₂' _
    rw [show ins (F₁' + F₂') (ConnesKreimer.of' C) =
            ins F₁' (ConnesKreimer.of' C : GrossmanLarson ℤ α) +
            ins F₂' (ConnesKreimer.of' C : GrossmanLarson ℤ α) from hinner]
    rw [hins_add_left]
    rw [ih₁, ih₂]
    rw [show ins (F₁' + F₂') (ConnesKreimer.of' (C + {v})) =
            ins F₁' (ConnesKreimer.of' (C + {v}) : GrossmanLarson ℤ α) +
            ins F₂' (ConnesKreimer.of' (C + {v}) : GrossmanLarson ℤ α) from
        hins_add_left F₁' F₂' _]
    have h_split_sum :
        ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins (F₁' + F₂') (ConnesKreimer.of' Y : GrossmanLarson ℤ α))).sum =
        ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins F₁' (ConnesKreimer.of' Y : GrossmanLarson ℤ α))).sum +
        ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins F₂' (ConnesKreimer.of' Y : GrossmanLarson ℤ α))).sum := by
      rw [← Multiset.sum_map_add]
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro Y _
      exact hins_add_left F₁' F₂' _
    rw [h_split_sum]
    abel
  · -- F = single A r — basis case.
    intro A r
    let F_single : GrossmanLarson ℤ α := ConnesKreimer.single A r
    show ins (ins F_single (ConnesKreimer.of' C))
          (op (ConnesKreimer.of' ({v} : Multiset _))) =
        ins F_single (ConnesKreimer.of' (C + {v})) +
        ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins F_single (ConnesKreimer.of' Y))).sum
    -- ins is bilinear; reduce F_single = r • of' A.
    have hF : F_single = r • (of' A : GrossmanLarson ℤ α) :=
      ConnesKreimer.smul_single_one A r
    rw [hF]
    -- Helper: insertion respects smul in first arg.
    have hins_smul_left : ∀ (X Z : GrossmanLarson ℤ α),
        ins (r • X) Z = r • ins X Z := fun X Z => by
      rw [show ins (r • X) = r • ins X from ins.map_smul r X]
      rfl
    rw [hins_smul_left]
    -- Now LHS has `ins (r • ins (of'A) (of'C)) (op of'{v}) = r • ins (ins (of'A) (of'C)) (op of'{v})`
    rw [show ins (r • ins (of' A : GrossmanLarson ℤ α)
                  (ConnesKreimer.of' C : GrossmanLarson ℤ α))
              (op (ConnesKreimer.of' ({v} : Multiset _))) =
            r • ins (ins (of' A : GrossmanLarson ℤ α)
                  (ConnesKreimer.of' C : GrossmanLarson ℤ α))
              (op (ConnesKreimer.of' ({v} : Multiset _))) from
        hins_smul_left _ _]
    rw [hins_smul_left]
    -- Sum side: pull r out.
    have h_smul_sum :
        ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins (r • (of' A : GrossmanLarson ℤ α))
            (ConnesKreimer.of' Y : GrossmanLarson ℤ α))).sum =
        r • ((Nonplanar.insertionMultiset C ({v} : Multiset _)).map
          (fun Y => ins (of' A : GrossmanLarson ℤ α)
            (ConnesKreimer.of' Y : GrossmanLarson ℤ α))).sum := by
      rw [Multiset.smul_sum, Multiset.map_map]
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro Y _
      exact hins_smul_left _ _
    rw [h_smul_sum, ← smul_add]
    -- Reduce to basis identity at F = of' A.
    congr 1
    -- Basis identity: ins(ins(of'A)(of'C))(op of'{v}) = ins(of'A)(of'(C+{v})) +
    --                                                  Σ_{Y ∈ NIM C {v}} ins(of'A)(of'Y)
    rw [hins]
    show insertion
        (insertion (of' A : GrossmanLarson ℤ α)
          (of' C : GrossmanLarson ℤ α))
        (of' ({v} : Multiset _) : GrossmanLarson ℤ α) = _
    rw [insertion_of'_of']
    -- Inner: insertionBasis A C = (NIM A C).map of'.sum.
    show insertion
        (((Nonplanar.insertionMultiset A C).map
          fun F' => of' (R := ℤ) F').sum)
        (of' ({v} : Multiset _) : GrossmanLarson ℤ α) = _
    -- Push insertion through the sum via insertion_sum_left.
    rw [insertion_sum_left, Multiset.map_map]
    -- Per X ∈ NIM A C, insertion (of' X) (of' {v}) = insertionBasis X {v}.
    have h_per_X : ∀ X : Forest (Nonplanar α),
        insertion (of' X)
            (of' ({v} : Multiset _) : GrossmanLarson ℤ α) =
          ((Nonplanar.insertionMultiset X ({v} : Multiset _)).map
            fun F' => of' (R := ℤ) F').sum := by
      intro X
      rw [insertion_of'_of']
      rfl
    -- Rewrite the inner expression. After Multiset.map_map, the goal's map function
    -- has shape (fun X => insertion (of' X) (of'{v}) : GrossmanLarson ℤ α).
    rw [show ((fun (Y : GrossmanLarson ℤ α) =>
              insertion Y
                (of' ({v} : Multiset _) : GrossmanLarson ℤ α)) ∘
              fun (F' : Forest (Nonplanar α)) => of' (R := ℤ) F') =
          (fun X : Forest (Nonplanar α) =>
            ((Nonplanar.insertionMultiset X ({v} : Multiset _)).map
              fun F' => of' (R := ℤ) F').sum) from by
        funext X
        exact h_per_X X]
    -- Push the outer sum: ((bind).map of').sum form.
    rw [show ((Nonplanar.insertionMultiset A C).map
              (fun X => ((Nonplanar.insertionMultiset X ({v} : Multiset _)).map
                fun F' => of' (R := ℤ) F').sum)).sum =
            (((Nonplanar.insertionMultiset A C).bind
                fun X => Nonplanar.insertionMultiset X ({v} : Multiset _)).map
              fun F' => of' (R := ℤ) F').sum from by
          rw [Multiset.map_bind, Multiset.sum_bind]]
    -- Apply insertionMultiset_singleton_assoc.
    rw [Nonplanar.insertionMultiset_singleton_assoc]
    rw [Multiset.map_add, Multiset.sum_add]
    congr 1
    · -- Left: NIM A (C + {v}) → ins (of' A) (of' (C+{v})) = insertionBasis A (C+{v}).
      rw [show insertion (of' A : GrossmanLarson ℤ α)
                  (ConnesKreimer.of' (C + {v}) : GrossmanLarson ℤ α) =
              insertion (of' A : GrossmanLarson ℤ α)
                (of' (C + {v}) : GrossmanLarson ℤ α) from rfl,
          insertion_of'_of']
      rfl
    · -- Right: (NIM C {v}).bind (NIM A ·) → Σ_{Y ∈ NIM C {v}} ins (of'A) (of'Y).
      rw [Multiset.map_bind, Multiset.sum_bind]
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro Y _
      rw [show (ConnesKreimer.of' Y : GrossmanLarson ℤ α) =
              (of' Y : GrossmanLarson ℤ α) from rfl,
          insertion_of'_of']
      rfl

/-- Generic "swap two outer sums" lemma. Used in `GL_T2_reindexing_key`. -/
private theorem swap_sum_map_sum {β γ δ : Type*} [AddCommMonoid δ]
    (s : Multiset β) (t : Multiset γ) (f : γ → β → δ) :
    (s.map (fun b => (t.map (fun c => f c b)).sum)).sum =
    (t.map (fun c => (s.map (fun b => f c b)).sum)).sum := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, Multiset.sum_zero]
    -- RHS: (t.map (fun c => (0.map _).sum)).sum = (t.map (fun _ => 0)).sum = 0.
    symm
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨c, _, hc_eq⟩ := hx
    rw [← hc_eq, Multiset.map_zero, Multiset.sum_zero]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Multiset.sum_map_add]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro c _
    rw [Multiset.map_cons, Multiset.sum_cons]

/-- Sum of a bind of singletons equals the sum of the map. -/
private theorem sum_bind_singleton {γ δ : Type*} [AddCommMonoid δ]
    (s : Multiset γ) (f : γ → δ) :
    (s.bind fun x => ({f x} : Multiset δ)).sum = (s.map f).sum := by
  rw [Multiset.bind_singleton]

omit [DecidableEq α] in
/-- Helper: `mk`-image of the t-bucket of a List (RoseTree α). -/
private theorem zip_filter_t_map_mk (L : List (RoseTree α)) (m : List Bool) :
    ((L.map Nonplanar.mk).zip m).filterMap
        (fun p : Nonplanar α × Bool => if p.snd then some p.fst else none) =
      ((L.zip m).filterMap
        (fun p : RoseTree α × Bool => if p.snd then some p.fst else none)).map
          Nonplanar.mk := by
  induction L generalizing m with
  | nil => rfl
  | cons x L ih =>
    cases m with
    | nil => rfl
    | cons b m =>
      cases b with
      | true =>
        show Nonplanar.mk x :: (((L.map Nonplanar.mk).zip m).filterMap _) =
          (x :: ((L.zip m).filterMap _)).map Nonplanar.mk
        rw [ih m]; rfl
      | false => exact ih m

omit [DecidableEq α] in
/-- Helper: `mk`-image of the f-bucket of a List (RoseTree α). -/
private theorem zip_filter_f_map_mk (L : List (RoseTree α)) (m : List Bool) :
    ((L.map Nonplanar.mk).zip m).filterMap
        (fun p : Nonplanar α × Bool => if p.snd then none else some p.fst) =
      ((L.zip m).filterMap
        (fun p : RoseTree α × Bool => if p.snd then none else some p.fst)).map
          Nonplanar.mk := by
  induction L generalizing m with
  | nil => rfl
  | cons x L ih =>
    cases m with
    | nil => rfl
    | cons b m =>
      cases b with
      | true => exact ih m
      | false =>
        show Nonplanar.mk x :: (((L.map Nonplanar.mk).zip m).filterMap _) =
          (x :: ((L.zip m).filterMap _)).map Nonplanar.mk
        rw [ih m]; rfl

/-- **T2 reindexing key step**: the multiset-level reindexing that
    expresses `F * insertion (op (of' B)) (op of'{v})` (expanded via
    `mul_of'_sum_form` over `NIM B {v}`) as a sum over `B.powerset`.
    This is the `RoseTree`-level bucket-split lemma after descent through
    `listChoices_bridge_powerset_paired`.

    Stated abstractly to be reusable: for any consumer `g`, the LHS sum
    (over `X' ∈ NIM B {v}`, then `D ⊆ X'`) equals the RHS sum (over
    `C₁ ⊆ B`, splitting whether `v` lands in the powerset side or its
    complement). -/
private theorem GL_T2_reindexing_key
    (B : Forest (Nonplanar α)) (v : Nonplanar α)
    (g : Multiset (Nonplanar α) → Multiset (Nonplanar α) → GrossmanLarson ℤ α) :
    ((Nonplanar.insertionMultiset B ({v} : Multiset _)).map (fun X' =>
        (X'.powerset.map fun D => g D (X' - D)).sum)).sum =
      (B.powerset.map fun C₁ =>
        ((Nonplanar.insertionMultiset C₁ ({v} : Multiset _)).map
            (fun Y => g Y (B - C₁))).sum +
        ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
            (fun Y' => g C₁ Y')).sum).sum := by
  -- Canonical `RoseTree`-level reps.
  set B_pl : List (RoseTree α) := B.toList.map Quotient.out with hB_pl_def
  set ov : RoseTree α := Quotient.out v with hov_def
  -- Mask filterMaps (RoseTree α).
  set tp : RoseTree α × Bool → Option (RoseTree α) :=
    fun p => if p.snd then some p.fst else none with htp_def
  set fp : RoseTree α × Bool → Option (RoseTree α) :=
    fun p => if p.snd then none else some p.fst with hfp_def
  -- msform : List (RoseTree α) → Multiset (Nonplanar α).
  set msform : List (RoseTree α) → Multiset (Nonplanar α) :=
    fun L => (↑(L.map Nonplanar.mk) : Multiset (Nonplanar α)) with hmsform_def
  -- §0: every B' ∈ iF B_pl [ov] has length B_pl.length.
  have hB'_len : ∀ B' ∈ RoseTree.Pathed.insertionForest B_pl [ov],
      B'.length = B_pl.length := by
    intro B' hB'
    rw [RoseTree.Pathed.insertionForest_singleton_guest_set] at hB'
    rw [Multiset.mem_bind] at hB'
    obtain ⟨k, _, hk⟩ := hB'
    rw [Multiset.mem_map] at hk
    obtain ⟨_, _, hk'⟩ := hk
    rw [← hk', List.length_set]
  -- §0b: B_pl.map mk recovers B.toList; ↑B_pl.toList recovers B.
  have h_B_pl_map_mk : B_pl.map Nonplanar.mk = B.toList := by
    rw [hB_pl_def, List.map_map]
    exact (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
  have hB_eq_msform_Bpl : B = msform B_pl := by
    show B = (↑(B_pl.map Nonplanar.mk) : Multiset (Nonplanar α))
    rw [h_B_pl_map_mk]; exact B.coe_toList.symm
  -- §1: rewrite NIM B {v} as the canonical `RoseTree`-level bind.
  have hNIM_B : Nonplanar.insertionMultiset B ({v} : Multiset _) =
      (RoseTree.Pathed.insertionForest B_pl [ov]).map msform := by
    apply Nonplanar.insertionMultiset_eq_of_reps
    · show (Multiset.ofList ((B.toList.map Quotient.out).map Nonplanar.mk) :
            Multiset (Nonplanar α)) = B
      rw [← hB_pl_def, h_B_pl_map_mk]
      exact B.coe_toList
    · show (Multiset.ofList ([Nonplanar.mk (Quotient.out v)]) :
            Multiset (Nonplanar α)) = ({v} : Multiset _)
      rw [show Nonplanar.mk (Quotient.out v) = v from Quotient.out_eq v]; rfl
  -- §2: per-B' powerset bridge: rewrite the inner powerset.map sum via masks.
  have h_powerset_per_B' : ∀ B' ∈ RoseTree.Pathed.insertionForest B_pl [ov],
      ((msform B').powerset.map (fun D => g D (msform B' - D))).sum =
      ((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length)).map
        (fun assn => g (msform ((B'.zip assn).filterMap tp))
                       (msform ((B'.zip assn).filterMap fp)))).sum := by
    intro B' hB'
    have hlen := hB'_len B' hB'
    have h_len_mk : (B'.map Nonplanar.mk).length = B_pl.length := by
      rw [List.length_map]; exact hlen
    have h_bridge := RoseTree.Pathed.listChoices_bridge_powerset_paired
      (l := B'.map Nonplanar.mk)
    rw [h_len_mk] at h_bridge
    have h_post := congr_arg
      (Multiset.map (fun pr : Multiset (Nonplanar α) × Multiset (Nonplanar α) =>
        g pr.1 pr.2)) h_bridge
    rw [Multiset.map_map, Multiset.map_map] at h_post
    -- h_post:
    --   (lc).map (assn ↦ g (filter_t over mk-list) (filter_f over mk-list)) =
    --   (↑(B'.map mk)).powerset.map (s ↦ g s (↑(B'.map mk) - s))
    -- Take sums of both sides; the RHS unfolds to our (msform B').powerset.map sum.
    have h_sum_eq := congr_arg Multiset.sum h_post
    -- Goal LHS = h_sum_eq RHS (modulo defeq on msform B' = ↑(B'.map mk)).
    -- So flip h_sum_eq.
    show (((↑(B'.map Nonplanar.mk) : Multiset (Nonplanar α))).powerset.map
            (fun D => g D ((↑(B'.map Nonplanar.mk) : Multiset (Nonplanar α)) - D))).sum =
          ((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length)).map
            (fun assn => g (msform ((B'.zip assn).filterMap tp))
                           (msform ((B'.zip assn).filterMap fp)))).sum
    -- Reshape h_sum_eq RHS to use D : Multiset (Nonplanar α).
    have h_sum_rhs :
        (((↑(B'.map Nonplanar.mk) : Multiset (Nonplanar α))).powerset.map
            (fun D => g D ((↑(B'.map Nonplanar.mk) : Multiset (Nonplanar α)) - D))).sum =
        (((↑(B'.map Nonplanar.mk) : Multiset (Nonplanar α))).powerset.map
          ((fun pr : Multiset (Nonplanar α) × Multiset (Nonplanar α) => g pr.1 pr.2) ∘
            fun s => (s, (↑(B'.map Nonplanar.mk) : Multiset (Nonplanar α)) - s))).sum := by
      rfl
    rw [h_sum_rhs, ← h_sum_eq]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro assn _
    show g ((↑(((B'.map Nonplanar.mk).zip assn).filterMap
              (fun p : Nonplanar α × Bool => if p.snd then some p.fst else none)) :
              Multiset (Nonplanar α)))
         ((↑(((B'.map Nonplanar.mk).zip assn).filterMap
              (fun p : Nonplanar α × Bool => if p.snd then none else some p.fst)) :
              Multiset (Nonplanar α))) =
       g (msform ((B'.zip assn).filterMap tp)) (msform ((B'.zip assn).filterMap fp))
    congr 1
    · show (↑(((B'.map Nonplanar.mk).zip assn).filterMap
            (fun p : Nonplanar α × Bool => if p.snd then some p.fst else none)) :
            Multiset (Nonplanar α)) = msform ((B'.zip assn).filterMap tp)
      rw [zip_filter_t_map_mk B' assn]
    · show (↑(((B'.map Nonplanar.mk).zip assn).filterMap
            (fun p : Nonplanar α × Bool => if p.snd then none else some p.fst)) :
            Multiset (Nonplanar α)) = msform ((B'.zip assn).filterMap fp)
      rw [zip_filter_f_map_mk B' assn]
  -- §3: LHS = (iF B_pl [ov]).map (B' ↦ inner sum) |>.sum.
  rw [hNIM_B, Multiset.map_map]
  -- Now: ((iF B_pl [ov]).map ((fun X' => ...) ∘ msform)).sum
  -- Equivalent (by composition unfolding): ((iF B_pl [ov]).map (fun B' => (msform B').powerset.map ...).sum)).sum
  -- Use Multiset.map_congr with the composition-form lhs.
  rw [show ((RoseTree.Pathed.insertionForest B_pl [ov]).map
            ((fun X' => (X'.powerset.map fun D => g D (X' - D)).sum) ∘ msform)).sum =
        ((RoseTree.Pathed.insertionForest B_pl [ov]).map
          (fun B' => ((msform B').powerset.map (fun D => g D (msform B' - D))).sum)).sum
      from rfl]
  -- Per-B' rewrite via h_powerset_per_B'.
  rw [show ((RoseTree.Pathed.insertionForest B_pl [ov]).map
              (fun B' => ((msform B').powerset.map (fun D => g D (msform B' - D))).sum)).sum =
            ((RoseTree.Pathed.insertionForest B_pl [ov]).map
              (fun B' =>
                ((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length)).map
                  (fun assn => g (msform ((B'.zip assn).filterMap tp))
                                 (msform ((B'.zip assn).filterMap fp)))).sum)).sum
        from by
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro B' hB'
      exact h_powerset_per_B' B' hB']
  -- §4: swap outer/inner sums.
  rw [swap_sum_map_sum (RoseTree.Pathed.insertionForest B_pl [ov])
    (Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length))
    (fun assn B' => g (msform ((B'.zip assn).filterMap tp))
                      (msform ((B'.zip assn).filterMap fp)))]
  -- §5: per-mask, apply the bucket-split.
  have h_per_mask : ∀ assn ∈
      (Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length) :
        Multiset (List Bool)),
      ((RoseTree.Pathed.insertionForest B_pl [ov]).map
          (fun B' => g (msform ((B'.zip assn).filterMap tp))
                       (msform ((B'.zip assn).filterMap fp)))).sum =
        ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap tp) [ov]).map
            (fun W => g (msform W) (msform ((B_pl.zip assn).filterMap fp)))).sum +
        ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap fp) [ov]).map
            (fun W' => g (msform ((B_pl.zip assn).filterMap tp)) (msform W'))).sum := by
    intro assn h_mem
    have h_mem' : assn ∈ RoseTree.Pathed.listChoices [true, false] B_pl.length := by
      rwa [Multiset.mem_coe] at h_mem
    have hlen : assn.length = B_pl.length :=
      RoseTree.Pathed.mem_listChoices_length [true, false] B_pl.length assn h_mem'
    have hbucket := RoseTree.Pathed.insertionForest_singleton_bucket_split
      B_pl assn ov
      (fun L R => ({g (msform L) (msform R)} : Multiset (GrossmanLarson ℤ α))) hlen
    have h_apply := congr_arg Multiset.sum hbucket
    rw [Multiset.sum_add] at h_apply
    rw [sum_bind_singleton, sum_bind_singleton, sum_bind_singleton] at h_apply
    exact h_apply
  rw [Multiset.map_congr rfl h_per_mask]
  -- Bridge each mask-sum to a powerset sum via `listChoices_bridge_powerset_paired`.
  -- For both summands, we go from a function of `assn → ...` to a function of `(s_t, s_f) → ...`
  -- via the bridge.
  -- §7a: define the per-pair consumer FUN1 for the first mask sum.
  set FUN1 : Multiset (Nonplanar α) × Multiset (Nonplanar α) → GrossmanLarson ℤ α :=
    fun pr =>
      ((Nonplanar.insertionMultiset pr.1 ({v} : Multiset _)).map
        (fun Y => g Y pr.2)).sum with hFUN1_def
  set FUN2 : Multiset (Nonplanar α) × Multiset (Nonplanar α) → GrossmanLarson ℤ α :=
    fun pr =>
      ((Nonplanar.insertionMultiset pr.2 ({v} : Multiset _)).map
        (fun Y' => g pr.1 Y')).sum with hFUN2_def
  -- §7b: rewrite each per-mask term as FUN1(pair) and FUN2(pair).
  -- For mask assn:
  --   First per-mask term = FUN1 (msform B_pl_t, msform B_pl_f) by rep lemma + msform expansion.
  --   Second per-mask term = FUN2 (msform B_pl_t, msform B_pl_f) by rep lemma + msform expansion.
  -- Then sum over masks = sum over (mskform * mskform) pairs = (via bridge) sum over (s, B-s) pairs.
  -- We use `insertionMultiset_eq_of_reps` to recover NIM (msform L) {v} from (iF L [ov]).map msform.
  have h_assn_to_FUN1 : ∀ assn,
      ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap tp) [ov]).map
          (fun W => g (msform W) (msform ((B_pl.zip assn).filterMap fp)))).sum =
        FUN1 (msform ((B_pl.zip assn).filterMap tp),
              msform ((B_pl.zip assn).filterMap fp)) := by
    intro assn
    show ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap tp) [ov]).map
            (fun W => g (msform W) (msform ((B_pl.zip assn).filterMap fp)))).sum =
        ((Nonplanar.insertionMultiset
          (msform ((B_pl.zip assn).filterMap tp)) ({v} : Multiset _)).map
            (fun Y => g Y (msform ((B_pl.zip assn).filterMap fp)))).sum
    -- Use `insertionMultiset_eq_of_reps` to compute NIM(msform L_t) {v}.
    rw [show Nonplanar.insertionMultiset
          (msform ((B_pl.zip assn).filterMap tp)) ({v} : Multiset _) =
          (RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap tp) [ov]).map msform from by
        apply Nonplanar.insertionMultiset_eq_of_reps
        · rfl
        · show (Multiset.ofList ([Nonplanar.mk ov]) : Multiset (Nonplanar α)) = ({v} : Multiset _)
          rw [hov_def, show Nonplanar.mk (Quotient.out v) = v from Quotient.out_eq v]; rfl]
    rw [Multiset.map_map]
    rfl
  have h_assn_to_FUN2 : ∀ assn,
      ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap fp) [ov]).map
          (fun W' => g (msform ((B_pl.zip assn).filterMap tp)) (msform W'))).sum =
        FUN2 (msform ((B_pl.zip assn).filterMap tp),
              msform ((B_pl.zip assn).filterMap fp)) := by
    intro assn
    show ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap fp) [ov]).map
            (fun W' => g (msform ((B_pl.zip assn).filterMap tp)) (msform W'))).sum =
        ((Nonplanar.insertionMultiset
          (msform ((B_pl.zip assn).filterMap fp)) ({v} : Multiset _)).map
            (fun Y' => g (msform ((B_pl.zip assn).filterMap tp)) Y')).sum
    rw [show Nonplanar.insertionMultiset
          (msform ((B_pl.zip assn).filterMap fp)) ({v} : Multiset _) =
          (RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap fp) [ov]).map msform from by
        apply Nonplanar.insertionMultiset_eq_of_reps
        · rfl
        · show (Multiset.ofList ([Nonplanar.mk ov]) : Multiset (Nonplanar α)) = ({v} : Multiset _)
          rw [hov_def, show Nonplanar.mk (Quotient.out v) = v from Quotient.out_eq v]; rfl]
    rw [Multiset.map_map]
    rfl
  -- §7c: rewrite the mask-sums in this FUN1/FUN2 form.
  rw [show
      (((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length)).map
        (fun assn =>
          ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap tp) [ov]).map
              (fun W => g (msform W) (msform ((B_pl.zip assn).filterMap fp)))).sum +
          ((RoseTree.Pathed.insertionForest ((B_pl.zip assn).filterMap fp) [ov]).map
              (fun W' => g (msform ((B_pl.zip assn).filterMap tp)) (msform W'))).sum))).sum =
      ((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length)).map
        (fun assn =>
          FUN1 (msform ((B_pl.zip assn).filterMap tp),
                msform ((B_pl.zip assn).filterMap fp)) +
          FUN2 (msform ((B_pl.zip assn).filterMap tp),
                msform ((B_pl.zip assn).filterMap fp)))).sum
        from by
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro assn _
      rw [h_assn_to_FUN1 assn, h_assn_to_FUN2 assn]]
  -- §8: bridge the mask sum to a powerset sum.
  -- The mask `assn` maps to the pair `(msform ((B_pl.zip assn).filterMap tp), msform ((B_pl.zip assn).filterMap fp))`.
  -- The bridge `listChoices_bridge_powerset_paired` applied to `l := B.toList` gives:
  --   (lc).map (assn ↦ ((filter_t over B.toList), (filter_f over B.toList))) =
  --   (↑B.toList).powerset.map (s ↦ (s, ↑B.toList - s)) = B.powerset.map (s ↦ (s, B - s))
  -- since ↑B.toList = B.
  -- BUT our per-mask function uses `(B_pl.zip assn).filterMap tp` (`RoseTree`-level) — not `(B.toList.zip assn).filterMap tpN`.
  -- We need to bridge between these.
  -- `msform ((B_pl.zip assn).filterMap tp) = ↑(((B_pl.zip assn).filterMap tp).map mk)`
  --                                      = ↑((B_pl.map mk).zip assn).filter_tN  [by zip_filter_t_map_mk reverse]
  --                                      = ↑((B.toList.zip assn).filter_tN)      [by h_B_pl_map_mk]
  -- So `msform ((B_pl.zip assn).filterMap tp) = ((B.toList.zip assn).filterMap (fun p => if p.snd then some p.fst else none) : Multiset (Nonplanar α))`.
  -- This is exactly the first component of the bridge pair when applied to `l := B.toList`.
  have h_to_BtoList_t : ∀ assn,
      msform ((B_pl.zip assn).filterMap tp) =
        (((B.toList.zip assn).filterMap
          (fun p : Nonplanar α × Bool => if p.snd then some p.fst else none) :
          List (Nonplanar α)) : Multiset (Nonplanar α)) := by
    intro assn
    show (↑(((B_pl.zip assn).filterMap tp).map Nonplanar.mk) : Multiset (Nonplanar α)) = _
    rw [← zip_filter_t_map_mk B_pl assn, h_B_pl_map_mk]
  have h_to_BtoList_f : ∀ assn,
      msform ((B_pl.zip assn).filterMap fp) =
        (((B.toList.zip assn).filterMap
          (fun p : Nonplanar α × Bool => if p.snd then none else some p.fst) :
          List (Nonplanar α)) : Multiset (Nonplanar α)) := by
    intro assn
    show (↑(((B_pl.zip assn).filterMap fp).map Nonplanar.mk) : Multiset (Nonplanar α)) = _
    rw [← zip_filter_f_map_mk B_pl assn, h_B_pl_map_mk]
  -- Rewrite the goal-LHS using h_to_BtoList_t, h_to_BtoList_f, and h_B_pl_map_mk to substitute B_pl.length = B.toList.length.
  have hB_pl_len : B_pl.length = B.toList.length := by
    show (B.toList.map Quotient.out).length = B.toList.length
    rw [List.length_map]
    rfl
  rw [show
      ((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B_pl.length)).map
        (fun assn =>
          FUN1 (msform ((B_pl.zip assn).filterMap tp),
                msform ((B_pl.zip assn).filterMap fp)) +
          FUN2 (msform ((B_pl.zip assn).filterMap tp),
                msform ((B_pl.zip assn).filterMap fp)))).sum =
      ((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B.toList.length)).map
        (fun assn =>
          FUN1 (((B.toList.zip assn).filterMap
                  (fun p : Nonplanar α × Bool => if p.snd then some p.fst else none) :
                  Multiset (Nonplanar α)),
                ((B.toList.zip assn).filterMap
                  (fun p : Nonplanar α × Bool => if p.snd then none else some p.fst) :
                  Multiset (Nonplanar α))) +
          FUN2 (((B.toList.zip assn).filterMap
                  (fun p : Nonplanar α × Bool => if p.snd then some p.fst else none) :
                  Multiset (Nonplanar α)),
                ((B.toList.zip assn).filterMap
                  (fun p : Nonplanar α × Bool => if p.snd then none else some p.fst) :
                  Multiset (Nonplanar α))))).sum from by
    rw [hB_pl_len]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro assn _
    rw [h_to_BtoList_t, h_to_BtoList_f]]
  -- §9: now apply the bridge on `l := B.toList`. The bridge pair function is:
  --   F(s_t, s_f) := FUN1(s_t, s_f) + FUN2(s_t, s_f).
  have h_bridge := RoseTree.Pathed.listChoices_bridge_powerset_paired
    (β := Nonplanar α) (l := B.toList)
  -- Apply Multiset.map (uncurry of FUN1 + FUN2) to both sides.
  have h_compose := congr_arg
    (Multiset.map (fun pr : Multiset (Nonplanar α) × Multiset (Nonplanar α) =>
      FUN1 pr + FUN2 pr)) h_bridge
  rw [Multiset.map_map, Multiset.map_map] at h_compose
  -- The composition `(fun pr => FUN1 pr + FUN2 pr) ∘ (fun assn => let ...; (s_t, s_f))`
  -- is defeq to `fun assn => let ...; FUN1 (s_t, s_f) + FUN2 (s_t, s_f)`, but `rw` doesn't
  -- auto-eta. Substitute via show.
  have h_compose_sum := congr_arg Multiset.sum h_compose
  show (((Multiset.ofList (RoseTree.Pathed.listChoices [true, false] B.toList.length)).map
        ((fun pr : Multiset (Nonplanar α) × Multiset (Nonplanar α) =>
            FUN1 pr + FUN2 pr) ∘
          (fun assn : List Bool =>
            let s_t : Multiset (Nonplanar α) :=
              (B.toList.zip assn).filterMap
                (fun p : Nonplanar α × Bool => if p.snd then some p.fst else none)
            let s_f : Multiset (Nonplanar α) :=
              (B.toList.zip assn).filterMap
                (fun p : Nonplanar α × Bool => if p.snd then none else some p.fst)
            (s_t, s_f)))).sum) = _
  rw [h_compose_sum]
  -- RHS goal form: (B.powerset.map (C₁ ↦ ...)).sum. Note ↑B.toList = B.
  have hB_coe : (↑B.toList : Multiset (Nonplanar α)) = B := B.coe_toList
  rw [hB_coe]
  -- Now: (B.powerset.map (s ↦ FUN1(s, B - s) + FUN2(s, B - s))).sum = goal RHS.
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro C₁ _
  show FUN1 (C₁, B - C₁) + FUN2 (C₁, B - C₁) =
        ((Nonplanar.insertionMultiset C₁ ({v} : Multiset _)).map
            (fun Y => g Y (B - C₁))).sum +
        ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
            (fun Y' => g C₁ Y')).sum
  rfl

/-- **Substrate 2 for Q5c**: the GL-side analog of OG Prop 2.7(ii)'s
    guest-splitting identity. It is the per-tprod `m+1` induction step of
    `gl_product_eq_oudomGuinStar_tprod`, using the singleton case
    `Nonplanar.insertionMultiset_singleton_assoc`.

    The four terms (T1 + T2 = T3 + T4):
    * T1 = `F * op (G * of'{v})` — single-shot CK multiplication.
    * T2 = `F * insertion (op G) (op of'{v})` — insert v into G first.
    * T3 = `insertion (F * op G) (op of'{v})` — insert v into the
      GL-product.
    * T4 = `op (unop (F * op G) * of'{v})` — append v to the CK image
      of the GL-product.

    Strategy: linearize G to basis `of' B`, expand T1, T3, T4 via
    `mul_of'_sum_form` over `Multiset.powerset_cons (v ::ₘ B)`. Apply
    `GL_insertion_leibniz_left_singleton_guest` summand-wise to T3,
    then `GL_iterated_insertion_singleton_v` to split each iterated
    insertion. The match against T2 then uses `GL_T2_reindexing_key`
    (a multiset reindexing identity proved by descent from the
    `RoseTree`-level bucket-split lemma `insertionForest_singleton_bucket_split`). -/
private theorem GL_product_split_mul_ι
    (F : GrossmanLarson ℤ α)
    (G : ConnesKreimer ℤ (Nonplanar α))
    (v : Nonplanar α) :
    F * op (G * ConnesKreimer.of' {v}) +
    F * insertion (op G)
        (op (ConnesKreimer.of' {v})) =
      insertion (F * op G)
        (op (ConnesKreimer.of' {v})) +
      op
        (unop (F * op G) * ConnesKreimer.of' {v}) := by
  -- Step 1: linearize G to basis. Use the underlying ℤ-linearity of
  -- both sides in G (each of T1, T2, T3, T4 is a ℤ-linear function of G).
  -- This standard ConnesKreimer.induction_linear pattern follows
  -- `insertion_mul_distrib_gen`/`GL_insertion_leibniz_basis_right`.
  refine ConnesKreimer.induction_linear G ?_ ?_ ?_
  · -- G = 0 case: T1=T2=T3=T4=0.
    show F * op
        ((0 : ConnesKreimer ℤ (Nonplanar α)) * ConnesKreimer.of' {v}) +
        F * insertion
              (op (0 : ConnesKreimer ℤ (Nonplanar α)))
              (op (ConnesKreimer.of' {v})) =
        insertion (F * op
            (0 : ConnesKreimer ℤ (Nonplanar α)))
          (op (ConnesKreimer.of' {v})) +
        op
          (unop (F * op
            (0 : ConnesKreimer ℤ (Nonplanar α))) * ConnesKreimer.of' {v})
    -- Rewrite step-by-step to avoid pattern-mismatch from compound rewrites.
    rw [show op (0 : ConnesKreimer ℤ (Nonplanar α)) =
          (0 : GrossmanLarson ℤ α) from rfl]
    rw [mul_zero_gl]
    rw [zero_mul, op_zero, mul_zero_gl]
    -- LHS: 0 + F * insertion 0 (op of'{v}); push insertion 0 = 0.
    have h_ins_zero : insertion (0 : GrossmanLarson ℤ α)
        (op (ConnesKreimer.of' ({v} : Multiset _))) = 0 :=
      ((insertion :
          GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α).flip
        (op (ConnesKreimer.of' ({v} : Multiset _)))).map_zero
    rw [h_ins_zero]
    rw [mul_zero_gl,
        show unop (0 : GrossmanLarson ℤ α) =
          (0 : ConnesKreimer ℤ (Nonplanar α)) from rfl,
        zero_mul, op_zero]
  · -- G = G₁ + G₂ additive case.
    intro G₁ G₂ ih₁ ih₂
    -- Use let-bindings to cast Finsupp into ConnesKreimer.
    let G₁' : ConnesKreimer ℤ (Nonplanar α) := G₁
    let G₂' : ConnesKreimer ℤ (Nonplanar α) := G₂
    show F * op ((G₁' + G₂') * ConnesKreimer.of' {v}) +
        F * insertion (op (G₁' + G₂'))
            (op (ConnesKreimer.of' {v})) =
      insertion (F * op (G₁' + G₂'))
        (op (ConnesKreimer.of' {v})) +
      op
        (unop (F * op (G₁' + G₂')) *
          ConnesKreimer.of' {v})
    -- Distribute (G₁' + G₂') through each operation. We rewrite each subterm
    -- to a (G₁'-part + G₂'-part) form, then apply ih₁, ih₂.
    -- T1: F * op((G₁'+G₂') * of'{v}) = F * op(G₁'*of'{v}) + F * op(G₂'*of'{v}).
    have hT1 : F * op
          ((G₁' + G₂') * ConnesKreimer.of' ({v} : Multiset _)) =
        F * op (G₁' * ConnesKreimer.of' ({v} : Multiset _)) +
        F * op (G₂' * ConnesKreimer.of' ({v} : Multiset _)) := by
      rw [add_mul,
          show op
            (G₁' * ConnesKreimer.of' ({v} : Multiset _) +
             G₂' * ConnesKreimer.of' ({v} : Multiset _)) =
          op (G₁' * ConnesKreimer.of' ({v} : Multiset _)) +
          op (G₂' * ConnesKreimer.of' ({v} : Multiset _)) from rfl]
      exact (product F).map_add _ _
    rw [hT1]
    -- T2: F * ins(op(G₁'+G₂'))(op of'{v}) = F * ins(opG₁')... + F * ins(opG₂')...
    have hT2 : F * insertion (op (G₁' + G₂'))
            (op (ConnesKreimer.of' ({v} : Multiset _))) =
        F * insertion (op G₁')
            (op (ConnesKreimer.of' ({v} : Multiset _))) +
        F * insertion (op G₂')
            (op (ConnesKreimer.of' ({v} : Multiset _))) := by
      rw [show op (G₁' + G₂') =
              op G₁' + op G₂' from rfl]
      rw [show insertion (op G₁' + op G₂')
              (op (ConnesKreimer.of' ({v} : Multiset _))) =
            insertion (op G₁')
              (op (ConnesKreimer.of' ({v} : Multiset _))) +
            insertion (op G₂')
              (op (ConnesKreimer.of' ({v} : Multiset _))) from by
        show ((insertion :
                GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α).flip
              (op (ConnesKreimer.of' ({v} : Multiset _))))
              (op G₁' + op G₂') = _
        rw [LinearMap.map_add]; rfl]
      exact (product F).map_add _ _
    rw [hT2]
    -- T3: ins(F * op(G₁'+G₂'))(op of'{v}) = ins(F * opG₁')(...) + ins(F * opG₂')(...)
    have hT3 : insertion (F * op (G₁' + G₂'))
            (op (ConnesKreimer.of' ({v} : Multiset _))) =
        insertion (F * op G₁')
            (op (ConnesKreimer.of' ({v} : Multiset _))) +
        insertion (F * op G₂')
            (op (ConnesKreimer.of' ({v} : Multiset _))) := by
      rw [show op (G₁' + G₂') =
              op G₁' + op G₂' from rfl]
      rw [show F * (op G₁' + op G₂') =
              F * op G₁' + F * op G₂' from
          (product F).map_add _ _]
      show ((insertion :
              GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α).flip
            (op (ConnesKreimer.of' ({v} : Multiset _))))
            (F * op G₁' + F * op G₂') = _
      rw [LinearMap.map_add]; rfl
    rw [hT3]
    -- T4: op (unop (F * op (G₁'+G₂')) * of'{v}) similarly.
    have hT4 : op
            (unop (F * op (G₁' + G₂')) *
              ConnesKreimer.of' ({v} : Multiset _)) =
        op
            (unop (F * op G₁') *
              ConnesKreimer.of' ({v} : Multiset _)) +
        op
            (unop (F * op G₂') *
              ConnesKreimer.of' ({v} : Multiset _)) := by
      rw [show op (G₁' + G₂') =
              op G₁' + op G₂' from rfl]
      rw [show F * (op G₁' + op G₂') =
              F * op G₁' + F * op G₂' from
          (product F).map_add _ _]
      rw [show unop (F * op G₁' + F * op G₂') =
              unop (F * op G₁') +
              unop (F * op G₂') from rfl,
          add_mul]
      rfl
    rw [hT4]
    -- Use ih₁, ih₂ via specialized casts (G₁', G₂' are CK by let-binding).
    have ih₁' :
        F * op (G₁' * ConnesKreimer.of' ({v} : Multiset _)) +
        F * insertion (op G₁')
            (op (ConnesKreimer.of' ({v} : Multiset _))) =
      insertion (F * op G₁')
          (op (ConnesKreimer.of' ({v} : Multiset _))) +
      op
        (unop (F * op G₁') *
          ConnesKreimer.of' ({v} : Multiset _)) := ih₁
    have ih₂' :
        F * op (G₂' * ConnesKreimer.of' ({v} : Multiset _)) +
        F * insertion (op G₂')
            (op (ConnesKreimer.of' ({v} : Multiset _))) =
      insertion (F * op G₂')
          (op (ConnesKreimer.of' ({v} : Multiset _))) +
      op
        (unop (F * op G₂') *
          ConnesKreimer.of' ({v} : Multiset _)) := ih₂
    -- Combine: the goal has the shape (A₁ + A₂) + (B₁ + B₂) = (C₁ + C₂) + (D₁ + D₂)
    -- where Aᵢ + Bᵢ = Cᵢ + Dᵢ. Add ih₁' + ih₂' and re-permute.
    -- Abel-rearrange LHS to (A₁ + B₁) + (A₂ + B₂); apply ih₁', ih₂'; abel back.
    have hLHS_perm :
        F * op (G₁' * ConnesKreimer.of' ({v} : Multiset _)) +
        F * op (G₂' * ConnesKreimer.of' ({v} : Multiset _)) +
        (F * insertion (op G₁')
            (op (ConnesKreimer.of' ({v} : Multiset _))) +
         F * insertion (op G₂')
            (op (ConnesKreimer.of' ({v} : Multiset _)))) =
      (F * op (G₁' * ConnesKreimer.of' ({v} : Multiset _)) +
        F * insertion (op G₁')
            (op (ConnesKreimer.of' ({v} : Multiset _)))) +
      (F * op (G₂' * ConnesKreimer.of' ({v} : Multiset _)) +
        F * insertion (op G₂')
            (op (ConnesKreimer.of' ({v} : Multiset _)))) := by abel
    rw [hLHS_perm, ih₁', ih₂']
    abel
  · -- G = single B r: scale out r, reduce to basis G = of' B.
    intro B r
    let G_single : ConnesKreimer ℤ (Nonplanar α) := ConnesKreimer.single B r
    show F * op (G_single * ConnesKreimer.of' {v}) +
        F * insertion (op G_single)
            (op (ConnesKreimer.of' {v})) =
      insertion (F * op G_single)
        (op (ConnesKreimer.of' {v})) +
      op
        (unop (F * op G_single) * ConnesKreimer.of' {v})
    have hG : G_single = r • (ConnesKreimer.of' B : ConnesKreimer ℤ (Nonplanar α)) :=
      ConnesKreimer.smul_single_one B r
    rw [hG]
    -- Push r through each term using smul_mul_assoc, op_smul, etc.
    have h_ins_smul_first :
        insertion (r • op
            (ConnesKreimer.of' B : ConnesKreimer ℤ _))
          (op (ConnesKreimer.of' ({v} : Multiset _))) =
        r • insertion (op
            (ConnesKreimer.of' B : ConnesKreimer ℤ _))
          (op (ConnesKreimer.of' ({v} : Multiset _))) := by
      show ((insertion :
              GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α).flip
            (op (ConnesKreimer.of' ({v} : Multiset _))))
            (r • op (ConnesKreimer.of' B : ConnesKreimer ℤ _)) = _
      rw [LinearMap.map_smul]
      rfl
    have h_T3_smul :
        insertion (r • (F * op
            (ConnesKreimer.of' B : ConnesKreimer ℤ _)))
          (op (ConnesKreimer.of' ({v} : Multiset _))) =
        r • insertion (F * op
            (ConnesKreimer.of' B : ConnesKreimer ℤ _))
          (op (ConnesKreimer.of' ({v} : Multiset _))) := by
      show ((insertion :
              GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α →ₗ[ℤ] GrossmanLarson ℤ α).flip
            (op (ConnesKreimer.of' ({v} : Multiset _))))
            (r • (F * op (ConnesKreimer.of' B : ConnesKreimer ℤ _))) = _
      rw [LinearMap.map_smul]
      rfl
    -- T1: (r•of'B) * of'{v} = r • (of'B * of'{v}); op_smul; F * r•x = r•(F*x).
    rw [smul_mul_assoc, op_smul, mul_smul_gl]
    -- T2: op(r•of'B) = r•opof'B; insertion(r•_)_ = r•insertion__; F * r•x = r•(F*x).
    rw [op_smul, h_ins_smul_first, mul_smul_gl]
    -- T3: F * r•opof'B = r•(F*opof'B); insertion(r•_)_ = r•insertion__.
    rw [mul_smul_gl, h_T3_smul]
    -- T4: unop(r•x) = r•unop x; (r•_)*of'{v} = r•(_*of'{v}); op(r•_) = r•op _.
    rw [show unop (r • (F * op
            (ConnesKreimer.of' B : ConnesKreimer ℤ _))) =
          r • unop (F * op
            (ConnesKreimer.of' B : ConnesKreimer ℤ _)) from rfl,
        smul_mul_assoc, op_smul]
    rw [← smul_add, ← smul_add]
    congr 1
    -- ===== BASIS CASE G = of' B =====
    -- T1 = F * op(of' B * of'{v}) = F * of'(B + {v}).
    have hT1 : F * op
          ((ConnesKreimer.of' B : ConnesKreimer ℤ (Nonplanar α)) *
            ConnesKreimer.of' ({v} : Multiset _)) =
        F * (of' (B + ({v} : Multiset _)) : GrossmanLarson ℤ α) := by
      rw [← ConnesKreimer.of'_add]
      rfl
    rw [hT1]
    -- op (of' B) = of' B, op (of' {v}) = of' {v} (definitionally).
    have hopofB : op
        (ConnesKreimer.of' B : ConnesKreimer ℤ (Nonplanar α)) =
        (of' B : GrossmanLarson ℤ α) := rfl
    rw [hopofB]
    -- The basis case G = of' B has four terms aligned via:
    -- T1 split via mul_of'_sum_form + powerset_cons (two halves: T1a, T1b)
    -- T3 split via mul_of'_sum_form + insertion_sum_left + Leibniz + iterated split
    --   (three pieces: T3-first, T3-residue, T3-second).
    -- T4 expanded via mul_of'_sum_form + multiplicative bookkeeping.
    -- T2 = T3-residue + T3-second's NIM expansion, matched via GL_T2_reindexing_key.
    --
    -- Cancellations:
    --   T1a = T4 (both = Σ_C₁ g_F C₁ ((B-C₁) + {v}))
    --   T1b = T3-first (both = Σ_C₁ g_F (C₁+{v}) (B-C₁))
    --   T2 = T3-residue + T3-second (via GL_T2_reindexing_key).
    --
    -- Goal: F * of'(B+{v}) + F * insertion (of' B) (op of'{v}) =
    --       insertion (F * of' B) (op of'{v}) + op(unop(F * of' B) * of'{v}).
    -- Define the per-(D : Multiset _) summand of mul_of'_sum_form, shared
    -- across T1, T3, T4 (the second slot varies, captured in T4 and T1a
    -- by passing in the "appended {v}" version).
    set g : Multiset (Nonplanar α) → Multiset (Nonplanar α) → GrossmanLarson ℤ α :=
      fun s t => op
        (unop (insertion F (ConnesKreimer.of' s)) *
          unop (ConnesKreimer.of' (R := ℤ) t :
            GrossmanLarson ℤ α)) with hg_def
    -- Bridge `B + {v} = v ::ₘ B` (via singleton_add + add_comm).
    have hB_add_v : B + ({v} : Multiset (Nonplanar α)) = v ::ₘ B := by
      rw [add_comm, Multiset.singleton_add]
    -- §A: T1 split via mul_of'_sum_form over (v ::ₘ B) and powerset_cons.
    --     T1 = T1a + T1b where:
    --     T1a = Σ_{C₁ ⊆ B} g C₁ (v ::ₘ (B - C₁))
    --     T1b = Σ_{C₁ ⊆ B} g (v ::ₘ C₁) (B - C₁)
    have hT1_split :
        F * (of' (B + ({v} : Multiset _)) : GrossmanLarson ℤ α) =
        (B.powerset.map (fun C₁ => g C₁ (v ::ₘ (B - C₁)))).sum +
        (B.powerset.map (fun C₁ => g (v ::ₘ C₁) (B - C₁))).sum := by
      rw [show (of' (B + ({v} : Multiset _)) : GrossmanLarson ℤ α) =
              (of' (v ::ₘ B) : GrossmanLarson ℤ α) by rw [hB_add_v],
          mul_of'_sum_form, Multiset.powerset_cons,
          Multiset.map_add, Multiset.sum_add, Multiset.map_map]
      congr 1
      · -- "no v in C₁" half: C₁ ⊆ B, second slot = (v ::ₘ B) - C₁ = v ::ₘ (B - C₁).
        apply congr_arg Multiset.sum
        apply Multiset.map_congr rfl
        intro C₁ hC₁
        have hC₁_le : C₁ ≤ B := Multiset.mem_powerset.mp hC₁
        show op (unop
              (insertion F (ConnesKreimer.of' C₁ : GrossmanLarson ℤ α)) *
            unop
              (ConnesKreimer.of' ((v ::ₘ B) - C₁) : GrossmanLarson ℤ α)) =
            g C₁ (v ::ₘ (B - C₁))
        rw [show ((v ::ₘ B) - C₁) = v ::ₘ (B - C₁) from
          Multiset.cons_sub_of_le v hC₁_le]
      · -- "v in C₁" half: image is C₁ ↦ (v ::ₘ C₁), then second slot =
        --   (v ::ₘ B) - (v ::ₘ C₁) = (v ::ₘ B).erase v - C₁ = B - C₁.
        apply congr_arg Multiset.sum
        apply Multiset.map_congr rfl
        intro C₁ _hC₁
        show op (unop
              (insertion F (ConnesKreimer.of' (v ::ₘ C₁) : GrossmanLarson ℤ α)) *
            unop
              (ConnesKreimer.of' ((v ::ₘ B) - (v ::ₘ C₁)) : GrossmanLarson ℤ α)) =
            g (v ::ₘ C₁) (B - C₁)
        rw [show ((v ::ₘ B) - (v ::ₘ C₁)) = B - C₁ by
          rw [Multiset.sub_cons, Multiset.erase_cons_head]]
    rw [hT1_split]
    -- Helpers: op/unop push through Multiset.sum on the powerset of B
    -- (and on any multiset, by induction).
    have h_unop_sum_gen :
        ∀ (s : Multiset (GrossmanLarson ℤ α)),
          unop s.sum = (s.map unop).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => rfl
      | cons a s ih =>
        rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, unop_add, ih]
    have h_op_sum_gen :
        ∀ (s : Multiset (ConnesKreimer ℤ (Nonplanar α))),
          op s.sum = (s.map op).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => rfl
      | cons a s ih =>
        rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, op_add, ih]
    -- Define the F-keyed CK-product family used as an intermediate.
    let f_F : Multiset (Nonplanar α) → ConnesKreimer ℤ (Nonplanar α) := fun C₁ =>
      unop
        (insertion F (ConnesKreimer.of' C₁ : GrossmanLarson ℤ α))
    -- §B: T4 = T1a, i.e. op(unop(F * of'B) * of'{v}) = Σ_{C₁ ⊆ B} g C₁ (v ::ₘ (B - C₁)).
    have hT4_eq_T1a :
        op
          (unop (F * (of' B : GrossmanLarson ℤ α)) *
            ConnesKreimer.of' ({v} : Multiset _)) =
        (B.powerset.map (fun C₁ => g C₁ (v ::ₘ (B - C₁)))).sum := by
      rw [mul_of'_sum_form]
      -- LHS = op (unop ((Σ_C₁ op(...)).sum) * of'{v}).
      -- Step 1: unop pushes through the sum (general op-sum lemma).
      rw [h_unop_sum_gen, Multiset.map_map]
      -- Now the sum is over (unop ∘ op (... CK product ...)), which definitionally
      -- reduces to the CK product.
      rw [show (unop ∘ fun G₁ =>
            op
              ((insertion F (of' G₁ : GrossmanLarson ℤ α)).unop *
                (of' (B - G₁) : GrossmanLarson ℤ α).unop)) =
              fun G₁ => f_F G₁ * ConnesKreimer.of' (B - G₁) from rfl]
      -- Step 2: push (* of'{v}) into the sum (CK comm-semiring distributivity).
      rw [← Multiset.sum_map_mul_right]
      -- Step 3: per-summand, B - C₁ + {v} = v ::ₘ (B - C₁); fold up via of'_add.
      rw [show (B.powerset.map (fun C₁ : Multiset (Nonplanar α) =>
                f_F C₁ * ConnesKreimer.of' (B - C₁) *
                  ConnesKreimer.of' ({v} : Multiset _))) =
              B.powerset.map (fun C₁ : Multiset (Nonplanar α) =>
                f_F C₁ * ConnesKreimer.of' (v ::ₘ (B - C₁))) from by
        apply Multiset.map_congr rfl
        intro C₁ _
        rw [mul_assoc, ← ConnesKreimer.of'_add]
        rw [show B - C₁ + ({v} : Multiset (Nonplanar α)) = v ::ₘ (B - C₁) by
          rw [add_comm, Multiset.singleton_add]]]
      -- Step 4: push op into the sum.
      rw [h_op_sum_gen, Multiset.map_map]
      -- Step 5: per C₁, fold up to g.
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro C₁ _hC₁
      rfl
    rw [hT4_eq_T1a]
    -- §C: T3 = Σ_{C₁ ⊆ B} [g(v ::ₘ C₁)(B - C₁) +
    --                       Σ_{Y ∈ NIM C₁ {v}} g Y (B - C₁) +
    --                       Σ_{Y' ∈ NIM (B - C₁) {v}} g C₁ Y']
    --       = T1b + Σ_{C₁ ⊆ B} (T3-residue(C₁) + T3-second(C₁))
    have hT3 :
        insertion (F * (of' B : GrossmanLarson ℤ α))
          (op (ConnesKreimer.of' ({v} : Multiset _))) =
        (B.powerset.map (fun C₁ => g (v ::ₘ C₁) (B - C₁))).sum +
        (B.powerset.map (fun C₁ =>
          ((Nonplanar.insertionMultiset C₁ ({v} : Multiset _)).map
            (fun Y => g Y (B - C₁))).sum +
          ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
            (fun Y' => g C₁ Y')).sum)).sum := by
      rw [mul_of'_sum_form]
      -- LHS = insertion ((sum over C₁) g_F(C₁)(B-C₁)) (op of'{v}).
      rw [insertion_sum_left, Multiset.map_map]
      -- Per C₁: apply Leibniz. The composed map function is
      --   (fun X => insertion X (op of'{v})) ∘ (fun G₁ => op (unop(...) * unop(...))),
      -- which beta-reduces to (fun G₁ => insertion (op (...)) (op of'{v})). We
      -- match the post-beta form (h_per_C₁) and step through it summand-wise.
      have h_per_C₁ : ∀ C₁ : Multiset (Nonplanar α),
          insertion
            (op
              ((insertion F (of' C₁ :
                  GrossmanLarson ℤ α)).unop *
                (of' (B - C₁) : GrossmanLarson ℤ α).unop))
            (op (ConnesKreimer.of' ({v} : Multiset _))) =
          g (v ::ₘ C₁) (B - C₁) +
          (((Nonplanar.insertionMultiset C₁ ({v} : Multiset _)).map
            (fun Y => g Y (B - C₁))).sum +
          ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
            (fun Y' => g C₁ Y')).sum) := by
        intro C₁
        -- Apply GL_insertion_leibniz_left_singleton_guest with
        --   A := unop(ins F (of' C₁)), B := of'(B - C₁) (as CK).
        set A_arg : ConnesKreimer ℤ (Nonplanar α) :=
          (insertion F (of' C₁ :
            GrossmanLarson ℤ α)).unop with hA_arg
        set B_arg : ConnesKreimer ℤ (Nonplanar α) :=
          (of' (B - C₁) : GrossmanLarson ℤ α).unop with hB_arg
        have h_leibniz := GL_insertion_leibniz_left_singleton_guest A_arg B_arg v
        rw [h_leibniz]
        -- First Leibniz piece: op(unop(ins (op A_arg)(op of'{v})) * B_arg).
        --   op A_arg = op (unop (ins F (of' C₁))) = ins F (of' C₁).
        rw [show op A_arg = insertion F
              (ConnesKreimer.of' C₁ : GrossmanLarson ℤ α) from
          op_unop _]
        -- Apply GL_iterated_insertion_singleton_v.
        rw [GL_iterated_insertion_singleton_v F C₁ v]
        -- Second Leibniz piece: op(A_arg * unop(ins (op B_arg)(op of'{v}))).
        --   op B_arg = of'(B - C₁).
        rw [show op B_arg =
              (of' (B - C₁) : GrossmanLarson ℤ α) from rfl]
        rw [show op (ConnesKreimer.of' ({v} : Multiset _)) =
              (of' ({v} : Multiset _) : GrossmanLarson ℤ α) from rfl]
        rw [insertion_of'_of']
        -- After Leibniz + iterated split + insertion_of'_of':
        --   LHS = op(unop((ins F (of'(C₁+{v})) + Σ_Y ins F (of' Y))) * B_arg) +
        --         op(A_arg * unop((Σ_Y' of' Y').sum))
        rw [unop_add, add_mul, op_add]
        -- The first piece becomes T1b summand: g(v ::ₘ C₁)(B-C₁).
        rw [show C₁ + ({v} : Multiset (Nonplanar α)) = v ::ₘ C₁ by
          rw [add_comm, Multiset.singleton_add]]
        rw [add_assoc]
        -- The first summand op(unop(ins F (of'(v::C₁))) * B_arg) reduces to
        -- g (v::C₁) (B-C₁) definitionally; the congr 1 then leaves T3R+T3S = sum.
        congr 1
        -- Remaining goal: op(unop(Σ_Y ins F (of' Y)) * B_arg) +
        --                 op(A_arg * unop((Σ_Y' of' Y').sum)) =
        --                 Σ_Y g Y (B-C₁) + Σ_Y' g C₁ Y'
        congr 1
        · -- T3-residue: distribute * B_arg through the sum.
          rw [h_unop_sum_gen, Multiset.map_map]
          rw [show
              (((Nonplanar.insertionMultiset C₁ ({v} : Multiset _)).map
                (unop ∘ fun Y : Multiset (Nonplanar α) =>
                  insertion F
                    (ConnesKreimer.of' Y : GrossmanLarson ℤ α))).sum *
                B_arg : ConnesKreimer ℤ (Nonplanar α)) =
              ((Nonplanar.insertionMultiset C₁ ({v} : Multiset _)).map
                (fun Y : Multiset (Nonplanar α) =>
                  (unop ∘ fun Y' : Multiset (Nonplanar α) =>
                    insertion F
                      (ConnesKreimer.of' Y' : GrossmanLarson ℤ α)) Y *
                  B_arg)).sum from Multiset.sum_map_mul_right.symm]
          rw [h_op_sum_gen, Multiset.map_map]
          apply congr_arg Multiset.sum
          apply Multiset.map_congr rfl
          intro Y _hY
          rfl
        · -- T3-second: unfold insertionBasis to a sum, then distribute A_arg *.
          show op (A_arg *
              (insertionBasis (B - C₁) ({v} : Multiset _)).unop) =
              ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
                (fun Y' => g C₁ Y')).sum
          show op (A_arg *
              (((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
                (fun F' => (of' (R := ℤ) F' :
                  GrossmanLarson ℤ α))).sum).unop) =
              ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
                (fun Y' => g C₁ Y')).sum
          rw [h_unop_sum_gen, Multiset.map_map]
          rw [show (A_arg *
              ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
                (unop ∘ fun F' : Multiset (Nonplanar α) =>
                  (of' (R := ℤ) F' : GrossmanLarson ℤ α))).sum :
              ConnesKreimer ℤ (Nonplanar α)) =
              ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
                (fun F' : Multiset (Nonplanar α) => A_arg *
                  (unop ∘ fun F'' : Multiset (Nonplanar α) =>
                    (of' (R := ℤ) F'' :
                      GrossmanLarson ℤ α)) F')).sum from
            Multiset.sum_map_mul_left.symm]
          rw [h_op_sum_gen, Multiset.map_map]
          apply congr_arg Multiset.sum
          apply Multiset.map_congr rfl
          intro Y' _hY'
          rfl
      -- Apply h_per_C₁ summand-wise, then split the resulting Σ(_ + _) sum.
      apply Eq.trans
      · apply congr_arg Multiset.sum
        apply Multiset.map_congr rfl
        intro C₁ _hC₁
        -- The map function is (fun X => insertion X (op of'{v})) ∘ (fun G₁ => op (...))
        -- which beta-reduces to insertion (op (...)) (op of'{v}) per C₁.
        exact h_per_C₁ C₁
      -- Split the Σ(_ + _) into two sums via Multiset.sum_map_add.
      rw [← Multiset.sum_map_add]
    rw [hT3]
    -- §D: T2 = Σ_{C₁ ⊆ B} (T3-residue(C₁) + T3-second(C₁))
    --    via GL_T2_reindexing_key with g_consumer = g.
    have hT2 :
        F * insertion
            (of' B : GrossmanLarson ℤ α)
            (op (ConnesKreimer.of' ({v} : Multiset _))) =
        (B.powerset.map (fun C₁ =>
          ((Nonplanar.insertionMultiset C₁ ({v} : Multiset _)).map
            (fun Y => g Y (B - C₁))).sum +
          ((Nonplanar.insertionMultiset (B - C₁) ({v} : Multiset _)).map
            (fun Y' => g C₁ Y')).sum)).sum := by
      -- Rewrite insertion (of' B)(op of'{v}) = insertion (of' B)(of' {v})
      -- (definitional: op = id on of'{v}), then = insertionBasis B {v}.
      rw [show op (ConnesKreimer.of' ({v} : Multiset _)) =
              (of' ({v} : Multiset _) : GrossmanLarson ℤ α) from rfl,
          insertion_of'_of']
      show F * ((Nonplanar.insertionMultiset B ({v} : Multiset _)).map
              (fun F' : Multiset (Nonplanar α) =>
                (of' (R := ℤ) F' : GrossmanLarson ℤ α))).sum = _
      -- Push F * through the sum (general bilinear distribution).
      have h_F_mul_sum : ∀ s : Multiset (GrossmanLarson ℤ α),
          F * s.sum = (s.map (fun X => F * X)).sum := by
        intro s
        induction s using Multiset.induction with
        | empty =>
          rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
          show product F 0 = 0
          exact (product F).map_zero
        | cons a s ih =>
          rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
          show product F (a + s.sum) = F * a + _
          rw [(product F).map_add]
          show product F a +
              (F * s.sum) = F * a + _
          rw [ih]
          rfl
      rw [h_F_mul_sum, Multiset.map_map]
      -- Per Y' ∈ NIM B {v}: F * of' Y' = mul_of'_sum_form over Y'.
      have h_per_Y : ∀ Y : Multiset (Nonplanar α),
          F * (of' Y : GrossmanLarson ℤ α) =
            (Y.powerset.map (fun D => g D (Y - D))).sum := by
        intro Y
        rw [mul_of'_sum_form]
        apply congr_arg Multiset.sum
        apply Multiset.map_congr rfl
        intro D _hD
        rfl
      rw [show ((fun X : GrossmanLarson ℤ α => F * X) ∘
                (fun F' : Multiset (Nonplanar α) =>
                  (of' (R := ℤ) F' : GrossmanLarson ℤ α))) =
              (fun Y => (Y.powerset.map (fun D => g D (Y - D))).sum) from by
        funext Y; exact h_per_Y Y]
      exact GL_T2_reindexing_key B v g
    rw [hT2]
    -- §E: Combine. LHS = T1a + T1b + T2. RHS = T3 + T4 = T1b + Σ + T1a.
    abel

/-- **Per-tprod form** of Q5c (lifts to full Q5c via `algHomL_surjective`).

    For all X ∈ S(L), m ∈ ℕ, a : Fin m → L:
      `ckIso(X ★ algHomL(tprod m a)) = (op (ckIso X)) * (op (ckIso (algHomL (tprod m a))))`

    Proof by induction on m, using `oudomGuinStar_mul_ι_split` + IH +
    `oudomGuinCirc_algHomL_tprod_ι` + `ckIso_circ_intertwine_insertion` +
    `GL_product_split_mul_ι`. The `m+1` case v-linearizes via
    `Finsupp.induction_linear`; the basis case `v = ofTree t` chains all
    substrate. Coercion discipline: work in CK (whose global `CommRing`
    instance supplies the `AddCommGroup`) for additive rearrangements;
    transport to GL via `op`/`unop` (which are the identity coercion). -/
private theorem gl_product_eq_oudomGuinStar_tprod
    (X : SymmetricAlgebra ℤ (InsertionAlgebra α)) :
    ∀ (m : ℕ) (a : Fin m → InsertionAlgebra α),
      ((ckIsoSymmetricAlgebra (oudomGuinStar X
          (PreLie.OudomGuinCircConstruct.algHomL
            (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m a))) :
        ConnesKreimer ℤ (Nonplanar α)) : GrossmanLarson ℤ α) =
      (op (ckIsoSymmetricAlgebra X)) *
      (op (ckIsoSymmetricAlgebra
        (PreLie.OudomGuinCircConstruct.algHomL
          (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m a)))) := by
  intro m
  induction m with
  | zero =>
    intro a
    -- algHomL(tprod 0) = 1; both sides reduce to op(ckIso X).
    have h_tprod0 : TensorAlgebra.tprod ℤ (InsertionAlgebra α) 0 a = 1 := by
      rw [TensorAlgebra.tprod_apply]; simp [List.ofFn_zero]
    rw [h_tprod0,
        show PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := InsertionAlgebra α)
              (1 : TensorAlgebra ℤ (InsertionAlgebra α)) =
            (1 : SymmetricAlgebra ℤ (InsertionAlgebra α)) from
          map_one (SymmetricAlgebra.algHom ℤ (InsertionAlgebra α))]
    rw [oudomGuinStar_one, map_one]
    show (ckIsoSymmetricAlgebra X : ConnesKreimer ℤ _) =
        unop
          (op (ckIsoSymmetricAlgebra X) * (1 : GrossmanLarson ℤ α))
    rw [GrossmanLarson.mul_one]
    rfl
  | succ m ih =>
    intro a
    -- Set up tprod (m+1) split + algHomL split.
    have h_a_eq : a = Fin.snoc (Fin.init a) (a (Fin.last m)) :=
      (Fin.snoc_init_self a).symm
    have h_tprod_succ :
        TensorAlgebra.tprod ℤ (InsertionAlgebra α) (m + 1) a =
        TensorAlgebra.tprod ℤ (InsertionAlgebra α) m (Fin.init a) *
          TensorAlgebra.ι ℤ (a (Fin.last m)) := by
      conv_lhs => rw [h_a_eq]
      rw [Fin.snoc_eq_append,
          PreLie.OudomGuinCircConstruct.ι_eq_tprod_one,
          ← PreLie.OudomGuinCircConstruct.tprod_mul_tprod]
      congr 1
    have h_algHomL_split :
        PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := InsertionAlgebra α)
            (TensorAlgebra.tprod ℤ (InsertionAlgebra α) (m + 1) a) =
          PreLie.OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m (Fin.init a)) *
            SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (a (Fin.last m)) := by
      rw [h_tprod_succ]
      show (SymmetricAlgebra.algHom ℤ (InsertionAlgebra α)) _ = _
      rw [map_mul]
      show (SymmetricAlgebra.algHom ℤ (InsertionAlgebra α))
            (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m (Fin.init a)) *
            (SymmetricAlgebra.algHom ℤ (InsertionAlgebra α))
              (TensorAlgebra.ι ℤ (a (Fin.last m))) =
          PreLie.OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m (Fin.init a)) *
            SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (a (Fin.last m))
      rfl
    rw [h_algHomL_split]
    -- Set up D = algHomL(tprod m init) and v-linearize.
    set D : SymmetricAlgebra ℤ (InsertionAlgebra α) :=
      PreLie.OudomGuinCircConstruct.algHomL
        (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m (Fin.init a)) with hD
    -- The claim parameterized over v : InsertionAlgebra α; we apply at
    -- v = a (Fin.last m). Both sides are linear in v through ι.
    suffices h_v_claim :
        ∀ v : InsertionAlgebra α,
          ((ckIsoSymmetricAlgebra
              (oudomGuinStar X (D * SymmetricAlgebra.ι ℤ _ v)) :
            ConnesKreimer ℤ (Nonplanar α)) : GrossmanLarson ℤ α) =
          (op (ckIsoSymmetricAlgebra X)) *
            (op (ckIsoSymmetricAlgebra
              (D * SymmetricAlgebra.ι ℤ _ v))) by
      exact h_v_claim (a (Fin.last m))
    -- v-induction via Finsupp.induction_linear.
    intro v
    refine Finsupp.induction_linear v ?_ ?_ ?_
    · -- v = 0: ι 0 = 0; D · 0 = 0; X ★ 0 = 0 (via star-linearity).
      -- Goal: ckIso(X ★ (D * ι 0)) = op(ckIso X) * op(ckIso(D * ι 0))
      -- Both sides reduce to 0 via map_zero cascades.
      have h_LHS_zero : (ckIsoSymmetricAlgebra
            (oudomGuinStar X (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0)) :
          ConnesKreimer ℤ (Nonplanar α)) = 0 := by
        have h1 : SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (0 : InsertionAlgebra α) =
            (0 : SymmetricAlgebra ℤ (InsertionAlgebra α)) :=
          (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)).map_zero
        rw [h1, mul_zero]
        rw [show oudomGuinStar (R := ℤ) X 0 = 0 from by
          rw [← oudomGuinStarL_apply X 0]; exact (oudomGuinStarL X).map_zero]
        exact map_zero _
      have h_RHS_zero : op (ckIsoSymmetricAlgebra X) *
            op (ckIsoSymmetricAlgebra
              (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0)) =
          (0 : GrossmanLarson ℤ α) := by
        have h1 : SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (0 : InsertionAlgebra α) =
            (0 : SymmetricAlgebra ℤ (InsertionAlgebra α)) :=
          (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)).map_zero
        rw [h1, mul_zero]
        rw [show ckIsoSymmetricAlgebra (0 : SymmetricAlgebra ℤ (InsertionAlgebra α)) =
              (0 : ConnesKreimer ℤ (Nonplanar α)) from map_zero _]
        rw [op_zero, mul_zero_gl]
      exact h_LHS_zero.trans h_RHS_zero.symm
    · -- v = v₁ + v₂: linearity in v through ι, mul, ★, ckIso, op, mul (GL).
      intro v₁ v₂ ih₁ ih₂
      have h_ι_add : SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (v₁ + v₂) =
            SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v₁ +
            SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v₂ :=
        (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)).map_add _ _
      have h_D_mul_add :
          D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (v₁ + v₂) =
            D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v₁ +
            D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v₂ := by
        rw [h_ι_add, mul_add]
      have h_star_add :
          oudomGuinStar (R := ℤ) X
              (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (v₁ + v₂)) =
            oudomGuinStar (R := ℤ) X
                (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v₁) +
            oudomGuinStar (R := ℤ) X
                (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v₂) := by
        rw [h_D_mul_add, oudomGuinStar_add_right]
      rw [h_star_add, map_add, h_D_mul_add, map_add, op_add, mul_add, ih₁, ih₂]
      rfl
    · -- v = single t r: factor scalar out, reduce to v = ofTree t basis case.
      intro t r
      -- Reduce single t r = r • ofTree t.
      have hv_eq : (Finsupp.single t r : InsertionAlgebra α) =
            r • InsertionAlgebra.ofTree t := by
        show (Finsupp.single t r : InsertionAlgebra α) =
              r • (Finsupp.single t 1 : InsertionAlgebra α)
        exact (Finsupp.smul_single_one t r).symm
      rw [hv_eq]
      -- ι (r • ofTree t) = r • ι (ofTree t)
      rw [(SymmetricAlgebra.ι ℤ (InsertionAlgebra α)).map_smul r _]
      -- D * (r • ι ofTree t) = r • (D * ι ofTree t)
      rw [mul_smul_comm]
      -- X ★ (r • Y) = r • (X ★ Y)
      rw [oudomGuinStar_smul_right X _ r]
      -- ckIso (r • Y) = r • ckIso Y (twice) — via simp on map_smul.
      simp only [_root_.map_smul]
      -- op (r • Y) = r • op Y (only the inner one — RHS has op applied to (r • ...))
      rw [show op
              (r • ckIsoSymmetricAlgebra
                (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                  (InsertionAlgebra.ofTree t))) =
            r • op (ckIsoSymmetricAlgebra
                (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                  (InsertionAlgebra.ofTree t))) from op_smul r _]
      -- F * (r • Y) = r • (F * Y) — use linearity of product.
      have h_smul_right : op (ckIsoSymmetricAlgebra X) *
              (r • op (ckIsoSymmetricAlgebra
                (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                  (InsertionAlgebra.ofTree t)))) =
            r • (op (ckIsoSymmetricAlgebra X) *
              op (ckIsoSymmetricAlgebra
                (D * SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                  (InsertionAlgebra.ofTree t)))) :=
          (product
            (op (ckIsoSymmetricAlgebra X))).map_smul r _
      rw [h_smul_right]
      congr 1
      -- Basis case: v = ofTree t.
      -- This is the heart of the proof.
      -- Notation: F := op(ckIso X), G := ckIso D, T := of'{t}.
      -- Goal: ckIso(X ★ (D · ι(ofTree t))) = F * op(ckIso D · ι(ofTree t)).
      -- Step 1: Apply SL split (oudomGuinStar_mul_ι_split) on LHS:
      --   X ★ (D · ι(ofTree t)) =
      --     (X★D) ○ ι(ofTree t) + (X★D) · ι(ofTree t) - X ★ (D ○ ι(ofTree t))
      have h_SL_split :
          oudomGuinStar X (D * SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) =
            oudomGuinCirc (oudomGuinStar X D)
                (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) +
            oudomGuinStar X D * SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t) -
            oudomGuinStar X (oudomGuinCirc D
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) :=
        oudomGuinStar_mul_ι_split X D (InsertionAlgebra.ofTree t)
      -- Step 2: Decompose D ○ ι(ofTree t) using oudomGuinCirc_algHomL_tprod_ι.
      have h_DcircTV :
          oudomGuinCirc D (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) =
            ∑ i : Fin m,
              PreLie.OudomGuinCircConstruct.algHomL
                (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                  (Function.update (Fin.init a) i
                    (Fin.init a i * InsertionAlgebra.ofTree t))) := by
        rw [hD]
        exact oudomGuinCirc_algHomL_tprod_ι
          (InsertionAlgebra.ofTree t) m (Fin.init a)
      -- Step 3: IH at each summand (`update (init a) i (init a i * ofTree t)`).
      -- This gives ckIso(X ★ algHomL(tprod m _)) = op(ckIso X) * op(ckIso(algHomL(...))).
      -- Combined into a sum.
      have h_star_sum : ∀ (Z : SymmetricAlgebra ℤ (InsertionAlgebra α))
          (f : Fin m → SymmetricAlgebra ℤ (InsertionAlgebra α)),
          oudomGuinStar Z (∑ i, f i) = ∑ i, oudomGuinStar Z (f i) := by
        intro Z f
        rw [← oudomGuinStarL_apply Z _, map_sum]
        simp only [oudomGuinStarL_apply]
      -- Apply IH summand-wise to X ★ (D ○ ι(ofTree t)).
      have h_ih_sum :
          ((ckIsoSymmetricAlgebra
              (oudomGuinStar X
                (oudomGuinCirc D
                  (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)))) :
            ConnesKreimer ℤ (Nonplanar α)) : GrossmanLarson ℤ α) =
            ∑ i : Fin m,
              (op (ckIsoSymmetricAlgebra X)) *
              (op (ckIsoSymmetricAlgebra
                (PreLie.OudomGuinCircConstruct.algHomL
                  (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                    (Function.update (Fin.init a) i
                      (Fin.init a i * InsertionAlgebra.ofTree t)))))) := by
        rw [h_DcircTV, h_star_sum]
        rw [show ckIsoSymmetricAlgebra (∑ i : Fin m,
                  oudomGuinStar X
                    (PreLie.OudomGuinCircConstruct.algHomL
                      (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                        (Function.update (Fin.init a) i
                          (Fin.init a i * InsertionAlgebra.ofTree t))))) =
                ∑ i : Fin m,
                  ckIsoSymmetricAlgebra
                    (oudomGuinStar X
                      (PreLie.OudomGuinCircConstruct.algHomL
                        (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                          (Function.update (Fin.init a) i
                            (Fin.init a i * InsertionAlgebra.ofTree t))))) from
            map_sum ckIsoSymmetricAlgebra.toLinearEquiv.toLinearMap _ _]
        -- Push (· : GL) through the sum: a CK sum coerces to GL by the same
        -- definitional equality.
        show (∑ i : Fin m, _ : ConnesKreimer ℤ (Nonplanar α)) =
            ∑ i : Fin m, _
        apply Finset.sum_congr rfl
        intro i _
        exact ih (Function.update (Fin.init a) i
          (Fin.init a i * InsertionAlgebra.ofTree t))
      -- Step 4: Apply ckIso to h_SL_split, split into +/- in CK, then transport
      -- to GL. The LHS (X★D) ○ ι v term goes via ckIso_circ_intertwine_insertion.
      -- Define F := op(ckIso X), G := ckIso D, T := of'{t} as a CK Multiset.
      set F : GrossmanLarson ℤ α := op (ckIsoSymmetricAlgebra X)
        with hF
      set G : ConnesKreimer ℤ (Nonplanar α) := ckIsoSymmetricAlgebra D with hG
      -- ckIso(ι(ofTree t)) = of'{t}.
      have h_ckIso_ι_ofTree :
          ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                (InsertionAlgebra.ofTree t)) =
            ConnesKreimer.of' ({t} : Multiset _) := by
        show ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                (Finsupp.single t 1)) = _
        exact ckIsoSymmetricAlgebra_ι_single t
      -- Apply IH at init to get ckIso(X★D) = F * op(G).
      have h_ih_init :
          ((ckIsoSymmetricAlgebra (oudomGuinStar X D) :
            ConnesKreimer ℤ (Nonplanar α)) : GrossmanLarson ℤ α) =
            F * op G := by
        rw [hF, hG, hD]
        exact ih (Fin.init a)
      -- Rearrange SL split additively (CK has the local AddCommGroup).
      -- h_SL_split (CK): X★(D·ιv) = (X★D)○ιv + (X★D)·ιv - X★(D○ιv).
      -- Apply ckIso, rearrange to: ckIso(X★(D·ιv)) + ckIso(X★(D○ιv))
      --                          = ckIso((X★D)○ιv) + ckIso((X★D)·ιv).
      have h_SL_split_additive :
          ckIsoSymmetricAlgebra
              (oudomGuinStar X
                (D * SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) +
            ckIsoSymmetricAlgebra
              (oudomGuinStar X
                (oudomGuinCirc D
                  (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)))) =
            ckIsoSymmetricAlgebra
              (oudomGuinCirc (oudomGuinStar X D)
                (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) +
            ckIsoSymmetricAlgebra
              (oudomGuinStar X D *
                SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) := by
        -- Apply ckIso to h_SL_split, then rearrange via AddCommGroup (CK side).
        have h := congrArg ckIsoSymmetricAlgebra h_SL_split
        -- h : ckIso (X★(D·ιv)) = ckIso ((X★D)○ιv + (X★D)·ιv - X★(D○ιv))
        rw [map_sub, map_add] at h
        -- h : ckIso(X★(D·ιv)) = (ckIso((X★D)○ιv) + ckIso((X★D)·ιv)) - ckIso(X★(D○ιv))
        -- Rearrange a = b - c ↔ a + c = b via AddCommGroup tactics.
        rw [h]
        abel
      -- GL split (additive form).
      have h_GL_split := GL_product_split_mul_ι F G t
      -- h_GL_split : F * op(G * of'{t}) + F * insertion(op G)(op of'{t})
      --              = insertion(F * op G)(op of'{t}) + op(unop(F * op G) * of'{t})
      -- Goal: ckIso(X★(D·ι(ofTree t))) = F * op(ckIso(D·ι(ofTree t)))
      -- Rewrite ckIso(D · ι(ofTree t)) = G * of'{t}.
      have h_ckIso_DιV :
          ckIsoSymmetricAlgebra
              (D * SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) =
            G * ConnesKreimer.of' ({t} : Multiset _) := by
        rw [map_mul, h_ckIso_ι_ofTree]
      rw [h_ckIso_DιV]
      -- Now goal: ckIso(X★(D·ι(ofTree t))) = F * op(G * of'{t}).
      -- The plan:
      -- (A) Express the (X★D)○ιv term in GL: ckIso((X★D)○ιv) = insertion(op(ckIso(X★D)))(op of'{t}) [substrate 1]
      --     and op(ckIso(X★D)) = F * op G [IH], so
      --     ckIso((X★D)○ιv) = unop(insertion(F * op G)(op of'{t})).
      -- (B) ckIso((X★D)·ιv) = ckIso(X★D) * of'{t} [ring hom + ι_single]
      --                    = unop(F * op G) * of'{t} [IH] (in CK product).
      -- (C) ckIso(X★(D○ιv)) = F * insertion(op G)(op of'{t}) [substrate via h_ih_sum + intertwine]
      -- Combining (A)+(B) on RHS of h_SL_split_additive, and (C) for the third term:
      -- LHS = ckIso(X★(D·ιv)) and RHS = ckIso((X★D)○ιv) + ckIso((X★D)·ιv) - ckIso(X★(D○ιv))
      -- so:
      --   ckIso(X★(D·ιv)) = unop(ins(F*opG)(op of'{t})) + (unop(F*opG)*of'{t}) - F*ins(opG)(op of'{t})
      -- Using h_GL_split: F * op(G * of'{t}) = ins(F*opG)(...) + op(unop(F*opG) * of'{t}) - F * ins(op G)(...)
      -- These should match modulo unop/op being identity.
      --
      -- Step (A): rewrite term (X★D)○ιv via substrate.
      have h_term_A :
          ckIsoSymmetricAlgebra
              (oudomGuinCirc (oudomGuinStar X D)
                (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            unop (insertion
              (F * op G)
              (op (ConnesKreimer.of' ({t} : Multiset _)))) := by
        rw [ckIso_circ_intertwine_insertion (oudomGuinStar X D)
              (InsertionAlgebra.ofTree t)]
        rw [h_ckIso_ι_ofTree]
        -- Substitute op(ckIso(X★D)) = F * op G via h_ih_init.
        rw [show op (ckIsoSymmetricAlgebra (oudomGuinStar X D)) =
              F * op G from h_ih_init]
      -- Step (B): rewrite term (X★D)·ιv via map_mul + ι_single + IH.
      have h_term_B :
          ckIsoSymmetricAlgebra
              (oudomGuinStar X D *
                SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) =
            unop (F * op G) *
              ConnesKreimer.of' ({t} : Multiset _) := by
        rw [map_mul, h_ckIso_ι_ofTree]
        -- Need: ckIso(X★D) * of'{t} = unop(F * op G) * of'{t}.
        -- h_ih_init says ckIso(X★D) = F * op G (as GL, but GL=CK by def).
        -- unop(F * op G) = F * op G as CK element (unop is identity).
        rw [show ckIsoSymmetricAlgebra (oudomGuinStar X D) =
              unop (F * op G) from h_ih_init]
      -- Step (C): rewrite term X★(D○ιv) via h_ih_sum.
      have h_term_C :
          ((ckIsoSymmetricAlgebra
              (oudomGuinStar X
                (oudomGuinCirc D
                  (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)))) :
            ConnesKreimer ℤ (Nonplanar α)) : GrossmanLarson ℤ α) =
            F * insertion (op G)
              (op (ConnesKreimer.of' ({t} : Multiset _))) := by
        -- Rewrite LHS via direct chain: use the substrate intertwine on D ○ ι(ofTree t)
        -- and IH-summand sum.
        -- ckIso(D ○ ι(ofTree t)) = unop(insertion(op(ckIso D))(op of'{t}))
        --                       = unop(insertion(op G)(op of'{t}))
        -- so as a CK element, equals the GL `insertion(op G)(op of'{t})`.
        -- Now we need ckIso(X ★ Z) where Z = ckIso(D ○ ι(ofTree t)) (as CK element).
        -- We use h_ih_sum which expresses this as a sum, and the sum-form via
        -- h_DcircTV (D ○ ι v = ∑ algHomL(...)) gives us the sum.
        -- Final identification: F * insertion(op G)(op of'{t}) is in GL; the sum
        -- of F * op(ckIso(algHomL ...)) equals F * op(ckIso(∑ algHomL ...))
        -- (by map_sum + multiplication distributivity).
        rw [h_ih_sum]
        -- Goal: ∑ i, F * op(ckIso(algHomL(tprod _ ...))) = F * insertion(op G)(op of'{t})
        -- Convert F * (...) to (product F) (...) (definitionally).
        show ∑ i : Fin m, (product F)
          (op (ckIsoSymmetricAlgebra
            (PreLie.OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                (Function.update (Fin.init a) i
                  (Fin.init a i * InsertionAlgebra.ofTree t)))))) =
          F * insertion (op G)
            (op (ConnesKreimer.of' ({t} : Multiset _)))
        -- Push F * out of the sum.
        rw [← _root_.map_sum (product F) _ Finset.univ]
        -- Goal: GL.product F (∑ ...) = F * insertion(op G)(op of'{t})
        show F * _ = _
        congr 1
        -- ∑ i, op(ckIso(algHomL(...))) = op(ckIso(∑ i, algHomL(...))) [op,ckIso linear].
        -- op : CK → GL is additive. So ∑ op(f i) = op (∑ f i).
        -- Use Finset.sum_congr + the fact that op is the identity coercion.
        rw [show (∑ i : Fin m, op (ckIsoSymmetricAlgebra
                (PreLie.OudomGuinCircConstruct.algHomL
                  (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                    (Function.update (Fin.init a) i
                      (Fin.init a i * InsertionAlgebra.ofTree t)))))) =
              op (∑ i : Fin m, ckIsoSymmetricAlgebra
                (PreLie.OudomGuinCircConstruct.algHomL
                  (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                    (Function.update (Fin.init a) i
                      (Fin.init a i * InsertionAlgebra.ofTree t))))) from
          -- op is the identity on data, so both sides are equal as CK elements.
          rfl]
        rw [show ∑ i : Fin m,
              ckIsoSymmetricAlgebra
                (PreLie.OudomGuinCircConstruct.algHomL
                  (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                    (Function.update (Fin.init a) i
                      (Fin.init a i * InsertionAlgebra.ofTree t)))) =
            ckIsoSymmetricAlgebra (∑ i : Fin m,
              PreLie.OudomGuinCircConstruct.algHomL
                (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m
                  (Function.update (Fin.init a) i
                    (Fin.init a i * InsertionAlgebra.ofTree t)))) from
          (map_sum ckIsoSymmetricAlgebra.toLinearEquiv.toLinearMap _ _).symm]
        rw [← h_DcircTV]
        rw [ckIso_circ_intertwine_insertion D (InsertionAlgebra.ofTree t)]
        rw [h_ckIso_ι_ofTree]
        -- Goal: op(unop(insertion(op G)(op of'{t}))) = insertion(op G)(op of'{t})
        rfl
      -- Apply h_GL_split + the three step rewrites to close the goal.
      -- h_SL_split_additive (in CK):
      --   LHS_target + ckIso(X★(D○ιv)) = ckIso((X★D)○ιv) + ckIso((X★D)·ιv)
      -- Substitute h_term_A, h_term_B, h_term_C (the latter two as
      -- equations in GL, but since CK = GL by def, all live additively).
      -- After substitution:
      --   LHS_target + F*ins(op G)(op of'{t})
      --     = unop(ins(F*opG)(op of'{t})) + (unop(F*opG) * of'{t})
      -- Apply h_GL_split rearranged:
      --   ins(F*opG)(op of'{t}) + op(unop(F*opG) * of'{t})
      --     = F * op(G * of'{t}) + F * ins(op G)(op of'{t})
      -- The unop/op identity pair turns this CK equality (via CK=GL=def) into:
      --   unop(ins(F*opG)(op of'{t})) + unop(F*opG) * of'{t}
      --     = F * op(G * of'{t}) + F * ins(op G)(op of'{t})
      -- which combined with h_SL_split_additive gives the goal.
      -- Concretely: derive goal by add_right_cancel on F*ins(op G)(op of'{t}).
      -- Goal: LHS_target = F * op(G * of'{t}).
      -- Approach: prove
      --   LHS_target + F*ins(op G)(op of'{t}) = F*op(G*of'{t}) + F*ins(op G)(op of'{t})
      -- and cancel.
      -- Work in CK throughout for the `+` form (avoids GL HAdd mismatch).
      -- Form ALL CK equations from substrates:
      -- (C-as-CK): ckIso(X ★ (D○ι(ofTree t))) = unop(F * insertion(op G)(op of'{t}))
      have h_term_C_CK :
          ckIsoSymmetricAlgebra
              (oudomGuinStar X
                (oudomGuinCirc D
                  (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)))) =
          unop
            (F * insertion (op G)
              (op (ConnesKreimer.of' ({t} : Multiset _)))) :=
        h_term_C
      -- Apply unop to h_GL_split to get a CK equation.
      -- h_GL_split: F*op(G*of'{t}) + F*insertion(op G)(op of'{t})
      --           = insertion(F*op G)(op of'{t}) + op(unop(F*op G) * of'{t})
      -- Take unop of both sides (op_unop = id):
      -- unop(F*op(G*of'{t})) + unop(F*insertion(op G)(op of'{t}))
      --   = unop(insertion(F*op G)(op of'{t})) + (unop(F*op G) * of'{t})
      have h_GL_split_CK :
          unop (F * op
              (G * ConnesKreimer.of' ({t} : Multiset _))) +
            unop (F * insertion (op G)
              (op (ConnesKreimer.of' ({t} : Multiset _)))) =
            unop (insertion (F * op G)
              (op (ConnesKreimer.of' ({t} : Multiset _)))) +
            unop (F * op G) *
              ConnesKreimer.of' ({t} : Multiset _) := by
        have h := congrArg unop h_GL_split
        rw [unop_add, unop_add] at h
        -- The last term has unop ∘ op = id (definitional).
        convert h using 2
        simp only [unop_op]
      -- Now use h_SL_split_additive to combine.
      -- h_SL_split_additive (CK):
      --   ckIso(X★(D·ι(ofTree t))) + ckIso(X★(D○ι(ofTree t)))
      --     = ckIso((X★D)○ι(ofTree t)) + ckIso((X★D)·ι(ofTree t))
      -- Substitute the term_A/B/C-CK forms:
      --   ckIso(X★(D·ι(ofTree t))) + unop(F * ins(op G)(op of'{t}))
      --     = unop(ins(F*op G)(op of'{t})) + (unop(F*op G) * of'{t})
      -- By h_GL_split_CK this equals:
      --   unop(F*op(G*of'{t})) + unop(F*ins(op G)(op of'{t}))
      -- Cancel the common unop(F*ins(op G)(op of'{t})) term.
      have h_goal_CK :
          ckIsoSymmetricAlgebra
              (oudomGuinStar X
                (D * SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            unop (F * op
              (G * ConnesKreimer.of' ({t} : Multiset _))) := by
        have h_LHS_plus_CK :
            ckIsoSymmetricAlgebra
                (oudomGuinStar X
                  (D * SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) +
              unop
                (F * insertion (op G)
                  (op (ConnesKreimer.of' ({t} : Multiset _)))) =
              unop (F * op
                (G * ConnesKreimer.of' ({t} : Multiset _))) +
              unop
                (F * insertion (op G)
                  (op (ConnesKreimer.of' ({t} : Multiset _)))) := by
          -- Apply ← h_term_C_CK ONLY on LHS, then chain rewrites on LHS.
          conv_lhs => rw [← h_term_C_CK]
          rw [h_SL_split_additive, h_term_A, h_term_B]
          -- Now LHS is `unop(ins(F*op G)(...)) + (unop(F*op G) * of'{t})`
          -- and RHS is `unop(F*op(G*of'{t})) + unop(F*ins(op G)(...))`.
          -- These match h_GL_split_CK (with sides swapped).
          exact h_GL_split_CK.symm
        exact add_right_cancel h_LHS_plus_CK
      -- The original goal is the GL form: ckIso(X★(D·ι(ofTree t))) = F * op(G*of'{t}).
      -- h_goal_CK gives the same equation with unop on the GL RHS.
      -- Since CK = GL definitionally and op/unop are identity, this is the goal.
      exact h_goal_CK

/-- **Q5c**: the OG `★` product, transported via `ckIsoSymmetricAlgebra`,
    equals the Grossman-Larson product on `ConnesKreimer ℤ (Nonplanar α)`.

    Lifted from `gl_product_eq_oudomGuinStar_tprod` via `algHomL_surjective`
    + `TA_linearMap_ext_tprod` for Y. Mirrors Q3's lifting pattern
    (`oudomGuinStar_assoc`). Proved sorry-free 2026-06-12. -/
theorem gl_product_eq_oudomGuinStar
    (X Y : SymmetricAlgebra ℤ (InsertionAlgebra α)) :
    ((ckIsoSymmetricAlgebra (oudomGuinStar X Y) : ConnesKreimer ℤ (Nonplanar α)) :
      GrossmanLarson ℤ α) =
      (op (ckIsoSymmetricAlgebra X)) *
      (op (ckIsoSymmetricAlgebra Y)) := by
  -- Reduce to TA-side LinearMap equality via `algHomL_surjective` (for Y),
  -- then TA_linearMap_ext_tprod to per-tprod.
  obtain ⟨z, hz⟩ := PreLie.OudomGuinCircConstruct.algHomL_surjective Y
  subst hz
  -- Both sides are linear maps TA →ₗ GL evaluated at z.
  set f_LHS : TensorAlgebra ℤ (InsertionAlgebra α) →ₗ[ℤ] GrossmanLarson ℤ α :=
    (ckIsoSymmetricAlgebra (α := α)).toLinearMap.comp
      ((oudomGuinStarL X).comp PreLie.OudomGuinCircConstruct.algHomL) with hf_LHS
  set f_RHS : TensorAlgebra ℤ (InsertionAlgebra α) →ₗ[ℤ] GrossmanLarson ℤ α :=
    (product (op (ckIsoSymmetricAlgebra X))).comp
      ((ckIsoSymmetricAlgebra (α := α)).toLinearMap.comp
        PreLie.OudomGuinCircConstruct.algHomL) with hf_RHS
  suffices h_LM : f_LHS = f_RHS by
    have := congrArg
      (fun (f : TensorAlgebra ℤ (InsertionAlgebra α) →ₗ[ℤ] GrossmanLarson ℤ α) => f z)
      h_LM
    simp only [hf_LHS, hf_RHS, LinearMap.comp_apply] at this
    -- `this` should now state the desired equation.
    exact this
  -- Apply TA_linearMap_ext_tprod.
  apply PreLie.OudomGuinCircConstruct.TA_linearMap_ext_tprod
  intro m a
  simp only [hf_LHS, hf_RHS]
  exact gl_product_eq_oudomGuinStar_tprod X m a

/-! ## §3: Q6 — `mul_assoc_basis` for `R = ℤ` via Q3 + Q5

Combining `oudomGuinStar_assoc` (Q3, proved sorry-free in
`OudomGuinCirc.lean`) with `gl_product_eq_oudomGuinStar` (Q5c,
proved above) closes `mul_assoc_basis` for `R = ℤ`. -/

/-- **Q6 (for R = ℤ)**: associativity of the Grossman-Larson product on basis.

    Both Q3 (`oudomGuinStar_assoc`) and Q5c (`gl_product_eq_oudomGuinStar`)
    are proved sorry-free; this theorem combines them. -/
theorem mul_assoc_basis_via_oudom_guin_pbw
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    ((of' F₁ : GrossmanLarson ℤ α) *
        of' F₂) * of' F₃ =
      of' F₁ *
        (of' F₂ * of' F₃) := by
  -- Lift `of' Fᵢ` back through `ckIsoSymmetricAlgebra⁻¹` to SymmetricAlgebra,
  -- apply oudomGuinStar_assoc there, transport back via Q5c.
  set X₁ := ckIsoSymmetricAlgebra.symm
    ((unop (of' F₁ : GrossmanLarson ℤ α))) with hX₁
  set X₂ := ckIsoSymmetricAlgebra.symm
    ((unop (of' F₂ : GrossmanLarson ℤ α))) with hX₂
  set X₃ := ckIsoSymmetricAlgebra.symm
    ((unop (of' F₃ : GrossmanLarson ℤ α))) with hX₃
  -- ckIso X_i = unop(of' F_i) = of' F_i (since ckIso ∘ ckIso.symm = id).
  have hckIsoX₁ : (ckIsoSymmetricAlgebra X₁ : ConnesKreimer ℤ (Nonplanar α)) =
      unop (of' F₁ : GrossmanLarson ℤ α) := by
    rw [hX₁]; exact ckIsoSymmetricAlgebra.apply_symm_apply _
  have hckIsoX₂ : (ckIsoSymmetricAlgebra X₂ : ConnesKreimer ℤ (Nonplanar α)) =
      unop (of' F₂ : GrossmanLarson ℤ α) := by
    rw [hX₂]; exact ckIsoSymmetricAlgebra.apply_symm_apply _
  have hckIsoX₃ : (ckIsoSymmetricAlgebra X₃ : ConnesKreimer ℤ (Nonplanar α)) =
      unop (of' F₃ : GrossmanLarson ℤ α) := by
    rw [hX₃]; exact ckIsoSymmetricAlgebra.apply_symm_apply _
  -- Apply Q5c to peel ckIso ∘ ★ into op(ckIso) * op(ckIso) at each fold.
  have h_LHS_step1 := gl_product_eq_oudomGuinStar (oudomGuinStar X₁ X₂) X₃
  have h_LHS_step2 := gl_product_eq_oudomGuinStar X₁ X₂
  have h_RHS_step1 := gl_product_eq_oudomGuinStar X₁ (oudomGuinStar X₂ X₃)
  have h_RHS_step2 := gl_product_eq_oudomGuinStar X₂ X₃
  -- Use Q3: (X₁ ★ X₂) ★ X₃ = X₁ ★ (X₂ ★ X₃).
  have h_assoc : oudomGuinStar (oudomGuinStar X₁ X₂) X₃ =
      oudomGuinStar X₁ (oudomGuinStar X₂ X₃) :=
    oudomGuinStar_assoc X₁ X₂ X₃
  -- Apply ckIso to h_assoc.
  have h_iso_assoc : (ckIsoSymmetricAlgebra
        (oudomGuinStar (oudomGuinStar X₁ X₂) X₃) : ConnesKreimer ℤ (Nonplanar α)) =
      ckIsoSymmetricAlgebra (oudomGuinStar X₁ (oudomGuinStar X₂ X₃)) :=
    congrArg _ h_assoc
  -- Rewrite both sides via Q5c, then via hckIsoX₁/X₂/X₃ + op_unop.
  rw [h_LHS_step1, h_LHS_step2, hckIsoX₁, hckIsoX₂, hckIsoX₃,
      op_unop, op_unop, op_unop] at h_iso_assoc
  rw [h_RHS_step1, h_RHS_step2, hckIsoX₁, hckIsoX₂, hckIsoX₃,
      op_unop, op_unop, op_unop] at h_iso_assoc
  exact h_iso_assoc

end RootedTree
