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
@cite{oudom-guin-2008} @cite{foissy-2021}

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
  equals the Grossman-Larson product. Currently `sorry`-fenced.

* `GrossmanLarson.mul_assoc_basis_via_oudom_guin_pbw` (Q6) : closure of
  `mul_assoc_basis` for `R = ℤ` using `oudomGuinStar_assoc` + Q5c.
  Currently `sorry`-fenced (depends on Q3's mul case + Q5c).

## Status

This file is the **Option 2 exploration** for the
`[[project-prelie-pbw-pivot]]`: verify the bridge structure works
BEFORE committing to the ~600-950 LOC Sweedler bash for Q3's mul case.

If Q5c proves tractable (~50-150 LOC), Q3's bash is worth the investment.
If Q5c has its own obstacles, the project pivots elsewhere.
-/

open PreLie.OudomGuinCirc

namespace RootedTree

-- OG `oudomGuinStar` is declared with `variable {L : Type}` (universe 0).
-- Restrict `α : Type` so `Nonplanar α : Type`, `InsertionAlgebra α : Type`.
-- Universe-polymorphizing OG is deferred to mathlib-quality polish.
variable {α : Type} [DecidableEq (Nonplanar α)]

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
    lands in `AddMonoidAlgebra ℤ (Multiset (Nonplanar α)) = ConnesKreimer ℤ _`. -/
noncomputable def ckIsoSymmetricAlgebra :
    SymmetricAlgebra ℤ (InsertionAlgebra α) ≃ₐ[ℤ] ConnesKreimer ℤ (Nonplanar α) :=
  (SymmetricAlgebra.equivMvPolynomial
      (Finsupp.basisSingleOne (R := ℤ) (ι := Nonplanar α) :
        Module.Basis (Nonplanar α) ℤ (InsertionAlgebra α))).trans
    (AddMonoidAlgebra.domCongr ℤ ℤ (Multiset.toFinsupp (α := Nonplanar α)).symm)

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
  show (AddMonoidAlgebra.domCongr ℤ ℤ Multiset.toFinsupp.symm)
        ((SymmetricAlgebra.equivMvPolynomial
            (Finsupp.basisSingleOne (R := ℤ) (ι := Nonplanar α) :
              Module.Basis (Nonplanar α) ℤ (InsertionAlgebra α)))
          ((SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) (Finsupp.single t 1))) = _
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
  show (AddMonoidAlgebra.domCongr ℤ ℤ Multiset.toFinsupp.symm)
      (AddMonoidAlgebra.single (Finsupp.single t 1) 1 :
        AddMonoidAlgebra ℤ (Nonplanar α →₀ ℕ)) = _
  rw [AddMonoidAlgebra.domCongr_single]
  -- Multiset.toFinsupp.symm (single t 1) = {t}
  have h2 : (Multiset.toFinsupp (α := Nonplanar α)).symm (Finsupp.single t 1) =
        ({t} : Multiset (Nonplanar α)) := by
    rw [AddEquiv.symm_apply_eq]; exact (Multiset.toFinsupp_singleton t).symm
  rw [h2]
  rfl

/-! ## §1c: Counit transport

The iso `ckIsoSymmetricAlgebra` is an `AlgEquiv`, so it intertwines the
counits of `SL = SymmetricAlgebra ℤ (InsertionAlgebra α)` (whose canonical
counit is `SymmetricAlgebra.algebraMapInv`) and `ConnesKreimer ℤ (Nonplanar α)`
(whose counit is `ConnesKreimer.counit`). Both are AlgHoms to `ℤ` that
vanish on `ι`-image, so `SymmetricAlgebra.algHom_ext` reduces equality to
a pointwise check on `ι`. -/

/-- **Counit transport** for `ckIsoSymmetricAlgebra`: the CK counit composed
    with `ckIso` equals `SymmetricAlgebra.algebraMapInv`. Both AlgHoms
    `SL →ₐ[ℤ] ℤ` vanish on `ι` (LHS via `counit_of'` with `|{t}| = 1 ≠ 0`;
    RHS via `algebraMapInv_ι`), and `SymmetricAlgebra.algHom_ext` lifts the
    `ι`-restricted equality to the full AlgHom. -/
@[simp] theorem counit_ckIsoSymmetricAlgebra
    (X : SymmetricAlgebra ℤ (InsertionAlgebra α)) :
    (ConnesKreimer.counit (R := ℤ) (T := Nonplanar α))
        (ckIsoSymmetricAlgebra X) =
      SymmetricAlgebra.algebraMapInv
        (R := ℤ) (M := InsertionAlgebra α) X := by
  have h_alg :
      ((ConnesKreimer.counit (R := ℤ) (T := Nonplanar α)).comp
          (ckIsoSymmetricAlgebra (α := α)).toAlgHom) =
        (SymmetricAlgebra.algebraMapInv
          (R := ℤ) (M := InsertionAlgebra α)) := by
    apply SymmetricAlgebra.algHom_ext
    -- Equality of LinearMaps `LL →ₗ[ℤ] ℤ` via Basis extension.
    -- `Finsupp.basisSingleOne` is the canonical basis of `LL = Nonplanar α →₀ ℤ`.
    apply Module.Basis.ext
      (Finsupp.basisSingleOne (R := ℤ) (ι := Nonplanar α) :
        Module.Basis (Nonplanar α) ℤ (InsertionAlgebra α))
    intro t
    -- Goal: `counit (ckIso (ι (single t 1))) = algebraMapInv (ι (single t 1))`.
    -- LHS = counit (of'({t})) = 0 (|{t}| = 1).
    -- RHS = algebraMapInv (ι _) = 0.
    show ConnesKreimer.counit (ckIsoSymmetricAlgebra
          ((SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) (Finsupp.single t (1 : ℤ)))) =
        SymmetricAlgebra.algebraMapInv
          ((SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) (Finsupp.single t (1 : ℤ)))
    rw [ckIsoSymmetricAlgebra_ι_single, ConnesKreimer.counit_of',
        SymmetricAlgebra.algebraMapInv_ι]
    simp [Multiset.card_singleton]
  exact AlgHom.congr_fun h_alg X

/-! ## §2: Q5c — bridge `oudomGuinStar` ↔ `GrossmanLarson.product`

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
   (via `GrossmanLarson.mul_one`).
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
stated as `sorry` pending dedicated combinatorial work. -/

/-! ### Sub-substrates for Q5c's substrate 1

Three combinatorial bridges that substrate 1 (`ckIso_circ_intertwine_insertion`)
will use:

1. **Planar bridge**: `Planar.Pathed.insertion T [s] = Planar.insertSum T s`.
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

Each is a standalone combinatorial lemma; closure roadmap is in the
docstring. All three are currently `sorry`-fenced. -/

/-- Helper: `listChoices V 1 = V.map (fun v => [v])`. By induction on `V`. -/
private theorem listChoices_one {β : Type*} (V : List β) :
    Planar.Pathed.listChoices V 1 = V.map (fun v => [v]) := by
  induction V with
  | nil => rfl
  | cons head tail _ =>
    -- Both sides reduce to `[head] :: tail.map (fun v => [v])` definitionally.
    show ([head] :: tail.flatMap (fun v => [[v]])) =
        [head] :: tail.map (fun v => [v])
    congr 1

/-- **Sub-substrate 1.1**: Planar Foissy multi-graft on single guest
    reduces to `insertSum`. Uses `listChoices V 1 = V.map [·]`,
    `multiGraft_singleton`, and `insertSum_eq_coe_map_insertAt`. -/
private theorem planar_insertion_singleton_guest_eq_insertSum
    (T s : Planar α) :
    Planar.Pathed.insertion T [s] = Planar.insertSum T s := by
  rw [Planar.Pathed.insertion_def]
  rw [Planar.insertSum_eq_coe_map_insertAt]
  simp only [List.length_singleton]
  rw [listChoices_one, List.map_map]
  -- Now: Multiset.ofList ((vertices T).map (fun v => multiGraft T ([v].zip [s])))
  --    = ((vertices T).map (fun p => insertAt p s T) : Multiset _)
  -- The two sides are `Multiset.ofList`/`coe` of two lists differing only by a funext.
  congr 1
  apply List.map_congr_left
  intro v _hv
  show Planar.Pathed.multiGraft T [(v, s)] = Planar.Pathed.insertAt v s T
  exact Planar.Pathed.multiGraft_singleton T v s

/-- Helper: `insertionForest [T] [s'] = (insertion T [s']).map (fun T' => [T'])`.
    Reduces the bind over `[true, false]` assignments: `[true]` contributes
    `(insertion T [s']).map (fun T' => [T'])`, `[false]` contributes `0`
    (because `insertionForest [] [s'] = 0`). -/
private theorem insertionForest_singleton_singleton (T s' : Planar α) :
    Planar.Pathed.insertionForest [T] [s'] =
      (Planar.Pathed.insertion T [s']).map (fun T' => [T']) := by
  rw [Planar.Pathed.insertionForest_cons_cons]
  -- listChoices [true, false] 1 = [[true], [false]] by computation.
  show ((Multiset.ofList [[true], [false]]).bind fun assignment =>
        (Planar.Pathed.insertion T
          (([s'].zip assignment).filterMap fun p => if p.snd then some p.fst else none)).bind
          fun T' => (Planar.Pathed.insertionForest []
              (([s'].zip assignment).filterMap fun p => if p.snd then none else some p.fst)).map
            fun F' => T' :: F') =
      (Planar.Pathed.insertion T [s']).map (fun T' => [T'])
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
  show (Planar.Pathed.insertion T [s']).bind
        (fun T' => (Planar.Pathed.insertionForest [] []).map (fun F' => T' :: F'))
      + (Planar.Pathed.insertion T []).bind
        (fun T' => (Planar.Pathed.insertionForest [] [s']).map (fun F' => T' :: F')) =
      (Planar.Pathed.insertion T [s']).map (fun T' => [T'])
  rw [Planar.Pathed.insertionForest_nil_nil,
      Planar.Pathed.insertionForest_empty_host_nonempty_guests]
  simp only [Multiset.map_singleton, Multiset.bind_singleton, Multiset.map_zero,
             Multiset.bind_zero, add_zero]

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
  show (Planar.Pathed.insertionForest [Quotient.out t] [Quotient.out s]).map
        (fun L => (Multiset.ofList (L.map Nonplanar.mk) : Multiset (Nonplanar α))) =
      (Nonplanar.insertSum t s).map fun r => ({r} : Multiset (Nonplanar α))
  -- Step 2: Reduce insertionForest [t.out] [s.out] via the helper.
  rw [insertionForest_singleton_singleton, Multiset.map_map]
  -- Step 3: Sub-substrate 1.1 reduces insertion to insertSum.
  rw [planar_insertion_singleton_guest_eq_insertSum]
  -- Goal:
  --   (Planar.insertSum t.out s.out).map
  --       (Function.comp (fun L => Multiset.ofList (L.map mk)) (fun T' => [T']))
  --   = (Nonplanar.insertSum t s).map (fun r => {r})
  -- Step 4: Reduce insertSum t s via Quotient.out_eq + Nonplanar.mk_insertSum.
  conv_rhs => rw [show t = Nonplanar.mk (Quotient.out t) from (Quotient.out_eq t).symm,
                  show s = Nonplanar.mk (Quotient.out s) from (Quotient.out_eq s).symm]
  rw [Nonplanar.mk_insertSum, Multiset.map_map]
  rfl

/-! ### Local op/unop simp lemmas

`GrossmanLarson.op` and `GrossmanLarson.unop` are identity coercions
between `ConnesKreimer ℤ (Nonplanar α)` and `GrossmanLarson ℤ α` (which
are definitionally equal). The forwarded `AddCommMonoid` and `Module ℤ`
instances make `op`/`unop` ℤ-linear; the lemmas below let `simp` cleanly
push `op`/`unop` through `+`, `0`, and `•`. -/

@[local simp]
private theorem op_zero :
    GrossmanLarson.op (0 : ConnesKreimer ℤ (Nonplanar α)) = (0 : GrossmanLarson ℤ α) := rfl

@[local simp]
private theorem op_add (x y : ConnesKreimer ℤ (Nonplanar α)) :
    GrossmanLarson.op (x + y) = GrossmanLarson.op x + GrossmanLarson.op y := rfl

@[local simp]
private theorem op_smul (r : ℤ) (x : ConnesKreimer ℤ (Nonplanar α)) :
    GrossmanLarson.op (r • x) = r • GrossmanLarson.op x := rfl

@[local simp]
private theorem unop_zero :
    GrossmanLarson.unop (0 : GrossmanLarson ℤ α) = (0 : ConnesKreimer ℤ (Nonplanar α)) := rfl

@[local simp]
private theorem unop_add (x y : GrossmanLarson ℤ α) :
    GrossmanLarson.unop (x + y) = GrossmanLarson.unop x + GrossmanLarson.unop y := rfl

@[local simp]
private theorem unop_smul (r : ℤ) (x : GrossmanLarson ℤ α) :
    GrossmanLarson.unop (r • x) = r • GrossmanLarson.unop x := rfl

/-- **Basis form of sub-substrate 1.3**: GL Leibniz at basis level.

    For `F_A, F_B : Forest, v : Nonplanar α`:
    `insertion (of' (F_A + F_B)) (of' {v}) =
        op (of' F_A * unop (insertion (of' F_B) (of' {v})))
      + op (unop (insertion (of' F_A) (of' {v})) * of' F_B)`

    Follows from `insertion_mul_distrib` with `C := {v}`. Since
    `{v}.powerset = 0 ::ₘ {{v}}`, the sum has exactly 2 terms; each
    reduces via `of'_zero` + `insertion_one_right`. The `unop` on `of' F_A`
    and `of' F_B` collapses to the CK side by definitional equality
    (`unop` and `GrossmanLarson.of'` are both identity wrt the underlying
    `ConnesKreimer.of'`). -/
private theorem GL_insertion_leibniz_basis_form
    (F_A F_B : Forest (Nonplanar α)) (v : Nonplanar α) :
    GrossmanLarson.insertion (R := ℤ)
        (GrossmanLarson.of' (F_A + F_B))
        (GrossmanLarson.of' ({v} : Multiset (Nonplanar α))) =
      GrossmanLarson.op
        ((ConnesKreimer.of' F_A : ConnesKreimer ℤ (Nonplanar α)) *
          GrossmanLarson.unop (GrossmanLarson.insertion (R := ℤ)
            (GrossmanLarson.of' F_B)
            (GrossmanLarson.of' ({v} : Multiset _)))) +
      GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion (R := ℤ)
            (GrossmanLarson.of' F_A)
            (GrossmanLarson.of' ({v} : Multiset _))) *
          (ConnesKreimer.of' F_B : ConnesKreimer ℤ (Nonplanar α))) := by
  -- Align DecidableEq instance with `insertion_mul_distrib`'s internal
  -- `Classical.decEq` so that subsequent `tsub_zero`/`tsub_self` rewrites
  -- see a single Multiset.instSub instance.
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [GrossmanLarson.insertion_mul_distrib]
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
  rw [GrossmanLarson.of'_zero,
      GrossmanLarson.insertion_one_right,
      GrossmanLarson.insertion_one_right]
  -- LHS: op (unop (of' F_A) * unop (insertion (of' F_B) (of' {v}))) +
  --      op (unop (insertion (of' F_A) (of' {v})) * unop (of' F_B))
  -- RHS: op (of' F_A * unop (insertion (of' F_B) (of' {v}))) +
  --      op (unop (insertion (of' F_A) (of' {v})) * of' F_B)
  -- unop (of' F_X) = of' F_X by definitional equality.
  rfl

/-- **Helper for 1.3**: Leibniz rule with right argument forced to be a
    Forest-basis element. Bilinear-in-A extension of the basis form via
    `Finsupp.induction_linear` on A (following `insertion_mul_distrib_gen`'s
    pattern of explicit `show` casts to navigate type-alias unfolding). -/
private theorem GL_insertion_leibniz_basis_right
    (A : ConnesKreimer ℤ (Nonplanar α)) (F_B : Forest (Nonplanar α))
    (v : Nonplanar α) :
    GrossmanLarson.insertion
        (GrossmanLarson.op (A * (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))) =
      GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op A)
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))) *
            (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
      GrossmanLarson.op
        (A * GrossmanLarson.unop (GrossmanLarson.insertion
          (GrossmanLarson.op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))))) := by
  refine Finsupp.induction_linear A ?_ ?_ ?_
  · -- A = 0: every term has a `0 *` or `* 0` or `unop 0`/`op 0` that
    -- reduces to 0 of the appropriate type.
    show GrossmanLarson.insertion
        (GrossmanLarson.op ((0 : ConnesKreimer ℤ (Nonplanar α)) *
          (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))) =
      GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion
            (GrossmanLarson.op (0 : ConnesKreimer ℤ (Nonplanar α)))
            (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))) *
            (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
      GrossmanLarson.op
        ((0 : ConnesKreimer ℤ (Nonplanar α)) *
          GrossmanLarson.unop (GrossmanLarson.insertion
            (GrossmanLarson.op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
            (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))))
    simp only [zero_mul, mul_zero, op_zero, unop_zero,
               (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_zero,
               LinearMap.zero_apply, add_zero]
  · -- additive
    intro A₁ A₂ ih₁ ih₂
    -- A₁, A₂ are typed as `Forest →₀ ℤ` by `Finsupp.induction_linear`.
    -- Cast each to `ConnesKreimer ℤ (Nonplanar α)` via `let`.
    let A₁' : ConnesKreimer ℤ (Nonplanar α) := A₁
    let A₂' : ConnesKreimer ℤ (Nonplanar α) := A₂
    show GrossmanLarson.insertion
        (GrossmanLarson.op ((A₁' + A₂') *
          (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))) =
        GrossmanLarson.op
          (GrossmanLarson.unop (GrossmanLarson.insertion
              (GrossmanLarson.op (A₁' + A₂')) _) *
              (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
        GrossmanLarson.op
          ((A₁' + A₂') *
            GrossmanLarson.unop (GrossmanLarson.insertion
              (GrossmanLarson.op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
              (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))))
    rw [add_mul, op_add,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, ih₁, ih₂]
    rw [op_add,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, unop_add, add_mul, add_mul]
    -- Now both sides are sums of `op (...)` expressions. Combine via op_add.
    simp only [← op_add]
    -- Goal: op(big CK expr) = op(big CK expr). Equate inside, then ring.
    congr 1
    ring
  · -- single F_A r
    intro F_A r
    -- Cast `Finsupp.single F_A r` from Finsupp to CK type explicitly.
    let A_single : ConnesKreimer ℤ (Nonplanar α) := Finsupp.single F_A r
    show GrossmanLarson.insertion
        (GrossmanLarson.op (A_single * (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))) =
        GrossmanLarson.op
          (GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op A_single) _) *
              (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)) +
        GrossmanLarson.op
          (A_single * GrossmanLarson.unop (GrossmanLarson.insertion
            (GrossmanLarson.op (ConnesKreimer.of' F_B : ConnesKreimer ℤ _))
            (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))))
    -- Unfold A_single = r • of' F_A.
    have hA : A_single = r • (ConnesKreimer.of' F_A : ConnesKreimer ℤ (Nonplanar α)) := by
      show (Finsupp.single F_A r : ConnesKreimer ℤ (Nonplanar α)) =
            r • (ConnesKreimer.of' F_A : ConnesKreimer ℤ _)
      rw [ConnesKreimer.of'_apply]
      exact (Finsupp.smul_single_one F_A r).symm
    rw [hA]
    rw [smul_mul_assoc, ← ConnesKreimer.of'_add, op_smul,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    -- Bridge `op (of' (F_A + F_B))` ≡ `GrossmanLarson.of' (F_A + F_B)` so
    -- `GL_insertion_leibniz_basis_form` (stated with `GrossmanLarson.of'`)
    -- applies.
    show r • GrossmanLarson.insertion
        (GrossmanLarson.of' (F_A + F_B)) (GrossmanLarson.of' ({v} : Multiset _)) =
      _
    rw [GL_insertion_leibniz_basis_form, op_smul,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    simp only [smul_add, unop_smul, smul_mul_assoc, mul_smul_comm, op_smul]
    rw [add_comm]
    rfl

/-- **Sub-substrate 1.3**: GL Leibniz rule for `insertion` w.r.t. CK product
    on first argument (single guest). Bilinear-in-B extension of
    `GL_insertion_leibniz_basis_right` (which already handles general A). -/
private theorem GL_insertion_leibniz_left_singleton_guest
    (A B : ConnesKreimer ℤ (Nonplanar α)) (v : Nonplanar α) :
    GrossmanLarson.insertion (GrossmanLarson.op (A * B))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset (Nonplanar α)))) =
      GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op A)
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset (Nonplanar α))))) * B) +
      GrossmanLarson.op
        (A * GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op B)
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset (Nonplanar α)))))) := by
  refine Finsupp.induction_linear B ?_ ?_ ?_
  · -- B = 0
    show GrossmanLarson.insertion
        (GrossmanLarson.op (A * (0 : ConnesKreimer ℤ (Nonplanar α))))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))) =
      GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op A)
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))) *
            (0 : ConnesKreimer ℤ (Nonplanar α))) +
      GrossmanLarson.op
        (A * GrossmanLarson.unop (GrossmanLarson.insertion
          (GrossmanLarson.op (0 : ConnesKreimer ℤ (Nonplanar α)))
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))))
    simp only [mul_zero, op_zero,
               (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_zero,
               LinearMap.zero_apply, unop_zero, add_zero, zero_add]
  · -- B = B₁ + B₂
    intro B₁ B₂ ih₁ ih₂
    let B₁' : ConnesKreimer ℤ (Nonplanar α) := B₁
    let B₂' : ConnesKreimer ℤ (Nonplanar α) := B₂
    show GrossmanLarson.insertion
        (GrossmanLarson.op (A * (B₁' + B₂')))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))) =
      GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op A)
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))) * (B₁' + B₂')) +
      GrossmanLarson.op
        (A * GrossmanLarson.unop (GrossmanLarson.insertion
          (GrossmanLarson.op (B₁' + B₂'))
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))))
    rw [mul_add, op_add,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, ih₁, ih₂]
    -- Distribute the (B₁' + B₂') on RHS: both via `mul_add` and via
    -- `op_add` then `insertion.map_add`.
    simp only [mul_add, op_add,
               (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
               LinearMap.add_apply, unop_add]
    simp only [mul_add, ← op_add]
    congr 1
    ring
  · -- B = single F_B r
    intro F_B r
    let B_single : ConnesKreimer ℤ (Nonplanar α) := Finsupp.single F_B r
    show GrossmanLarson.insertion
        (GrossmanLarson.op (A * B_single))
        (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _))) =
      GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op A)
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))) * B_single) +
      GrossmanLarson.op
        (A * GrossmanLarson.unop (GrossmanLarson.insertion
          (GrossmanLarson.op B_single)
          (GrossmanLarson.op (ConnesKreimer.of' ({v} : Multiset _)))))
    have hB : B_single = r • (ConnesKreimer.of' F_B : ConnesKreimer ℤ (Nonplanar α)) := by
      show (Finsupp.single F_B r : ConnesKreimer ℤ (Nonplanar α)) =
            r • (ConnesKreimer.of' F_B : ConnesKreimer ℤ _)
      rw [ConnesKreimer.of'_apply]
      exact (Finsupp.smul_single_one F_B r).symm
    rw [hB]
    -- A * (r • of' F_B) = r • (A * of' F_B). Then op + insertion scale out.
    rw [mul_smul_comm, op_smul,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply, GL_insertion_leibniz_basis_right, op_smul,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    simp only [smul_add, unop_smul, smul_mul_assoc, mul_smul_comm, op_smul]

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

    Proof by `SymmetricAlgebra.induction` on X. **TODO**: 4 cases:
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
    GrossmanLarson.unop
      (GrossmanLarson.insertion (GrossmanLarson.op (ckIsoSymmetricAlgebra X))
        (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _)))) := by
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
      GrossmanLarson.unop (GrossmanLarson.insertion
        (GrossmanLarson.op (ckIsoSymmetricAlgebra
          (algebraMap ℤ (SymmetricAlgebra ℤ (InsertionAlgebra α)) r)))
        (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _))))
    rw [AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one, op_smul,
        show GrossmanLarson.op (1 : ConnesKreimer ℤ (Nonplanar α)) =
            (1 : GrossmanLarson ℤ α) from rfl,
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_smul,
        LinearMap.smul_apply]
    -- Goal: 0 = (r • insertion 1 (op (of' {t}))).unop
    rw [show GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset (Nonplanar α))) =
            GrossmanLarson.of' ({t} : Multiset _) from rfl]
    rw [GrossmanLarson.insertion_one_of'_ne_zero ({t} : Multiset _)
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
        (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
        LinearMap.add_apply, unop_add]
  | ι w =>
    -- w : InsertionAlgebra α. Use Finsupp.induction_linear.
    refine Finsupp.induction_linear w ?_ ?_ ?_
    · -- w = 0: ι 0 = 0; both sides 0.
      show ckIsoSymmetricAlgebra ((oudomGuinCirc
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0))
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            GrossmanLarson.unop ((GrossmanLarson.insertion
              (GrossmanLarson.op (ckIsoSymmetricAlgebra
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0))))
              (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _))))
      rw [LinearMap.map_zero (SymmetricAlgebra.ι ℤ (InsertionAlgebra α))]
      rw [show oudomGuinCirc (R := ℤ) (0 : SymmetricAlgebra ℤ _)
                (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t)) = 0 by
            rw [oudomGuinCirc_eq_ofConv, map_zero, WithConv.ofConv_zero,
                LinearMap.zero_apply]]
      simp only [map_zero, op_zero,
                 (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_zero,
                 LinearMap.zero_apply, unop_zero]
    · -- w = w₁ + w₂: linearity in w.
      intro w₁ w₂ ih₁ ih₂
      let w₁' : InsertionAlgebra α := w₁
      let w₂' : InsertionAlgebra α := w₂
      show ckIsoSymmetricAlgebra ((oudomGuinCirc
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (w₁' + w₂')))
              (SymmetricAlgebra.ι ℤ _ (InsertionAlgebra.ofTree t))) =
            GrossmanLarson.unop ((GrossmanLarson.insertion
              (GrossmanLarson.op (ckIsoSymmetricAlgebra
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (w₁' + w₂')))))
              (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _))))
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
          (GrossmanLarson.insertion : GrossmanLarson ℤ α →ₗ[ℤ] _).map_add,
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
            GrossmanLarson.unop ((GrossmanLarson.insertion
              (GrossmanLarson.op (ckIsoSymmetricAlgebra
                (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w_single))))
              (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _))))
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
        simp only [_root_.map_smul, WithConv.ofConv_smul, LinearMap.smul_apply]
        rw [← oudomGuinCirc_eq_ofConv]
        exact ckIsoSymmetricAlgebra.toLinearEquiv.map_smul r _
      have rhs_reduce : GrossmanLarson.unop ((GrossmanLarson.insertion
                (GrossmanLarson.op (ckIsoSymmetricAlgebra
                  (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) w_single))))
                (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _)))) =
            r • GrossmanLarson.unop ((GrossmanLarson.insertion
                (GrossmanLarson.op (ckIsoSymmetricAlgebra
                  (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)
                    (InsertionAlgebra.ofTree s)))))
                (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _)))) := by
        rw [hw]
        simp only [_root_.map_smul, op_smul, unop_smul, LinearMap.smul_apply,
                   LinearMap.map_smul]
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
      rw [show GrossmanLarson.op (ConnesKreimer.of' ({s} : Multiset (Nonplanar α))) =
              GrossmanLarson.of' ({s} : Multiset _) from rfl,
          show GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset (Nonplanar α))) =
              GrossmanLarson.of' ({t} : Multiset _) from rfl,
          GrossmanLarson.insertion_of'_of']
      show ((Nonplanar.insertSum s t).map fun r' =>
              (ConnesKreimer.of' ({r'} : Multiset (Nonplanar α)) :
                ConnesKreimer ℤ _)).sum =
          GrossmanLarson.unop (GrossmanLarson.insertionBasis ({s} : Multiset _)
              ({t} : Multiset _))
      rw [show GrossmanLarson.insertionBasis ({s} : Multiset (Nonplanar α))
              ({t} : Multiset _) =
            ((Nonplanar.insertionMultiset ({s} : Multiset _) ({t} : Multiset _)).map
              fun F' => (GrossmanLarson.of' (R := ℤ) F' :
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
    show GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op (ckIsoSymmetricAlgebra X))
            (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _)))) * ckIsoSymmetricAlgebra Y +
        ckIsoSymmetricAlgebra X *
          GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op (ckIsoSymmetricAlgebra Y))
            (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _)))) =
      GrossmanLarson.unop (GrossmanLarson.op
        (GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op (ckIsoSymmetricAlgebra X))
          (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _)))) * ckIsoSymmetricAlgebra Y) +
        GrossmanLarson.op
          (ckIsoSymmetricAlgebra X *
            GrossmanLarson.unop (GrossmanLarson.insertion (GrossmanLarson.op (ckIsoSymmetricAlgebra Y))
              (GrossmanLarson.op (ConnesKreimer.of' ({t} : Multiset _))))))
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

    Pending: sub-substrates 1.1, 1.2, 1.3 above. -/
private theorem ckIso_circ_intertwine_insertion
    (X : SymmetricAlgebra ℤ (InsertionAlgebra α))
    (v : InsertionAlgebra α) :
    (ckIsoSymmetricAlgebra (oudomGuinCirc X (SymmetricAlgebra.ι ℤ _ v)) :
      ConnesKreimer ℤ (Nonplanar α)) =
    GrossmanLarson.unop
      (GrossmanLarson.insertion (GrossmanLarson.op (ckIsoSymmetricAlgebra X))
        (GrossmanLarson.op (ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ _ v)))) := by
  -- v-induction: both sides linear in v.
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · -- v = 0: ι 0 = 0; both sides 0.
    show ckIsoSymmetricAlgebra (oudomGuinCirc X
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0)) =
        GrossmanLarson.unop (GrossmanLarson.insertion
          (GrossmanLarson.op (ckIsoSymmetricAlgebra X))
          (GrossmanLarson.op (ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) 0))))
    rw [LinearMap.map_zero (SymmetricAlgebra.ι ℤ (InsertionAlgebra α))]
    simp only [(oudomGuinCirc (R := ℤ) X).map_zero,
               map_zero, op_zero,
               ((GrossmanLarson.insertion (R := ℤ) (α := α)
                 (GrossmanLarson.op (ckIsoSymmetricAlgebra X))).map_zero),
               unop_zero]
  · -- v = v₁ + v₂: linearity in v.
    intro v₁ v₂ ih₁ ih₂
    let v₁' : InsertionAlgebra α := v₁
    let v₂' : InsertionAlgebra α := v₂
    show ckIsoSymmetricAlgebra (oudomGuinCirc X
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (v₁' + v₂'))) =
        GrossmanLarson.unop (GrossmanLarson.insertion
          (GrossmanLarson.op (ckIsoSymmetricAlgebra X))
          (GrossmanLarson.op (ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (v₁' + v₂')))))
    rw [LinearMap.map_add (SymmetricAlgebra.ι ℤ (InsertionAlgebra α)) v₁' v₂',
        (oudomGuinCirc (R := ℤ) X).map_add, map_add, ih₁, ih₂,
        map_add, op_add,
        ((GrossmanLarson.insertion (R := ℤ) (α := α)
          (GrossmanLarson.op (ckIsoSymmetricAlgebra X))).map_add _ _), unop_add]
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
        GrossmanLarson.unop ((GrossmanLarson.insertion
          (GrossmanLarson.op (ckIsoSymmetricAlgebra X)))
          (GrossmanLarson.op (ckIsoSymmetricAlgebra
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
    have rhs_reduce : GrossmanLarson.unop ((GrossmanLarson.insertion
            (GrossmanLarson.op (ckIsoSymmetricAlgebra X)))
            (GrossmanLarson.op (ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) v_single)))) =
          r • GrossmanLarson.unop ((GrossmanLarson.insertion
            (GrossmanLarson.op (ckIsoSymmetricAlgebra X)))
            (GrossmanLarson.op (ckIsoSymmetricAlgebra
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
      rw [((GrossmanLarson.insertion (R := ℤ) (α := α)
            (GrossmanLarson.op (ckIsoSymmetricAlgebra X))).map_smul r _)]
      rw [unop_smul]
    rw [lhs_reduce, rhs_reduce, h_basis]
    -- Now: r • (insertion ... (op (of' {t}))).unop =
    --      r • (insertion ... (op (ckIso (ι (ofTree t))))).unop
    -- Equal since ckIso (ι (ofTree t)) = of' {t}.
    rw [show ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ (InsertionAlgebra α) (InsertionAlgebra.ofTree t)) =
          ConnesKreimer.of' ({t} : Multiset _) from
        ckIsoSymmetricAlgebra_ι_single t]

/-- **Q5c — pre-Lie PBW iso for Hopf algebras of rooted trees**.

    The OG `★` product on `S(InsertionAlgebra α)`, transported via
    `ckIsoSymmetricAlgebra`, equals the Grossman-Larson product on
    `ConnesKreimer ℤ (Nonplanar α)`.

    `ckIso (X ★ Y) = unop (op (ckIso X) * op (ckIso Y))`

    **This is a known result** in the literature:
    * Foissy 2002, "Les algèbres de Hopf des arbres enracinés décorés"
      (arXiv:math/0105212), §13.3 Prop 85 + Cor 86: identifies
      `(Ker Φ)^⊥ ⊂ HP,R` with the universal enveloping algebra of the
      Grossman-Larson Lie algebra, with the product matching `★`.
    * Manchon, "Hopf algebras, from basics to applications to
      renormalization" (arXiv:math/0408405) — survey treatment.
    * Oudom-Guin 2008, "On the Lie envelopping algebra of a pre-Lie
      algebra" (arXiv:math/0404457) — implicit via their construction.

    **Formalization status (2026-05-18)**: `sorry`-fenced as a top-level
    axiom. Previous attempts to close combinatorially:
    * Per-tprod induction with `GL_product_split_mul_ι` substrate
      (deprecated 2026-05-17 — bridge to `insertionMultiset_assoc`'s
      A3.3 keystone, multi-session dead-end).
    * Pairing-route via `gl_product_eq_oudomGuinStar_via_pairing`
      (`OudomGuinBridgePairing.lean`) — also blocked on
      A3.3-family combinatorics + multi-tree-z handling.
    * Foissy 2002's planar-bialgebra dual identification — would
      require substantial new planar substrate (~1000-2000 LOC).

    Closure is **deferred**. Downstream consumers (`bMinusLin_gl_mul_via_pbw`,
    Q6 = `mul_assoc_basis_via_oudom_guin_pbw`, MCB Lemma 1.2.10) trust
    this as a named axiom. -/
theorem gl_product_eq_oudomGuinStar
    (X Y : SymmetricAlgebra ℤ (InsertionAlgebra α)) :
    ((ckIsoSymmetricAlgebra (oudomGuinStar X Y) : ConnesKreimer ℤ (Nonplanar α)) :
      GrossmanLarson ℤ α) =
      (GrossmanLarson.op (ckIsoSymmetricAlgebra X)) *
      (GrossmanLarson.op (ckIsoSymmetricAlgebra Y)) := by
  sorry

/-! ## §3: Q6 — `mul_assoc_basis` for `R = ℤ` via Q3 + Q5

Combining `oudomGuinStar_assoc` (Q3, **sorry-free** as of 2026-05-17) with
`gl_product_eq_oudomGuinStar` (Q5c, single top-level sorry — the pre-Lie
PBW iso, a known result) closes `mul_assoc_basis` for `R = ℤ`. -/

/-- **Q6 (for R = ℤ)**: associativity of the Grossman-Larson product on basis.

    Sorry-fenced on Q5c (`gl_product_eq_oudomGuinStar`). The mechanical
    wiring (lift via `ckIsoSymmetricAlgebra.symm`, apply `oudomGuinStar_assoc`
    on SL side, transport back via Q5c) is straightforward (~10-20 LOC). -/
theorem GrossmanLarson.mul_assoc_basis_via_oudom_guin_pbw
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    ((GrossmanLarson.of' F₁ : GrossmanLarson ℤ α) *
        GrossmanLarson.of' F₂) * GrossmanLarson.of' F₃ =
      GrossmanLarson.of' F₁ *
        (GrossmanLarson.of' F₂ * GrossmanLarson.of' F₃) := by
  -- Lift each `of' Fᵢ` back to S(L) via `ckIsoSymmetricAlgebra.symm`.
  set X₁ : SymmetricAlgebra ℤ (InsertionAlgebra α) :=
    ckIsoSymmetricAlgebra.symm
      (GrossmanLarson.unop (GrossmanLarson.of' F₁ : GrossmanLarson ℤ α))
    with hX₁
  set X₂ : SymmetricAlgebra ℤ (InsertionAlgebra α) :=
    ckIsoSymmetricAlgebra.symm
      (GrossmanLarson.unop (GrossmanLarson.of' F₂ : GrossmanLarson ℤ α))
    with hX₂
  set X₃ : SymmetricAlgebra ℤ (InsertionAlgebra α) :=
    ckIsoSymmetricAlgebra.symm
      (GrossmanLarson.unop (GrossmanLarson.of' F₃ : GrossmanLarson ℤ α))
    with hX₃
  -- Each `of' Fᵢ` = `op (ckIso Xᵢ)` via `apply_symm_apply` (`unop` is identity).
  have h_F₁ : (GrossmanLarson.of' F₁ : GrossmanLarson ℤ α) =
              GrossmanLarson.op (ckIsoSymmetricAlgebra X₁) := by
    rw [hX₁, ckIsoSymmetricAlgebra.apply_symm_apply]; rfl
  have h_F₂ : (GrossmanLarson.of' F₂ : GrossmanLarson ℤ α) =
              GrossmanLarson.op (ckIsoSymmetricAlgebra X₂) := by
    rw [hX₂, ckIsoSymmetricAlgebra.apply_symm_apply]; rfl
  have h_F₃ : (GrossmanLarson.of' F₃ : GrossmanLarson ℤ α) =
              GrossmanLarson.op (ckIsoSymmetricAlgebra X₃) := by
    rw [hX₃, ckIsoSymmetricAlgebra.apply_symm_apply]; rfl
  rw [h_F₁, h_F₂, h_F₃]
  -- Helper: applied Q5c forward turns `op (ckIso (X ★ Y))` into
  -- `op (ckIso X) * op (ckIso Y)`. The CK→GL coercion in Q5c's LHS
  -- is the same as `op` definitionally; we expose this with `show`.
  have Q5c_op : ∀ (X Y : SymmetricAlgebra ℤ (InsertionAlgebra α)),
      GrossmanLarson.op (ckIsoSymmetricAlgebra (oudomGuinStar X Y)) =
      GrossmanLarson.op (ckIsoSymmetricAlgebra X) *
      GrossmanLarson.op (ckIsoSymmetricAlgebra Y) := fun X Y =>
    gl_product_eq_oudomGuinStar X Y
  -- Fold each binary product back into `op (ckIso (X ★ Y))` via Q5c.
  rw [← Q5c_op X₁ X₂, ← Q5c_op X₂ X₃,
      ← Q5c_op (oudomGuinStar X₁ X₂) X₃,
      ← Q5c_op X₁ (oudomGuinStar X₂ X₃)]
  -- Goal: op (ckIso ((X₁ ★ X₂) ★ X₃)) = op (ckIso (X₁ ★ (X₂ ★ X₃)))
  -- Follows from Q3 (`oudomGuinStar_assoc`, sorry-free 2026-05-17).
  rw [oudomGuinStar_assoc]

/-- **Q6 lift to general elements**: `mul_assoc` for `GrossmanLarson ℤ α`,
    via triple bilinearity reduction (`Finsupp.addHom_ext` thrice) to the
    basis case `mul_assoc_basis_via_oudom_guin_pbw` (Q6). Mirrors the
    structure of `GrossmanLarson.mul_assoc` (general R, sorry-fenced) but
    closes the basis step via Q5c-PBW. -/
theorem GrossmanLarson.mul_assoc_ℤ (F₁ F₂ F₃ : GrossmanLarson ℤ α) :
    F₁ * F₂ * F₃ = F₁ * (F₂ * F₃) := by
  -- Reduce F₁ to single via addHom_ext.
  have h₁ : GrossmanLarson.assocLHSHom F₂ F₃ = GrossmanLarson.assocRHSHom F₂ F₃ := by
    refine Finsupp.addHom_ext fun T₁ a₁ => ?_
    set s₁ : GrossmanLarson ℤ α := Finsupp.single T₁ a₁ with s₁_def
    show GrossmanLarson.assocLHSHom F₂ F₃ s₁ = GrossmanLarson.assocRHSHom F₂ F₃ s₁
    rw [GrossmanLarson.assocLHSHom_apply, GrossmanLarson.assocRHSHom_apply]
    -- Reduce F₂ to single.
    have h₂ : GrossmanLarson.assocLHSHomY s₁ F₃ = GrossmanLarson.assocRHSHomY s₁ F₃ := by
      refine Finsupp.addHom_ext fun T₂ a₂ => ?_
      set s₂ : GrossmanLarson ℤ α := Finsupp.single T₂ a₂ with s₂_def
      show GrossmanLarson.assocLHSHomY s₁ F₃ s₂ = GrossmanLarson.assocRHSHomY s₁ F₃ s₂
      rw [GrossmanLarson.assocLHSHomY_apply, GrossmanLarson.assocRHSHomY_apply]
      -- Reduce F₃ to single.
      have h₃ : GrossmanLarson.assocLHSHomZ s₁ s₂ = GrossmanLarson.assocRHSHomZ s₁ s₂ := by
        refine Finsupp.addHom_ext fun T₃ a₃ => ?_
        set s₃ : GrossmanLarson ℤ α := Finsupp.single T₃ a₃ with s₃_def
        show GrossmanLarson.assocLHSHomZ s₁ s₂ s₃ = GrossmanLarson.assocRHSHomZ s₁ s₂ s₃
        rw [GrossmanLarson.assocLHSHomZ_apply, GrossmanLarson.assocRHSHomZ_apply]
        -- Scalar pull-out to `aᵢ • of' Tᵢ` form.
        rw [show s₁ = a₁ • (GrossmanLarson.of' T₁ : GrossmanLarson ℤ α) from
              (Finsupp.smul_single_one T₁ a₁).symm,
            show s₂ = a₂ • (GrossmanLarson.of' T₂ : GrossmanLarson ℤ α) from
              (Finsupp.smul_single_one T₂ a₂).symm,
            show s₃ = a₃ • (GrossmanLarson.of' T₃ : GrossmanLarson ℤ α) from
              (Finsupp.smul_single_one T₃ a₃).symm]
        simp only [GrossmanLarson.smul_mul_left, GrossmanLarson.mul_smul_right]
        rw [GrossmanLarson.mul_assoc_basis_via_oudom_guin_pbw T₁ T₂ T₃]
      have h₃App := DFunLike.congr_fun h₃ F₃
      rw [GrossmanLarson.assocLHSHomZ_apply, GrossmanLarson.assocRHSHomZ_apply] at h₃App
      exact h₃App
    have h₂App := DFunLike.congr_fun h₂ F₂
    rw [GrossmanLarson.assocLHSHomY_apply, GrossmanLarson.assocRHSHomY_apply] at h₂App
    exact h₂App
  have h₁App := DFunLike.congr_fun h₁ F₁
  rw [GrossmanLarson.assocLHSHom_apply, GrossmanLarson.assocRHSHom_apply] at h₁App
  exact h₁App

/-! ## §4: `Semigroup` / `Monoid` instances for `GrossmanLarson ℤ α`

With `mul_assoc_ℤ` closed, register the algebraic typeclass instances
at the `ℤ` specialization. Downstream Bialgebra / Hopf registration
(MCB Lemma 1.2.10 / 1.2.11) depends on these. -/

namespace GrossmanLarson

variable {α : Type} [DecidableEq (Nonplanar α)]

noncomputable instance instSemigroup_ℤ : Semigroup (GrossmanLarson ℤ α) where
  mul_assoc := mul_assoc_ℤ

noncomputable instance instMonoid_ℤ : Monoid (GrossmanLarson ℤ α) where
  mul_assoc := mul_assoc_ℤ
  one_mul := one_mul
  mul_one := mul_one

noncomputable instance instSemiring_ℤ : Semiring (GrossmanLarson ℤ α) where
  mul_assoc := mul_assoc_ℤ
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul_gl
  mul_zero := mul_zero_gl

end GrossmanLarson

end RootedTree
