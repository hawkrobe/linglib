/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Algebra.RootedTree.PreLie.InsertSum
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Combinatorics.RootedTree.Nonplanar.Insertion
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

/-!
# Grossman-Larson Hopf algebra on forests of nonplanar rooted trees
[grossman-larson-1989]
[foissy-typed-decorated-rooted-trees-2018]
[marcolli-chomsky-berwick-2025]

The **Grossman-Larson product** `⋆` is the associative non-commutative
product on `ConnesKreimer R (Nonplanar α)`, dual to the disjoint-union
product. Together with the appropriate coproduct, it yields a Hopf
algebra dual to the Connes-Kreimer Hopf algebra.

## MCB targets

The GL framework is **the unification** that lets MCB's three coproducts
(Δ^c, Δ^d, Δ^ρ) share one substrate (see
`memory/project_mcb_unification_rationale.md`). Specifically:

* **Lemma 1.2.10** (Δ^c bialgebra on `V(F_{SO_0})`): closed via the
  GL-CK duality once R.5/R.6/R.7 sorries land. See
  `Coproduct/TraceNonplanar.lean`.
* **Lemma 1.2.11** (Δ^ρ Hopf algebra on `V(\tilde F_{SO_0})`):
  currently has a parallel proof in `Coproduct/PruningNonplanar.lean`
  (Foissy clean coassoc); R.8 will redo via GL duality and delete the
  parallel.
* **Lemma 1.7.3** (Insertion Lie Algebra of §1.7 = Lie algebra of
  primitives in `H^∨` after `1 − α` quotient): direct consequence of
  the GL-dual Lie bracket, with MCB Def 1.7.1's binary `◁_e` being the
  binary specialization (NOT a parallel algebra; see
  `feedback_mcb_section_1_7_not_foissy.md`).
* **Δ^d** (MCB Def 1.2.5): falls out as a different extraction policy
  + projection from the same framework (NOT a parallel substrate; see
  `project_mcb_unification_rationale.md`).

## Construction

For trees `T₁, T₂ : Nonplanar α`:
* The **insertion operator** `T₁ • T₂` sums over each vertex `v` of `T₁`
  the tree obtained by grafting `T₂` at `v` as a new child. Reduces to
  `Nonplanar.insertSum T₁ T₂` from `PreLie/Nonplanar.lean` (whose
  convention is `insertSum T_host T_graft`).
* For a single tree `T` and a forest `F`, `F • T` is the forest obtained
  by replacing one occurrence of a tree `S ∈ F` with `S` augmented by
  `T` grafted at one of its vertices: `F • T = Σ_{S ∈ F, v ∈ V(S)}
  (F.erase S + {S[v ↦ T]})`. Implemented as `insertTreeForest`.
* For a multi-tree operand `G_forest`, the multi-tree insertion `F • G`
  is defined as the **all-at-once** sum over assignments of each tree
  in `G` to a vertex of the *original* `F`. **Importantly, this is NOT
  the iterated single-tree insertion**: those don't commute (see
  `feedback_inserttree_does_not_commute.md`). The correct definition
  is `F • G_forest = Σ_{f : G_forest → V(F)} of' (F with each T ∈ G
  grafted at f(T))`, implemented as `Tree.Pathed.insertionForest` in
  `MultiGraft.lean` and lifted to `H` as `insertion` below.

The Grossman-Larson product is given by Foissy 2021 Theorem 5.1:
```
F ⋆ G = Σ_{G₁ ⊆ G_forest} (F • of' G₁) · of' (G_forest - G₁)
```
where the sum is over sub-multisets of `G_forest` and `·` is the
disjoint-union product on `ConnesKreimer R (Nonplanar α)`.

## Type alias

`GrossmanLarson R α` is a type alias for `ConnesKreimer R (Nonplanar α)`
that overrides the default disjoint-union `Mul` with the Grossman-Larson
product. Mirrors mathlib's `MultiplicativeOpposite` pattern: same
underlying carrier, different multiplication.

## Status

`[UPSTREAM]` candidate. Skeleton API (basis embeddings, single-tree
insertion, multi-tree `insertion`, GL product, `Mul` instance), with
`mul_one` and `one_mul` proved in-file.

`mul_assoc_basis` and `mul_assoc` (R-generic, `α : Type*`) live in
`GrossmanLarsonMonoid.lean`, proved sorry-free via the OudomGuin / PBW
bridge in `OudomGuinBridge.lean`
(`mul_assoc_basis_via_oudom_guin_pbw`) lifted to arbitrary
`CommSemiring R` by multiset-coefficient extraction. The `Semigroup`
and `Monoid` typeclass instances are registered there.
-/

namespace RootedTree

/-! ### The Grossman-Larson Hopf algebra carrier -/

/-- The Hopf algebra of forests of nonplanar rooted trees, equipped
    (via the `Mul` instance below) with the Grossman-Larson product. -/
def GrossmanLarson (R : Type*) [CommSemiring R] (α : Type*) : Type _ :=
  ConnesKreimer R (Nonplanar α)

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### Forwarded module instances

These propagate from the underlying `ConnesKreimer` carrier without
exposing the disjoint-union `Mul` (which would clash with the
Grossman-Larson `Mul` defined later). -/

noncomputable instance instAddCommMonoid : AddCommMonoid (GrossmanLarson R α) :=
  inferInstanceAs (AddCommMonoid (ConnesKreimer R (Nonplanar α)))

noncomputable instance instModule : Module R (GrossmanLarson R α) :=
  inferInstanceAs (Module R (ConnesKreimer R (Nonplanar α)))

noncomputable instance instOne : One (GrossmanLarson R α) :=
  inferInstanceAs (One (ConnesKreimer R (Nonplanar α)))

instance instFunLike : FunLike (GrossmanLarson R α) (Forest (Nonplanar α)) R :=
  inferInstanceAs (FunLike (ConnesKreimer R (Nonplanar α)) (Forest (Nonplanar α)) R)

/-! ### Underlying-carrier coercions

The type alias `GrossmanLarson R α := ConnesKreimer R (Nonplanar α)`
makes the carriers definitionally equal, but Lean does not always
unfold `def` for type ascription or instance resolution. Explicit
identity-coercion helpers `op`/`unop` (mirroring `MulOpposite.op` /
`unop` from mathlib) let us reach the underlying disjoint-union `Mul`
when defining the GL product, without exposing the disjoint-union
`Mul` on `GrossmanLarson R α` itself. -/

/-- Reinterpret a `ConnesKreimer R (Nonplanar α)` element as a
    `GrossmanLarson R α` element (identity at the carrier level). -/
def op (x : ConnesKreimer R (Nonplanar α)) : GrossmanLarson R α := x

/-- Reinterpret a `GrossmanLarson R α` element as a
    `ConnesKreimer R (Nonplanar α)` element (identity at the carrier level). -/
def unop (x : GrossmanLarson R α) : ConnesKreimer R (Nonplanar α) := x

@[simp] theorem op_unop (x : GrossmanLarson R α) :
    op (unop (R := R) x) = x := rfl

@[simp] theorem unop_op (x : ConnesKreimer R (Nonplanar α)) :
    unop (op (R := R) (α := α) x) = x := rfl

/-! ### Smart constructors

The basis-embedding constructors are inherited from the underlying
`ConnesKreimer` via definitional equality. -/

/-- Embed a forest as a basis vector. -/
noncomputable def of' (F : Forest (Nonplanar α)) : GrossmanLarson R α :=
  ConnesKreimer.of' (R := R) F

/-- Embed a single tree as a singleton-forest basis vector. -/
noncomputable def ofTree (t : Nonplanar α) : GrossmanLarson R α :=
  ConnesKreimer.ofTree (R := R) t

@[simp] theorem of'_zero :
    (of' (R := R) (0 : Forest (Nonplanar α)) : GrossmanLarson R α) = 1 :=
  ConnesKreimer.of'_zero

/-! ### Single-tree insertion

`insertTreeForest T F : GrossmanLarson R α` is the basis-level
forest-insertion operator: for each occurrence of a tree `S ∈ F` (with
multiplicity), sum over each grafting summand `S' ∈ Nonplanar.insertSum
S T` (`S` host, `T` graft, summed over vertices of `S`) the basis
vector for the resulting forest `S ::ₘ F.erase S` with `S` replaced by
`S'`. The convention `Nonplanar.insertSum T_host T_graft` is fixed by
`PreLie/Defs.lean` (verified against test + `card_insertSum_eq_weight`). -/

/-- Forest-level single-tree insertion: graft `T` at one vertex of one
    tree of `F`, summed over (tree, vertex). -/
noncomputable def insertTreeForest (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    GrossmanLarson R α :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  (F.bind fun S =>
    (Nonplanar.insertSum S T).map fun S' => of' (R := R) (S' ::ₘ F.erase S)).sum

@[simp] theorem insertTreeForest_zero (T : Nonplanar α) :
    insertTreeForest (R := R) T (0 : Forest (Nonplanar α)) = 0 := by
  simp only [insertTreeForest, Multiset.zero_bind, Multiset.sum_zero]

/-- ℤ-linear extension of `insertTreeForest T` to `GrossmanLarson R α`. -/
noncomputable def insertTree (T : Nonplanar α) :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  Finsupp.linearCombination R (insertTreeForest T)

@[simp] theorem insertTree_of' (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    insertTree (R := R) T (of' F) = insertTreeForest T F := by
  show Finsupp.linearCombination R (insertTreeForest T) (Finsupp.single F 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- **Leibniz cons decomposition for `insertTreeForest`** (CK-level form).

    Stated at the underlying `ConnesKreimer` level (via `unop`) where the
    disjoint-union `*` is unambiguous. The GL-level corollary
    `insertTreeForest_cons` follows.

    Strategy: `Multiset.cons_bind` + `Multiset.sum_add` split LHS into
    "S as cons-front" + "S₀ ∈ F" parts. The front simplifies via
    `Multiset.erase_cons_head`. For the tail, the auxiliary
    `(S ::ₘ F).erase S₀ = S ::ₘ F.erase S₀` (case-split on `S₀ = S`,
    using `cons_erase` on the equal case) lets us apply
    `ConnesKreimer.of'_add` to factor `of' {S}` out of each summand. Then
    `Multiset.sum_bind` + `Multiset.sum_map_mul_left` (twice) pull
    `of' {S}` out of the bind. -/
private theorem unop_insertTreeForest_cons
    (T S : Nonplanar α) (F : Forest (Nonplanar α)) :
    unop (insertTreeForest (R := R) T (S ::ₘ F)) =
      ((Nonplanar.insertSum S T).map
        (fun S' => unop (of' (R := R) (S' ::ₘ F)))).sum +
      unop (of' (R := R) ({S} : Forest (Nonplanar α))) *
        unop (insertTreeForest (R := R) T F) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- `unop` is the identity; unfolding both `unop` and `insertTreeForest`
  -- + `of'` (which is `ConnesKreimer.of'` definitionally) reduces the
  -- statement to a pure CK equality.
  show ((((S : Nonplanar α) ::ₘ F).bind fun S₀ =>
          (Nonplanar.insertSum S₀ T).map fun S' =>
            ConnesKreimer.of' (R := R) (S' ::ₘ ((S : Nonplanar α) ::ₘ F).erase S₀)).sum)
      = ((Nonplanar.insertSum S T).map fun S' =>
          ConnesKreimer.of' (R := R) (S' ::ₘ F)).sum +
        ConnesKreimer.of' (R := R) ({S} : Forest (Nonplanar α)) *
          ((F.bind fun S₀ =>
            (Nonplanar.insertSum S₀ T).map fun S' =>
              ConnesKreimer.of' (R := R) (S' ::ₘ F.erase S₀)).sum)
  rw [Multiset.cons_bind, Multiset.sum_add]
  congr 1
  · -- Front: erase_cons_head simplifies (S ::ₘ F).erase S to F
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intros
    rw [Multiset.erase_cons_head]
  · -- Tail: factor `of' {S}` from each summand
    have h_erase : ∀ S₀ ∈ F,
        ((S : Nonplanar α) ::ₘ F).erase S₀ = S ::ₘ F.erase S₀ := fun S₀ hS₀ => by
      by_cases h : S₀ = S
      · subst h; rw [Multiset.erase_cons_head, Multiset.cons_erase hS₀]
      · exact Multiset.erase_cons_tail _ (Ne.symm h)
    have h_factor : ∀ S₀ ∈ F,
        ((Nonplanar.insertSum S₀ T).map fun S' =>
            ConnesKreimer.of' (R := R) (S' ::ₘ ((S : Nonplanar α) ::ₘ F).erase S₀))
        = ((Nonplanar.insertSum S₀ T).map fun S' =>
            ConnesKreimer.of' (R := R) ({S} : Forest (Nonplanar α)) *
              ConnesKreimer.of' (R := R) (S' ::ₘ F.erase S₀)) := fun S₀ hS₀ => by
      apply Multiset.map_congr rfl
      intro S' _
      rw [h_erase S₀ hS₀, Multiset.cons_swap, ← Multiset.singleton_add,
          ConnesKreimer.of'_add]
    rw [Multiset.bind_congr h_factor]
    -- Pull out `of' {S}`: sum_bind, sum_map_mul_left (pointwise), again, reverse.
    rw [Multiset.sum_bind,
        Multiset.map_congr (rfl : F = F) (fun _ _ => Multiset.sum_map_mul_left),
        Multiset.sum_map_mul_left, ← Multiset.sum_bind]

/-- **Leibniz cons decomposition** for `insertTreeForest` (GL-level form).
    GL-level corollary of `unop_insertTreeForest_cons` via the
    definitional identity of `op` and `unop`. -/
theorem insertTreeForest_cons (T S : Nonplanar α) (F : Forest (Nonplanar α)) :
    insertTreeForest (R := R) T (S ::ₘ F) =
      ((Nonplanar.insertSum S T).map
        (fun S' => of' (R := R) (S' ::ₘ F))).sum +
      op (unop (of' (R := R) ({S} : Forest (Nonplanar α))) *
          unop (insertTreeForest T F)) :=
  unop_insertTreeForest_cons T S F

/-! ### Multi-tree insertion (the insertion operator `F • G`)

The bilinear operator `F • G : GrossmanLarson R α` for `F G : H`
inserts each tree of `G` (counted with multiplicity) at a vertex of
the *original* `F`. Specifically, for `F = of' F_forest` and `G = of'
G_forest`:
```
F • G = Σ_{f : G_forest → V(F_forest)} of' (F_forest with each T ∈ G grafted at f(T))
```
where the sum is over functions from `G_forest`'s elements to vertices
of `F_forest` (counted with multiplicity).

**This is well-defined on `G_forest` as a multiset** because the result
is invariant under permutation of `G_forest`'s elements (the
function-sum doesn't care about the order of `G_forest`'s indexing).

**This is NOT iterated single-tree insertion**: `insertTree` applications
do *not* commute (single-tree insertions add new vertices that subsequent
insertions could graft into, breaking permutation-invariance). See
`feedback_inserttree_does_not_commute.md` for the counterexample
(F = {leaf a}, T₁ = leaf b, T₂ = node(c, [d]) gives 3 vs 2 summands
for the two orders) and the correct semantics. The earlier scaffold
that defined `insertForest` via `Multiset.foldr` of `insertTree` was
based on this misreading and has been removed.

**Implementation status**: defined via Foissy 2021 Theorem 5.1's
combinatorial formula at the `Tree` level (`PreLie/MultiGraft.lean`'s
`Tree.Pathed.insertionForest`), descended through `Nonplanar.mk`
(`Nonplanar.insertionMultiset`), then bilinear-extended via
`Finsupp.linearCombination`. The substrate invariance theorems
(PermEquiv on host/guest, Perm on multiset arguments) are stated
as `sorry`'d theorems in `MultiGraftNonplanar.lean`. Closing those
substrate sorries unblocks all of R.5.3/4/5 + R.6 + R.7. -/

/-- Basis-level multi-graft on Multiset forests: each pair `(F_basis,
    G_basis)` produces a multiset of grafted forests, summed as basis
    vectors in `H = ConnesKreimer R (Nonplanar α)`. -/
noncomputable def insertionBasis (F_basis G_basis : Forest (Nonplanar α)) :
    GrossmanLarson R α :=
  ((Nonplanar.insertionMultiset F_basis G_basis).map
    fun F' => of' (R := R) F').sum

/-- Internal: `insertionBasis`-bundled-as-LinearMap-in-F. -/
private noncomputable def insertionBasisLin (G_basis : Forest (Nonplanar α)) :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  Finsupp.linearCombination R (fun F_basis => insertionBasis (R := R) F_basis G_basis)

/-- The bilinear insertion operator `F • G : GrossmanLarson R α`.
    Defined as the bilinear extension of `insertionBasis` via
    `Finsupp.linearCombination` twice (once over G's basis, once over
    F's via `insertionBasisLin`). -/
noncomputable def insertion :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  (Finsupp.linearCombination R (insertionBasisLin (R := R) (α := α))).flip

/-- Bridge: on basis vectors, `insertion (of' F) (of' G) = insertionBasis F G`.
    Unfolds the bilinear extension on both basis arguments. -/
theorem insertion_of'_of' (F G : Forest (Nonplanar α)) :
    insertion (R := R) (of' F) (of' G) = insertionBasis F G := by
  show ((insertion (R := R)).flip (of' G)) (of' F) = _
  show ((Finsupp.linearCombination R (insertionBasisLin (R := R) (α := α)))
          (of' G)) (of' F) = _
  show ((Finsupp.linearCombination R (insertionBasisLin (R := R) (α := α)))
          (Finsupp.single G 1)) (Finsupp.single F 1) = _
  rw [Finsupp.linearCombination_single, one_smul]
  show ((Finsupp.linearCombination R
          (fun F_basis => insertionBasis (R := R) F_basis G))
        (Finsupp.single F 1)) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-! ### Grossman-Larson product

The associative product `F ⋆ G` is defined via the Foissy 2021 closed
form (sum over sub-multisets of `G`'s underlying forest). The
disjoint-union `*` used inside the definition is the underlying
`ConnesKreimer` multiplication, exposed via type ascription (the def
`GrossmanLarson R α := ConnesKreimer R (Nonplanar α)` makes the
ascription a no-op). -/

/-- Forest-level Grossman-Larson product. -/
noncomputable def productForest (F : GrossmanLarson R α)
    (G : Forest (Nonplanar α)) : GrossmanLarson R α :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  (G.powerset.map fun G₁ =>
    op (unop (insertion F (of' (R := R) G₁)) * unop (of' (R := R) (G - G₁)))).sum

/-- F-zero. Each powerset summand is `op (unop (insertion 0 (of' G₁)) *
    ...) = op (0 * ...) = 0` by bilinearity of `insertion`. -/
private theorem productForest_zero_left (G : Forest (Nonplanar α)) :
    productForest (0 : GrossmanLarson R α) G = 0 := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  unfold productForest
  rw [show (G.powerset.map fun G₁ =>
        op (unop (insertion (R := R) (α := α) 0 (of' (R := R) G₁)) *
            unop (of' (R := R) (G - G₁)))) =
      G.powerset.map (fun _ => (0 : GrossmanLarson R α)) from ?_]
  · rw [Multiset.map_const', Multiset.sum_replicate, smul_zero]
  · apply Multiset.map_congr rfl
    intro G₁ _
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_zero, LinearMap.zero_apply]
    show op ((0 : ConnesKreimer R (Nonplanar α)) *
        unop (of' (R := R) (G - G₁))) = 0
    rw [zero_mul]
    rfl

/-- F-additivity. Each powerset summand is additive in F via bilinearity
    of `insertion`, then `unop`/`op` (identity coercions) and right
    distributivity in `ConnesKreimer`. -/
private theorem productForest_add_left
    (F₁ F₂ : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    productForest (F₁ + F₂) G = productForest F₁ G + productForest F₂ G := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  show ((G.powerset.map fun G₁ =>
      op (unop (insertion (F₁ + F₂) (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum : GrossmanLarson R α) =
    (G.powerset.map fun G₁ =>
      op (unop (insertion F₁ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum +
    (G.powerset.map fun G₁ =>
      op (unop (insertion F₂ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum
  rw [← Multiset.sum_map_add]
  congr 1
  apply Multiset.map_congr rfl
  intro G₁ _
  rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_add, LinearMap.add_apply]
  show op ((unop (insertion F₁ (of' (R := R) G₁)) +
            unop (insertion F₂ (of' (R := R) G₁))) *
           unop (of' (R := R) (G - G₁))) =
      op (unop (insertion F₁ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁))) +
      op (unop (insertion F₂ (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))
  rw [add_mul]
  rfl

/-- F-scalar-compatibility. Each powerset summand is scalar-compatible
    in F via bilinearity of `insertion`, then `unop`/`op` (identity
    coercions) and `smul_mul_assoc` in `ConnesKreimer`. -/
private theorem productForest_smul_left
    (c : R) (F : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    productForest (c • F) G = c • productForest F G := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  show ((G.powerset.map fun G₁ =>
      op (unop (insertion (c • F) (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum : GrossmanLarson R α) =
    c • (G.powerset.map fun G₁ =>
      op (unop (insertion F (of' (R := R) G₁)) *
          unop (of' (R := R) (G - G₁)))).sum
  rw [Multiset.smul_sum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro G₁ _
  rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_smul, LinearMap.smul_apply]
  show op ((c • unop (insertion F (of' (R := R) G₁))) *
           unop (of' (R := R) (G - G₁))) =
      (fun x => c • x) (op (unop (insertion F (of' (R := R) G₁)) *
                            unop (of' (R := R) (G - G₁))))
  show op ((c • unop (insertion F (of' (R := R) G₁))) *
           unop (of' (R := R) (G - G₁))) =
      c • op (unop (insertion F (of' (R := R) G₁)) *
              unop (of' (R := R) (G - G₁)))
  rw [smul_mul_assoc]
  rfl

/-- Internal: `productForest`-bundled-as-LinearMap-in-F. -/
private noncomputable def productForestLin (G : Forest (Nonplanar α)) :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α where
  toFun F := productForest F G
  map_add' F₁ F₂ := productForest_add_left F₁ F₂ G
  map_smul' c F := productForest_smul_left c F G

/-- The **Grossman-Larson product** `F ⋆ G : GrossmanLarson R α`,
    bilinear in both arguments. -/
noncomputable def product :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  (Finsupp.linearCombination R (productForestLin (R := R) (α := α))).flip

/-! ### Multiplicative structure

The `Mul` instance is registered here; `Semigroup`/`Monoid` are
registered in `GrossmanLarsonMonoid.lean` once associativity is in
hand. -/

noncomputable instance instMul : Mul (GrossmanLarson R α) where
  mul x y := product x y

theorem mul_def (x y : GrossmanLarson R α) : x * y = product x y := rfl

/-- **Left distributivity**: `a * (b + c) = a * b + a * c`. Follows from
    `product`'s bilinearity. Registered as `LeftDistribClass` (a Prop-only
    class that doesn't extend `Mul`/`Add`, avoiding parent-class disagreement
    with the existing `instMul` and `instAddCommMonoid`). Sorry-free. -/
instance instLeftDistribClass : LeftDistribClass (GrossmanLarson R α) where
  left_distrib a b c := by
    show product a (b + c) = product a b + product a c
    exact map_add (product a) b c

/-- **Right distributivity**: `(a + b) * c = a * c + b * c`. Same approach as
    `instLeftDistribClass`. Sorry-free. -/
instance instRightDistribClass : RightDistribClass (GrossmanLarson R α) where
  right_distrib a b c := by
    show product (a + b) c = product a c + product b c
    rw [show product (a + b) = product a + product b from
        map_add product a b]
    rfl

/-- Direct lemmas for `0 * a = 0` and `a * 0 = 0`. Registering `MulZeroClass`
    runs into the parent-class disagreement issue (it extends `Mul`/`Zero`),
    so we expose these as plain theorems. Invoke as
    `GrossmanLarson.zero_mul_gl`/`mul_zero_gl`. -/
theorem zero_mul_gl (x : GrossmanLarson R α) : (0 : GrossmanLarson R α) * x = 0 := by
  show product 0 x = 0
  rw [map_zero]
  rfl

theorem mul_zero_gl (x : GrossmanLarson R α) : x * (0 : GrossmanLarson R α) = 0 := by
  show product x 0 = 0
  exact map_zero _

/-- Direct lemma for `(r • a) * b = r • (a * b)`. Standalone since
    `IsScalarTower R GL GL` isn't registered (parent-class disagreement). -/
theorem smul_mul_gl (r : R) (a b : GrossmanLarson R α) :
    (r • a) * b = r • (a * b) := by
  show product (r • a) b = r • product a b
  rw [LinearMap.map_smul]
  rfl

/-- Direct lemma for `a * (s • b) = s • (a * b)`. Standalone since
    `SMulCommClass R GL GL` isn't registered (parent-class disagreement). -/
theorem mul_smul_gl (s : R) (a b : GrossmanLarson R α) :
    a * (s • b) = s • (a * b) :=
  LinearMap.map_smul (product a) s b

/-- **Basis form** of the GL product: `(of' F) * (of' G) = productForest (of' F) G`.
    Reduces the `linearCombination`-extended product to the explicit
    powerset-sum formula. -/
theorem of'_mul_of' (F G : Forest (Nonplanar α)) :
    (of' F : GrossmanLarson R α) * of' G = productForest (of' F) G := by
  show product (of' F) (of' G) = productForest (of' F) G
  show ((Finsupp.linearCombination R (productForestLin (R := R) (α := α))).flip
          (of' F)) (of' G) = productForest (of' F) G
  rw [LinearMap.flip_apply]
  show ((Finsupp.linearCombination R (productForestLin (R := R) (α := α)))
          (Finsupp.single G (1 : R))) (of' F) = productForest (of' F) G
  rw [Finsupp.linearCombination_single, one_smul]
  rfl

/-! ### Unit lemmas

Helper lemmas: `insertionBasis F_basis 0 = of' F_basis` (Foissy's empty-
guest case) and `insertionBasis 0 G_basis = if G_basis = 0 then 1 else 0`
(empty-host case). These let `mul_one` and `one_mul` reduce via the
powerset formula. -/

/-- `insertionBasis F 0 = of' F`: with no guests, the multi-graft leaves
    F unchanged. -/
private theorem insertionBasis_zero_right (F_basis : Forest (Nonplanar α)) :
    insertionBasis (R := R) F_basis (0 : Forest (Nonplanar α)) = of' F_basis := by
  unfold insertionBasis
  rw [Nonplanar.insertionMultiset_zero_right, Multiset.map_singleton,
      Multiset.sum_singleton]

/-- `insertionBasis 0 0 = 1`: inserting nothing into the empty forest
    gives the empty forest. -/
private theorem insertionBasis_zero_zero :
    insertionBasis (R := R) (0 : Forest (Nonplanar α)) 0 = 1 := by
  rw [insertionBasis_zero_right, of'_zero]

/-- `insertionBasis 0 G = 0` for non-empty G: no host vertices to graft
    guests into. -/
private theorem insertionBasis_zero_left_of_ne_zero
    (G_basis : Forest (Nonplanar α)) (h : G_basis ≠ 0) :
    insertionBasis (R := R) (0 : Forest (Nonplanar α)) G_basis = 0 := by
  unfold insertionBasis
  rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero G_basis h,
      Multiset.map_zero, Multiset.sum_zero]

/-- `insertion F 1 = F`. The bilinear extension at the unit
    of H reduces to summing `insertionBasis F_basis 0 = of' F_basis`
    over F's basis decomposition, which equals F by `Finsupp.sum_single`. -/
theorem insertion_one_right (F : GrossmanLarson R α) :
    insertion F (1 : GrossmanLarson R α) = F := by
  -- Unfold (1 : GrossmanLarson R α) = AddMonoidAlgebra.one_def = single 0 1
  show insertion F (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = F
  -- insertion.flip F : H →ₗ H. Apply on single 0 1.
  show (insertion (R := R) (α := α)).flip.flip F
    (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = F
  rw [LinearMap.flip_flip]
  -- Goal: insertion F (single 0 1) = F. Use flip_apply to get
  -- (insertion).flip (single 0 1) F = F.
  -- Actually let's evaluate via insertion's def.
  show ((Finsupp.linearCombination R insertionBasisLin).flip F)
    (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = F
  rw [LinearMap.flip_apply]
  show ((Finsupp.linearCombination R (insertionBasisLin (R := R) (α := α)))
    (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R))) F = F
  rw [Finsupp.linearCombination_single, one_smul]
  -- insertionBasisLin 0 F = (linearCombination (fun F_b => insertionBasis F_b 0)) F
  show (Finsupp.linearCombination R
        (fun F_basis : Forest (Nonplanar α) =>
          insertionBasis (R := R) F_basis (0 : Forest (Nonplanar α)))) F = F
  rw [show (fun F_basis : Forest (Nonplanar α) =>
        insertionBasis (R := R) F_basis (0 : Forest (Nonplanar α))) =
      (fun F_basis : Forest (Nonplanar α) =>
        of' (R := R) F_basis) from
    funext fun F_basis => insertionBasis_zero_right F_basis]
  rw [Finsupp.linearCombination_apply]
  show (F.sum fun F_basis r => r • of' (R := R) F_basis) = F
  rw [show (fun F_basis r => r • of' (R := R) F_basis) =
      (fun F_basis (r : R) => (Finsupp.single F_basis r : GrossmanLarson R α))
      from funext fun F_basis => funext fun r => by
        show r • (Finsupp.single F_basis (1 : R) : GrossmanLarson R α) =
            Finsupp.single F_basis r
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
  exact Finsupp.sum_single F

/-- **Right unit**. `mul_one` for the GL product. The powerset
    `(0:Multiset).powerset = {0}` collapses to a single summand, which
    reduces via `insertion_one_right` to F. -/
theorem mul_one (F : GrossmanLarson R α) : F * 1 = F := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  show product F 1 = F
  show ((Finsupp.linearCombination R productForestLin).flip F)
       (1 : GrossmanLarson R α) = F
  rw [LinearMap.flip_apply]
  show ((Finsupp.linearCombination R (productForestLin (R := R) (α := α)))
       (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R))) F = F
  rw [Finsupp.linearCombination_single, one_smul]
  show productForest F 0 = F
  show ((((0 : Forest (Nonplanar α)).powerset).map fun G₁ =>
        op (unop (insertion F (of' (R := R) G₁)) *
            unop (of' (R := R) ((0 : Forest (Nonplanar α)) - G₁)))).sum
      : GrossmanLarson R α) = F
  rw [Multiset.powerset_zero, Multiset.map_singleton, Multiset.sum_singleton,
      tsub_self, of'_zero]
  show op (unop (insertion F (of' (R := R) (0 : Forest (Nonplanar α)))) *
           unop (1 : GrossmanLarson R α)) = F
  rw [show unop (1 : GrossmanLarson R α) = (1 : ConnesKreimer R (Nonplanar α))
      from rfl, _root_.mul_one]
  show op (unop (insertion F (of' (R := R) (0 : Forest (Nonplanar α))))) = F
  show insertion F (of' (R := R) (0 : Forest (Nonplanar α))) = F
  rw [show (of' (R := R) (0 : Forest (Nonplanar α)) : GrossmanLarson R α) =
        (1 : GrossmanLarson R α) from of'_zero]
  exact insertion_one_right F

/-- Auxiliary: `insertion 1 (of' 0) = 1`. -/
private theorem insertion_one_of'_zero :
    insertion (1 : GrossmanLarson R α)
        (of' (R := R) (0 : Forest (Nonplanar α))) =
      (1 : GrossmanLarson R α) := by
  show ((Finsupp.linearCombination R insertionBasisLin).flip
        (1 : GrossmanLarson R α))
       (of' (R := R) (0 : Forest (Nonplanar α))) = _
  rw [LinearMap.flip_apply]
  show ((Finsupp.linearCombination R (insertionBasisLin (R := R) (α := α)))
        (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)))
       (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = _
  rw [Finsupp.linearCombination_single, one_smul]
  show insertionBasisLin (R := R) (α := α) 0
       (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = _
  show (Finsupp.linearCombination R
        (fun F_basis : Forest (Nonplanar α) =>
          insertionBasis (R := R) F_basis 0))
       (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = _
  rw [Finsupp.linearCombination_single, one_smul]
  exact insertionBasis_zero_zero

/-- `insertion 1 (of' G₁) = 0` for non-empty G₁. -/
theorem insertion_one_of'_ne_zero (G₁ : Forest (Nonplanar α))
    (h : G₁ ≠ 0) :
    insertion (1 : GrossmanLarson R α) (of' (R := R) G₁) =
      (0 : GrossmanLarson R α) := by
  show ((Finsupp.linearCombination R insertionBasisLin).flip
        (1 : GrossmanLarson R α)) (of' (R := R) G₁) = _
  rw [LinearMap.flip_apply]
  show ((Finsupp.linearCombination R (insertionBasisLin (R := R) (α := α)))
        (Finsupp.single G₁ (1 : R)))
       (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = _
  rw [Finsupp.linearCombination_single, one_smul]
  show insertionBasisLin (R := R) (α := α) G₁
       (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = _
  show (Finsupp.linearCombination R
        (fun F_basis : Forest (Nonplanar α) =>
          insertionBasis (R := R) F_basis G₁))
       (Finsupp.single (0 : Forest (Nonplanar α)) (1 : R)) = _
  rw [Finsupp.linearCombination_single, one_smul]
  exact insertionBasis_zero_left_of_ne_zero G₁ h

/-- `Multiset.count 0 s.powerset = 1`: the empty submultiset appears
    exactly once in the powerset of any multiset. By induction on `s`:
    base case via `powerset_zero = {0}`; cons case via `powerset_cons`
    splits the count additively, and the `map (cons a)` half contains
    no `0` (by `cons_ne_zero`). -/
private theorem count_zero_powerset [DecidableEq (Nonplanar α)]
    (s : Multiset (Nonplanar α)) :
    Multiset.count (0 : Forest (Nonplanar α)) s.powerset = 1 := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.powerset_zero, Multiset.count_singleton_self]
  | cons a s ih =>
    rw [Multiset.powerset_cons, Multiset.count_add, ih]
    have hmap : Multiset.count (0 : Forest (Nonplanar α))
                  (s.powerset.map (a ::ₘ ·)) = 0 := by
      rw [Multiset.count_eq_zero, Multiset.mem_map]
      rintro ⟨x, _, hx⟩
      exact Multiset.cons_ne_zero hx
    rw [hmap]

/-- `productForest 1 G_basis = of' G_basis`: the only non-vanishing
    powerset summand is `G₁ = 0`, contributing `of' G_basis` exactly
    once. The `G₁ ≠ 0` summands vanish via `insertion_one_of'_ne_zero`. -/
private theorem productForest_one_left (G_basis : Forest (Nonplanar α)) :
    productForest (1 : GrossmanLarson R α) G_basis = of' G_basis := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  unfold productForest
  -- Split powerset as `0 ::ₘ powerset.erase 0`
  have h0_mem : (0 : Forest (Nonplanar α)) ∈ G_basis.powerset :=
    Multiset.zero_mem_powerset _
  rw [← Multiset.cons_erase h0_mem, Multiset.map_cons, Multiset.sum_cons]
  -- Simplify the `G₁ = 0` summand to `of' G_basis`
  have hf0 :
      op (unop (insertion (1 : GrossmanLarson R α)
                (of' (R := R) (0 : Forest (Nonplanar α)))) *
          unop (of' (R := R) (G_basis - 0)))
        = of' (R := R) G_basis := by
    rw [insertion_one_of'_zero, tsub_zero]
    show op ((1 : ConnesKreimer R (Nonplanar α)) *
              unop (of' (R := R) G_basis)) = _
    rw [_root_.one_mul]; rfl
  -- The `erase 0` part has every G₁ ≠ 0, so each summand vanishes
  have h_no_zero : (0 : Forest (Nonplanar α)) ∉ G_basis.powerset.erase 0 := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self,
        count_zero_powerset G_basis]
  have hrest :
      ((G_basis.powerset.erase 0).map fun G₁ =>
          op (unop (insertion (1 : GrossmanLarson R α) (of' (R := R) G₁)) *
              unop (of' (R := R) (G_basis - G₁)))).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨G₁, hG₁_mem, hG₁_eq⟩ := hx
    have hG₁_ne : G₁ ≠ 0 := fun h => h_no_zero (h ▸ hG₁_mem)
    rw [← hG₁_eq, insertion_one_of'_ne_zero G₁ hG₁_ne]
    show op ((0 : ConnesKreimer R (Nonplanar α)) *
              unop (of' (R := R) (G_basis - G₁))) = 0
    rw [zero_mul]; rfl
  rw [hf0, hrest, add_zero]

/-- **Left unit**. `one_mul` for the GL product. The powerset sum
    in `productForest 1 G_basis` collapses to a single non-zero summand
    at `G₁ = 0` (via `productForest_one_left`), giving `of' G_basis`.
    The outer `linearCombination` then reduces to `F.sum single = F`. -/
theorem one_mul (F : GrossmanLarson R α) : (1 : GrossmanLarson R α) * F = F := by
  show product 1 F = F
  show ((Finsupp.linearCombination R productForestLin).flip
        (1 : GrossmanLarson R α)) F = F
  rw [LinearMap.flip_apply]
  show ((Finsupp.linearCombination R (productForestLin (R := R) (α := α))) F)
       (1 : GrossmanLarson R α) = F
  rw [Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply]
  -- Goal: F.sum (fun G_basis r => (r • productForestLin G_basis) 1) = F
  -- Push smul through apply, then unfold productForestLin and use the helper
  rw [show (fun G_basis r =>
              (r • productForestLin (R := R) (α := α) G_basis)
                (1 : GrossmanLarson R α)) =
        (fun G_basis (r : R) =>
          (Finsupp.single G_basis r : GrossmanLarson R α)) from ?_]
  · exact Finsupp.sum_single F
  · funext G_basis r
    rw [LinearMap.smul_apply]
    show r • productForest (1 : GrossmanLarson R α) G_basis =
        Finsupp.single G_basis r
    rw [productForest_one_left]
    show r • (Finsupp.single G_basis (1 : R) : GrossmanLarson R α) =
        Finsupp.single G_basis r
    rw [Finsupp.smul_single, smul_eq_mul, _root_.mul_one]

/-! ### Associativity

`mul_assoc_basis` and `mul_assoc` (both R-generic, `α : Type*`) are
proved sorry-free in `GrossmanLarsonMonoid.lean` via the Oudom-Guin
/ PBW route — see `OudomGuinBridge.lean`'s
`mul_assoc_basis_via_oudom_guin_pbw` (Q6 for `R = ℤ`), lifted to arbitrary
`CommSemiring R` via multiset-coefficient extraction. The
`Semigroup`/`Monoid` instances are registered there. -/

end GrossmanLarson

end RootedTree
