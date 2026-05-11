/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Algebra.RootedTree.PreLie.Nonplanar
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
@cite{grossman-larson-1989}
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{marcolli-chomsky-berwick-2025}

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
* The **insertion operator** `T₁ • T₂` sums over each vertex `v` of `T₂`
  the tree obtained by grafting `T₁` at `v` as a new child. Reduces to
  `Nonplanar.insertSum T₁ T₂` from `PreLie/Nonplanar.lean`.
* For a single tree `T` and a forest `F`, `F • T` extends bilinearly:
  `(S₁ ⊔ ⋯ ⊔ Sₘ) • T = Σⱼ {S₁, …, insertAt(T, vⱼ, Sⱼ), …, Sₘ}` summed
  over `vⱼ ∈ V(Sⱼ)`. Implemented as `insertTreeForest`.

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
insertion, multi-tree insertion, GL product) sorry-free for the bilinear
infrastructure. The combinatorial commutativity (`insertTree_comm`),
the cons-decomposition lemma (`insertTreeForest_cons`), forest-level
linearity-in-F lemmas for `productForest`, and the unitality + assoc
theorems remain as `sorry`s. The `Semigroup`/`Monoid` typeclass
instances for the GL product are NOT registered until the underlying
proofs land — only the forwarding `theorem`s are stated.
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
noncomputable def op (x : ConnesKreimer R (Nonplanar α)) : GrossmanLarson R α := x

/-- Reinterpret a `GrossmanLarson R α` element as a
    `ConnesKreimer R (Nonplanar α)` element (identity at the carrier level). -/
noncomputable def unop (x : GrossmanLarson R α) : ConnesKreimer R (Nonplanar α) := x

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
T S` the basis vector for the resulting forest `S ::ₘ F.erase S` with
`S` replaced by `S'`. -/

/-- Forest-level single-tree insertion. -/
noncomputable def insertTreeForest (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    GrossmanLarson R α :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  (F.bind fun S =>
    (Nonplanar.insertSum T S).map fun S' => of' (R := R) (S' ::ₘ F.erase S)).sum

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
      ((Nonplanar.insertSum T S).map
        (fun S' => unop (of' (R := R) (S' ::ₘ F)))).sum +
      unop (of' (R := R) ({S} : Forest (Nonplanar α))) *
        unop (insertTreeForest (R := R) T F) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- `unop` is the identity; unfolding both `unop` and `insertTreeForest`
  -- + `of'` (which is `ConnesKreimer.of'` definitionally) reduces the
  -- statement to a pure CK equality.
  show ((((S : Nonplanar α) ::ₘ F).bind fun S₀ =>
          (Nonplanar.insertSum T S₀).map fun S' =>
            ConnesKreimer.of' (R := R) (S' ::ₘ ((S : Nonplanar α) ::ₘ F).erase S₀)).sum)
      = ((Nonplanar.insertSum T S).map fun S' =>
          ConnesKreimer.of' (R := R) (S' ::ₘ F)).sum +
        ConnesKreimer.of' (R := R) ({S} : Forest (Nonplanar α)) *
          ((F.bind fun S₀ =>
            (Nonplanar.insertSum T S₀).map fun S' =>
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
        ((Nonplanar.insertSum T S₀).map fun S' =>
            ConnesKreimer.of' (R := R) (S' ::ₘ ((S : Nonplanar α) ::ₘ F).erase S₀))
        = ((Nonplanar.insertSum T S₀).map fun S' =>
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
      ((Nonplanar.insertSum T S).map
        (fun S' => of' (R := R) (S' ::ₘ F))).sum +
      op (unop (of' (R := R) ({S} : Forest (Nonplanar α))) *
          unop (insertTreeForest T F)) :=
  unop_insertTreeForest_cons T S F

/-! ### Multi-tree insertion

`insertOp F G` (notation `F • G`) inserts each tree of `G` into `F`,
summed over all sequences of vertex choices. Order-independence
(commutativity of single-tree insertions) is encoded as a
`LeftCommutative` instance on `insertTree`, used by `Multiset.foldr`
to define the basis-level `insertForest`. The bilinear bundle
`insertOp` lifts this to all of `GrossmanLarson R α` in both arguments. -/

/-- **Order-independence of single-tree insertions**. Reduces to a
    vertex-bijection between double-insertion sites of `T₁ • T₂` and
    `T₂ • T₁`. **TODO**: proof. -/
private theorem insertTree_comm (T₁ T₂ : Nonplanar α) (X : GrossmanLarson R α) :
    insertTree T₁ (insertTree T₂ X) = insertTree T₂ (insertTree T₁ X) := by
  sorry

instance instLeftCommutative :
    LeftCommutative (fun (T : Nonplanar α) (acc : GrossmanLarson R α) =>
      insertTree (R := R) T acc) where
  left_comm := insertTree_comm

/-- Forest-level multi-tree insertion via `Multiset.foldr`. -/
noncomputable def insertForest (F : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    GrossmanLarson R α :=
  G.foldr (fun T acc => insertTree T acc) F

@[simp] theorem insertForest_zero (F : GrossmanLarson R α) :
    insertForest F (0 : Forest (Nonplanar α)) = F :=
  Multiset.foldr_zero _ _

@[simp] theorem insertForest_cons (F : GrossmanLarson R α) (T : Nonplanar α)
    (G : Forest (Nonplanar α)) :
    insertForest F (T ::ₘ G) = insertTree T (insertForest F G) :=
  Multiset.foldr_cons _ _ _ _

private theorem insertForest_zero_left (G : Forest (Nonplanar α)) :
    insertForest (0 : GrossmanLarson R α) G = 0 := by
  induction G using Multiset.induction with
  | empty => exact insertForest_zero _
  | cons T G' ih => rw [insertForest_cons, ih, LinearMap.map_zero]

private theorem insertForest_add_left
    (F₁ F₂ : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    insertForest (F₁ + F₂) G = insertForest F₁ G + insertForest F₂ G := by
  induction G using Multiset.induction with
  | empty => simp only [insertForest_zero]
  | cons T G' ih =>
    rw [insertForest_cons, insertForest_cons, insertForest_cons, ih,
        LinearMap.map_add]

private theorem insertForest_smul_left
    (c : R) (F : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    insertForest (c • F) G = c • insertForest F G := by
  induction G using Multiset.induction with
  | empty => simp only [insertForest_zero]
  | cons T G' ih =>
    rw [insertForest_cons, insertForest_cons, ih, LinearMap.map_smul]

/-- Internal: `insertForest`-bundled-as-LinearMap-in-F, parameterized by
    the operand forest. Used to lift to the bilinear `insertOp`. -/
private noncomputable def insertForestLin (G : Forest (Nonplanar α)) :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α where
  toFun F := insertForest F G
  map_add' F₁ F₂ := insertForest_add_left F₁ F₂ G
  map_smul' c F := insertForest_smul_left c F G

/-- The bilinear insertion operator `F • G : GrossmanLarson R α`. -/
noncomputable def insertOp :
    GrossmanLarson R α →ₗ[R] GrossmanLarson R α →ₗ[R] GrossmanLarson R α :=
  (Finsupp.linearCombination R (insertForestLin (R := R) (α := α))).flip

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
    op (unop (insertOp F (of' (R := R) G₁)) * unop (of' (R := R) (G - G₁)))).sum

/-- F-additivity. **TODO**: proof. -/
private theorem productForest_zero_left (G : Forest (Nonplanar α)) :
    productForest (0 : GrossmanLarson R α) G = 0 := by
  sorry

/-- F-additivity. **TODO**: proof. -/
private theorem productForest_add_left
    (F₁ F₂ : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    productForest (F₁ + F₂) G = productForest F₁ G + productForest F₂ G := by
  sorry

/-- F-scalar-compatibility. **TODO**: proof. -/
private theorem productForest_smul_left
    (c : R) (F : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    productForest (c • F) G = c • productForest F G := by
  sorry

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

The `Mul` instance is registered now. The `Semigroup`/`Monoid` instances
are intentionally NOT registered until associativity is proved
(registering them prematurely would silently propagate the open `sorry`
through any `[Semigroup]`-using consumer). The forwarding `theorem`s
`mul_one`, `one_mul`, `mul_assoc` are stated for downstream convenience
but carry the same `sorry`s. -/

noncomputable instance instMul : Mul (GrossmanLarson R α) where
  mul x y := product x y

theorem mul_def (x y : GrossmanLarson R α) : x * y = product x y := rfl

/-- **Right unit**. `mul_one` for the GL product. **TODO**: proof.
    Sketch: `productForest F 0 = (powerset 0).map (...) = {0}.map (...)
    .sum = insertOp F 1 * 1 = F * 1 = F`, using `insertOp F 1 = F`
    (empty-forest insertion is identity). -/
theorem mul_one (F : GrossmanLarson R α) : F * 1 = F := by
  sorry

/-- **Left unit**. `one_mul` for the GL product. **TODO**: proof. Holds
    because `insertOp 1 (of' G₁) = 0` for non-empty `G₁` (inserting
    trees into the empty forest produces `0`, since the empty forest
    has no host vertices), so the powerset sum collapses to the single
    `G₁ = 0` summand `1 * of' G_forest = of' G_forest = F`. -/
theorem one_mul (F : GrossmanLarson R α) : (1 : GrossmanLarson R α) * F = F := by
  sorry

/-- **Associativity**. Proved by induction on the multiset structure of
    the rightmost argument, using the `productForest` powerset formula
    and Fubini-style re-indexing of nested sub-multiset choices. Foissy
    2018 §4.2 establishes this via Guin-Oudom + PBW; we bypass PBW
    with a direct combinatorial induction. **TODO**: proof. -/
theorem mul_assoc (F₁ F₂ F₃ : GrossmanLarson R α) :
    F₁ * F₂ * F₃ = F₁ * (F₂ * F₃) := by
  sorry

end GrossmanLarson

end RootedTree
