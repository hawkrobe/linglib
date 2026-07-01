import Linglib.Core.Algebra.RootedTree.PreLie.InsertSum
import Linglib.Core.Algebra.RootedTree.PreLie.Insert
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# `InsertionAlgebra α` — pre-Lie algebra on `(Nonplanar α) →₀ ℤ`
[foissy-typed-decorated-rooted-trees-2018]
[chapoton-livernet-2001]

The bilinear extension of `Nonplanar.insertSum` to the free
ℤ-module `(Nonplanar α) →₀ ℤ` gives a `RightPreLieAlgebra ℤ` instance,
realizing Foissy 2018 Proposition 2.2 specialized to a single edge type
(matching the `Nonplanar α` carrier from `PreLie/Nonplanar.lean`).

## Carrier

```
def InsertionAlgebra (α : Type*) := Nonplanar α →₀ ℤ
```

A type alias (à la `MonoidAlgebra k G := G →₀ k`) gives a fresh slot
for a custom non-pointwise `Mul`. The custom multiplication is the
bilinear extension of `Nonplanar.insertSum`, which on singletons
satisfies
`single t 1 * single s 1 = (Nonplanar.insertSum t s).toFinsupp.mapℤ`
(where the multiset of grafting summands is converted to a Finsupp,
each summand contributing 1).

## The pre-Lie identity

Foissy 2018 Definition 2.1 (page 6) defines a **multiple pre-Lie
algebra** by the identity
`x •_{t'} (y •_t z) − (x •_{t'} y) •_t z = x •_t (z •_{t'} y) − (x •_t z) •_{t'} y`

Specializing to a single edge type collapses both subscripts and gives:
`x • (y • z) − (x • y) • z = x • (z • y) − (x • z) • y`

i.e., `(x • y) • z − x • (y • z) = (x • z) • y − x • (z • y)`, which is
exactly mathlib's `RightPreLieRing` axiom
`associator x y z = associator x z y`.

## Proof structure (Foissy 2018 Proposition 2.2)

By bilinearity, suffices on singletons. For
`T₁ T₂ T₃ : Nonplanar α`:
1. Decompose `(T₁ • T₂) • T₃` as `Σ_{v ∈ V(T₁), u ∈ V(insertAt v T₂)} insertAt u T₃ (insertAt v T₂)`.
2. Classify each `u` via `Vertex.classifyEquiv` (R.3b §9):
   - `lifted g` (g ∈ V(T₂)): contribution = `insertAt v (insertAt g T₃) T₁`
     by `insertAt_lift_eq_nested`. Sums to `T₁ • (T₂ • T₃)`. Cancels
     in `(T₁ • T₂) • T₃ − T₁ • (T₂ • T₃)`.
   - `preserved w` (w ∈ V(T₁), w ≠ v): contribution =
     `insertAt (preserveOf v w h T₂) T₃ (insertAt v T₂)` =
     `insertAt (preserveOf w v h.symm T₃) T₂` by `insertAt_commute_diff`.
     This re-keys (v, w) ↔ (w, v): summand of `(T₁ • T₃) • T₂` in the
     symmetric class.
   - `sourceSelf` (u = v itself, v carries both T₂ and T₃ as new
     children): contribution = `node a (T₃ :: T₂ :: cs)` (for v = root).
     Symmetric counterpart: `node a (T₂ :: T₃ :: cs)`. **Equal as
     Nonplanar trees** (children-list permutation), making this case
     cancellable in `Nonplanar` but not `Tree`.

The Nonplanar-only swap-cancellation in the `sourceSelf` case is what
distinguishes the Nonplanar pre-Lie algebra from the (non-existent)
Tree one.

## Mathlib upstream considerations

`InsertionAlgebra` is **noncomputable** because `Nonplanar α` is a
`Quotient` and `DecidableEq (Nonplanar α)` requires canonicalization
(typically via `[LinearOrder α]` and recursive children-list sorting).
For mathlib upstream, a sibling `DecidableEq (Nonplanar α)` instance
under `[LinearOrder α]` would let consumers opt into computability;
that's deferred to a separate file
(`Combinatorics/RootedTree/Nonplanar/Decidable.lean`?).

The pattern matches mathlib's `LieAlgebra.UniversalEnveloping` and
`TensorProduct`: noncomputable for "abstract algebraic structure where
evaluation isn't the point."

## Main definitions

- `InsertionAlgebra α` — the carrier `Nonplanar α →₀ ℤ` with custom `Mul`.
- `ofTree` / `ofMultiset` — smart constructors for basis vectors.
- `instMul` — bilinear extension of `Nonplanar.insertSum`.

## Main theorems

- `assoc_symm` — the pre-Lie identity (associator symmetry on the right).
- `instRightPreLieRing` / `instRightPreLieAlgebra` — typeclass instances.
-/

namespace RootedTree

/-! ### Carrier + module instances -/

/-- The **insertion algebra** on `Nonplanar α`: the free ℤ-module on
    `Nonplanar α` with multiplication given by the bilinear extension of
    `Nonplanar.insertSum`. Defined as a type alias of `Nonplanar α →₀ ℤ`
    (the `MonoidAlgebra` pattern) so that we can attach a custom `Mul`. -/
def InsertionAlgebra (α : Type*) := Nonplanar α →₀ ℤ

namespace InsertionAlgebra

variable {α : Type*}

noncomputable instance instAddCommGroup : AddCommGroup (InsertionAlgebra α) :=
  inferInstanceAs (AddCommGroup (Nonplanar α →₀ ℤ))

noncomputable instance instModule : Module ℤ (InsertionAlgebra α) :=
  inferInstanceAs (Module ℤ (Nonplanar α →₀ ℤ))

instance instInhabited : Inhabited (InsertionAlgebra α) :=
  inferInstanceAs (Inhabited (Nonplanar α →₀ ℤ))

instance instFunLike : FunLike (InsertionAlgebra α) (Nonplanar α) ℤ :=
  inferInstanceAs (FunLike (Nonplanar α →₀ ℤ) (Nonplanar α) ℤ)

/-! ### Smart constructor + custom Mul

`ofTree t` is the basis vector `Finsupp.single t 1`. The custom Mul is
the bilinear extension of `Nonplanar.insertSum`, computed via
`Finsupp.sum`. -/

/-- The basis vector for a single tree. -/
noncomputable def ofTree (t : Nonplanar α) : InsertionAlgebra α :=
  Finsupp.single t 1

theorem ofTree_apply (t : Nonplanar α) :
    (ofTree t : InsertionAlgebra α) = Finsupp.single t 1 := rfl

/-- Convert a `Multiset (Nonplanar α)` to an `InsertionAlgebra α` by
    summing each element as a singleton basis vector. Bypasses
    `Multiset.toFinsupp` (which requires `DecidableEq`) by using
    `Multiset.sum` over `(Finsupp.single · 1)`-valued maps. -/
noncomputable def ofMultiset (m : Multiset (Nonplanar α)) :
    InsertionAlgebra α :=
  (m.map (fun t => (Finsupp.single t 1 : Nonplanar α →₀ ℤ))).sum

@[simp] theorem ofMultiset_zero :
    (ofMultiset (0 : Multiset (Nonplanar α)) : InsertionAlgebra α) = 0 := by
  show (Multiset.map _ 0).sum = 0
  rw [Multiset.map_zero, Multiset.sum_zero]
  rfl

@[simp] theorem ofMultiset_singleton (t : Nonplanar α) :
    (ofMultiset ({t} : Multiset (Nonplanar α)) : InsertionAlgebra α) =
      ofTree t := by
  show (Multiset.map _ {t}).sum = _
  rw [Multiset.map_singleton, Multiset.sum_singleton]
  rfl

@[simp] theorem ofMultiset_add (m₁ m₂ : Multiset (Nonplanar α)) :
    (ofMultiset (m₁ + m₂) : InsertionAlgebra α) =
      ofMultiset m₁ + ofMultiset m₂ := by
  show (Multiset.map _ (m₁ + m₂)).sum =
       (Multiset.map _ m₁).sum + (Multiset.map _ m₂).sum
  rw [Multiset.map_add, Multiset.sum_add]
  rfl

@[simp] theorem ofMultiset_cons (t : Nonplanar α) (m : Multiset (Nonplanar α)) :
    (ofMultiset (t ::ₘ m) : InsertionAlgebra α) = ofTree t + ofMultiset m := by
  show (Multiset.map _ (t ::ₘ m)).sum = _ + _
  rw [Multiset.map_cons, Multiset.sum_cons]
  rfl

/-- The bilinear extension of `Nonplanar.insertSum`: for singletons,
    `single t 1 * single s 1 = ofMultiset (Nonplanar.insertSum t s)`.
    Defined via `Finsupp.sum`, which gives a clean bilinear extension
    over `(Nonplanar α →₀ ℤ)`. -/
noncomputable instance instMul : Mul (InsertionAlgebra α) where
  mul x y :=
    x.sum (fun t (a : ℤ) =>
      y.sum (fun s (b : ℤ) =>
        (a * b) • ofMultiset (Nonplanar.insertSum t s)))

theorem mul_def (x y : InsertionAlgebra α) :
    x * y = x.sum (fun t a =>
      y.sum (fun s b =>
        (a * b) • ofMultiset (Nonplanar.insertSum t s))) := rfl

/-- The headline computation: on singletons, multiplication is the
    bilinear extension of `Nonplanar.insertSum`. -/
@[simp] theorem ofTree_mul_ofTree (t s : Nonplanar α) :
    (ofTree t : InsertionAlgebra α) * ofTree s =
      ofMultiset (Nonplanar.insertSum t s) := by
  show (Finsupp.single t 1).sum
        (fun t (a : ℤ) =>
          (Finsupp.single s 1).sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s))) = _
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  · -- (1 * 1) • ofMultiset (...) = ofMultiset (...)
    simp only [one_mul, one_smul]
  · -- (1 * 0) • ofMultiset (...) = 0
    simp only [mul_zero, zero_smul]
  · -- ((Finsupp.single s 1).sum (fun ... 0 ...)) = 0
    have hfun : (fun (s : Nonplanar α) (b : ℤ) =>
            ((0 : ℤ) * b) • ofMultiset (Nonplanar.insertSum t s)) =
        (fun (_ : Nonplanar α) (_ : ℤ) => (0 : InsertionAlgebra α)) :=
      funext fun _ => funext fun _ => by rw [zero_mul, zero_smul]
    rw [hfun]
    exact Finsupp.sum_fun_zero (f := Finsupp.single s (1 : ℤ))
                                (N := InsertionAlgebra α)

/-! ### Bilinearity + `NonUnitalNonAssocRing`

The custom `Mul` is bilinear by construction (built from `Finsupp.sum`).
Standard lemmas: `zero_mul`, `mul_zero`, `left_distrib`, `right_distrib`.
With these, `InsertionAlgebra α` becomes a `NonUnitalNonAssocRing`. -/

@[simp] theorem zero_mul (x : InsertionAlgebra α) :
    (0 : InsertionAlgebra α) * x = 0 := by
  show (0 : Nonplanar α →₀ ℤ).sum
        (fun t (a : ℤ) =>
          x.sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s))) = 0
  rw [Finsupp.sum_zero_index]

@[simp] theorem mul_zero (x : InsertionAlgebra α) :
    x * (0 : InsertionAlgebra α) = 0 := by
  show x.sum
        (fun t (a : ℤ) =>
          (0 : Nonplanar α →₀ ℤ).sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s))) = 0
  conv_lhs =>
    rw [show (fun (t : Nonplanar α) (a : ℤ) =>
                (0 : Nonplanar α →₀ ℤ).sum (fun s (b : ℤ) =>
                  (a * b) • ofMultiset (Nonplanar.insertSum t s))) =
            (fun (_ : Nonplanar α) (_ : ℤ) => (0 : InsertionAlgebra α)) from
          funext fun t => funext fun a => by
            rw [Finsupp.sum_zero_index]]
  exact Finsupp.sum_fun_zero (f := x) (N := InsertionAlgebra α)

theorem add_mul (x y z : InsertionAlgebra α) :
    (x + y) * z = x * z + y * z := by
  show (x + y).sum
        (fun t (a : ℤ) =>
          z.sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s))) =
       x.sum (fun t (a : ℤ) =>
          z.sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s))) +
       y.sum (fun t (a : ℤ) =>
          z.sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s)))
  apply Finsupp.sum_add_index'
  · -- function is 0 at coeff 0
    intro t
    have hfun : (fun (s : Nonplanar α) (b : ℤ) =>
            ((0 : ℤ) * b) • ofMultiset (Nonplanar.insertSum t s)) =
        (fun (_ : Nonplanar α) (_ : ℤ) => (0 : InsertionAlgebra α)) :=
      funext fun _ => funext fun _ => by
        rw [show ((0 : ℤ) * _) = 0 from Int.zero_mul _, zero_smul]
    show z.sum _ = (0 : InsertionAlgebra α)
    rw [hfun]
    exact Finsupp.sum_fun_zero (f := z) (N := InsertionAlgebra α)
  · -- Additivity in the coefficient
    intro t a₁ a₂
    show z.sum (fun s (b : ℤ) =>
        ((a₁ + a₂) * b) • ofMultiset (Nonplanar.insertSum t s)) =
      z.sum (fun s (b : ℤ) =>
        (a₁ * b) • ofMultiset (Nonplanar.insertSum t s)) +
      z.sum (fun s (b : ℤ) =>
        (a₂ * b) • ofMultiset (Nonplanar.insertSum t s))
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro s _
    rw [Int.add_mul, add_smul]

theorem mul_add (x y z : InsertionAlgebra α) :
    x * (y + z) = x * y + x * z := by
  show x.sum
        (fun t (a : ℤ) =>
          (y + z).sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s))) =
       x.sum
        (fun t (a : ℤ) =>
          y.sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s))) +
       x.sum
        (fun t (a : ℤ) =>
          z.sum (fun s (b : ℤ) =>
            (a * b) • ofMultiset (Nonplanar.insertSum t s)))
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro t _
  apply Finsupp.sum_add_index'
  · -- function is 0 at coeff 0
    intro s
    rw [Int.mul_zero, zero_smul]
  · -- additivity in coeff
    intro s b₁ b₂
    rw [Int.mul_add, add_smul]

noncomputable instance instMulZeroClass : MulZeroClass (InsertionAlgebra α) where
  zero_mul := zero_mul
  mul_zero := mul_zero

noncomputable instance instDistrib : Distrib (InsertionAlgebra α) where
  left_distrib := mul_add
  right_distrib := add_mul

noncomputable instance instNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (InsertionAlgebra α) :=
  { instAddCommGroup, instMulZeroClass, instDistrib with }

noncomputable instance instNonUnitalNonAssocRing :
    NonUnitalNonAssocRing (InsertionAlgebra α) :=
  { instAddCommGroup, instNonUnitalNonAssocSemiring with }

/-! ### Source-self swap `PermEquiv`

The pre-Lie identity reduces, after the lifted/preserved cancellations,
to a `mk`-equality between two singleton trees that differ by a
children-list swap at the source vertex `e`. Realized by structural
induction on `e : Path` + `t₁ : Tree α`: a `swapAtRoot` `PermStep`
at the root-path case, `recurse_lift` at the in-child cases. This is
the only Nonplanar-specific cancellation in the pre-Lie identity
proof; everything else holds at the planar level. -/

/-- Inserting `T₂` then `T₃` at path `e`, vs inserting `T₃` then `T₂` at
    path `e`, produces planar trees related by a `PermEquiv`
    (children-list swap at the source vertex `e`).

    Path form of `mk_insertAt_sourceSelf_swap_permEquiv`: since
    `Pathed.sourceSelf e = e` (the source vertex's path doesn't shift),
    the LHS/RHS shape just inserts twice at the same path with the two
    grafts in opposite orders. -/
private theorem mk_insertAt_sourceSelf_swap_permEquiv :
    ∀ (e : Tree.Pathed.Path) (t₁ T₂ T₃ : Tree α),
    Tree.PermEquiv
      (Tree.Pathed.insertAt e T₃ (Tree.Pathed.insertAt e T₂ t₁))
      (Tree.Pathed.insertAt e T₂ (Tree.Pathed.insertAt e T₃ t₁))
  | [], .node a cs, T₂, T₃ => by
    -- Root case: both nested grafts produce `node a (... :: ... :: cs)`
    -- differing only in the order of the first two children.
    -- A single `swapAtRoot` step suffices.
    rw [Tree.Pathed.insertAt_nil, Tree.Pathed.insertAt_nil,
        Tree.Pathed.insertAt_nil, Tree.Pathed.insertAt_nil]
    exact Tree.PermEquiv.of_step
      (Tree.PermStep.swapAtRoot (a := a) (l := T₃) (r := T₂)
        (pre := []) (post := cs))
  | i :: rest, .node a cs, T₂, T₃ => by
    by_cases hi : i < cs.length
    · -- In-bounds: collapse the nested sets via `List.set_set` + `getElem_set_self`,
      -- apply IH on `rest, cs[i]`, then lift through `node a (cs.set i ·)` via
      -- `permEquiv_recurse_lift (pre := cs.take i) (post := cs.drop (i+1))`.
      have ih := mk_insertAt_sourceSelf_swap_permEquiv rest (cs[i]'hi) T₂ T₃
      have hlen_T2 : i < (cs.set i (Tree.Pathed.insertAt rest T₂ (cs[i]'hi))).length := by
        rw [List.length_set]; exact hi
      have hlen_T3 : i < (cs.set i (Tree.Pathed.insertAt rest T₃ (cs[i]'hi))).length := by
        rw [List.length_set]; exact hi
      rw [Tree.Pathed.insertAt_cons_of_lt _ _ _ _ _ hi,
          Tree.Pathed.insertAt_cons_of_lt _ _ _ _ _ hi,
          Tree.Pathed.insertAt_cons_of_lt _ _ _ _ _ hlen_T2,
          Tree.Pathed.insertAt_cons_of_lt _ _ _ _ _ hlen_T3,
          List.getElem_set_self, List.getElem_set_self,
          List.set_set, List.set_set,
          show cs.set i (Tree.Pathed.insertAt rest T₃
                (Tree.Pathed.insertAt rest T₂ (cs[i]'hi)))
              = cs.take i ++ Tree.Pathed.insertAt rest T₃
                  (Tree.Pathed.insertAt rest T₂ (cs[i]'hi))
                  :: cs.drop (i + 1) from by
            rw [List.set_eq_take_append_cons_drop, if_pos hi],
          show cs.set i (Tree.Pathed.insertAt rest T₂
                (Tree.Pathed.insertAt rest T₃ (cs[i]'hi)))
              = cs.take i ++ Tree.Pathed.insertAt rest T₂
                  (Tree.Pathed.insertAt rest T₃ (cs[i]'hi))
                  :: cs.drop (i + 1) from by
            rw [List.set_eq_take_append_cons_drop, if_pos hi]]
      exact Tree.permEquiv_recurse_lift (cs.take i) (cs.drop (i + 1)) ih
    · -- Out-of-bounds: both `insertAt` calls are no-ops.
      simp only [Tree.Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi]
      exact Tree.PermEquiv.refl _

/-- Source-self swap as a `Nonplanar` equality. The form needed when the
    pre-Lie identity's source-self class is contracted. -/
private theorem mk_insertAt_sourceSelf_swap
    (e : Tree.Pathed.Path) (t₁ T₂ T₃ : Tree α) :
    Nonplanar.mk (Tree.Pathed.insertAt e T₃ (Tree.Pathed.insertAt e T₂ t₁)) =
    Nonplanar.mk (Tree.Pathed.insertAt e T₂ (Tree.Pathed.insertAt e T₃ t₁)) :=
  Nonplanar.mk_eq_mk_iff.mpr (mk_insertAt_sourceSelf_swap_permEquiv e t₁ T₂ T₃)

/-! ### Multiset bilinearity helpers

The custom `Mul` is bilinear, so multiplying an `ofMultiset` against a
single basis vector (or vice versa) yields an `ofMultiset` of a `bind`
of the underlying grafting product. These helpers chain into the
double-grafting form needed by the pre-Lie identity. -/

/-- Right-multiplication of `ofMultiset` against a single tree
    distributes as a `Multiset.bind` of `Nonplanar.insertSum`. -/
private theorem ofMultiset_mul_ofTree (M : Multiset (Nonplanar α)) (S : Nonplanar α) :
    (ofMultiset M : InsertionAlgebra α) * ofTree S =
      ofMultiset (M.bind (fun T => Nonplanar.insertSum T S)) := by
  induction M using Multiset.induction with
  | empty =>
    rw [ofMultiset_zero, zero_mul, Multiset.zero_bind, ofMultiset_zero]
  | cons t M ih =>
    rw [ofMultiset_cons, add_mul, ih, ofTree_mul_ofTree,
        Multiset.cons_bind, ofMultiset_add]

/-- Left-multiplication of a single tree against `ofMultiset`
    distributes as a `Multiset.bind` of `Nonplanar.insertSum`. -/
private theorem ofTree_mul_ofMultiset (T : Nonplanar α) (M : Multiset (Nonplanar α)) :
    (ofTree T : InsertionAlgebra α) * ofMultiset M =
      ofMultiset (M.bind (fun S => Nonplanar.insertSum T S)) := by
  induction M using Multiset.induction with
  | empty =>
    rw [ofMultiset_zero, mul_zero, Multiset.zero_bind, ofMultiset_zero]
  | cons s M ih =>
    rw [ofMultiset_cons, mul_add, ih, ofTree_mul_ofTree,
        Multiset.cons_bind, ofMultiset_add]

/-! ### Triple-product unfolding

Two glue lemmas reducing `ofTree T₁ * ofTree T₂ * ofTree T₃` (and the
right-associated form) to `ofMultiset` of a Multiset.bind chain. These
are the chain `ofTree_mul_ofTree → ofMultiset_mul_ofTree` (left-assoc)
and `ofTree_mul_ofTree → ofTree_mul_ofMultiset` (right-assoc). Used in
`assoc_symm_singleton` (§5) to drop into Multiset arithmetic. -/

/-- Left-associated triple product unfolds to `ofMultiset` of a
    `Multiset.bind` chain: first graft `T₂` at every vertex of `T₁`,
    then graft `T₃` at every vertex of each resulting tree. -/
private theorem ofTree_triple_left (T₁ T₂ T₃ : Nonplanar α) :
    (ofTree T₁ : InsertionAlgebra α) * ofTree T₂ * ofTree T₃ =
      ofMultiset ((Nonplanar.insertSum T₁ T₂).bind
        (fun T => Nonplanar.insertSum T T₃)) := by
  rw [ofTree_mul_ofTree, ofMultiset_mul_ofTree]

/-- Right-associated triple product unfolds analogously: first graft `T₃`
    at every vertex of `T₂`, then graft each resulting tree at every
    vertex of `T₁`. -/
private theorem ofTree_triple_right (T₁ T₂ T₃ : Nonplanar α) :
    (ofTree T₁ : InsertionAlgebra α) * (ofTree T₂ * ofTree T₃) =
      ofMultiset ((Nonplanar.insertSum T₂ T₃).bind
        (fun S => Nonplanar.insertSum T₁ S)) := by
  rw [ofTree_mul_ofTree, ofTree_mul_ofMultiset]

/-! ### Path-indexed bind reformulation

Two reformulation lemmas that convert `(t₁ ◁ t₂).bind (T ↦ T ◁ t₃)` and
`(Pathed.vertices t₁).bind (fun e => map (insertAt (lift e q) t₃)` to
the clean path-indexed and cross-term forms used by `assoc_symm_planar`. -/

/-- Step A reformulation: the outer-then-inner double-`insertSum` rewrites
    as a `Pathed.vertices`-indexed `bind`. Pure mathlib `bind_map`. -/
private theorem insertSum_bind_insertSum_eq_bind_vertices
    (t₁ t₂ t₃ : Tree α) :
    (Tree.insertSum t₁ t₂).bind (fun T => Tree.insertSum T t₃)
      = ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
          (fun e => Tree.insertSum (Tree.Pathed.insertAt e t₂ t₁) t₃)) := by
  rw [Tree.insertSum_eq_coe_map_insertAt t₁ t₂, ← Multiset.map_coe,
      Multiset.bind_map]

/-- Step C reformulation: the lifted class summed over `Pathed.vertices t₁`
    coincides with the cross term `(t₂ ◁ t₃).bind (t₁ ◁ ·)`. The proof
    chains `Pathed.insertAt_lift_eq_nested` + Fubini swap (`Multiset.bind_bind`-style)
    + backward `insertSum_eq_coe_map_insertAt` twice. -/
private theorem lifted_class_eq_cross (t₁ t₂ t₃ : Tree α) :
    ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind (fun e =>
        ((↑(Tree.Pathed.vertices t₂) : Multiset Tree.Pathed.Path).map
          (fun q => Tree.Pathed.insertAt (Tree.Pathed.lift e q) t₃
                      (Tree.Pathed.insertAt e t₂ t₁)))))
      = (Tree.insertSum t₂ t₃).bind (fun S => Tree.insertSum t₁ S) := by
  -- Step C.1: rewrite each summand via insertAt_lift_eq_nested.
  simp_rw [Tree.Pathed.insertAt_lift_eq_nested]
  -- Goal: (vertices t₁).bind (fun e =>
  --        (vertices t₂).map (fun q => insertAt e (insertAt q t₃ t₂) t₁)) =
  --       (insertSum t₂ t₃).bind (fun S => insertSum t₁ S)
  -- Step C.2: swap the two binds (Fubini) so e is inner and q is outer.
  rw [Multiset.bind_map_comm]
  -- Goal: (vertices t₂).bind (fun q =>
  --        (vertices t₁).map (fun e => insertAt e (insertAt q t₃ t₂) t₁)) = ...
  -- Step C.3: recognize inner map as `t₁ ◁ (insertAt q t₃ t₂)` via Multiset.map_coe
  -- (forward) followed by backward insertSum_eq_coe_map_insertAt.
  rw [show (fun q : Tree.Pathed.Path =>
            Multiset.map (fun e => Tree.Pathed.insertAt e
                            (Tree.Pathed.insertAt q t₃ t₂) t₁)
              (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path)) =
          (fun q => Tree.insertSum t₁
                      (Tree.Pathed.insertAt q t₃ t₂)) from
        funext fun q => by
          rw [Multiset.map_coe,
              ← Tree.insertSum_eq_coe_map_insertAt t₁
                  (Tree.Pathed.insertAt q t₃ t₂)]]
  -- Goal: (vertices t₂).bind (fun q => insertSum t₁ (insertAt q t₃ t₂)) =
  --       (insertSum t₂ t₃).bind (fun S => insertSum t₁ S)
  -- Step C.4: recognize outer bind as bind over (insertSum t₂ t₃).
  rw [Tree.insertSum_eq_coe_map_insertAt t₂ t₃, ← Multiset.map_coe,
      Multiset.bind_map]

/-! ### Tree 3-class identity

The planar Multiset (Nonplanar α) equality at the heart of the pre-Lie
identity. After `Quotient.inductionOn₃` reduces to planar `t₁ t₂ t₃`,
the pre-Lie associator's two halves rearrange to this form. The proof
uses `vertices_insertAt_decomp` to split each `(insertAt v t₂) ◁ t₃`
into preserved + sourceSelf + lifted classes:

- **Lifted** cancels with the cross term (LHS₂ / RHS₂) via
  `insertAt_lift_eq_nested` + `Multiset.bind_bind`.
- **Preserved** cancels at PLANAR level (no Nonplanar quotient needed)
  via `insertAt_commute_diff` + (v, w) ↔ (w, v) re-keying.
- **SourceSelf** cancels at NONPLANAR level via
  `mk_insertAt_sourceSelf_swap` (the only Nonplanar-specific step). -/

/-- The planar Multiset (Nonplanar α) identity: combining the four
    bind-of-insertSum chains for `t₁, t₂, t₃` (and their t₂↔t₃ swap)
    gives equal sums after `.map mk`. This is the substance of the
    pre-Lie identity, modulo the bilinear extension to InsertionAlgebra.

    Proof: decompose each `(insertAt e t₂) ◁ t₃` into preserved + sourceSelf
    + lifted classes via `vertices_insertAt_decomp` (path-form, with validity
    discharged by `forall_isValidPath`). The preserved class matches across
    LHS/RHS via `bind_filterMap_preserve?_swap`. SourceSelf matches via
    `mk_insertAt_sourceSelf_swap` (Nonplanar level). Lifted matches LHS₂/RHS₂
    via `lifted_class_eq_cross`. -/
private theorem assoc_symm_planar (t₁ t₂ t₃ : Tree α) :
    (((Tree.insertSum t₁ t₂).bind (fun T => Tree.insertSum T t₃)).map
        Nonplanar.mk : Multiset (Nonplanar α))
      + (((Tree.insertSum t₃ t₂).bind (fun S => Tree.insertSum t₁ S)).map
          Nonplanar.mk : Multiset (Nonplanar α)) =
    (((Tree.insertSum t₁ t₃).bind (fun T => Tree.insertSum T t₂)).map
        Nonplanar.mk : Multiset (Nonplanar α))
      + (((Tree.insertSum t₂ t₃).bind (fun S => Tree.insertSum t₁ S)).map
          Nonplanar.mk : Multiset (Nonplanar α)) := by
  -- Step 1: Reduce each "(t ◁ s) ◁ u" to a path-indexed bind.
  rw [insertSum_bind_insertSum_eq_bind_vertices t₁ t₂ t₃,
      insertSum_bind_insertSum_eq_bind_vertices t₁ t₃ t₂]
  simp_rw [Multiset.map_bind]
  -- Step 2: Apply the 3-class decomposition inside each outer bind.
  -- The target form mirrors what `simp_rw` produces (filterMap-Option.map +
  -- evaluated singleton + Multiset.map with composed function).
  have hdecomp_lhs : ∀ e ∈ (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path),
      Multiset.map Nonplanar.mk
          (Tree.insertSum (Tree.Pathed.insertAt e t₂ t₁) t₃) =
        Multiset.filterMap
            (fun a => Option.map
              (fun p => Nonplanar.mk
                (Tree.Pathed.insertAt p t₃ (Tree.Pathed.insertAt e t₂ t₁)))
              (Tree.Pathed.preserve? e a))
            (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path)
          + ({Nonplanar.mk
              (Tree.Pathed.insertAt (Tree.Pathed.sourceSelf e) t₃
                (Tree.Pathed.insertAt e t₂ t₁))} : Multiset (Nonplanar α))
          + Multiset.map
              (fun q => Nonplanar.mk
                (Tree.Pathed.insertAt (Tree.Pathed.lift e q) t₃
                  (Tree.Pathed.insertAt e t₂ t₁)))
              (↑(Tree.Pathed.vertices t₂) : Multiset Tree.Pathed.Path) := by
    intros e he
    have hv : Tree.Pathed.IsValidPath e t₁ :=
      Tree.Pathed.forall_isValidPath t₁ (by simpa using he)
    rw [Tree.insertSum_eq_coe_map_insertAt (Tree.Pathed.insertAt e t₂ t₁) t₃,
        ← Multiset.map_coe,
        Tree.Pathed.vertices_insertAt_decomp e t₁ t₂ hv]
    simp_rw [Multiset.map_add, Multiset.map_map, Multiset.map_filterMap,
             Multiset.map_singleton, Function.comp_def]
  have hdecomp_rhs : ∀ e ∈ (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path),
      Multiset.map Nonplanar.mk
          (Tree.insertSum (Tree.Pathed.insertAt e t₃ t₁) t₂) =
        Multiset.filterMap
            (fun a => Option.map
              (fun p => Nonplanar.mk
                (Tree.Pathed.insertAt p t₂ (Tree.Pathed.insertAt e t₃ t₁)))
              (Tree.Pathed.preserve? e a))
            (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path)
          + ({Nonplanar.mk
              (Tree.Pathed.insertAt (Tree.Pathed.sourceSelf e) t₂
                (Tree.Pathed.insertAt e t₃ t₁))} : Multiset (Nonplanar α))
          + Multiset.map
              (fun q => Nonplanar.mk
                (Tree.Pathed.insertAt (Tree.Pathed.lift e q) t₂
                  (Tree.Pathed.insertAt e t₃ t₁)))
              (↑(Tree.Pathed.vertices t₃) : Multiset Tree.Pathed.Path) := by
    intros e he
    have hv : Tree.Pathed.IsValidPath e t₁ :=
      Tree.Pathed.forall_isValidPath t₁ (by simpa using he)
    rw [Tree.insertSum_eq_coe_map_insertAt (Tree.Pathed.insertAt e t₃ t₁) t₂,
        ← Multiset.map_coe,
        Tree.Pathed.vertices_insertAt_decomp e t₁ t₃ hv]
    simp_rw [Multiset.map_add, Multiset.map_map, Multiset.map_filterMap,
             Multiset.map_singleton, Function.comp_def]
  rw [Multiset.bind_congr hdecomp_lhs, Multiset.bind_congr hdecomp_rhs]
  simp_rw [Multiset.bind_add]
  -- Step 3: Identify the three classes.
  -- Preserved class match: `bind_filterMap_preserve?_swap` composed with `mk`.
  have hpres : ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                  (fun e => Multiset.filterMap
                    (fun a => Option.map
                      (fun p => Nonplanar.mk
                        (Tree.Pathed.insertAt p t₃ (Tree.Pathed.insertAt e t₂ t₁)))
                      (Tree.Pathed.preserve? e a))
                    (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path)))
              = ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                  (fun e => Multiset.filterMap
                    (fun a => Option.map
                      (fun p => Nonplanar.mk
                        (Tree.Pathed.insertAt p t₂ (Tree.Pathed.insertAt e t₃ t₁)))
                      (Tree.Pathed.preserve? e a))
                    (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path))) := by
    have hkey : Multiset.map Nonplanar.mk
            ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
              (fun e => Multiset.filterMap
                (fun f => (Tree.Pathed.preserve? e f).map
                  (fun pos => Tree.Pathed.insertAt pos t₃
                    (Tree.Pathed.insertAt e t₂ t₁)))
                (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path)))
          = Multiset.map Nonplanar.mk
              ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                (fun e => Multiset.filterMap
                  (fun f => (Tree.Pathed.preserve? e f).map
                    (fun pos => Tree.Pathed.insertAt pos t₂
                      (Tree.Pathed.insertAt e t₃ t₁)))
                  (↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path))) :=
      congrArg (Multiset.map Nonplanar.mk)
        (Tree.Pathed.bind_filterMap_preserve?_swap t₁ t₂ t₃)
    rw [Multiset.map_bind, Multiset.map_bind] at hkey
    simp_rw [Multiset.map_filterMap, Option.map_map, Function.comp_def] at hkey
    exact hkey
  -- SourceSelf class match: `mk_insertAt_sourceSelf_swap` pointwise.
  have hself : ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                  (fun e => ({Nonplanar.mk
                      (Tree.Pathed.insertAt (Tree.Pathed.sourceSelf e) t₃
                        (Tree.Pathed.insertAt e t₂ t₁))} : Multiset (Nonplanar α))))
              = ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                  (fun e => ({Nonplanar.mk
                      (Tree.Pathed.insertAt (Tree.Pathed.sourceSelf e) t₂
                        (Tree.Pathed.insertAt e t₃ t₁))} : Multiset (Nonplanar α)))) := by
    apply Multiset.bind_congr
    intros e _
    simp only [Tree.Pathed.sourceSelf]
    rw [mk_insertAt_sourceSelf_swap e t₁ t₂ t₃]
  -- Lifted class for LHS₁: lifted_LHS_mk = RHS₂_mk via lifted_class_eq_cross.
  have hlift_lhs : ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                    (fun e => Multiset.map
                      (fun q => Nonplanar.mk
                        (Tree.Pathed.insertAt (Tree.Pathed.lift e q) t₃
                          (Tree.Pathed.insertAt e t₂ t₁)))
                      (↑(Tree.Pathed.vertices t₂) : Multiset Tree.Pathed.Path)))
                  = (Tree.insertSum t₂ t₃).bind
                      (fun S => Multiset.map Nonplanar.mk
                          (Tree.insertSum t₁ S)) := by
    have hkey : Multiset.map Nonplanar.mk
                  ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                    (fun e => Multiset.map
                      (fun q => Tree.Pathed.insertAt (Tree.Pathed.lift e q) t₃
                                  (Tree.Pathed.insertAt e t₂ t₁))
                      (↑(Tree.Pathed.vertices t₂) : Multiset Tree.Pathed.Path)))
              = Multiset.map Nonplanar.mk
                  ((Tree.insertSum t₂ t₃).bind
                    (fun S => Tree.insertSum t₁ S)) :=
      congrArg (Multiset.map Nonplanar.mk) (lifted_class_eq_cross t₁ t₂ t₃)
    rw [Multiset.map_bind, Multiset.map_bind] at hkey
    simp_rw [Multiset.map_map, Function.comp_def] at hkey
    exact hkey
  -- Lifted class for RHS₁: lifted_RHS_mk = LHS₂_mk (with t₂ ↔ t₃).
  have hlift_rhs : ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                    (fun e => Multiset.map
                      (fun q => Nonplanar.mk
                        (Tree.Pathed.insertAt (Tree.Pathed.lift e q) t₂
                          (Tree.Pathed.insertAt e t₃ t₁)))
                      (↑(Tree.Pathed.vertices t₃) : Multiset Tree.Pathed.Path)))
                  = (Tree.insertSum t₃ t₂).bind
                      (fun S => Multiset.map Nonplanar.mk
                          (Tree.insertSum t₁ S)) := by
    have hkey : Multiset.map Nonplanar.mk
                  ((↑(Tree.Pathed.vertices t₁) : Multiset Tree.Pathed.Path).bind
                    (fun e => Multiset.map
                      (fun q => Tree.Pathed.insertAt (Tree.Pathed.lift e q) t₂
                                  (Tree.Pathed.insertAt e t₃ t₁))
                      (↑(Tree.Pathed.vertices t₃) : Multiset Tree.Pathed.Path)))
              = Multiset.map Nonplanar.mk
                  ((Tree.insertSum t₃ t₂).bind
                    (fun S => Tree.insertSum t₁ S)) :=
      congrArg (Multiset.map Nonplanar.mk) (lifted_class_eq_cross t₁ t₃ t₂)
    rw [Multiset.map_bind, Multiset.map_bind] at hkey
    simp_rw [Multiset.map_map, Function.comp_def] at hkey
    exact hkey
  rw [hpres, hself, hlift_lhs, hlift_rhs]
  abel


/-! ### Singleton-reduction lemma

The pre-Lie identity `(x*y)*z - x*(y*z) = (x*z)*y - x*(z*y)` is bilinear
in each of x, y, z. By bilinearity, it suffices to prove on singletons
`ofTree T₁`, `ofTree T₂`, `ofTree T₃` for `T₁ T₂ T₃ : Nonplanar α`.

This section sets up the singleton reduction; the actual identity proof
is in §6. -/

/-- The pre-Lie identity on singletons. After `Quotient.inductionOn₃`
    reduces to planar t₁, t₂, t₃, the four triple products unfold via
    `ofTree_triple_left/right` to `ofMultiset` of planar bind chains
    projected through `Nonplanar.mk`. The combinatorial identity is
    `assoc_symm_planar`. -/
theorem assoc_symm_singleton (T₁ T₂ T₃ : Nonplanar α) :
    (ofTree T₁ : InsertionAlgebra α) * ofTree T₂ * ofTree T₃
      - ofTree T₁ * (ofTree T₂ * ofTree T₃) =
    (ofTree T₁ : InsertionAlgebra α) * ofTree T₃ * ofTree T₂
      - ofTree T₁ * (ofTree T₃ * ofTree T₂) := by
  refine Quotient.inductionOn₃ T₁ T₂ T₃ (fun t₁ t₂ t₃ => ?_)
  -- Reduce both sides via Step 1 helpers. After `change` to align ⟦t⟧ with Nonplanar.mk t,
  -- the chain simp fires.
  change (ofTree (Nonplanar.mk t₁) : InsertionAlgebra α) * ofTree (Nonplanar.mk t₂) *
            ofTree (Nonplanar.mk t₃)
      - ofTree (Nonplanar.mk t₁) * (ofTree (Nonplanar.mk t₂) * ofTree (Nonplanar.mk t₃)) =
        ofTree (Nonplanar.mk t₁) * ofTree (Nonplanar.mk t₃) * ofTree (Nonplanar.mk t₂)
      - ofTree (Nonplanar.mk t₁) * (ofTree (Nonplanar.mk t₃) * ofTree (Nonplanar.mk t₂))
  rw [ofTree_triple_left, ofTree_triple_right,
      ofTree_triple_left, ofTree_triple_right,
      Nonplanar.mk_insertSum, Nonplanar.mk_insertSum,
      Nonplanar.mk_insertSum, Nonplanar.mk_insertSum,
      Multiset.bind_map, Multiset.bind_map,
      Multiset.bind_map, Multiset.bind_map]
  -- Now each inner Nonplanar.insertSum (mk t) (mk s) → (Tree.insertSum t s).map mk
  -- + map_bind to extract .map mk
  conv_lhs =>
    rw [show ∀ M : Multiset (Tree α), ∀ s : Tree α,
            M.bind (fun t => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun t => Tree.insertSum t s)).map Nonplanar.mk from
        fun M s => by
          rw [show (fun t : Tree α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun t => (Tree.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm,
        show ∀ M : Multiset (Tree α), ∀ t : Tree α,
            M.bind (fun s => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun s => Tree.insertSum t s)).map Nonplanar.mk from
        fun M t => by
          rw [show (fun s : Tree α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun s => (Tree.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm]
  conv_rhs =>
    rw [show ∀ M : Multiset (Tree α), ∀ s : Tree α,
            M.bind (fun t => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun t => Tree.insertSum t s)).map Nonplanar.mk from
        fun M s => by
          rw [show (fun t : Tree α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun t => (Tree.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm,
        show ∀ M : Multiset (Tree α), ∀ t : Tree α,
            M.bind (fun s => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun s => Tree.insertSum t s)).map Nonplanar.mk from
        fun M t => by
          rw [show (fun s : Tree α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun s => (Tree.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm]
  -- Goal: ofMultiset ((bind ...).map mk) - ofMultiset ((bind ...).map mk) = ...
  rw [sub_eq_sub_iff_add_eq_add, ← ofMultiset_add, ← ofMultiset_add]
  congr 1
  exact assoc_symm_planar t₁ t₂ t₃

/-! ### Scalar pull-out for the custom `Mul`

The custom `Mul` is bilinear in the ℤ-coefficients: `(c • x) * y = c • (x * y)`
and `x * (c • y) = c • (x * y)`. Proved by direct unfolding of `mul_def` +
`Finsupp.sum_smul_index'` + `Finsupp.smul_sum`. These are needed by the
basis case of `assoc_symm`'s triple `Finsupp.induction_linear`. -/

/-- Scalar pull-out on the LEFT factor for the basis case:
    `(c • ofTree t) * y = c • (ofTree t * y)`. -/
private theorem smul_ofTree_mul (c : ℤ) (t : Nonplanar α) (y : InsertionAlgebra α) :
    ((c • ofTree t : InsertionAlgebra α) * y) = c • (ofTree t * y) := by
  -- c • ofTree t = single t c; ofTree t = single t 1.
  have h_ot : (c • ofTree t : InsertionAlgebra α) = Finsupp.single t c := by
    show (c • Finsupp.single t (1 : ℤ) : Nonplanar α →₀ ℤ) = Finsupp.single t c
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h_ot]
  show (Finsupp.single t c).sum
        (fun t' (a' : ℤ) =>
          y.sum (fun s (b : ℤ) =>
            (a' * b) • ofMultiset (Nonplanar.insertSum t' s))) =
       c • (Finsupp.single t (1 : ℤ)).sum
        (fun t' (a' : ℤ) =>
          y.sum (fun s (b : ℤ) =>
            (a' * b) • ofMultiset (Nonplanar.insertSum t' s)))
  have hzero : ∀ (t' : Nonplanar α),
      y.sum (fun s (b : ℤ) =>
          ((0 : ℤ) * b) • ofMultiset (Nonplanar.insertSum t' s)) = 0 := fun t' => by
    simp only [Int.zero_mul, zero_smul]
    exact Finsupp.sum_fun_zero (f := y) (N := InsertionAlgebra α)
  rw [Finsupp.sum_single_index (hzero t),
      Finsupp.sum_single_index (hzero t)]
  -- Now: y.sum (fun s b => (c * b) • _) = c • y.sum (fun s b => (1 * b) • _)
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr; intro s b_in
  -- Goal: (c * b_in) • _ = c • ((1 * b_in) • _)
  rw [one_mul, mul_smul]

/-- Scalar pull-out on the RIGHT factor for the basis case. -/
private theorem mul_smul_ofTree (x : InsertionAlgebra α) (c : ℤ) (s : Nonplanar α) :
    (x * (c • ofTree s : InsertionAlgebra α)) = c • (x * ofTree s) := by
  have h_os : (c • ofTree s : InsertionAlgebra α) = Finsupp.single s c := by
    show (c • Finsupp.single s (1 : ℤ) : Nonplanar α →₀ ℤ) = Finsupp.single s c
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h_os]
  show x.sum (fun t (a : ℤ) =>
        (Finsupp.single s c).sum (fun s' (b' : ℤ) =>
          (a * b') • ofMultiset (Nonplanar.insertSum t s'))) =
       c • x.sum (fun t (a : ℤ) =>
        (Finsupp.single s (1 : ℤ)).sum (fun s' (b' : ℤ) =>
          (a * b') • ofMultiset (Nonplanar.insertSum t s')))
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr; intro t _
  -- The inner `a` value of the Finsupp.sum is unbound here; use a fresh name.
  show (Finsupp.single s c).sum (fun s' (b' : ℤ) =>
          (x t * b') • ofMultiset (Nonplanar.insertSum t s')) =
       c • (Finsupp.single s (1 : ℤ)).sum (fun s' (b' : ℤ) =>
          (x t * b') • ofMultiset (Nonplanar.insertSum t s'))
  have hzero : ∀ (s' : Nonplanar α),
      (((x t : ℤ) * 0)) • ofMultiset (Nonplanar.insertSum t s') = 0 := fun s' => by
    simp only [Int.mul_zero, zero_smul]
  rw [Finsupp.sum_single_index (hzero s),
      Finsupp.sum_single_index (hzero s)]
  -- Goal: (x t * c) • _ = c • ((x t * 1) • _)
  rw [mul_one, show ((x t : ℤ) * c) = c * x t from mul_comm _ _, mul_smul]

/-- Right multiplication by `y` is an `AddMonoidHom`. Used to derive
    ℤ-linearity (`smul_mul_left`) from `add_mul` + `zero_mul`. -/
private noncomputable def mulRightHom (y : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α where
  toFun x := x * y
  map_zero' := zero_mul y
  map_add' x₁ x₂ := add_mul x₁ x₂ y

/-- Left multiplication by `x` is an `AddMonoidHom`. Used to derive
    ℤ-linearity (`mul_smul_right`) from `mul_add` + `mul_zero`. -/
private noncomputable def mulLeftHom (x : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α where
  toFun y := x * y
  map_zero' := mul_zero x
  map_add' y₁ y₂ := mul_add x y₁ y₂

/-- Scalar pull-out on the LEFT factor: `(c • x) * y = c • (x * y)`.
    Direct corollary of `AddMonoidHom.map_zsmul` for `mulRightHom y`. -/
private theorem smul_mul_left (c : ℤ) (x y : InsertionAlgebra α) :
    ((c • x : InsertionAlgebra α) * y) = c • (x * y) :=
  (mulRightHom y).map_zsmul c x

/-- Scalar pull-out on the RIGHT factor: `x * (c • y) = c • (x * y)`.
    Direct corollary of `AddMonoidHom.map_zsmul` for `mulLeftHom x`. -/
private theorem mul_smul_right (x : InsertionAlgebra α) (c : ℤ) (y : InsertionAlgebra α) :
    (x * (c • y : InsertionAlgebra α)) = c • (x * y) :=
  (mulLeftHom x).map_zsmul c y

/-! ### Pre-Lie identity

The headline. By bilinearity, reduces to `assoc_symm_singleton`. -/

/-- Each of the four product terms reduces to a single scalar coefficient
    times a tree-product. Helper for `assoc_symm_basis`. -/
private theorem smul_triple_left (a b c : ℤ) (X Y Z : InsertionAlgebra α) :
    (a • X) * (b • Y) * (c • Z) = (a * b * c) • ((X * Y) * Z) := by
  simp only [smul_mul_left, mul_smul_right, smul_smul, mul_assoc]
  congr 1
  ring

private theorem smul_triple_right (a b c : ℤ) (X Y Z : InsertionAlgebra α) :
    (a • X) * ((b • Y) * (c • Z)) = (a * b * c) • (X * (Y * Z)) := by
  simp only [smul_mul_left, mul_smul_right, smul_smul, mul_assoc]
  congr 1
  ring

/-- Triple-singleton basis case in `a • ofTree T` form. -/
private theorem assoc_symm_basis (T₁ T₂ T₃ : Nonplanar α) (a₁ a₂ a₃ : ℤ) :
    (a₁ • ofTree T₁ : InsertionAlgebra α) * (a₂ • ofTree T₂) * (a₃ • ofTree T₃) -
      (a₁ • ofTree T₁ : InsertionAlgebra α) *
        ((a₂ • ofTree T₂) * (a₃ • ofTree T₃)) =
    (a₁ • ofTree T₁ : InsertionAlgebra α) * (a₃ • ofTree T₃) * (a₂ • ofTree T₂) -
      (a₁ • ofTree T₁ : InsertionAlgebra α) *
        ((a₃ • ofTree T₃) * (a₂ • ofTree T₂)) := by
  rw [smul_triple_left, smul_triple_right, smul_triple_left, smul_triple_right]
  -- Goal: (a₁*a₂*a₃) • ((T₁*T₂)*T₃) - (a₁*a₂*a₃) • (T₁*(T₂*T₃)) =
  --       (a₁*a₃*a₂) • ((T₁*T₃)*T₂) - (a₁*a₃*a₂) • (T₁*(T₃*T₂))
  rw [show a₁ * a₃ * a₂ = a₁ * a₂ * a₃ from by ring]
  rw [← smul_sub, ← smul_sub, assoc_symm_singleton T₁ T₂ T₃]

/-- Triple-singleton form (with explicit `a • ofTree T` packaging). Workhorse
    for `assoc_symm`'s singleton basis after triple `addHom_ext`. -/
private theorem assoc_symm_three_singletons
    (T₁ T₂ T₃ : Nonplanar α) (a₁ a₂ a₃ : ℤ) :
    let s₁ : InsertionAlgebra α := a₁ • ofTree T₁
    let s₂ : InsertionAlgebra α := a₂ • ofTree T₂
    let s₃ : InsertionAlgebra α := a₃ • ofTree T₃
    s₁ * s₂ * s₃ - s₁ * (s₂ * s₃) = s₁ * s₃ * s₂ - s₁ * (s₃ * s₂) :=
  assoc_symm_basis T₁ T₂ T₃ a₁ a₂ a₃

/-- AddMonoidHom for `x ↦ x * y * z - x * (y * z)`, additive in `x`. -/
private noncomputable def assocLHSHom (y z : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α :=
  (mulRightHom z).comp (mulRightHom y) - mulRightHom (y * z)

/-- AddMonoidHom for `x ↦ x * z * y - x * (z * y)`, additive in `x`. -/
private noncomputable def assocRHSHom (y z : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α :=
  (mulRightHom y).comp (mulRightHom z) - mulRightHom (z * y)

/-- `assocLHSHom y z x = x * y * z - x * (y * z)`. -/
private theorem assocLHSHom_apply (x y z : InsertionAlgebra α) :
    assocLHSHom y z x = x * y * z - x * (y * z) := by
  show (mulRightHom z) ((mulRightHom y) x) - (mulRightHom (y * z)) x =
       x * y * z - x * (y * z)
  rfl

/-- `assocRHSHom y z x = x * z * y - x * (z * y)`. -/
private theorem assocRHSHom_apply (x y z : InsertionAlgebra α) :
    assocRHSHom y z x = x * z * y - x * (z * y) := by
  show (mulRightHom y) ((mulRightHom z) x) - (mulRightHom (z * y)) x =
       x * z * y - x * (z * y)
  rfl

/-- AddMonoidHom for `y ↦ x * y * z - x * (y * z)`, additive in `y`
    (with `x, z` fixed). -/
private noncomputable def assocLHSHomY (x z : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α :=
  (mulRightHom z).comp (mulLeftHom x) -
    (mulLeftHom x).comp (mulRightHom z)

/-- AddMonoidHom for `y ↦ x * z * y - x * (z * y)`, additive in `y`
    (with `x, z` fixed). -/
private noncomputable def assocRHSHomY (x z : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α :=
  (mulLeftHom (x * z)) - (mulLeftHom x).comp (mulLeftHom z)

/-- `assocLHSHomY x z y = x * y * z - x * (y * z)`. -/
private theorem assocLHSHomY_apply (x y z : InsertionAlgebra α) :
    assocLHSHomY x z y = x * y * z - x * (y * z) := by
  show (mulRightHom z) ((mulLeftHom x) y) - (mulLeftHom x) ((mulRightHom z) y) =
       x * y * z - x * (y * z)
  rfl

/-- `assocRHSHomY x z y = x * z * y - x * (z * y)`. -/
private theorem assocRHSHomY_apply (x y z : InsertionAlgebra α) :
    assocRHSHomY x z y = x * z * y - x * (z * y) := by
  show (mulLeftHom (x * z)) y - (mulLeftHom x) ((mulLeftHom z) y) =
       x * z * y - x * (z * y)
  rfl

/-- AddMonoidHom for `z ↦ x * y * z - x * (y * z)`, additive in `z`
    (with `x, y` fixed). -/
private noncomputable def assocLHSHomZ (x y : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α :=
  (mulLeftHom (x * y)) - (mulLeftHom x).comp (mulLeftHom y)

/-- AddMonoidHom for `z ↦ x * z * y - x * (z * y)`, additive in `z`
    (with `x, y` fixed). -/
private noncomputable def assocRHSHomZ (x y : InsertionAlgebra α) :
    InsertionAlgebra α →+ InsertionAlgebra α :=
  (mulRightHom y).comp (mulLeftHom x) -
    (mulLeftHom x).comp (mulRightHom y)

/-- `assocLHSHomZ x y z = x * y * z - x * (y * z)`. -/
private theorem assocLHSHomZ_apply (x y z : InsertionAlgebra α) :
    assocLHSHomZ x y z = x * y * z - x * (y * z) := by
  show (mulLeftHom (x * y)) z - (mulLeftHom x) ((mulLeftHom y) z) =
       x * y * z - x * (y * z)
  rfl

/-- `assocRHSHomZ x y z = x * z * y - x * (z * y)`. -/
private theorem assocRHSHomZ_apply (x y z : InsertionAlgebra α) :
    assocRHSHomZ x y z = x * z * y - x * (z * y) := by
  show (mulRightHom y) ((mulLeftHom x) z) - (mulLeftHom x) ((mulRightHom y) z) =
       x * z * y - x * (z * y)
  rfl

/-- The **pre-Lie identity** on `InsertionAlgebra α`:
    `(x * y) * z - x * (y * z) = (x * z) * y - x * (z * y)`.

    By trilinearity (three nested `Finsupp.addHom_ext`), reduces to
    `assoc_symm_three_singletons`. -/
theorem assoc_symm (x y z : InsertionAlgebra α) :
    x * y * z - x * (y * z) = x * z * y - x * (z * y) := by
  -- Reduce x to single via addHom_ext on x.
  have hx : assocLHSHom y z = assocRHSHom y z := by
    refine Finsupp.addHom_ext fun T₁ a₁ => ?_
    -- Goal: assocLHSHom y z (single T₁ a₁) = assocRHSHom y z (single T₁ a₁)
    -- Use a let-binding to give the singleton an explicit IA type.
    set s₁ : InsertionAlgebra α := Finsupp.single T₁ a₁ with s₁_def
    show assocLHSHom y z s₁ = assocRHSHom y z s₁
    rw [assocLHSHom_apply, assocRHSHom_apply]
    -- Reduce y to single via addHom_ext on y.
    have hy : assocLHSHomY s₁ z = assocRHSHomY s₁ z := by
      refine Finsupp.addHom_ext fun T₂ a₂ => ?_
      set s₂ : InsertionAlgebra α := Finsupp.single T₂ a₂ with s₂_def
      show assocLHSHomY s₁ z s₂ = assocRHSHomY s₁ z s₂
      rw [assocLHSHomY_apply, assocRHSHomY_apply]
      -- Reduce z to single via addHom_ext on z.
      have hz : assocLHSHomZ s₁ s₂ = assocRHSHomZ s₁ s₂ := by
        refine Finsupp.addHom_ext fun T₃ a₃ => ?_
        set s₃ : InsertionAlgebra α := Finsupp.single T₃ a₃ with s₃_def
        show assocLHSHomZ s₁ s₂ s₃ = assocRHSHomZ s₁ s₂ s₃
        rw [assocLHSHomZ_apply, assocRHSHomZ_apply]
        -- Convert each sᵢ to aᵢ • ofTree Tᵢ form.
        rw [show s₁ = a₁ • ofTree T₁ from (Finsupp.smul_single_one T₁ a₁).symm,
            show s₂ = a₂ • ofTree T₂ from (Finsupp.smul_single_one T₂ a₂).symm,
            show s₃ = a₃ • ofTree T₃ from (Finsupp.smul_single_one T₃ a₃).symm]
        exact assoc_symm_basis T₁ T₂ T₃ a₁ a₂ a₃
      have hzApp := DFunLike.congr_fun hz z
      rw [assocLHSHomZ_apply, assocRHSHomZ_apply] at hzApp
      exact hzApp
    have hyApp := DFunLike.congr_fun hy y
    rw [assocLHSHomY_apply, assocRHSHomY_apply] at hyApp
    exact hyApp
  have hxApp := DFunLike.congr_fun hx x
  rw [assocLHSHom_apply, assocRHSHom_apply] at hxApp
  exact hxApp

/-! ### `RightPreLieRing` instance -/

/-- The headline algebraic structure: `InsertionAlgebra α` is a right
    pre-Lie ring, with the `Vertex.classifyEquiv`-driven pre-Lie identity
    of `assoc_symm`. -/
noncomputable instance instRightPreLieRing :
    RightPreLieRing (InsertionAlgebra α) :=
  { instNonUnitalNonAssocRing with
    assoc_symm' := fun x y z => by
      show associator x y z = associator x z y
      unfold associator
      exact assoc_symm x y z }

/-! ### `RightPreLieAlgebra ℤ` instance

`InsertionAlgebra α` is a `RightPreLieAlgebra` over `ℤ`: the ℤ-module
structure plus scalar-tower / smul-comm-class follows from the
ℤ-bilinear `Mul`. -/

noncomputable instance instRightPreLieAlgebra :
    RightPreLieAlgebra ℤ (InsertionAlgebra α) where

end InsertionAlgebra

end RootedTree
