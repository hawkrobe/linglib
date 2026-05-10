import Linglib.Core.Algebra.RootedTree.PreLie.Defs
import Linglib.Core.Algebra.RootedTree.PreLie.VertexBijection
import Linglib.Core.Algebra.RootedTree.PreLie.Nonplanar
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
# `InsertionAlgebra α` — pre-Lie algebra on `(Nonplanar α) →₀ ℤ`
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{chapoton-livernet-2001}

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
     cancellable in `Nonplanar` but not `Planar`.

The Nonplanar-only swap-cancellation in the `sourceSelf` case is what
distinguishes the Nonplanar pre-Lie algebra from the (non-existent)
Planar one.

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

## Status

`[UPSTREAM]` candidate. **In progress** — Phase A wrapper landing now.

## File scope (R.3d)

This file (`PreLie/Algebra.lean`) carries:
- §1: `InsertionAlgebra` carrier + `AddCommGroup` / `Module ℤ` (Phase A)
- §2: `multisetToFinsupp` + custom `Mul` (Phase A)
- §3: Bilinearity lemmas + `NonUnitalNonAssocRing` (Phase B)
- §4: Singleton-reduction lemma (Phase C, prep)
- §5: Pre-Lie identity proof (Phase C, the meat)
- §6: `RightPreLieRing` instance (Phase D)
- §7: `RightPreLieAlgebra ℤ` instance (Phase E)
- §8: Sanity tests
-/

namespace RootedTree

namespace InsertionAlgebra

variable {α : Type*}

end InsertionAlgebra

/-! ## §1: Carrier + module instances (Phase A) -/

/-- The **insertion algebra** on `Nonplanar α`: the free ℤ-module on
    `Nonplanar α` with multiplication given by the bilinear extension of
    `Nonplanar.insertSum`. Defined as a type alias of `Nonplanar α →₀ ℤ`
    (the `MonoidAlgebra` pattern) so that we can attach a custom `Mul`. -/
def InsertionAlgebra (α : Type*) : Type _ := Nonplanar α →₀ ℤ

namespace InsertionAlgebra

variable {α : Type*}

noncomputable instance instAddCommGroup : AddCommGroup (InsertionAlgebra α) :=
  inferInstanceAs (AddCommGroup (Nonplanar α →₀ ℤ))

noncomputable instance instModule : Module ℤ (InsertionAlgebra α) :=
  inferInstanceAs (Module ℤ (Nonplanar α →₀ ℤ))

noncomputable instance instInhabited : Inhabited (InsertionAlgebra α) :=
  inferInstanceAs (Inhabited (Nonplanar α →₀ ℤ))

instance instFunLike : FunLike (InsertionAlgebra α) (Nonplanar α) ℤ :=
  inferInstanceAs (FunLike (Nonplanar α →₀ ℤ) (Nonplanar α) ℤ)

/-! ## §2: Smart constructor + custom Mul

`ofTree t` is the basis vector `Finsupp.single t 1`. The custom Mul is
the bilinear extension of `Nonplanar.insertSum`, computed via
`Finsupp.sum`. -/

/-- The basis vector for a single tree. -/
noncomputable def ofTree (t : Nonplanar α) : InsertionAlgebra α :=
  Finsupp.single t 1

@[simp] theorem ofTree_apply (t : Nonplanar α) :
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

/-! ## §3: Bilinearity + `NonUnitalNonAssocRing` (Phase B)

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

/-! ## §4-prep: source-self swap PlanarEquiv (R.3d Part 2)

The pre-Lie identity reduces, after the lifted/preserved cancellations,
to a `mk`-equality between two singleton trees that differ by a
children-list swap at the source vertex `v`. Realized by mutual
structural induction on `Vertex` / `VertexList`, with a `swapAtRoot`
`PlanarStep` at the root case and `recurse_lift` / `cons_lift` at the
inductive cases. This is the only Nonplanar-specific cancellation in
the pre-Lie identity proof; everything else holds at the planar level. -/

mutual
/-- Inserting `T₂` at `sourceSelf v T₂` then `T₃`, vs inserting `T₃` at
    `sourceSelf v T₃` then `T₂`, produces planar trees related by a
    `PlanarEquiv` (children-list swap at vertex `v`). -/
private theorem mk_insertAt_sourceSelf_swap_planarEquiv :
    ∀ {T : Planar α} (v : Planar.Vertex T) (T₂ T₃ : Planar α),
    Planar.PlanarEquiv (Planar.insertAt (Planar.Vertex.sourceSelf v T₂) T₃)
                       (Planar.insertAt (Planar.Vertex.sourceSelf v T₃) T₂)
  | _, .root a cs, T₂, T₃ => by
    -- LHS = node a (T₃ :: T₂ :: cs); RHS = node a (T₂ :: T₃ :: cs).
    -- Single swapAtRoot at position 0.
    apply Planar.PlanarEquiv.of_step
    show Planar.PlanarStep (Planar.node a ([] ++ T₃ :: T₂ :: cs))
                           (Planar.node a ([] ++ T₂ :: T₃ :: cs))
    exact .swapAtRoot
  | _, .inChild a cs vl, T₂, T₃ => by
    -- LHS = node a (insertAtList (sourceSelf vl T₂) T₃);
    -- RHS = node a (insertAtList (sourceSelf vl T₃) T₂).
    -- Push the swap inside via the list-version IH.
    exact mk_insertAtList_sourceSelf_swap_planarEquiv a vl T₂ T₃
/-- Sibling on `VertexList`: same swap, with the swap site somewhere
    inside the children list, lifted through `node a` via the appropriate
    `PlanarEquiv` lift. -/
private theorem mk_insertAtList_sourceSelf_swap_planarEquiv :
    ∀ (a : α) {cs : List (Planar α)} (vl : Planar.VertexList cs) (T₂ T₃ : Planar α),
    Planar.PlanarEquiv
      (Planar.node a (Planar.insertAtList (Planar.VertexList.sourceSelf vl T₂) T₃))
      (Planar.node a (Planar.insertAtList (Planar.VertexList.sourceSelf vl T₃) T₂))
  | a, _, .head c cs v, T₂, T₃ => by
    -- LHS = node a (insertAt (sourceSelf v T₂) T₃ :: cs);
    -- RHS = node a (insertAt (sourceSelf v T₃) T₂ :: cs).
    -- Lift the inner Vertex equivalence via recurse_lift at position 0.
    exact Planar.planarEquiv_recurse_lift [] cs
      (mk_insertAt_sourceSelf_swap_planarEquiv v T₂ T₃)
  | a, _, .tail c cs vl, T₂, T₃ => by
    -- LHS = node a (c :: insertAtList (sourceSelf vl T₂) T₃);
    -- RHS = node a (c :: insertAtList (sourceSelf vl T₃) T₂).
    -- Lift the inner VertexList equivalence via cons_lift.
    exact Planar.planarEquiv_cons_lift c
      (mk_insertAtList_sourceSelf_swap_planarEquiv a vl T₂ T₃)
end

/-- Source-self swap as a `Nonplanar` equality. The form needed when the
    pre-Lie identity's source-self class is contracted. -/
private theorem mk_insertAt_sourceSelf_swap {T : Planar α}
    (v : Planar.Vertex T) (T₂ T₃ : Planar α) :
    Nonplanar.mk (Planar.insertAt (Planar.Vertex.sourceSelf v T₂) T₃) =
    Nonplanar.mk (Planar.insertAt (Planar.Vertex.sourceSelf v T₃) T₂) :=
  Nonplanar.mk_eq_mk_iff.mpr (mk_insertAt_sourceSelf_swap_planarEquiv v T₂ T₃)

/-! ## §4-prep: Multiset bilinearity helpers (R.3d Part 2)

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

/-! ## §4-prep: Triple-product unfolding (R.3d Part 2 Step 1)

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

/-! ## §4: Planar 3-class identity (R.3d Part 2 Step 2)

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
    pre-Lie identity, modulo the bilinear extension to InsertionAlgebra. -/
private theorem assoc_symm_planar (t₁ t₂ t₃ : Planar α) :
    (((Planar.insertSum t₁ t₂).bind (fun T => Planar.insertSum T t₃)).map
        Nonplanar.mk : Multiset (Nonplanar α))
      + (((Planar.insertSum t₃ t₂).bind (fun S => Planar.insertSum t₁ S)).map
          Nonplanar.mk : Multiset (Nonplanar α)) =
    (((Planar.insertSum t₁ t₃).bind (fun T => Planar.insertSum T t₂)).map
        Nonplanar.mk : Multiset (Nonplanar α))
      + (((Planar.insertSum t₂ t₃).bind (fun S => Planar.insertSum t₁ S)).map
          Nonplanar.mk : Multiset (Nonplanar α)) := by
  -- TODO Step 2: 3-class decomposition of inner insertSum via vertices_insertAt_decomp.
  -- See plan at /Users/rxdh/.claude/plans/partitioned-yawning-parrot.md §"Step 2".
  sorry

/-! ## §5: Singleton-reduction lemma (Phase C, prep)

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
  -- Now each inner Nonplanar.insertSum (mk t) (mk s) → (Planar.insertSum t s).map mk
  -- + map_bind to extract .map mk
  conv_lhs =>
    rw [show ∀ M : Multiset (Planar α), ∀ s : Planar α,
            M.bind (fun t => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun t => Planar.insertSum t s)).map Nonplanar.mk from
        fun M s => by
          rw [show (fun t : Planar α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun t => (Planar.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm,
        show ∀ M : Multiset (Planar α), ∀ t : Planar α,
            M.bind (fun s => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun s => Planar.insertSum t s)).map Nonplanar.mk from
        fun M t => by
          rw [show (fun s : Planar α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun s => (Planar.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm]
  conv_rhs =>
    rw [show ∀ M : Multiset (Planar α), ∀ s : Planar α,
            M.bind (fun t => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun t => Planar.insertSum t s)).map Nonplanar.mk from
        fun M s => by
          rw [show (fun t : Planar α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun t => (Planar.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm,
        show ∀ M : Multiset (Planar α), ∀ t : Planar α,
            M.bind (fun s => Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
            (M.bind (fun s => Planar.insertSum t s)).map Nonplanar.mk from
        fun M t => by
          rw [show (fun s : Planar α =>
                    Nonplanar.insertSum (Nonplanar.mk t) (Nonplanar.mk s)) =
                  (fun s => (Planar.insertSum t s).map Nonplanar.mk) from
                funext fun _ => Nonplanar.mk_insertSum _ _]
          exact (Multiset.map_bind M _ _).symm]
  -- Goal: ofMultiset ((bind ...).map mk) - ofMultiset ((bind ...).map mk) = ...
  rw [sub_eq_sub_iff_add_eq_add, ← ofMultiset_add, ← ofMultiset_add]
  congr 1
  exact assoc_symm_planar t₁ t₂ t₃

/-! ## §5: Pre-Lie identity (Phase C, the meat)

The headline. By bilinearity, reduces to `assoc_symm_singleton`. -/

/-- The **pre-Lie identity** on `InsertionAlgebra α`:
    `(x * y) * z - x * (y * z) = (x * z) * y - x * (z * y)`.

    Equivalently, the associator `(x * y) * z - x * (y * z)` is symmetric
    in its last two arguments. This is exactly mathlib's
    `RightPreLieRing.assoc_symm'`. -/
theorem assoc_symm (x y z : InsertionAlgebra α) :
    x * y * z - x * (y * z) = x * z * y - x * (z * y) := by
  -- TODO Step 5: bilinear extension via triple Finsupp.induction_linear.
  -- Strategy: smul_mul_left/right helpers (Step 4) + triple Finsupp.induction_linear.
  -- Basis case (single t₁ a₁ * single t₂ a₂ * single t₃ a₃ ...) reduces via
  -- Finsupp.smul_single + scalar pull-outs to (a₁ * a₂ * a₃) • assoc_symm_singleton t₁ t₂ t₃.
  -- Plan: /Users/rxdh/.claude/plans/partitioned-yawning-parrot.md §"Step 4+5".
  sorry

/-! ## §6: `RightPreLieRing` instance (Phase D) -/

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

/-! ## §7: `RightPreLieAlgebra ℤ` instance (Phase E)

`InsertionAlgebra α` is a `RightPreLieAlgebra` over `ℤ`: the ℤ-module
structure plus scalar-tower / smul-comm-class follows from the
ℤ-bilinear `Mul`. -/

noncomputable instance instRightPreLieAlgebra :
    RightPreLieAlgebra ℤ (InsertionAlgebra α) where

end InsertionAlgebra

end RootedTree
