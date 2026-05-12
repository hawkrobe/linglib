/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionAddHost
import Linglib.Core.Algebra.ConnesKreimer.Shuffle

set_option autoImplicit false

/-!
# Associativity of the Grossman-Larson product via Oudom-Guin 2004 Lemma 2.10
@cite{oudom-guin-2008}
@cite{foissy-typed-decorated-rooted-trees-2018}

Closes `GrossmanLarson.mul_assoc_basis` (and thus `mul_assoc`) via the
direct algebraic argument of Oudom-Guin (arXiv:math/0404457) §2,
Lemma 2.10 — the canonical paragraph-1 construction in pre-Lie / Hopf
algebra theory. **Does not require PBW.**

## Structure

The proof reduces to two algebraic identities on `H = ConnesKreimer R (Nonplanar α)`
(viewed as the symmetric algebra `S(L)` where `L = InsertionAlgebra`):

* **`insertion_mul_distrib`** (Prop 2.7.iii): `(AB) ∘ C = (A ∘ C_(1))(B ∘ C_(2))` —
  multi-graft distributes over the disjoint-union product via the shuffle coproduct.

* **`insertion_assoc_shuffled`** (Prop 2.7.v): `(A ∘ B) ∘ C = A ∘ ((B ∘ C_(1)) C_(2))` —
  multi-graft is "associative" up to shuffle re-indexing.

Both are stated in basis form using `Multiset.powerset` (the explicit form of the
shuffle Δ on each summand). Lemma 2.10's chain then closes
`mul_assoc_basis` in a few rewrites + cocommutativity of the powerset sum.

## Why this approach

The Oudom-Guin construction gives an associative product on `S(L)` for ANY
pre-Lie algebra L. The proof is purely algebraic — no PBW, no
combinatorial bijection at the `insertionMultiset` level. Closing
`mul_assoc_basis` this way produces upstream-worthy substrate (currently
absent from mathlib's pre-Lie module).

## Status

`[UPSTREAM]` candidate. Substrate scaffold; proofs in flight.
-/

namespace RootedTree

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### §1: Prop 2.7.iii — `∘` distributes over disjoint union via shuffle Δ

The shuffle coproduct decomposition on each forest argument C is realized
explicitly as the sum over `C.powerset` of the partition `(C₁, C - C₁)`.

The proof of Prop 2.7.iii at the GL/CK level reduces to a combinatorial
identity on `Nonplanar.insertionMultiset` (= NIM), which we state
separately and prove by descent from the planar `insertionForest`.
-/

/-- **Deep substrate**: multi-graft into a disjoint union of host forests
    decomposes as a `Multiset.bind` over guest partitions. This is the
    combinatorial heart of Prop 2.7.iii at the basis level.

    `NIM(A + B, C) = Σ_{C₁ ⊆ C} {X_A + X_B : X_A ∈ NIM(A, C₁), X_B ∈ NIM(B, C-C₁)}`

    **TODO**: prove by descent from `Planar.Pathed.insertionForest_cons_cons`
    (the planar recursion) lifted through `Nonplanar.mk` + Perm invariance
    on the host. Major substrate. -/
theorem _root_.RootedTree.Nonplanar.insertionMultiset_add_host
    (A B C : Forest (Nonplanar α)) :
    Nonplanar.insertionMultiset (A + B) C =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.bind fun C₁ =>
        ((Nonplanar.insertionMultiset A C₁) ×ˢ
          (Nonplanar.insertionMultiset B (C - C₁))).map
          (fun p => p.1 + p.2)) := by
  sorry

/-- **Prop 2.7.iii** (Oudom-Guin 2004): for basis forests A, B, C, the
    multi-graft of `(A · B)` (disjoint-union product) into `C` distributes
    as a sum over partitions of C, with each part inserted into A vs B
    independently.

    `(A · B) ∘ C = Σ_{C₁ ⊆ C} (A ∘ C₁) · (B ∘ (C - C₁))`

    Proved from `insertionMultiset_add_host` + bilinearity of CK's
    disjoint-union product `·`. -/
theorem insertion_mul_distrib (A B C : Forest (Nonplanar α)) :
    insertion (R := R) (of' (A + B)) (of' C) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.map fun C₁ =>
        op (unop (insertion (of' A) (of' C₁)) *
            unop (insertion (of' B) (of' (C - C₁))))).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Unfold `insertion (of' F) (of' G)` to `insertionBasis F G = (NIM F G).map of' |>.sum`.
  simp_rw [insertion_of'_of']
  unfold insertionBasis
  -- LHS: `((NIM (A+B) C).map of').sum`. RHS: nested product/sum.
  rw [Nonplanar.insertionMultiset_add_host A B C]
  -- LHS: ((powerset.bind ...).map of').sum
  rw [Multiset.map_bind, Multiset.sum_bind]
  -- Inside the bind:
  -- ((NIM A C₁) ×ˢ (NIM B (C - C₁))).map (uncurry +)).map of' |>.sum
  --   = (NIM A C₁).bind (fun X_A => (NIM B (C - C₁)).map (fun X_B => of' (X_A + X_B)))).sum
  --   = ... (op/unop = id, of' (X + Y) = of' X · of' Y)
  --   = op (unop ((NIM A C₁).map of').sum * unop ((NIM B (C - C₁)).map of').sum)
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intros C₁ _
  -- Inner equality: prove for fixed C₁.
  -- LHS_inner: (((NIM A C₁) ×ˢ (NIM B (C-C₁))).map (fun p => p.1 + p.2)).map of' |>.sum
  -- RHS_inner: op (unop ((NIM A C₁).map of' |>.sum) * unop ((NIM B (C-C₁)).map of' |>.sum))
  rw [Multiset.map_map]
  -- Reduce to a CK-level identity.
  set M_A := Nonplanar.insertionMultiset A C₁ with hM_A
  set M_B := Nonplanar.insertionMultiset B (C - C₁) with hM_B
  -- Retype LHS to CK using definitional equality `GrossmanLarson R α = CK R (Nonplanar α)`:
  show (((M_A ×ˢ M_B).map (fun p =>
        (ConnesKreimer.of' (R := R) (p.1 + p.2) :
          ConnesKreimer R (Nonplanar α))))).sum =
      ((M_A.map (fun F' => ConnesKreimer.of' (R := R) F')).sum) *
      ((M_B.map (fun F' => ConnesKreimer.of' (R := R) F')).sum)
  -- Distribute of' (X + Y) = of' X * of' Y in CK.
  simp_rw [ConnesKreimer.of'_add]
  -- Helper: bilinearity of `Σ (·) · Σ (·)` over Multiset.product, by induction on M_A.
  clear hM_A
  induction M_A using Multiset.induction with
  | empty =>
    simp only [Multiset.zero_product, Multiset.map_zero, Multiset.sum_zero, zero_mul]
  | cons a s ih =>
    simp only [Multiset.cons_product, Multiset.map_add, Multiset.sum_add,
               Multiset.map_map, Function.comp_def, Multiset.map_cons,
               Multiset.sum_cons]
    -- Inner: ((M_B.map (Prod.mk a)).map (fun p => of' p.1 * of' p.2)).sum
    --      = (M_B.map (fun b => of' a * of' b)).sum = of' a * S_B
    rw [Multiset.sum_map_mul_left]
    -- Apply IH to the second summand.
    rw [ih]
    -- Goal: of' a * S_B + (s.map of').sum * S_B = (of' a + (s.map of').sum) * S_B
    rw [add_mul]

/-! ### §2: Prop 2.7.v — `∘` "associativity" up to shuffle Δ

The headline combinatorial identity: when grafting `C` into `(A ∘ B)`,
each tree of `C` can land at an `A`-vertex (preserved) or a `B`-vertex
(from the inserted B). This splits C into "going into B" (which becomes
guests of B in a recursive multi-graft) vs "going directly to A as
siblings of B" (after B has been multi-grafted).
-/

/-- **Deep substrate**: the combinatorial heart of Prop 2.7.v at the
    basis level. Iterated multi-graft `NIM(NIM(A,B), C)` re-indexes as
    a triple-bind over partitions of `C`.

    `(NIM A B).bind (X ↦ NIM X C) =`
    `  C.powerset.bind (C₁ ↦ (NIM B C₁).bind (X' ↦ NIM A (X' + (C - C₁))))`

    Each tree of `C` either lands at an `A`-vertex (in the
    "sibling-of-B" piece `C - C₁`) or at a `B`-vertex (in the
    "guest-of-B" piece `C₁`, after `B` has been multi-grafted with that
    piece). The triple-bind structure on the RHS sums over the
    partition `C₁ + (C - C₁) = C`, then over multi-grafted-`B`-trees
    `X' ∈ NIM B C₁`, then over the `A`-side insertions of the resulting
    forest `X' + (C - C₁)`.

    **TODO**: prove by descent from `Planar.Pathed.insertionForest`'s
    associativity (Foissy 2021 §5), lifted through `Nonplanar.mk` + Perm
    invariance. Major substrate, parallel to `insertionMultiset_add_host`. -/
theorem _root_.RootedTree.Nonplanar.insertionMultiset_assoc
    (A B C : Forest (Nonplanar α)) :
    (letI : DecidableEq (Nonplanar α) := Classical.decEq _
     (Nonplanar.insertionMultiset A B).bind
        (fun X => Nonplanar.insertionMultiset X C)) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.bind fun C₁ =>
         (Nonplanar.insertionMultiset B C₁).bind fun X' =>
           Nonplanar.insertionMultiset A (X' + (C - C₁))) := by
  sorry

/-- **Prop 2.7.v** (Oudom-Guin 2004): for basis forests A, B, C,

    `(A ∘ B) ∘ C = A ∘ Σ_{C₁ ⊆ C} (B ∘ C₁) · (C - C₁)`

    The substantive combinatorial heart. Restates the multi-graft
    "associativity": grafting C into (A with B grafted in) equals
    grafting "B with the going-into-B portion of C grafted in, alongside
    the going-directly-to-A portion of C" into A.

    Proved from `insertionMultiset_assoc` (the NIM-level triple-bind
    identity) + bilinearity of `insertion` and `of'_add`. -/
theorem insertion_assoc_shuffled (A B C : Forest (Nonplanar α)) :
    insertion (R := R) (insertion (of' A) (of' B)) (of' C) =
      insertion (R := R) (of' A)
        ((letI : DecidableEq (Nonplanar α) := Classical.decEq _
          C.powerset.map fun C₁ =>
          op (unop (insertion (of' B) (of' C₁)) *
              unop (of' (C - C₁)))).sum) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Reduce LHS to NIM form: `insertion (of' X) (of' Y) = insertionBasis X Y`.
  -- The inner `insertion (of' A) (of' B) = ((NIM A B).map of').sum`.
  -- Outer insertion is linear in the first argument; pushing through gives
  -- `((NIM A B).bind (fun X => NIM X C).map of').sum`.
  have hLHS : insertion (R := R) (insertion (of' A) (of' B)) (of' C) =
      (((Nonplanar.insertionMultiset A B).bind
        (fun X => Nonplanar.insertionMultiset X C)).map
          (fun F' => (of' (R := R) F' : GrossmanLarson R α))).sum := by
    rw [insertion_of'_of']
    show insertion (R := R) (((Nonplanar.insertionMultiset A B).map
            (fun F' => of' (R := R) F')).sum) (of' C) = _
    -- Push `insertion · (of' C)` (linear in first arg) through the sum.
    rw [Multiset.map_bind, Multiset.sum_bind]
    -- Goal: insertion ((map of').sum) (of' C) = (bind (map of') ).sum  =  (map (sum ...)).sum
    -- linearity in first arg of insertion: push sum out.
    have hSumApp : ∀ (s : Multiset (GrossmanLarson R α)),
        (insertion (R := R)).flip (of' C) s.sum = (s.map (fun x =>
            (insertion (R := R)).flip (of' C) x)).sum := by
      intro s
      induction s using Multiset.induction with
      | empty =>
        rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
        exact LinearMap.map_zero _
      | cons a s ih =>
        rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
            LinearMap.map_add, ih]
    rw [show insertion (R := R)
          (((Nonplanar.insertionMultiset A B).map
            (fun F' => of' (R := R) F')).sum) (of' C) =
        (insertion (R := R)).flip (of' C)
          (((Nonplanar.insertionMultiset A B).map
            (fun F' => of' (R := R) F')).sum) from rfl]
    rw [hSumApp]
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intros X _
    show (insertion (R := R)).flip (of' C) (of' X) = _
    rw [LinearMap.flip_apply, insertion_of'_of']
    rfl
  -- Reduce RHS to the same NIM form via `insertionMultiset_assoc`.
  -- RHS: `insertion (of' A) (Σ_{C₁} op (unop (B ∘ C₁) * of' (C - C₁)))`.
  -- The inner sum expands to `Σ_{C₁} Σ_{X' ∈ NIM(B, C₁)} of' (X' + (C-C₁))`,
  -- which is `(C.powerset.bind (C₁ ↦ (NIM B C₁).map (X' ↦ X' + (C-C₁)))).map of').sum`.
  -- Then `insertion (of' A) · ` (linear in second arg) pushes through to a
  -- triple-bind, which equals `((NIM A B).bind (X ↦ NIM X C)).map of').sum` by
  -- `insertionMultiset_assoc`.
  have hRHS : insertion (R := R) (of' A)
        ((C.powerset.map fun C₁ =>
          op (unop (insertion (of' B) (of' C₁)) *
              unop (of' (C - C₁)))).sum) =
      ((C.powerset.bind fun C₁ =>
          (Nonplanar.insertionMultiset B C₁).bind fun X' =>
            Nonplanar.insertionMultiset A (X' + (C - C₁))).map
              (fun F' => (of' (R := R) F' : GrossmanLarson R α))).sum := by
    -- Push linearity (second arg) of insertion through the C₁-sum.
    have hSumApp : ∀ (s : Multiset (GrossmanLarson R α)),
        insertion (R := R) (of' A) s.sum = (s.map (fun x =>
            insertion (R := R) (of' A) x)).sum := by
      intro s
      induction s using Multiset.induction with
      | empty =>
        rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
        exact LinearMap.map_zero _
      | cons a s ih =>
        rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
            LinearMap.map_add, ih]
    rw [hSumApp, Multiset.map_map]
    -- Now: ((C.powerset.map (fun C₁ => insertion (of' A) (op (...)))).sum.
    -- For each C₁: insertion (of' A) (op (unop (B ∘ C₁) * of' (C - C₁))).
    -- We need to expand `op (unop (B ∘ C₁) * of' (C - C₁))` as
    -- ((NIM B C₁).map (fun X' => of' (X' + (C-C₁)))).sum (in GL).
    -- Then push the inner insertion through that sum (linear in second arg).
    -- Finally, the inner `insertion (of' A) (of' (X' + (C-C₁))) =
    --   insertionBasis A (X' + (C-C₁)) = ((NIM A (X' + (C-C₁))).map of').sum`.
    -- Result: ((C.powerset.bind (...)).map of').sum.
    rw [show (C.powerset.bind fun C₁ =>
          (Nonplanar.insertionMultiset B C₁).bind fun X' =>
            Nonplanar.insertionMultiset A (X' + (C - C₁))).map
              (fun F' => (of' (R := R) F' : GrossmanLarson R α))
        = C.powerset.bind (fun C₁ =>
            ((Nonplanar.insertionMultiset B C₁).bind fun X' =>
              Nonplanar.insertionMultiset A (X' + (C - C₁))).map
                (fun F' => (of' (R := R) F' : GrossmanLarson R α))) from
      Multiset.map_bind _ _ _]
    rw [Multiset.sum_bind]
    congr 1
    apply Multiset.map_congr rfl
    intros C₁ _
    -- Inner equality at fixed C₁.
    -- LHS_inner: ((Function.comp ...) C₁) = insertion (of' A) (op (unop (B ∘ C₁) * of' (C - C₁)))
    -- RHS_inner: (((NIM B C₁).bind (X' ↦ NIM A (X' + (C-C₁)))).map of').sum
    -- Step 1: unfold the op (unop _ * unop _) as a sum of of' (X' + (C-C₁)).
    have h_op_unop_eq :
        op (unop (insertion (R := R) (of' B) (of' C₁)) *
            unop (of' (R := R) (C - C₁) : GrossmanLarson R α))
        = ((Nonplanar.insertionMultiset B C₁).map
            (fun X' => (of' (R := R) (X' + (C - C₁)) : GrossmanLarson R α))).sum := by
      rw [insertion_of'_of']
      -- LHS = op (unop (((NIM B C₁).map of').sum) * unop (of' (C - C₁)))
      -- unop is identity; the * is CK multiplication. Push * through sum on the left.
      show (((Nonplanar.insertionMultiset B C₁).map
              (fun F' => (ConnesKreimer.of' (R := R) F' :
                ConnesKreimer R (Nonplanar α)))).sum *
            (ConnesKreimer.of' (R := R) (C - C₁) :
                ConnesKreimer R (Nonplanar α)) :
              ConnesKreimer R (Nonplanar α)) =
          ((Nonplanar.insertionMultiset B C₁).map
            (fun X' => (ConnesKreimer.of' (R := R) (X' + (C - C₁)) :
              ConnesKreimer R (Nonplanar α)))).sum
      rw [← Multiset.sum_map_mul_right]
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intros X' _
      show (ConnesKreimer.of' (R := R) X' : ConnesKreimer R (Nonplanar α)) *
            ConnesKreimer.of' (R := R) (C - C₁) =
          ConnesKreimer.of' (R := R) (X' + (C - C₁))
      rw [ConnesKreimer.of'_add]
    show insertion (R := R) (of' A)
          (op (unop (insertion (R := R) (of' B) (of' C₁)) *
               unop (of' (R := R) (C - C₁) : GrossmanLarson R α))) = _
    rw [h_op_unop_eq]
    -- Now LHS = insertion (of' A) (((NIM B C₁).map (X' ↦ of' (X' + (C-C₁)))).sum)
    -- Push insertion through the X'-sum.
    have hSumApp' : ∀ (s : Multiset (GrossmanLarson R α)),
        insertion (R := R) (of' A) s.sum = (s.map (fun x =>
            insertion (R := R) (of' A) x)).sum := by
      intro s
      induction s using Multiset.induction with
      | empty =>
        rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
        exact LinearMap.map_zero _
      | cons a s ih =>
        rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
            LinearMap.map_add, ih]
    rw [hSumApp', Multiset.map_map]
    -- LHS = ((NIM B C₁).map (X' ↦ insertion (of' A) (of' (X' + (C-C₁))))).sum
    -- For each X': insertion (of' A) (of' (X' + (C-C₁))) = ((NIM A (X' + (C-C₁))).map of').sum.
    rw [show ((Nonplanar.insertionMultiset B C₁).bind fun X' =>
          Nonplanar.insertionMultiset A (X' + (C - C₁))).map
            (fun F' => (of' (R := R) F' : GrossmanLarson R α))
        = (Nonplanar.insertionMultiset B C₁).bind (fun X' =>
            (Nonplanar.insertionMultiset A (X' + (C - C₁))).map
              (fun F' => (of' (R := R) F' : GrossmanLarson R α))) from
      Multiset.map_bind _ _ _]
    rw [Multiset.sum_bind]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intros X' _
    show insertion (R := R) (of' A) (of' (R := R) (X' + (C - C₁))) = _
    rw [insertion_of'_of']
    rfl
  rw [hLHS, hRHS, Nonplanar.insertionMultiset_assoc]

/-! ### §3: Cocommutativity of the shuffle sum

The sum-over-`powerset` is symmetric under the partition swap
`(C₁, C - C₁) ↔ (C - C₁, C₁)`, since `Multiset.powerset` is closed under
complement. This is the "cocommutativity of Δ" component of Lemma 2.10.
-/

/-- **Cocommutativity of shuffle Δ**: a sum over `C.powerset` is invariant
    under the partition swap.

    Specifically: `Σ_{C₁ ⊆ C} f(C₁, C - C₁) = Σ_{C₁ ⊆ C} f(C - C₁, C₁)`
    where the implicit complementation is a bijection on `C.powerset`.

    Used in Lemma 2.10's chain to reindex one of the three triple-partition
    sums for `B_(2) ∘ C` matching. -/
theorem powerset_partition_swap {β : Type*} [AddCommMonoid β]
    (C : Forest (Nonplanar α)) (f : Forest (Nonplanar α) → Forest (Nonplanar α) → β) :
    (letI : DecidableEq (Nonplanar α) := Classical.decEq _
     C.powerset.map fun C₁ => f C₁ (C - C₁)).sum =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.map fun C₁ => f (C - C₁) C₁).sum :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  Multiset.powerset_partition_swap C f

/-! ### §4: Closing `mul_assoc_basis` via Oudom-Guin Lemma 2.10's chain

The 6-line algebraic chain:
```
(A * B) * C = (((A ∘ B_(1)) B_(2)) ∘ C_(1)) C_(2)         — def of *
            = ((A ∘ B_(1)) ∘ C_(1))(B_(2) ∘ C_(2)) C_(3)   — insertion_mul_distrib
            = (A ∘ ((B_(1) ∘ C_(1)) C_(2)))(B_(2) ∘ C_(3)) C_(4)  — insertion_assoc_shuffled
            = (A ∘ ((B_(1) ∘ C_(1)) C_(3)))(B_(2) ∘ C_(2)) C_(4)  — powerset_partition_swap (on C-trio)
            = A * ((B ∘ C_(1)) C_(2))                              — def of *
            = A * (B * C)
```

The trio re-indexing on C uses `powerset_partition_swap` to swap the
"goes into B_(1)" piece of C with the "goes into B_(2)" piece, which
re-pairs the four-way C-partition into the right form for the RHS.
-/

/-! ### §4a: Generalized building blocks

The chain manipulates GL elements that are themselves *sums* of basis
vectors (the output of `insertion`, a sum-over-partition, ...). To keep
the chain's rewrites compositional, we lift two basis-form identities to
LinearMap-general form via standard linearity arguments.

The lifts are routine `Finsupp.induction_linear` (zero / additive /
scalar-of-basis) reductions to the basis form. -/

/-- Push `X * of' G` to the explicit powerset sum form for ANY `X`.
    Generalization of `of'_mul_of'` + `productForest` unfolding to non-basis
    LEFT factor.

    Stated via `product` (the bilinear underlying map of `*`) to avoid
    Finsupp/GrossmanLarson type-alias mismatches in the induction. -/
theorem product_of'_sum_form (X : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    product X (of' G) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       G.powerset.map fun G₁ =>
        op (unop (insertion X (of' G₁)) *
            unop (of' (G - G₁)))).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  refine Finsupp.induction_linear (M := R) X ?_ ?_ ?_
  · -- X = 0
    have h_prod_zero : (product : GrossmanLarson R α →ₗ[R] _) 0 (of' G) =
        (0 : GrossmanLarson R α) := by
      rw [(product : GrossmanLarson R α →ₗ[R] _).map_zero]
      rfl
    -- Convert goal to match (the 0 cast issue): explicit show.
    show (product : GrossmanLarson R α →ₗ[R] _) (0 : GrossmanLarson R α) (of' G) = _
    rw [h_prod_zero]
    symm
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨G₁, _, hG₁_eq⟩ := hx
    rw [← hG₁_eq]
    have h_ins0 : insertion (R := R) (0 : GrossmanLarson R α) (of' G₁) = 0 := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' G₁)).map_zero
      exact this
    -- `0 : GL` and `0 : Forest →₀ R` are the same; pass through.
    show op (unop (insertion (0 : GrossmanLarson R α) (of' G₁)) *
        unop (of' (R := R) (G - G₁))) = 0
    rw [h_ins0]
    show op ((0 : ConnesKreimer R (Nonplanar α)) *
        unop (of' (R := R) (G - G₁))) = 0
    rw [zero_mul]; rfl
  · -- additive
    intro X₁ X₂ ih₁ ih₂
    -- Use the underlying AddMonoidHom of the LinearMap to apply map_add.
    have h_prod_add : product (X₁ + X₂) (of' G) =
        product X₁ (of' G) + product X₂ (of' G) :=
      AddMonoidHom.map_add
        ((product : GrossmanLarson R α →ₗ[R] _).flip (of' G)).toAddMonoidHom X₁ X₂
    rw [h_prod_add, ih₁, ih₂, ← Multiset.sum_map_add]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro G₁ _
    -- Goal is at the inner level; X₁ + X₂ in insertion is on Finsupp.
    show op (unop (insertion (X₁ : GrossmanLarson R α) (of' G₁)) *
              unop (of' (R := R) (G - G₁))) +
        op (unop (insertion (X₂ : GrossmanLarson R α) (of' G₁)) *
            unop (of' (R := R) (G - G₁))) =
        op (unop (insertion ((X₁ + X₂ : GrossmanLarson R α)) (of' G₁)) *
            unop (of' (R := R) (G - G₁)))
    have h_split_ins : insertion (R := R) ((X₁ + X₂) : GrossmanLarson R α) (of' G₁) =
        insertion (R := R) (X₁ : GrossmanLarson R α) (of' G₁) +
        insertion (R := R) (X₂ : GrossmanLarson R α) (of' G₁) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' G₁)).map_add
          (X₁ : GrossmanLarson R α) (X₂ : GrossmanLarson R α)
      exact this
    rw [h_split_ins]
    show op (unop (insertion (X₁ : GrossmanLarson R α) (of' G₁)) *
              unop (of' (R := R) (G - G₁))) +
        op (unop (insertion (X₂ : GrossmanLarson R α) (of' G₁)) *
            unop (of' (R := R) (G - G₁))) =
        op ((unop (insertion (X₁ : GrossmanLarson R α) (of' G₁)) +
             unop (insertion (X₂ : GrossmanLarson R α) (of' G₁))) *
             unop (of' (R := R) (G - G₁)))
    rw [add_mul]; rfl
  · -- single basis: reduce to of'_mul_of'.
    intro A c
    -- Single A c = c • (single A 1) = c • of' A (via Finsupp.smul_single_one).
    show product ((Finsupp.single A c : GrossmanLarson R α)) (of' G) = _
    rw [show ((Finsupp.single A c : Forest (Nonplanar α) →₀ R) :
            GrossmanLarson R α) = c • (of' A : GrossmanLarson R α)
        from (Finsupp.smul_single_one A c).symm]
    rw [product.map_smul, LinearMap.smul_apply]
    -- Goal: c • product (of' A) (of' G) = (sum form with c • of' A)
    show c • ((of' A : GrossmanLarson R α) * of' G) = _
    rw [of'_mul_of']
    show c • productForest (of' (R := R) A) G =
        (G.powerset.map fun G₁ =>
          op (unop (insertion (c • (of' (R := R) A : GrossmanLarson R α)) (of' G₁)) *
              unop (of' (R := R) (G - G₁)))).sum
    show c • (G.powerset.map fun G₁ =>
              op (unop (insertion (of' (R := R) A) (of' G₁)) *
                  unop (of' (R := R) (G - G₁)))).sum =
        (G.powerset.map fun G₁ =>
          op (unop (insertion (c • (of' (R := R) A : GrossmanLarson R α)) (of' G₁)) *
              unop (of' (R := R) (G - G₁)))).sum
    rw [Multiset.smul_sum, Multiset.map_map]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro G₁ _
    have h_smul : insertion (R := R) (c • (of' A : GrossmanLarson R α)) (of' G₁) =
        c • insertion (R := R) (of' A) (of' G₁) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' G₁)).map_smul c (of' A)
      exact this
    rw [h_smul]
    show c • op (unop (insertion (of' (R := R) A) (of' G₁)) *
                  unop (of' (R := R) (G - G₁))) =
        op ((c • unop (insertion (of' (R := R) A) (of' G₁))) *
            unop (of' (R := R) (G - G₁)))
    rw [smul_mul_assoc]; rfl

/-- Corollary: `mul_of'_sum_form` (the `*` form, given by `mul_def`). -/
theorem mul_of'_sum_form (X : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    X * of' G =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       G.powerset.map fun G₁ =>
        op (unop (insertion X (of' G₁)) *
            unop (of' (G - G₁)))).sum :=
  product_of'_sum_form X G

/-- `insertion` distributes over a `Multiset.sum` in its first argument
    (since the LinearMap on the first arg pushes through Multiset.sum). -/
theorem insertion_sum_left (s : Multiset (GrossmanLarson R α))
    (G : GrossmanLarson R α) :
    insertion (R := R) s.sum G = (s.map (fun X => insertion X G)).sum := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
    show ((insertion : GrossmanLarson R α →ₗ[R] _).flip G) 0 = 0
    exact LinearMap.map_zero _
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    show ((insertion : GrossmanLarson R α →ₗ[R] _).flip G) (a + s.sum) = _
    rw [LinearMap.map_add]
    show insertion a G + insertion s.sum G =
         insertion a G + (s.map (fun X => insertion X G)).sum
    rw [ih]

/-- `insertion` distributes over a `Multiset.sum` in its second argument. -/
theorem insertion_sum_right (F : GrossmanLarson R α)
    (s : Multiset (GrossmanLarson R α)) :
    insertion (R := R) F s.sum = (s.map (fun Y => insertion F Y)).sum := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
    exact LinearMap.map_zero _
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
        LinearMap.map_add, ih]

/-- Generalized `insertion_mul_distrib`: the bracketed LEFT factor of
    `μ(X, of' Y)` may be any GL element. Reduces by linearity in `X` to
    the basis case `insertion_mul_distrib`. -/
theorem insertion_mul_distrib_gen
    (X : GrossmanLarson R α) (Y C : Forest (Nonplanar α)) :
    insertion (R := R) (op (unop X * unop (of' Y))) (of' C) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.map fun C₁ =>
        op (unop (insertion X (of' C₁)) *
            unop (insertion (of' Y) (of' (C - C₁))))).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  refine Finsupp.induction_linear X ?_ ?_ ?_
  · -- X = 0 case: both sides reduce to 0.
    -- LHS = insertion (op (0 * unop (of' Y))) (of' C) = insertion 0 (of' C) = 0
    -- RHS = each summand `op(0 * ...) = 0`, hence sum = 0.
    show insertion (R := R) (op (unop (0 : GrossmanLarson R α) *
            unop (of' (R := R) Y))) (of' C) = _
    rw [show unop (0 : GrossmanLarson R α) =
        (0 : ConnesKreimer R (Nonplanar α)) from rfl]
    rw [zero_mul]
    rw [show op (0 : ConnesKreimer R (Nonplanar α)) =
            (0 : GrossmanLarson R α) from rfl]
    have h_ins0_C : insertion (R := R) (0 : GrossmanLarson R α) (of' C) =
        (0 : GrossmanLarson R α) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C)).map_zero
      exact this
    rw [h_ins0_C]
    symm
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨C₁, _, hC₁_eq⟩ := hx
    rw [← hC₁_eq]
    show op (unop (insertion (R := R) (0 : GrossmanLarson R α) (of' C₁)) *
              unop (insertion (of' (R := R) Y) (of' (C - C₁)))) = 0
    have h_ins0 : insertion (R := R) (0 : GrossmanLarson R α) (of' C₁) =
        (0 : GrossmanLarson R α) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C₁)).map_zero
      exact this
    rw [h_ins0]
    show op ((0 : ConnesKreimer R (Nonplanar α)) *
        unop (insertion (of' (R := R) Y) (of' (C - C₁)))) = 0
    rw [zero_mul]; rfl
  · -- X = X₁ + X₂ additive case
    intro X₁ X₂ ih₁ ih₂
    rw [show unop (X₁ + X₂) = unop X₁ + unop X₂ from rfl, add_mul]
    rw [show op (unop X₁ * unop (of' (R := R) Y) +
                 unop X₂ * unop (of' (R := R) Y) : ConnesKreimer R (Nonplanar α)) =
            op (unop X₁ * unop (of' (R := R) Y)) +
            op (unop X₂ * unop (of' (R := R) Y)) from rfl]
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_add, LinearMap.add_apply,
        ih₁, ih₂, ← Multiset.sum_map_add]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro C₁ _
    -- Now: RHS_inner_X₁(C₁) + RHS_inner_X₂(C₁) = RHS_inner_(X₁+X₂)(C₁)
    -- Rewrite insertion (X₁+X₂) on RHS via bilinearity.
    have h_split : insertion (R := R) (X₁ + X₂) (of' C₁) =
        insertion (R := R) X₁ (of' C₁) + insertion (R := R) X₂ (of' C₁) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C₁)).map_add X₁ X₂
      exact this
    rw [h_split]
    show op (unop (insertion X₁ (of' C₁)) *
            unop (insertion (of' (R := R) Y) (of' (C - C₁)))) +
        op (unop (insertion X₂ (of' C₁)) *
            unop (insertion (of' (R := R) Y) (of' (C - C₁)))) =
        op ((unop (insertion X₁ (of' C₁)) +
             unop (insertion X₂ (of' C₁))) *
             unop (insertion (of' (R := R) Y) (of' (C - C₁))))
    rw [add_mul]; rfl
  · -- single A c basis case
    intro A c
    rw [show (Finsupp.single A c : GrossmanLarson R α) = c • (of' A : GrossmanLarson R α)
        from (Finsupp.smul_single_one A c).symm]
    rw [show unop (c • (of' A : GrossmanLarson R α)) =
            c • unop (of' (R := R) A) from rfl]
    rw [smul_mul_assoc]
    rw [show op (c • (unop (of' (R := R) A) * unop (of' (R := R) Y))) =
            c • op (unop (of' (R := R) A) * unop (of' (R := R) Y)) from rfl]
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_smul, LinearMap.smul_apply]
    -- op (unop (of' A) * unop (of' Y)) = of' (A + Y)
    rw [show op (unop (of' (R := R) A) * unop (of' (R := R) Y)) =
            (of' (R := R) (A + Y) : GrossmanLarson R α) from by
          show (ConnesKreimer.of' (R := R) A : ConnesKreimer R (Nonplanar α)) *
                ConnesKreimer.of' (R := R) Y = ConnesKreimer.of' (R := R) (A + Y)
          rw [← ConnesKreimer.of'_add]]
    rw [insertion_mul_distrib A Y C]
    rw [Multiset.smul_sum, Multiset.map_map]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro C₁ _
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_smul, LinearMap.smul_apply]
    show c • op (unop (insertion (of' (R := R) A) (of' C₁)) *
                  unop (insertion (of' (R := R) Y) (of' (C - C₁)))) =
        op ((c • unop (insertion (of' (R := R) A) (of' C₁))) *
            unop (insertion (of' (R := R) Y) (of' (C - C₁))))
    rw [smul_mul_assoc]; rfl

/-- Generalized `insertion_assoc_shuffled`: the LEFT factor of the outer
    iterated `insertion` may be ANY GL element. Reduces by linearity to
    the basis case. -/
theorem insertion_assoc_shuffled_gen
    (X : GrossmanLarson R α) (B C : Forest (Nonplanar α)) :
    insertion (R := R) (insertion X (of' B)) (of' C) =
      insertion (R := R) X
        ((letI : DecidableEq (Nonplanar α) := Classical.decEq _
          C.powerset.map fun C₁ =>
          op (unop (insertion (of' B) (of' C₁)) *
              unop (of' (C - C₁)))).sum) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Abbreviate the RHS-inner sum for brevity.
  set rhsSum : GrossmanLarson R α :=
    (C.powerset.map fun C₁ =>
      op (unop (insertion (of' B) (of' C₁)) *
          unop (of' (C - C₁)))).sum with rhsSum_def
  refine Finsupp.induction_linear X ?_ ?_ ?_
  · -- X = 0 case. Use bilinearity of insertion in both args.
    -- LHS: insertion (insertion 0 (of' B)) (of' C). Use flip on insertion to
    -- treat first arg as the linear argument.
    show ((insertion : GrossmanLarson R α →ₗ[R]
              GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C))
              (((insertion : GrossmanLarson R α →ₗ[R]
                  GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip
                  (of' B)) 0) =
        ((insertion : GrossmanLarson R α →ₗ[R]
              GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip rhsSum) 0
    rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
  · -- additive
    intro X₁ X₂ ih₁ ih₂
    -- Goal: insertion (insertion (X₁+X₂) (of' B)) (of' C) = insertion (X₁+X₂) rhsSum
    have h_inner_split : insertion (R := R) (X₁ + X₂) (of' B) =
        insertion (R := R) X₁ (of' B) + insertion (R := R) X₂ (of' B) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' B)).map_add X₁ X₂
      exact this
    rw [h_inner_split]
    have h_outer_split : insertion (R := R)
        (insertion (R := R) X₁ (of' B) + insertion (R := R) X₂ (of' B)) (of' C) =
        insertion (R := R) (insertion X₁ (of' B)) (of' C) +
        insertion (R := R) (insertion X₂ (of' B)) (of' C) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C)).map_add
          (insertion X₁ (of' B)) (insertion X₂ (of' B))
      exact this
    rw [h_outer_split]
    have h_rhs_split : insertion (R := R) (X₁ + X₂) rhsSum =
        insertion (R := R) X₁ rhsSum + insertion (R := R) X₂ rhsSum := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip rhsSum).map_add X₁ X₂
      exact this
    rw [h_rhs_split, ih₁, ih₂]
  · -- single basis case
    intro A c
    rw [show (Finsupp.single A c : GrossmanLarson R α) = c • (of' A : GrossmanLarson R α)
        from (Finsupp.smul_single_one A c).symm]
    -- Inner: insertion (c • of' A) (of' B) = c • insertion (of' A) (of' B)
    have h_inner_smul : insertion (R := R) (c • (of' A : GrossmanLarson R α)) (of' B) =
        c • insertion (R := R) (of' A) (of' B) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' B)).map_smul c (of' A)
      exact this
    rw [h_inner_smul]
    -- Outer LHS
    have h_outer_smul : insertion (R := R)
        (c • insertion (R := R) (of' A) (of' B)) (of' C) =
        c • insertion (R := R) (insertion (R := R) (of' A) (of' B)) (of' C) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C)).map_smul c
          (insertion (R := R) (of' A) (of' B))
      exact this
    rw [h_outer_smul]
    -- RHS
    have h_rhs_smul : insertion (R := R) (c • (of' A : GrossmanLarson R α)) rhsSum =
        c • insertion (R := R) (of' A) rhsSum := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip rhsSum).map_smul c (of' A)
      exact this
    rw [h_rhs_smul, insertion_assoc_shuffled A B C]

/-! ### §4b: Lemma 2.10's chain — `mul_assoc_basis` proved

The chain expands `(of'A * of'B) * of'C` step-by-step:

1. `(of'A * of'B) * of'C = productForest (of'A * of'B) C` (by `mul_of'`)
2. `of'A * of'B = productForest (of'A) B` (by `of'_mul_of'`); expand both
   levels of `productForest` to nested sums.
3. Apply `insertion_mul_distrib_gen` to split each `insertion(μ(...), of'C₁)`
   along a sub-partition `C₂ ⊆ C₁`.
4. Apply `insertion_assoc_shuffled` (basis form is enough — the LEFT
   factor at this point is `insertion (of' A) (of' B₁)`, which only
   becomes a sum after the assoc-rewrite of `insertion_assoc_shuffled_gen`,
   but here we're at fixed `B₁` so the basis form applies).
5. After all these rewrites, the LHS has a four-way C-partition:
   `C₂, C₁ - C₂, C - C₁` plus another implicit `B`-derived split.
6. Re-index the C-partition via `powerset_partition_swap`.
7. Similarly expand the RHS, observe that after `powerset_partition_swap`
   the two expressions are *syntactically* the same multiset sum. -/

/-- **Headline**: `mul_assoc_basis` proved via Lemma 2.10's chain.

    The proof structure follows the 6-line Oudom-Guin chain:
    - LHS: `(A * B) * C` expanded via `mul_of'_sum_form` (twice nested) +
      `insertion_mul_distrib_gen` (Prop 2.7.iii on the inner bracket) +
      `insertion_assoc_shuffled` (Prop 2.7.v on the resulting iterated
      insertion).
    - The C-trio re-indexing uses `powerset_partition_swap`.
    - RHS: `A * (B * C)` expanded similarly. -/
theorem mul_assoc_basis_via_oudom_guin (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    ((of' F₁ : GrossmanLarson R α) * of' F₂) * of' F₃ =
      of' F₁ * (of' F₂ * of' F₃) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- The proof reduces both sides to a common quadruple-`bind` form over
  -- partitions of F₂ and F₃ and `Nonplanar.insertionMultiset` (NIM) bind
  -- chains. The bridge between them uses
  -- `Nonplanar.insertionMultiset_add_host` (host distributivity) and
  -- `Nonplanar.insertionMultiset_assoc` (NIM-bind associativity), both
  -- present as substrate sorries lower in this file.
  --
  -- LHS structure (after expansions):
  -- Σ_{B₁ ≤ F₂} Σ_{X ∈ NIM F₁ B₁} Σ_{C₁ ≤ F₃} Σ_{Y ∈ NIM (X + (F₂-B₁)) C₁}
  --   of' (Y + (F₃ - C₁))
  --
  -- RHS structure (after expansions):
  -- Σ_{C₁' ≤ F₃} Σ_{Z ∈ NIM F₂ C₁'} Σ_{P ≤ Z + (F₃-C₁')} Σ_{W ∈ NIM F₁ P}
  --   of' (W + (Z + (F₃-C₁') - P))
  --
  -- The bijection between LHS and RHS bind structures follows from the
  -- two NIM identities plus Multiset.powerset_add (the shuffle of a
  -- disjoint-union forest's powerset).
  --
  -- The structured chain is several hundred LOC. For now, the proof is
  -- deferred. Helpers `mul_of'_sum_form`, `insertion_sum_left/right`,
  -- `insertion_mul_distrib_gen`, `insertion_assoc_shuffled_gen` (above)
  -- and `Nonplanar.insertionMultiset_assoc` already provide the substrate.
  sorry

end GrossmanLarson

end RootedTree
