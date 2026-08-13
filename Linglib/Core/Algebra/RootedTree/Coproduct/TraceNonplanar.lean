/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.Trace
import Linglib.Core.Combinatorics.RootedTree.DoubleCut
import Linglib.Core.Combinatorics.RootedTree.Cut
import Mathlib.RingTheory.Bialgebra.Basic

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false
-- Nested tensor squares `CK ⊗ (CK ⊗ CK)` need one extra pending step during
-- instance synthesis: the chain `Semiring (CK ⊗ (CK ⊗ CK)) → Algebra R (CK ⊗ CK)
-- → Semiring (CK ⊗ CK) → …` nests pending subgoals past the default limit
-- (verified still required with the full granular instance set on the wrapper).
set_option maxSynthPendingDepth 2

/-!
# Δ^c on `ConnesKreimer R (Nonplanar (α ⊕ β))` via descent
[marcolli-chomsky-berwick-2025]
[foissy-typed-decorated-rooted-trees-2018]

The decorated coproduct Δ^c (contraction-extraction with trace
placeholders), descended from the tree-level `comulCAlgHomP` in
`Coproduct/Trace.lean` to `Nonplanar` trees, with its coassociativity,
counit laws, and `Bialgebra` packaging. Together with the edge grading
in `Coproduct/TraceGrading.lean` this closes
[marcolli-chomsky-berwick-2025] Lemma 1.2.10, the graded bialgebra
structure of `(V(F_{SO_0}), ⊔, Δ^c)`.

## Construction

1. **`comulCTreeN`, `comulCForestN`, `comulCAlgHomN`** — Nonplanar
   tree/forest-level Δ^c, packaged as algebra hom. The descent layer
   mirrors `Coproduct/PruningNonplanar.lean`'s descent of Δ^ρ.
2. **Coassociativity** (`comulCN_coassoc`, under `TraceCoherent`) by
   the direct double-cut bijection: both composites expand to sums
   over double-cut enumerators (`lhsExpand`/`rhsExpand`), which agree
   under trace coherence (`doubleCut_eq`), descended from the planar
   `DoubleCut.coassT` (`Core/Combinatorics/RootedTree/DoubleCut.lean`)
   through `Nonplanar.mk`.
3. **Counit laws** from the empty-cut uniqueness of the enumeration
   (`cutSummandsCN_filter_empty`, `Core/Combinatorics/RootedTree/Cut.lean`).
4. **`bialgebraC`** — the `Bialgebra` structure, via `Bialgebra.ofAlgHom`.

## No GL/Δ^c duality

The GL/CK pairing duality that proves Δ^ρ coassociativity in
`Coproduct/PruningDuality.lean` is **false** for Δ^c: GL grafting never
removes trace markers, so no orientation of
`⟨x ⋆ y, z⟩ = pairing₂ (…) (Δ^c z)` can hold, and B+ is not a Hochschild
1-cocycle for Δ^c either (see the Trace-coherence section below). The
pairings themselves live in `Coproduct/Pairing.lean`.

## Status

`[UPSTREAM]` candidate.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### Nonplanar tree- and forest-level Δ^c -/

/-- The Nonplanar tree-level Δ^c coproduct. -/
noncomputable def comulCTreeN (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar (α ⊕ β)))
  + ((cutSummandsCN τ T).map
      (fun p => ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.ofTree p.2)).sum

/-- The Nonplanar forest-level Δ^c (multiplicative extension). -/
noncomputable def comulCForestN (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  (F.map (comulCTreeN (R := R) τ)).prod

@[simp] theorem comulCForestN_zero (τ : Nonplanar (α ⊕ β) → β) :
    comulCForestN (R := R) τ (0 : Forest (Nonplanar (α ⊕ β))) = 1 := by
  simp only [comulCForestN, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulCForestN_add (τ : Nonplanar (α ⊕ β) → β)
    (F G : Forest (Nonplanar (α ⊕ β))) :
    comulCForestN (R := R) τ (F + G) =
      comulCForestN (R := R) τ F * comulCForestN (R := R) τ G := by
  unfold comulCForestN
  rw [Multiset.map_add, Multiset.prod_add]

/-- Forest-level Δ^c as a `MonoidHom` from `Multiplicative (Forest ...)`. -/
noncomputable def comulCMonoidHomN (τ : Nonplanar (α ⊕ β) → β) :
    Multiplicative (Forest (Nonplanar (α ⊕ β))) →*
      (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Nonplanar (α ⊕ β))) where
  toFun F := comulCForestN (R := R) τ F.toAdd
  map_one' := comulCForestN_zero τ
  map_mul' F G := comulCForestN_add τ F.toAdd G.toAdd

/-- The **Δ^c coproduct on `ConnesKreimer R (Nonplanar (α ⊕ β))`** as
    an algebra hom, parameterized by the trace encoder `τ`. -/
noncomputable def comulCAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.lift (comulCMonoidHomN τ)

@[simp] theorem comulCAlgHomN_apply_of' (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.of' F) = comulCForestN τ F := by
  rw [comulCAlgHomN, ConnesKreimer.lift_of']
  rfl

@[simp] theorem comulCAlgHomN_apply_ofTree (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.ofTree T) = comulCTreeN τ T := by
  rw [show (ConnesKreimer.ofTree T : ConnesKreimer R (Nonplanar (α ⊕ β)))
        = ConnesKreimer.of' {T} from rfl, comulCAlgHomN_apply_of']
  show comulCForestN τ {T} = _
  unfold comulCForestN
  rw [Multiset.map_singleton, Multiset.prod_singleton]

/-! ### Trace coherence

There is **no** GL/Δ^c pairing duality: for any marker-free `z` with a
proper admissible cut, the trunk side of `Δ^c z` carries trace-marker
leaves, while every forest in the support of a GL product `x ⋆ y` has at
least as many markers as `x` and `y` combined (grafting never removes
vertices) — so `⟨x ⋆ y, z⟩ = 0` against any cut summand that would make
the right side nonzero, in either slot orientation. The duality (with
crossed slots) is true for the deletion variant Δ^ρ and is proved in
`Coproduct/PruningDuality.lean`.

Δ^c coassociativity itself is **not τ-generic** either: iterating Δ^c
re-encodes already-cut subtrees, so the marker written by a second-stage
cut is `τ` of a tree *containing markers*, while the opposite cut order
writes `τ` of the original subtree. For `τ` sensitive to that difference
coassociativity fails (counterexample: `τ` = count of `Sum.inl`
vertices, `z` an inl-labeled 3-chain).
[marcolli-chomsky-berwick-2025]'s proof of Lemma 1.2.10 (book
p. 37–38) silently uses that their trace labels compose under
contraction ("the accessible terms of accessible terms … are themselves
accessible terms"); `TraceCoherent` is that hypothesis made explicit. -/

/-- **Trace coherence**: `τ` does not distinguish a cut trunk (with its
    trace markers) from the tree it was cut from. This is the condition
    under which iterated Δ^c cuts commute (coassociativity): second-stage
    markers computed on marked trunks agree with markers computed on the
    original tree. Constant encoders satisfy it (`traceCoherent_const`);
    [marcolli-chomsky-berwick-2025]'s identity trace satisfies it in
    spirit via label expansion (their marker labels denote subtrees of
    the *original* tree). -/
def TraceCoherent (τ : Nonplanar (α ⊕ β) → β) : Prop :=
  ∀ T : Nonplanar (α ⊕ β), ∀ p ∈ cutSummandsCN τ T, τ p.2 = τ T

/-- Constant trace encoders are coherent. -/
theorem traceCoherent_const (b : β) :
    TraceCoherent (fun _ : Nonplanar (α ⊕ β) => b) :=
  fun _ _ _ => rfl

/-! ### Double-cut enumeration — substrate for the direct coassoc proof

The combinatorial core of Δ^c coassociativity (`comulCN_coassoc_tree`),
following the [marcolli-chomsky-berwick-2025] Lemma 1.2.10 argument
("the accessible terms of accessible terms … are themselves accessible
terms"). Both `(Δ^c ⊗ id) ∘ Δ^c` and `(id ⊗ Δ^c) ∘ Δ^c` enumerate
ordered pairs of nested admissible cuts of a tree; the two enumerations
biject under `TraceCoherent`.

The proof structure:
1. `comulCTreeN`/`comulCForestN` as multiset sums over cut enumerators
   `treeCutsN`/`forestCutsN` (this section).
2. Each composite expands to a sum over a double-cut enumerator
   `dcLHS`/`dcRHS` (`lhsExpand`/`rhsExpand`).
3. `dcLHS = dcRHS` as Nonplanar multisets under coherence
   (`doubleCut_eq`, the bijection). -/

section DoubleCut
variable {R : Type*} [CommSemiring R] {α β : Type*}

/-- Tensor-product factor of a (crown, trunk) cut pair. -/
private noncomputable def cutTensor
    (p : Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.of' p.2

/-- Triple-tensor factor for the coassoc target `CK ⊗ (CK ⊗ CK)`. -/
private noncomputable def tripleTensor
    (q : Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) ×
         Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
      (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β))) :=
  ConnesKreimer.of' (R := R) q.1 ⊗ₜ[R]
    (ConnesKreimer.of' q.2.1 ⊗ₜ[R] ConnesKreimer.of' q.2.2)

/-- Product of two multiset-sums equals the sum over their cartesian
    product. The combinatorial backbone of `comulCForestN_eq_sum`. -/
private theorem sum_product_map_mul {A B M : Type*} [NonUnitalNonAssocSemiring M]
    (s : Multiset A) (t : Multiset B) (f : A → M) (g : B → M) :
    ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum =
      (s.map f).sum * (t.map g).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [Multiset.map_map,
        show (fun p => f p.1 * g p.2) ∘ (Prod.mk a) = (fun b => f a * g b) from rfl,
        ← Multiset.sum_map_mul_left]

/-- Convolution-of-cuts is left-commutative (it is the symmetric
    `combinerProjG` of the descent layer); needed for `Multiset.foldr`. -/
instance instLeftCommConvCut : LeftCommutative
    (fun (s acc : Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)))) =>
      (s ×ˢ acc).map ConnesKreimer.combinerProjG) :=
  ⟨fun a b c => ConnesKreimer.swap_double_combinerProjG a b c⟩

/-- All cut summands of a tree as (crown forest, trunk forest) pairs:
    full cut `({T}, ∅)`, plus `cutSummandsCN` (which already includes the
    empty cut `(∅, {T})` and all proper cuts, each with a single-tree
    trunk). -/
private noncomputable def treeCutsN (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β))) :=
  ({T}, 0) ::ₘ (cutSummandsCN τ T).map (fun p => (p.1, {p.2}))

/-- `comulCTreeN` as a single multiset sum over `treeCutsN`. -/
private theorem comulCTreeN_eq_sum (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    comulCTreeN (R := R) τ T = ((treeCutsN τ T).map (cutTensor (R := R))).sum := by
  unfold comulCTreeN treeCutsN
  rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
  congr 1

/-- Forest-level cut enumeration via convolution over the component trees. -/
private noncomputable def forestCutsN (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β))) :=
  (F.map (treeCutsN τ)).foldr
    (fun s acc => (s ×ˢ acc).map ConnesKreimer.combinerProjG) {(0, 0)}

private theorem forestCutsN_zero (τ : Nonplanar (α ⊕ β) → β) :
    forestCutsN τ (0 : Forest (Nonplanar (α ⊕ β))) = {(0, 0)} := by
  unfold forestCutsN; simp

private theorem forestCutsN_cons (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (F : Forest (Nonplanar (α ⊕ β))) :
    forestCutsN τ (T ::ₘ F) =
      (treeCutsN τ T ×ˢ forestCutsN τ F).map ConnesKreimer.combinerProjG := by
  unfold forestCutsN
  rw [Multiset.map_cons, Multiset.foldr_cons]

/-- `comulCForestN` as a single multiset sum over `forestCutsN`. -/
private theorem comulCForestN_eq_sum (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    comulCForestN (R := R) τ F = ((forestCutsN τ F).map (cutTensor (R := R))).sum := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, forestCutsN_zero, Multiset.map_singleton,
        Multiset.sum_singleton]
    show (1 : _) = ConnesKreimer.of' (R := R) (0 : Forest (Nonplanar (α ⊕ β))) ⊗ₜ[R]
      ConnesKreimer.of' 0
    rw [ConnesKreimer.of'_zero, Algebra.TensorProduct.one_def]
  | cons T F ih =>
    rw [show (T ::ₘ F : Forest (Nonplanar (α ⊕ β))) = {T} + F from
          (Multiset.singleton_add T F).symm, comulCForestN_add]
    rw [show comulCForestN (R := R) τ {T} = comulCTreeN τ T from by
          unfold comulCForestN; rw [Multiset.map_singleton, Multiset.prod_singleton],
        comulCTreeN_eq_sum, ih]
    rw [show ({T} + F : Forest (Nonplanar (α ⊕ β))) = T ::ₘ F from
          (Multiset.singleton_add T F), forestCutsN_cons, Multiset.map_map]
    rw [show (cutTensor (R := R) ∘ ConnesKreimer.combinerProjG) =
          (fun p => cutTensor (R := R) p.1 * cutTensor p.2) from ?_]
    · rw [sum_product_map_mul]
    · funext p
      obtain ⟨⟨F1, m1⟩, ⟨F2, m2⟩⟩ := p
      show cutTensor (R := R) (F1 + F2, m1 + m2) =
        cutTensor (R := R) (F1, m1) * cutTensor (F2, m2)
      unfold cutTensor
      simp only [ConnesKreimer.of'_add, Algebra.TensorProduct.tmul_mul_tmul]

/-- LHS double-cut enumerator: outer cut of `T`, then re-cut its crown. -/
private noncomputable def dcLHS (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) ×
              Forest (Nonplanar (α ⊕ β))) :=
  (treeCutsN τ T).bind (fun AB =>
    (forestCutsN τ AB.1).map (fun A12 => (A12.1, A12.2, AB.2)))

/-- RHS double-cut enumerator: outer cut of `T`, then re-cut its trunk. -/
private noncomputable def dcRHS (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) ×
              Forest (Nonplanar (α ⊕ β))) :=
  (treeCutsN τ T).bind (fun AB =>
    (forestCutsN τ AB.2).map (fun B12 => (AB.1, B12.1, B12.2)))

/-- Per-cut-pair LHS: reassociating `comulCForestN`-of-crown ⊗ trunk
    enumerates the crown's forest cuts. -/
private theorem lhs_per_pair (τ : Nonplanar (α ⊕ β) → β)
    (A B : Forest (Nonplanar (α ⊕ β))) :
    (TensorProduct.assoc R (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β))) (ConnesKreimer R (Nonplanar (α ⊕ β))))
        (comulCForestN (R := R) τ A ⊗ₜ[R] ConnesKreimer.of' B) =
      ((forestCutsN τ A).map
        (fun A12 => tripleTensor (R := R) (A12.1, A12.2, B))).sum := by
  rw [comulCForestN_eq_sum]
  let φ : (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
                ConnesKreimer R (Nonplanar (α ⊕ β))) :=
    (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
      ((TensorProduct.mk R _ _).flip (ConnesKreimer.of' B))
  show φ ((Multiset.map (cutTensor (R := R)) (forestCutsN τ A)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _
  show (TensorProduct.assoc R _ _ _)
      ((ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.of' p.2) ⊗ₜ[R]
        ConnesKreimer.of' B) = _
  rw [TensorProduct.assoc_tmul]
  rfl

/-- Per-cut-pair RHS: crown ⊗ `comulCForestN`-of-trunk enumerates the
    trunk's forest cuts. -/
private theorem rhs_per_pair (τ : Nonplanar (α ⊕ β) → β)
    (A B : Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer.of' (R := R) A ⊗ₜ[R] comulCForestN (R := R) τ B =
      ((forestCutsN τ B).map
        (fun B12 => tripleTensor (R := R) (A, B12.1, B12.2))).sum := by
  rw [comulCForestN_eq_sum]
  let ψ : (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
                ConnesKreimer R (Nonplanar (α ⊕ β))) :=
    (TensorProduct.mk R _ _) (ConnesKreimer.of' A)
  show ψ ((Multiset.map (cutTensor (R := R)) (forestCutsN τ B)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _
  rfl

/-- **LHS expansion**: `assoc ∘ (Δ^c ⊗ id) ∘ Δ^c` on a tree enumerates
    `dcLHS`. -/
private theorem lhsExpand (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    (TensorProduct.assoc R (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β))) (ConnesKreimer R (Nonplanar (α ⊕ β))))
        ((comulCAlgHomN (R := R) τ).toLinearMap.rTensor _ (comulCTreeN τ T)) =
      ((dcLHS τ T).map (tripleTensor (R := R))).sum := by
  rw [comulCTreeN_eq_sum]
  let Λ := (TensorProduct.assoc R (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β)))).toLinearMap ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap.rTensor
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
  show Λ ((Multiset.map (cutTensor (R := R)) (treeCutsN τ T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold dcLHS
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show Λ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCutsN τ A).map (fun A12 => (A12.1, A12.2, B)))).sum
  rw [Multiset.map_map]
  show (TensorProduct.assoc R _ _ _)
      ((comulCAlgHomN (R := R) τ).toLinearMap.rTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B)) = _
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, comulCAlgHomN_apply_of',
      lhs_per_pair]
  rfl

/-- **RHS expansion**: `(id ⊗ Δ^c) ∘ Δ^c` on a tree enumerates `dcRHS`. -/
private theorem rhsExpand (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ (comulCTreeN τ T) =
      ((dcRHS τ T).map (tripleTensor (R := R))).sum := by
  rw [comulCTreeN_eq_sum]
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _
        ((Multiset.map (cutTensor (R := R)) (treeCutsN τ T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold dcRHS
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCutsN τ B).map (fun B12 => (A, B12.1, B12.2)))).sum
  rw [Multiset.map_map]
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B) = _
  rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, comulCAlgHomN_apply_of',
      rhs_per_pair]
  rfl

/-! ### Descent of the double-cut enumerators through `Nonplanar.mk`

The Nonplanar `dcLHS`/`dcRHS` are the projections (via `Nonplanar.mk`) of the
tree-level `DoubleCut.dcLHSP`/`dcRHSP`; `DoubleCut.coassT` then gives the bijection. -/

/-- Project a tree-level (crown, trunk) pair to Nonplanar. -/
private def projPair (p : Forest (RoseTree (α ⊕ β)) × Forest (RoseTree (α ⊕ β))) :
    Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) :=
  (p.1.map Nonplanar.mk, p.2.map Nonplanar.mk)

private theorem treeCutsN_mk (τ : Nonplanar (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    treeCutsN τ (Nonplanar.mk t)
      = (DoubleCut.treeCutsP (τ ∘ Nonplanar.mk) t).map projPair := by
  unfold treeCutsN DoubleCut.treeCutsP
  rw [cutSummandsCN_mk, Multiset.map_cons, Multiset.map_map, Multiset.map_map]
  congr 1

/-- Naturality of the cut combiner under `projPair`. -/
private theorem combinerProjG_nat
    (A B : Multiset (Forest (RoseTree (α ⊕ β)) × Forest (RoseTree (α ⊕ β)))) :
    ((A.map projPair) ×ˢ (B.map projPair)).map ConnesKreimer.combinerProjG
      = ((A ×ˢ B).map (fun pq => (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2))).map projPair := by
  rw [← ConnesKreimer.map_prodMap_product_G, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨⟨F1, m1⟩, ⟨F2, m2⟩⟩ _
  show ConnesKreimer.combinerProjG
      ((F1.map Nonplanar.mk, m1.map Nonplanar.mk), (F2.map Nonplanar.mk, m2.map Nonplanar.mk))
    = projPair (F1 + F2, m1 + m2)
  show (F1.map Nonplanar.mk + F2.map Nonplanar.mk, m1.map Nonplanar.mk + m2.map Nonplanar.mk)
      = ((F1 + F2).map Nonplanar.mk, (m1 + m2).map Nonplanar.mk)
  rw [Multiset.map_add, Multiset.map_add]

private theorem forestCutsN_mk (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (RoseTree (α ⊕ β))) :
    forestCutsN τ (F.map Nonplanar.mk)
      = (DoubleCut.forestCutsP (τ ∘ Nonplanar.mk) F).map projPair := by
  induction F using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, forestCutsN_zero, DoubleCut.forestCutsP_zero,
        Multiset.map_singleton]; rfl
  | cons t F ih =>
    rw [Multiset.map_cons, forestCutsN_cons, treeCutsN_mk, ih, DoubleCut.forestCutsP_cons,
        DoubleCut.convFP_eq, combinerProjG_nat]

private theorem dcLHS_mk (τ : Nonplanar (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcLHS τ (Nonplanar.mk t) = (DoubleCut.dcLHSP (τ ∘ Nonplanar.mk) t).map DoubleCut.proj3 := by
  unfold dcLHS DoubleCut.dcLHSP
  rw [treeCutsN_mk, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; rintro ⟨F, G⟩ _
  show (forestCutsN τ (F.map Nonplanar.mk)).map (fun A12 => (A12.1, A12.2, G.map Nonplanar.mk))
      = ((DoubleCut.forestCutsP (τ ∘ Nonplanar.mk) F).map
          (fun A12 => (A12.1, A12.2, G))).map DoubleCut.proj3
  rw [forestCutsN_mk, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨A1, A2⟩ _; rfl

private theorem dcRHS_mk (τ : Nonplanar (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcRHS τ (Nonplanar.mk t) = (DoubleCut.dcRHSP (τ ∘ Nonplanar.mk) t).map DoubleCut.proj3 := by
  unfold dcRHS DoubleCut.dcRHSP
  rw [treeCutsN_mk, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; rintro ⟨F, G⟩ _
  show (forestCutsN τ (G.map Nonplanar.mk)).map (fun B12 => (F.map Nonplanar.mk, B12.1, B12.2))
      = ((DoubleCut.forestCutsP (τ ∘ Nonplanar.mk) G).map
          (fun B12 => (F, B12.1, B12.2))).map DoubleCut.proj3
  rw [forestCutsN_mk, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨B1, B2⟩ _; rfl

/-- The tree-level trace coherence descends from the Nonplanar one. -/
private theorem traceCoherentP_of_coherent (τ : Nonplanar (α ⊕ β) → β)
    (hτ : TraceCoherent τ) : DoubleCut.TraceCoherentP (τ ∘ Nonplanar.mk) := by
  intro t p hp
  have hmem : ConnesKreimer.projSummand p ∈ cutSummandsCN τ (Nonplanar.mk t) := by
    rw [cutSummandsCN_mk]; exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩
  exact hτ (Nonplanar.mk t) (ConnesKreimer.projSummand p) hmem

/-- **The double-cut bijection** (MCB Lemma 1.2.10's combinatorial core):
    the LHS and RHS double-cut enumerators of a tree agree as Nonplanar
    multisets, under trace coherence. Proved by descending through
    `Nonplanar.mk` to the tree-level `DoubleCut.coassT`. -/
private theorem doubleCut_eq (τ : Nonplanar (α ⊕ β) → β)
    (hτ : TraceCoherent τ) (T : Nonplanar (α ⊕ β)) :
    dcLHS τ T = dcRHS τ T := by
  induction T using Quotient.inductionOn with
  | _ t =>
    show dcLHS τ (Nonplanar.mk t) = dcRHS τ (Nonplanar.mk t)
    rw [dcLHS_mk, dcRHS_mk,
        DoubleCut.coassT (τ ∘ Nonplanar.mk) (traceCoherentP_of_coherent τ hτ) t]

end DoubleCut

/-! ### Coassociativity of Δ^c on Nonplanar (direct double-cut bijection)

Specialized to `[CommRing R]` (rather than `[CommSemiring R]`) only for
uniformity with the `Bialgebra` consumers; the double-cut proof itself is
`CommSemiring`-generic. -/

section CoassocCommRing
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- **Per-tree Δ^c coassociativity** (LinearMap-applied form on a single
    tree's coproduct `comulCTreeN τ T`). The combinatorial heart of
    coassociativity: both sides enumerate ordered pairs of nested
    admissible cuts of `T`, and `TraceCoherent τ` makes the trunk-marker
    labels written by the two cut orders agree.

    Reduced by the two expansion lemmas (`lhsExpand`, `rhsExpand`) to the
    double-cut bijection `doubleCut_eq`. The headline `comulCN_coassoc`
    reduces to this by multiplicativity (forest = product of trees). -/
theorem comulCN_coassoc_tree
    (τ : Nonplanar (α' ⊕ β') → β') (hτ : TraceCoherent τ)
    (T : Nonplanar (α' ⊕ β')) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        ((comulCAlgHomN (R := R') τ).toLinearMap.rTensor _ (comulCTreeN τ T)) =
      (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _ (comulCTreeN τ T) := by
  rw [lhsExpand, rhsExpand, doubleCut_eq τ hτ T]

/-- **Coassociativity of `comulCAlgHomN` (Δ^c on Nonplanar)**, under
    trace coherence.

    NOT τ-generic: without `TraceCoherent τ`, iterating Δ^c writes
    second-stage markers computed on marked trunks, and the two cut
    orders disagree (counterexample: `τ` = inl-vertex count on an
    inl-labeled 3-chain). Under coherence the double-cut enumerations
    agree — this is
    [marcolli-chomsky-berwick-2025] Lemma 1.2.10's coassociativity
    (book p. 37–38, the quotient-composition argument "the accessible
    terms of accessible terms … are themselves accessible terms").

    Proved by the double-cut bijection on each tree
    (`comulCN_coassoc_tree`), lifted to forests by multiplicativity
    (both composites are algebra homs, so they agree on a product
    `of' F = ∏ ofTree Tᵢ` once they agree on each `ofTree Tᵢ`). The
    earlier plan to transport `mul_assoc` through a
    GL/Δ^c pairing duality is dead — that duality is false (see the
    Trace coherence section above); the duality route works only for
    Δ^ρ (`Coproduct/PruningDuality.lean`). -/
theorem comulCN_coassoc
    (τ : Nonplanar (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β'))) ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap.rTensor _ ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap =
    (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _ ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap := by
  -- Package both composites as algebra homs (defeq to the LinearMap
  -- composites in the statement) and prove the AlgHom equality.
  let CK := ConnesKreimer R' (Nonplanar (α' ⊕ β'))
  let Δ := comulCAlgHomN (R := R') τ
  let L : CK →ₐ[R'] CK ⊗[R'] (CK ⊗[R'] CK) :=
    (Algebra.TensorProduct.assoc R' R' R' CK CK CK).toAlgHom.comp
      ((Algebra.TensorProduct.map Δ (AlgHom.id R' CK)).comp Δ)
  let Rr : CK →ₐ[R'] CK ⊗[R'] (CK ⊗[R'] CK) :=
    (Algebra.TensorProduct.map (AlgHom.id R' CK) Δ).comp Δ
  suffices hLR : L = Rr by
    -- L.toLinearMap and Rr.toLinearMap are defeq to the two composites.
    exact congrArg AlgHom.toLinearMap hLR
  -- Both AlgHoms agree on every basis forest `of' G`, by induction on
  -- `G` using multiplicativity and the per-tree statement.
  have key : ∀ G : Forest (Nonplanar (α' ⊕ β')),
      L (ConnesKreimer.of' G) = Rr (ConnesKreimer.of' G) := by
    intro G
    induction G using Multiset.induction with
    | empty => rw [ConnesKreimer.of'_zero, map_one, map_one]
    | cons T G ihG =>
      rw [show (T ::ₘ G : Forest (Nonplanar (α' ⊕ β'))) = {T} + G from
            (Multiset.singleton_add T G).symm,
          ConnesKreimer.of'_add, map_mul, map_mul, ihG, ConnesKreimer.of'_singleton]
      congr 1
      -- L (ofTree T) = Rr (ofTree T): the per-tree statement (the AlgHom
      -- applications are defeq to the LinearMap-applied per-tree form).
      show TensorProduct.assoc R' CK CK CK
          ((comulCAlgHomN (R := R') τ).toLinearMap.rTensor _
            (comulCAlgHomN (R := R') τ (ConnesKreimer.ofTree T))) =
        (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _
          (comulCAlgHomN (R := R') τ (ConnesKreimer.ofTree T))
      rw [comulCAlgHomN_apply_ofTree]
      exact comulCN_coassoc_tree τ hτ T
  exact ConnesKreimer.algHom_ext (fun F => key F)

end CoassocCommRing

/-- Sum-of-conditional helper: sum of a multiset map where each entry is
    conditionally zero equals the sum over the filtered subset. -/
private lemma sum_map_ite_zero {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (p : ι → Prop) [DecidablePred p] (g : ι → M) :
    (s.map (fun a => if p a then g a else (0 : M))).sum =
      ((s.filter p).map g).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    by_cases hpa : p a
    · rw [if_pos hpa, Multiset.filter_cons_of_pos _ hpa,
          Multiset.map_cons, Multiset.sum_cons]
    · rw [if_neg hpa, Multiset.filter_cons_of_neg _ hpa, zero_add]

/-! ### Counit laws + Bialgebra instance

The three inputs to `Bialgebra.ofAlgHom`:
1. The AlgHom-form coassoc (`comulCAlgHomN_coassoc_algHom`).
2. The right counit law (`counit_rTensor_comulCAlgHomN`).
3. The left counit law (`counit_lTensor_comulCAlgHomN`).

The per-tree counit laws are derived from the empty-cut uniqueness of
the enumeration (`cutSummandsCN_filter_empty`,
`Core/Combinatorics/RootedTree/Cut.lean`). -/

section BialgebraInst
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- **AlgHom-form coassoc** of `comulCAlgHomN` under trace coherence.
    Follows from `comulCN_coassoc` by AlgHom extensionality. -/
theorem comulCAlgHomN_coassoc_algHom
    (τ : Nonplanar (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    (Algebra.TensorProduct.assoc R' R' R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulCAlgHomN (R := R') τ) (AlgHom.id R' _)).comp
        (comulCAlgHomN (R := R') τ)) =
    (Algebra.TensorProduct.map (AlgHom.id R' _) (comulCAlgHomN (R := R') τ)).comp
      (comulCAlgHomN (R := R') τ) := by
  apply AlgHom.toLinearMap_injective
  -- The .toLinearMap of both AlgHom expressions equals the corresponding
  -- LinearMap composition. `comulCN_coassoc` gives the equality.
  exact comulCN_coassoc τ hτ

/-! ### Counit laws — factored via per-tree + forest helpers

Mirrors the Δ^ρ proof structure in `Coproduct/PruningNonplanar.lean`:
per-tree laws from empty-cut uniqueness, lifted to forests by
multiplicativity. -/

/-- **Per-tree right counit law**: under `(counit ⊗ id)`, only the `(0, T)`
    cut summand of `cutSummandsCN τ T` survives, contributing `1 ⊗ ofTree T`.

    Proof: expand `comulCTreeN τ T = ofTree T ⊗ 1 + Σ (of' p₁ ⊗ ofTree p₂)`.
    Apply `(counit ⊗ id)`: the first summand vanishes via `counit_ofTree`;
    each cut-summand contribution becomes `(if p₁.card = 0 then 1 else 0) ⊗
    ofTree p₂`. Extract the filtered sum via `sum_map_ite_zero`, then use
    `cutSummandsCN_filter_empty` to show the filter yields exactly `{(0, T)}`. -/
private theorem counit_rTensor_comulCTreeN (τ : Nonplanar (α' ⊕ β') → β')
    (T : Nonplanar (α' ⊕ β')) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
      (comulCTreeN τ T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T := by
  -- Expand comulCTreeN τ T.
  unfold comulCTreeN
  rw [map_add]
  -- First summand: (counit ⊗ id)(ofTree T ⊗ 1) = counit(ofTree T) ⊗ 1 = 0 ⊗ 1 = 0.
  rw [show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
            (ConnesKreimer.ofTree T ⊗ₜ[R']
              (1 : ConnesKreimer R' (Nonplanar (α' ⊕ β')))) = 0 from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_ofTree,
        TensorProduct.zero_tmul]]
  rw [zero_add]
  -- Distribute (counit ⊗ id) through the multiset sum.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
          (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))]
  simp only [Multiset.map_map]
  -- Each summand: (counit ⊗ id)(of' p.1 ⊗ ofTree p.2) =
  --   (if p.1.card = 0 then 1 else 0) ⊗ ofTree p.2.
  rw [show ((Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))) ∘
            (fun p : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2)) =
            (fun p => (if p.1.card = 0 then (1 : R') else 0) ⊗ₜ[R']
                       ConnesKreimer.ofTree p.2) from by
    funext p
    show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
            (AlgHom.id R' _))
          (ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_of']]
  -- Pull the if outside the tensor product: (if h then 1 else 0) ⊗ y = if h then 1 ⊗ y else 0.
  rw [show (fun p : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              (if p.1.card = 0 then (1 : R') else 0) ⊗ₜ[R']
                ConnesKreimer.ofTree p.2) =
            (fun p =>
              if p.1.card = 0 then
                ((1 : R') ⊗ₜ[R'] ConnesKreimer.ofTree p.2 :
                  R' ⊗[R'] ConnesKreimer R' (Nonplanar (α' ⊕ β')))
              else 0) from by
    funext p
    by_cases hp : p.1.card = 0
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp, TensorProduct.zero_tmul]]
  -- Extract the filter via sum_map_ite_zero.
  rw [sum_map_ite_zero]
  -- Filter equals {(0, T)} by cutSummandsCN_filter_empty.
  rw [ConnesKreimer.cutSummandsCN_filter_empty τ T,
      Multiset.map_singleton, Multiset.sum_singleton]

/-- **Per-tree left counit law**: mirror of the right counit. Same
    `cutSummandsCN` substrate, with `counit` on the right factor. -/
private theorem counit_lTensor_comulCTreeN (τ : Nonplanar (α' ⊕ β') → β')
    (T : Nonplanar (α' ⊕ β')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
      (comulCTreeN τ T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R') := by
  unfold comulCTreeN
  rw [map_add]
  -- First summand: (id ⊗ counit)(ofTree T ⊗ 1) = ofTree T ⊗ counit(1) = ofTree T ⊗ 1.
  rw [show (Algebra.TensorProduct.map
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
              ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
            (ConnesKreimer.ofTree T ⊗ₜ[R']
              (1 : ConnesKreimer R' (Nonplanar (α' ⊕ β')))) =
          ConnesKreimer.ofTree T ⊗ₜ[R'] (1 : R') from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]]
  -- Second summand: distribute via map_multiset_sum, then show the entire sum is 0.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
          ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))]
  simp only [Multiset.map_map]
  -- Each summand: (id ⊗ counit)(of' p.1 ⊗ ofTree p.2) = of' p.1 ⊗ counit(ofTree p.2)
  --              = of' p.1 ⊗ 0 = 0.
  rw [show ((Algebra.TensorProduct.map
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
              ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')) ∘
            (fun p : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2)) =
            (fun _ => (0 : ConnesKreimer R' (Nonplanar (α' ⊕ β')) ⊗[R'] R')) from by
    funext p
    show (Algebra.TensorProduct.map
            (AlgHom.id R' _) ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
          (ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_ofTree,
        TensorProduct.tmul_zero]]
  -- The sum of all zeros over a multiset is 0.
  rw [show ((cutSummandsCN τ T).map (fun _ : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              (0 : ConnesKreimer R' (Nonplanar (α' ⊕ β')) ⊗[R'] R'))).sum = 0 from by
    induction (cutSummandsCN τ T) using Multiset.induction with
    | empty => simp
    | cons _ _ ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, add_zero]]
  rw [add_zero]

/-- **Forest right counit law**: lift per-tree to forest via `Multiset.induction`
    + multiplicativity of `comulCForestN` and `(counit ⊗ id)` as AlgHom.
    Mirrors `PruningNonplanar.comulForestN_counit_rTensor`. -/
private theorem counit_rTensor_comulCForestN (τ : Nonplanar (α' ⊕ β') → β')
    (F : Forest (Nonplanar (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
        (comulCTreeN τ T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
      (comulCForestN (R := R') τ F) = (1 : R') ⊗ₜ ConnesKreimer.of' F := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (Nonplanar (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') := by
      rw [show (T ::ₘ F' : Forest (Nonplanar (α' ⊕ β'))) = {T} + F' from
            (Multiset.singleton_add T F').symm,
          ConnesKreimer.of'_add, ConnesKreimer.of'_singleton]
    -- comulCForestN (T ::ₘ F') = comulCTreeN τ T * comulCForestN τ F'
    have hCons : comulCForestN (R := R') τ (T ::ₘ F') =
        comulCTreeN (R := R') τ T * comulCForestN (R := R') τ F' := by
      unfold comulCForestN
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [hCons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hForest]

/-- **Forest left counit law**: mirror. -/
private theorem counit_lTensor_comulCForestN (τ : Nonplanar (α' ⊕ β') → β')
    (F : Forest (Nonplanar (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
        (comulCTreeN τ T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
      (comulCForestN (R := R') τ F) = ConnesKreimer.of' F ⊗ₜ (1 : R') := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (Nonplanar (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') := by
      rw [show (T ::ₘ F' : Forest (Nonplanar (α' ⊕ β'))) = {T} + F' from
            (Multiset.singleton_add T F').symm,
          ConnesKreimer.of'_add, ConnesKreimer.of'_singleton]
    have hCons : comulCForestN (R := R') τ (T ::ₘ F') =
        comulCTreeN (R := R') τ T * comulCForestN (R := R') τ F' := by
      unfold comulCForestN
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [hCons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, hForest]

/-- **Right counit law** (CLOSED via per-tree + forest helpers): `(counit ⊗ id) ∘ Δ^c = lid⁻¹`. -/
theorem counit_rTensor_comulCAlgHomN (τ : Nonplanar (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' _)).comp (comulCAlgHomN (R := R') τ) =
      (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
          (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
        (comulCAlgHomN (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [comulCAlgHomN_apply_of', Algebra.TensorProduct.lid_symm_apply]
  exact counit_rTensor_comulCForestN τ F (fun T _ => counit_rTensor_comulCTreeN τ T)

/-- **Left counit law** (CLOSED via per-tree + forest helpers): `(id ⊗ counit) ∘ Δ^c = rid⁻¹`. -/
theorem counit_lTensor_comulCAlgHomN (τ : Nonplanar (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map (AlgHom.id R' _)
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')).comp (comulCAlgHomN (R := R') τ) =
      (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
          ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
        (comulCAlgHomN (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [comulCAlgHomN_apply_of', Algebra.TensorProduct.rid_symm_apply]
  exact counit_lTensor_comulCForestN τ F (fun T _ => counit_lTensor_comulCTreeN τ T)

/-- **`Bialgebra` structure** on `ConnesKreimer R' (Nonplanar (α' ⊕ β'))`
    with Δ^c as the coproduct, for a trace-coherent encoder.

    The graded bialgebra structure of MCB Lemma 1.2.10. Built via
    `Bialgebra.ofAlgHom` with `comulCAlgHomN τ` as the coproduct and the
    inherited `counit` from CK. A `def`, not an `instance`: coassociativity
    needs `TraceCoherent τ` (it is false for arbitrary `τ` — see
    `comulCN_coassoc`), which instance resolution cannot synthesize. -/
@[reducible] noncomputable def bialgebraC
    (τ : Nonplanar (α' ⊕ β') → β')
    (hτ : TraceCoherent τ) :
    Bialgebra R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))) :=
  Bialgebra.ofAlgHom (comulCAlgHomN (R := R') τ) ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
    (comulCAlgHomN_coassoc_algHom τ hτ)
    (counit_rTensor_comulCAlgHomN τ)
    (counit_lTensor_comulCAlgHomN τ)

end BialgebraInst

end ConnesKreimer
