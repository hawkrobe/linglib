/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Multiset
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Pairing

/-!
# The pairing product rule for the Grossman–Larson product

This file proves that pairing a Grossman–Larson product `A ⋆ B` against a Connes–Kreimer product
`C₁ · C₂` decomposes over independent splits of `A` and `B`. The proof combines the splitting of
grafted forests, `UnorderedTree.insertionMultiset_antidiagonal`, with the pairing product rule
`pairing_of'_mul`; the result feeds the duality between the Grossman–Larson product and the
pruning coproduct in `Coproduct/PruningDuality.lean`.

## Main results

* `GrossmanLarson.pairing_product_of'_mul_of'`:
  `⟨A ⋆ B, C₁ · C₂⟩ = Σ_{A = A₁ + A₂} Σ_{B = B₁ + B₂} ⟨A₁ ⋆ B₁, C₁⟩ ⟨A₂ ⋆ B₂, C₂⟩`.

## References

* [foissy-2002]
* [oudom-guin-2008]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### Generic sum/product plumbing -/

/-- `(s ×ˢ t).bind F = s.bind (a ↦ t.bind (b ↦ F (a, b)))`. -/
private theorem product_bind {β γ δ : Type*} (s : Multiset β) (t : Multiset γ)
    (F : β × γ → Multiset δ) :
    (s ×ˢ t).bind F = s.bind (fun a => t.bind (fun b => F (a, b))) := by
  show (s.bind (fun a => t.map (Prod.mk a))).bind F = _
  rw [Multiset.bind_assoc]
  exact Multiset.bind_congr fun a _ => Multiset.bind_map t F (Prod.mk a)

/-- `(s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t)`. -/
private theorem bind_product_left {β γ δ : Type*} (s : Multiset β)
    (f : β → Multiset γ) (t : Multiset δ) :
    (s.bind f) ×ˢ t = s.bind (fun a => f a ×ˢ t) := by
  show (s.bind f).bind (fun a => t.map (Prod.mk a)) = _
  rw [Multiset.bind_assoc]
  rfl

/-- `s ×ˢ (t.bind g) = t.bind (b ↦ s ×ˢ g b)`. -/
private theorem product_bind_right {β γ δ : Type*} (s : Multiset β)
    (t : Multiset γ) (g : γ → Multiset δ) :
    s ×ˢ (t.bind g) = t.bind (fun b => s ×ˢ g b) := by
  show s.bind (fun a => (t.bind g).map (Prod.mk a)) = _
  rw [show (fun a => (t.bind g).map (Prod.mk a)) =
      fun a => t.bind (fun b => (g b).map (Prod.mk a)) from
    funext fun a => Multiset.map_bind t g (Prod.mk a)]
  rw [Multiset.bind_bind]
  rfl

/-- `(s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g)`. -/
private theorem map_product_map {β γ β' γ' : Type*} (s : Multiset β) (t : Multiset γ)
    (f : β → β') (g : γ → γ') :
    (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g) := by
  show (s.map f).bind (fun a => (t.map g).map (Prod.mk a)) = _
  rw [Multiset.bind_map]
  show (s.bind fun a => (t.map g).map (Prod.mk (f a))) = _
  rw [show (fun a => (t.map g).map (Prod.mk (f a))) =
      fun a => t.map (fun b => (f a, g b)) from
    funext fun a => by rw [Multiset.map_map]; rfl]
  show _ = ((s.bind fun a => t.map (Prod.mk a)).map (Prod.map f g))
  rw [Multiset.map_bind]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map]
  rfl

/-! ### quadBind (from dev_quad.lean) -/

private def quadBind {β γ : Type*} (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    Multiset γ :=
  (Multiset.antidiagonal B).bind (fun p =>
    (Multiset.antidiagonal p.1).bind (fun u =>
      (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))

private theorem quadBind_zero {β γ : Type*}
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind 0 g = g 0 0 0 0 := by
  simp only [quadBind, Multiset.antidiagonal_zero, Multiset.singleton_bind]

private theorem quadBind_cons {β γ : Type*} (x : β) (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind (x ::ₘ B) g =
      quadBind B (fun a b c d => g (x ::ₘ a) b c d) +
      quadBind B (fun a b c d => g a (x ::ₘ b) c d) +
      quadBind B (fun a b c d => g a b (x ::ₘ c) d) +
      quadBind B (fun a b c d => g a b c (x ::ₘ d)) := by
  have h2 : (((Multiset.antidiagonal B).map (Prod.map id (x ::ₘ ·))).bind
        (fun p => (Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) =
      quadBind B (fun a b c d => g a b c (x ::ₘ d)) +
      quadBind B (fun a b c d => g a b (x ::ₘ c) d) := by
    rw [Multiset.bind_map]
    have step : ∀ p ∈ Multiset.antidiagonal B,
        ((Multiset.antidiagonal (Prod.map id (x ::ₘ ·) p).1).bind (fun u =>
          (Multiset.antidiagonal (Prod.map id (x ::ₘ ·) p).2).bind (fun v =>
            g u.1 u.2 v.1 v.2))) =
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 (x ::ₘ v.2)))) +
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 (x ::ₘ v.1) v.2))) := by
      intro p _
      have inner : ∀ u : Multiset β × Multiset β,
          ((Multiset.antidiagonal (x ::ₘ p.2)).bind (fun v => g u.1 u.2 v.1 v.2)) =
          ((Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 (x ::ₘ v.2))) +
          ((Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 (x ::ₘ v.1) v.2)) := by
        intro u
        rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
            Multiset.bind_map]
        rfl
      show ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal (x ::ₘ p.2)).bind (fun v => g u.1 u.2 v.1 v.2))) = _
      rw [Multiset.bind_congr (fun u _ => inner u), Multiset.bind_add]
    rw [Multiset.bind_congr step, Multiset.bind_add]
    rfl
  have h1 : (((Multiset.antidiagonal B).map (Prod.map (x ::ₘ ·) id)).bind
        (fun p => (Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) =
      quadBind B (fun a b c d => g a (x ::ₘ b) c d) +
      quadBind B (fun a b c d => g (x ::ₘ a) b c d) := by
    rw [Multiset.bind_map]
    have step : ∀ p ∈ Multiset.antidiagonal B,
        ((Multiset.antidiagonal (Prod.map (x ::ₘ ·) id p).1).bind (fun u =>
          (Multiset.antidiagonal (Prod.map (x ::ₘ ·) id p).2).bind (fun v =>
            g u.1 u.2 v.1 v.2))) =
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 (x ::ₘ u.2) v.1 v.2))) +
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g (x ::ₘ u.1) u.2 v.1 v.2))) := by
      intro p _
      show ((Multiset.antidiagonal (x ::ₘ p.1)).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2))) = _
      rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
          Multiset.bind_map]
      rfl
    rw [Multiset.bind_congr step, Multiset.bind_add]
    rfl
  show ((Multiset.antidiagonal (x ::ₘ B)).bind (fun p =>
      (Multiset.antidiagonal p.1).bind (fun u =>
        (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) = _
  rw [Multiset.antidiagonal_cons, Multiset.add_bind, h2, h1]
  abel

private theorem quadBind_middle_swap {β γ : Type*} (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind B g = quadBind B (fun a b c d => g a c b d) := by
  induction B using Multiset.induction_on generalizing g with
  | empty => rw [quadBind_zero, quadBind_zero]
  | cons x B ih =>
    rw [quadBind_cons, quadBind_cons]
    rw [← ih (fun a b c d => g (x ::ₘ a) b c d),
        ← ih (fun a b c d => g a b (x ::ₘ c) d),
        ← ih (fun a b c d => g a (x ::ₘ b) c d),
        ← ih (fun a b c d => g a b c (x ::ₘ d))]
    abel

/-! ### The index identity -/

/-- Pairing a Grossman–Larson product of basis forests is a sum over `productMultiset`. -/
private theorem pairing_product_of'_of' (A B : Forest (UnorderedTree α))
    (z : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) (product (ConnesKreimer.of' A) (ConnesKreimer.of' B)) z =
      ((productMultiset A B).map fun W ↦ pairing (R := R) (ConnesKreimer.of' W) z).sum := by
  change pairing.flip z _ = _
  rw [product_of'_of', map_multiset_sum, Multiset.map_map]
  rfl

omit [DecidableEq α] in
/-- **Index identity**: splitting the forests of `A ⋆ B` is splitting `A` and `B` and multiplying
the parts. The multiset backbone of `pairing_product_of'_mul_of'`. -/
private theorem productMultiset_bind_antidiagonal (A B : Forest (UnorderedTree α)) :
    (productMultiset A B).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).bind (fun pq =>
        productMultiset pq.1.1 pq.2.1 ×ˢ productMultiset pq.1.2 pq.2.2) := by
  -- Split each output forest `X + p.1` as a split of `X` plus a split of `p.1`.
  have stepACD : ∀ p ∈ Multiset.antidiagonal B,
      ((UnorderedTree.insertionMultiset A p.2).map (· + p.1)).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal p.2).bind (fun pH =>
          (Multiset.antidiagonal p.1).bind (fun q =>
            (UnorderedTree.insertionMultiset pa.1 pH.1 ×ˢ
              UnorderedTree.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) := by
    intro p _
    have h1 : ((UnorderedTree.insertionMultiset A p.2).map (· + p.1)).bind
          Multiset.antidiagonal =
        ((UnorderedTree.insertionMultiset A p.2).bind Multiset.antidiagonal).bind
          (fun r => (Multiset.antidiagonal p.1).map
            (fun q => (r.1 + q.1, r.2 + q.2))) := by
      rw [Multiset.bind_map, Multiset.bind_assoc]
      exact Multiset.bind_congr fun X _ => Multiset.antidiagonal_add X p.1
    rw [h1, UnorderedTree.insertionMultiset_antidiagonal, Multiset.bind_assoc]
    refine Multiset.bind_congr fun pa _ => ?_
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun pH _ => ?_
    exact Multiset.bind_map_comm _ _
  rw [productMultiset, Multiset.bind_assoc, Multiset.bind_congr stepACD, Multiset.bind_bind,
    product_bind]
  refine Multiset.bind_congr fun pa _ => ?_
  -- Commute the two inner antidiagonal binds to reach `quadBind` shape.
  rw [Multiset.bind_congr fun pb _ => Multiset.bind_bind _ _]
  rw [show ((Multiset.antidiagonal B).bind (fun pb =>
      (Multiset.antidiagonal pb.1).bind (fun q =>
        (Multiset.antidiagonal pb.2).bind (fun pH =>
          (UnorderedTree.insertionMultiset pa.1 pH.1 ×ˢ
            UnorderedTree.insertionMultiset pa.2 pH.2).map
            (fun pX => (pX.1 + q.1, pX.2 + q.2)))))) =
    quadBind B (fun a b c d =>
      (UnorderedTree.insertionMultiset pa.1 c ×ˢ
        UnorderedTree.insertionMultiset pa.2 d).map
        (fun pX => (pX.1 + a, pX.2 + b))) from rfl]
  rw [quadBind_middle_swap]
  refine Multiset.bind_congr fun pb _ => ?_
  rw [productMultiset, productMultiset, bind_product_left]
  refine Multiset.bind_congr fun u _ => ?_
  rw [product_bind_right]
  refine Multiset.bind_congr fun v _ => ?_
  rw [map_product_map]
  rfl

/-! ### The fused product rule for the GL product -/

/-- **GL-product/CK-product pairing duality** (basis form): pairing a GL
    product against a CK product decomposes over independent splits of
    the two GL factors:

    `⟨A ⋆ B, C₁ · C₂⟩ =
       Σ_{A = A₁+A₂} Σ_{B = B₁+B₂} ⟨A₁ ⋆ B₁, C₁⟩ · ⟨A₂ ⋆ B₂, C₂⟩`.

    This is the multiplicative-structure compatibility making the GL
    basis dual to the CK polynomial algebra: combines
    `pairing_of'_mul` (pairing product rule, one application per output
    forest of `A ⋆ B`) with the index identity
    `productMultiset_bind_antidiagonal`, whose combinatorial heart is the
    middle-four interchange `quadBind_middle_swap`. -/
theorem pairing_product_of'_mul_of' (A B C₁ C₂ : Forest (UnorderedTree α)) :
    pairing (R := R)
        (product (ConnesKreimer.of' A) (ConnesKreimer.of' B))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
        pairing (R := R)
            (product (ConnesKreimer.of' pq.1.1) (ConnesKreimer.of' pq.2.1))
            (ConnesKreimer.of' C₁) *
        pairing (R := R)
            (product (ConnesKreimer.of' pq.1.2) (ConnesKreimer.of' pq.2.2))
            (ConnesKreimer.of' C₂))).sum := by
  -- φ evaluates a split pair against (C₁, C₂).
  set φ : Forest (UnorderedTree α) × Forest (UnorderedTree α) → R :=
    fun p => pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
      pairing (R := R) (ConnesKreimer.of' p.2) (ConnesKreimer.of' C₂) with hφ
  -- LHS = sum of φ over the splits of the output forests.
  have hLHS : pairing (R := R)
        (product (ConnesKreimer.of' A) (ConnesKreimer.of' B))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      (((productMultiset A B).bind Multiset.antidiagonal).map φ).sum := by
    rw [pairing_product_of'_of', Multiset.map_bind, Multiset.sum_bind]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun W _ => pairing_of'_mul W _ _)
  rw [hLHS, productMultiset_bind_antidiagonal, Multiset.map_bind, Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ => ?_)
  rw [hφ, Multiset.sum_map_product_mul (productMultiset pq.1.1 pq.2.1)
      (productMultiset pq.1.2 pq.2.2)
      (fun W => pairing (R := R) (ConnesKreimer.of' W) (ConnesKreimer.of' C₁))
      (fun W => pairing (R := R) (ConnesKreimer.of' W) (ConnesKreimer.of' C₂)),
    ← pairing_product_of'_of', ← pairing_product_of'_of']

end GrossmanLarson
