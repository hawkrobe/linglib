/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.BigOperators.Multiset
import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Pairing

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# The pairing product rule for the Grossman-Larson product
[foissy-2002] [oudom-guin-2008]

`pairing_product_of'_mul_of'` — the GL-product/CK-product duality at
the pairing level: `⟨A ⋆ B, C₁ · C₂⟩` decomposes over independent
splits of `A` and `B`. Combines the insertion split law
`Nonplanar.insertionMultiset_antidiagonal`
(`PreLie/InsertionNonplanar.lean`) with the pairing product rule
`pairing_of'_mul` (`GrossmanLarson/Pairing.lean`); substrate for the
GL/CK duality theorem `pairing_gl_eq_pairing_coproduct_Rho`
(`Coproduct/PruningDuality.lean`).

Computationally validated against the planar simulation harness
(`scratch/validate_duality.lean`, V3/V3b batteries, exhaustive over
forests of weight ≤ 3 plus duplicate-tree traps).
-/

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

/-- Boundary conversion: a powerset-with-complement bind equals an
    antidiagonal bind (second slot = chosen sub-multiset). -/
private theorem powerset_bind_eq_antidiagonal_bind {β γ : Type*} [DecidableEq β]
    (B : Multiset β) (m : Multiset β → Multiset β → Multiset γ) :
    B.powerset.bind (fun B₁ => m B₁ (B - B₁)) =
      (Multiset.antidiagonal B).bind (fun pb => m pb.2 pb.1) := by
  rw [Multiset.antidiagonal_eq_map_powerset, Multiset.bind_map]

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

/-! ### The product index multiset -/

/-- Index multiset of GL-product outputs: forests `X + (B' − H)` over
    `H ⊆ B'` and `X ∈ NIM(A', H)`. `product (of' A') (of' B')` is the
    formal sum of `of'` over this multiset (`of'_mul_of'_nim_form`). -/
private noncomputable def productIdx (A' B' : Forest (Nonplanar α)) :
    Multiset (Forest (Nonplanar α)) :=
  B'.powerset.bind (fun H =>
    (Nonplanar.insertionMultiset A' H).map (fun X => X + (B' - H)))

/-- Antidiagonal form of `productIdx`. -/
private theorem productIdx_eq_antidiagonal (A' B' : Forest (Nonplanar α)) :
    productIdx A' B' =
      (Multiset.antidiagonal B').bind (fun u =>
        (Nonplanar.insertionMultiset A' u.2).map (fun X => X + u.1)) := by
  unfold productIdx
  exact powerset_bind_eq_antidiagonal_bind B'
    (fun H Bf => (Nonplanar.insertionMultiset A' H).map (fun X => X + Bf))

/-- `pairing (product (of' A') (of' B')) z` as a `productIdx`-indexed sum. -/
private theorem pairing_product_of'_expand (A' B' : Forest (Nonplanar α))
    (z : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (product (ConnesKreimer.of' A') (ConnesKreimer.of' B')) z =
      ((productIdx A' B').map (fun W =>
        pairing (R := R) (ConnesKreimer.of' W) z)).sum := by
  have hexp : product (ConnesKreimer.of' (R := R) A') (ConnesKreimer.of' B') =
      (((productIdx A' B').map (fun W => ConnesKreimer.of' (R := R) W)).sum :
        ConnesKreimer R (Nonplanar α)) := by
    show ((of' (R := R) A' : GrossmanLarson R α) * of' B' : GrossmanLarson R α) = _
    rw [of'_mul_of'_nim_form]
    show (((B'.powerset.bind fun H =>
        (Nonplanar.insertionMultiset A' H).map fun X =>
          ConnesKreimer.of' (R := R) (X + (B' - H))).sum :
        ConnesKreimer R (Nonplanar α))) = _
    unfold productIdx
    rw [Multiset.map_bind]
    congr 1
    refine Multiset.bind_congr fun H _ => ?_
    rw [Multiset.map_map]
    rfl
  rw [show pairing (R := R) (product (ConnesKreimer.of' A') (ConnesKreimer.of' B')) z =
      (pairing (R := R)).flip z (product (ConnesKreimer.of' A') (ConnesKreimer.of' B'))
    from rfl]
  rw [hexp, map_multiset_sum, Multiset.map_map]
  rfl

/-! ### The index identity -/

/-- **Index identity**: the cut-split index multiset of `A ⋆ B` against a
    two-factor product equals the doubly-split product index. The multiset
    backbone of `pairing_product_of'_mul_of'`. -/
private theorem productIdx_mul_split (A B : Forest (Nonplanar α)) :
    (B.powerset.bind (fun B₁ =>
       (Nonplanar.insertionMultiset A B₁).bind (fun X =>
         Multiset.antidiagonal (X + (B - B₁))))) =
      (Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).bind (fun pq =>
        productIdx pq.1.1 pq.2.1 ×ˢ productIdx pq.1.2 pq.2.2) := by
  -- Step A+B+C+D: inner antidiagonal split + Lemma G, per B₁.
  have stepACD : ∀ B₁ ∈ B.powerset,
      ((Nonplanar.insertionMultiset A B₁).bind (fun X =>
        Multiset.antidiagonal (X + (B - B₁)))) =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal B₁).bind (fun pH =>
          (Multiset.antidiagonal (B - B₁)).bind (fun q =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) := by
    intro B₁ _
    have h1 : ((Nonplanar.insertionMultiset A B₁).bind (fun X =>
          Multiset.antidiagonal (X + (B - B₁)))) =
        ((Nonplanar.insertionMultiset A B₁).bind Multiset.antidiagonal).bind
          (fun p => (Multiset.antidiagonal (B - B₁)).map
            (fun q => (p.1 + q.1, p.2 + q.2))) := by
      rw [Multiset.bind_assoc]
      refine Multiset.bind_congr fun X _ => ?_
      exact Multiset.antidiagonal_add X (B - B₁)
    rw [h1, Nonplanar.insertionMultiset_antidiagonal, Multiset.bind_assoc]
    refine Multiset.bind_congr fun pa _ => ?_
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun pH _ => ?_
    -- (NIMprod).bind (pX ↦ (antidiag Bf).map h) = (antidiag Bf).bind (q ↦ NIMprod.map ...)
    exact Multiset.bind_map_comm _ _
  rw [Multiset.bind_congr stepACD]
  -- Step E: pull the antidiagonal-A bind out front.
  rw [Multiset.bind_bind]
  -- Step F+G+H: per pa, reorganize the B-part into quadBind form and swap.
  have stepB : ∀ pa : Forest (Nonplanar α) × Forest (Nonplanar α),
      (B.powerset.bind (fun B₁ =>
        (Multiset.antidiagonal B₁).bind (fun pH =>
          (Multiset.antidiagonal (B - B₁)).bind (fun q =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2)))))) =
      (Multiset.antidiagonal B).bind (fun pb =>
        productIdx pa.1 pb.1 ×ˢ productIdx pa.2 pb.2) := by
    intro pa
    -- Boundary: powerset + complement → antidiagonal.
    rw [powerset_bind_eq_antidiagonal_bind B (fun B₁ Bf =>
      (Multiset.antidiagonal B₁).bind (fun pH =>
        (Multiset.antidiagonal Bf).bind (fun q =>
          (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
            Nonplanar.insertionMultiset pa.2 pH.2).map
            (fun pX => (pX.1 + q.1, pX.2 + q.2)))))]
    -- Commute the two inner antidiagonal binds to reach quadBind shape.
    have hcomm : ∀ pb : Forest (Nonplanar α) × Forest (Nonplanar α),
        ((Multiset.antidiagonal pb.2).bind (fun pH =>
          (Multiset.antidiagonal pb.1).bind (fun q =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) =
        ((Multiset.antidiagonal pb.1).bind (fun q =>
          (Multiset.antidiagonal pb.2).bind (fun pH =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) := by
      intro pb
      exact Multiset.bind_bind _ _
    rw [Multiset.bind_congr (fun pb _ => hcomm pb)]
    -- Now: quadBind B (fun q₁ q₂ H₁ H₂ => k H₁ H₂ q₁ q₂); middle-swap it.
    rw [show ((Multiset.antidiagonal B).bind (fun pb =>
        (Multiset.antidiagonal pb.1).bind (fun q =>
          (Multiset.antidiagonal pb.2).bind (fun pH =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2)))))) =
      quadBind B (fun a b c d =>
        (Nonplanar.insertionMultiset pa.1 c ×ˢ
          Nonplanar.insertionMultiset pa.2 d).map
          (fun pX => (pX.1 + a, pX.2 + b))) from rfl]
    rw [quadBind_middle_swap]
    -- Unfold back and match against productIdx ×ˢ productIdx.
    show ((Multiset.antidiagonal B).bind (fun pb =>
        (Multiset.antidiagonal pb.1).bind (fun u =>
          (Multiset.antidiagonal pb.2).bind (fun v =>
            (Nonplanar.insertionMultiset pa.1 u.2 ×ˢ
              Nonplanar.insertionMultiset pa.2 v.2).map
              (fun pX => (pX.1 + u.1, pX.2 + v.1)))))) = _
    refine Multiset.bind_congr fun pb _ => ?_
    rw [productIdx_eq_antidiagonal, productIdx_eq_antidiagonal,
        bind_product_left]
    refine Multiset.bind_congr fun u _ => ?_
    rw [product_bind_right]
    refine Multiset.bind_congr fun v _ => ?_
    rw [map_product_map]
    rfl
  rw [Multiset.bind_congr (fun pa _ => stepB pa)]
  -- Outer product-bind unfolding on the RHS.
  rw [product_bind]

/-! ### The fused product rule for the GL product -/

/-- **GL-product/CK-product pairing duality** (basis form): pairing a GL
    product against a CK product decomposes over independent splits of
    the two GL factors:

    `⟨A ⋆ B, C₁ · C₂⟩ =
       Σ_{A = A₁+A₂} Σ_{B = B₁+B₂} ⟨A₁ ⋆ B₁, C₁⟩ · ⟨A₂ ⋆ B₂, C₂⟩`.

    This is the multiplicative-structure compatibility making the GL
    basis dual to the CK polynomial algebra: combines
    `pairing_of'_mul` (pairing product rule, one application per output
    forest of `A ⋆ B`) with `insertionMultiset_antidiagonal` (routing
    splits of grafted outputs) and the powerset/antidiagonal
    bookkeeping for the non-grafted guest components.

    Proof: reduce both sides to sums of the diagonal pairing over the
    index multiset `productIdx`; the multiset backbone is
    `productIdx_mul_split`, whose combinatorial heart is the middle-four
    interchange `quadBind_middle_swap`. -/
theorem pairing_product_of'_mul_of' (A B C₁ C₂ : Forest (Nonplanar α)) :
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
  set φ : Forest (Nonplanar α) × Forest (Nonplanar α) → R :=
    fun p => pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
      pairing (R := R) (ConnesKreimer.of' p.2) (ConnesKreimer.of' C₂) with hφ
  -- LHS = sum of φ over the cut-split index multiset.
  have hLHS : pairing (R := R)
        (product (ConnesKreimer.of' A) (ConnesKreimer.of' B))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      (((B.powerset.bind (fun B₁ =>
        (Nonplanar.insertionMultiset A B₁).bind (fun X =>
          Multiset.antidiagonal (X + (B - B₁)))))).map φ).sum := by
    rw [pairing_product_of'_expand]
    unfold productIdx
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.sum_bind, Multiset.sum_bind]
    congr 1
    refine Multiset.map_congr rfl fun B₁ _ => ?_
    rw [Multiset.map_map, Multiset.map_bind, Multiset.sum_bind]
    congr 1
    refine Multiset.map_congr rfl fun X _ => ?_
    show pairing (R := R) (ConnesKreimer.of' (X + (B - B₁)))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) = _
    rw [pairing_of'_mul]
  rw [hLHS, productIdx_mul_split, Multiset.map_bind, Multiset.sum_bind]
  congr 1
  refine Multiset.map_congr rfl fun pq _ => ?_
  show ((productIdx pq.1.1 pq.2.1 ×ˢ productIdx pq.1.2 pq.2.2).map φ).sum = _
  rw [hφ]
  rw [Multiset.sum_map_product_mul (productIdx pq.1.1 pq.2.1) (productIdx pq.1.2 pq.2.2)
      (fun W => pairing (R := R) (ConnesKreimer.of' W) (ConnesKreimer.of' C₁))
      (fun W => pairing (R := R) (ConnesKreimer.of' W) (ConnesKreimer.of' C₂))]
  rw [← pairing_product_of'_expand, ← pairing_product_of'_expand]

end GrossmanLarson
