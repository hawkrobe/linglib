/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Linglib.Core.Data.List.Factors
import Linglib.Phonology.Autosegmental.AR

/-!
# Normal forms of autosegmental representations

Every finite representation is isomorphic to its **normal form**: the same
representation reindexed onto the canonical vertex type `(i : ι) × Fin nᵢ`,
each tier fiber enumerated in ascending precedence order
(`IsTierOrdered.isStrictTotalOrder` → `linearOrderOfSTO` → `monoEquivOfFin`).
The normal form is a `AR` — not a separate carrier — and
`normalizeIso` is definitional: `normalize` pulls the graph back along the
enumeration equivalence.

Strictness lives on isomorphism classes of the precedence-preserving wide
subcategory (`PrecAR`): full-structure classes, since broad
categorical isomorphism forgets the arcs and is too coarse to preserve tier
words. `cls_normalize` says `normalize` chooses representatives.

## Main definitions

* `AR.fiber`, `AR.fiberEnum`, `AR.vertexEquiv`:
  the tier fibers of a finite representation and their canonical enumerations.
* `AR.tierLength`, `AR.tierWord`, `AR.linkRel`:
  the tuple reading — per-tier sizes, label words, and position-coordinate links.
* `AR.normalize`: the normal form, a `AR` on the
  canonical vertex type.
* `realize`, `realizeHom`, `tierProj`: [jardine-2019]'s `g` as iterated tensor,
  as a free-monoid hom into the class monoid, and its per-tier projections.

## Main results

* `AR.normalizeIso`: `X.normalize ≅ X`.
* `AR.arcs_normalize`, `AR.edges_normalize`: on normal
  forms the arcs are the ascending position order and the edges are `linkRel` —
  [jardine-heinz-2015]'s tiered presentation recovered as a theorem.
* `AR.tierWord_tensor`, `AR.tierWord_realize`:
  concatenation appends tier words; tier content of a realization is
  compositional.
* `PrecAR`, `AR.cls_normalize`: the monoid of
  isomorphism classes of the precedence-preserving category; normal forms
  represent their class.
-/

namespace Autosegmental

open CategoryTheory

variable {ι : Type*} {τ : ι → Type*}

/-! ### The monoid of representations up to isomorphism

Isomorphism classes in the **precedence-preserving** wide subcategory — the
theory's identity criterion. The broad categorical `≅` forgets arcs and is too
coarse (it identifies tier orders); wide-subcategory isos are exactly the
full-structure isomorphisms, so the tuple readers descend to classes. The
monoid structure is stock: `precPreserving` is monoidally stable, so
`WideSubcategory` inherits the monoidal category and `Monoidal.Skeleton` the
strictly associative monoid. -/

section IsoClasses
open scoped MonoidalCategory

/-- Representations with the classical precedence-preserving morphisms. -/
abbrev PrecAR (ι : Type*) (τ : ι → Type*) :=
  WideSubcategory (AR.precPreserving (t := (Sigma.fst : ((i : ι) × τ i) → ι)))

/-- A full isomorphism is an isomorphism of the precedence-preserving
    category: both directions preserve arcs. -/
noncomputable def AR.fullIsoToWideIso
    {A B : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    (e : Graph.Iso A.obj B.obj) :
    (⟨A⟩ : PrecAR ι τ) ≅ ⟨B⟩ where
  hom := ⟨InducedCategory.homMk e.toHom, e.toHom_precPreserving⟩
  inv := ⟨InducedCategory.homMk e.symm.toHom, e.symm.toHom_precPreserving⟩
  hom_inv_id := InducedWideCategory.Hom.ext (InducedCategory.hom_ext
    (Graph.Hom.ext (funext fun v => e.toEquiv.symm_apply_apply v)))
  inv_hom_id := InducedWideCategory.Hom.ext (InducedCategory.hom_ext
    (Graph.Hom.ext (funext fun v => e.toEquiv.apply_symm_apply v)))

/-- The class of a representation: its isomorphism class in the skeleton of the
    precedence-preserving category — the monoid of ARs. -/
noncomputable def AR.cls
    (A : AR (Sigma.fst : ((i : ι) × τ i) → ι)) :
    Skeleton (PrecAR ι τ) :=
  toSkeleton ⟨A⟩

/-- Concatenation of classes is the class of the tensor. -/
theorem AR.cls_tensor
    (A B : AR (Sigma.fst : ((i : ι) × τ i) → ι)) :
    AR.cls (A ⊗ B) = AR.cls A * AR.cls B :=
  CategoryTheory.Skeleton.toSkeleton_tensorObj (⟨A⟩ : PrecAR ι τ) ⟨B⟩

end IsoClasses

section NormalForm
open scoped Classical

/-- Fiber of the tier coloring at `i`: vertices of `X.obj` labelled to tier `i`.
    Under `IsTierOrdered` its arcs form a strict total order, and under
    `Finite X.obj.V` it is finite — the two ingredients `monoEquivOfFin`
    needs to enumerate the fiber as `Fin _`. -/
def AR.fiber (X : AR (Sigma.fst : ((i : ι) × τ i) → ι)) (i : ι) :
    Type _ := {v : X.obj.V // (X.obj.label v).1 = i}

variable {X : AR (Sigma.fst : ((i : ι) × τ i) → ι)}

/-- The `τ i` component of a fiber element, extracted from the labeling by
    transporting along the fiber's tier-membership witness. -/
def AR.fiberLabel {i : ι} (v : X.fiber i) : τ i :=
  v.property ▸ (X.obj.label v.val).2

/-- The label of a fiber element decomposes as tier plus `fiberLabel`. -/
theorem AR.label_fiber {i : ι} (v : X.fiber i) :
    X.obj.label v.val = ⟨i, X.fiberLabel v⟩ := by
  obtain ⟨u, hu⟩ := v
  show X.obj.label u = _
  simp only [AR.fiberLabel]
  conv_lhs => rw [← Sigma.eta (X.obj.label u)]
  exact Sigma.eq hu rfl

instance AR.fiber.instFinite [Finite X.obj.V] (i : ι) : Finite (X.fiber i) :=
  Subtype.finite

/-- The arcs restricted to a tier fiber form a strict total order — the classed
    form of Axioms 1–2 applied to the tier coloring `Sigma.fst`. -/
instance AR.fiber.instIsStrictTotalOrder (i : ι) :
    IsStrictTotalOrder (X.fiber i) (fun a b => X.obj.arcs.Adj a.val b.val) :=
  X.property.1.isStrictTotalOrder i

/-- Classical linear order on the fiber, from `IsStrictTotalOrder` via
    `linearOrderOfSTO`. -/
noncomputable instance AR.fiber.instLinearOrder (i : ι) :
    LinearOrder (X.fiber i) := by
  classical
  exact linearOrderOfSTO (fun a b : X.fiber i => X.obj.arcs.Adj a.val b.val)

/-- The number of tier-`i` vertices. -/
noncomputable def AR.tierLength (X : AR (Sigma.fst : ((i : ι) × τ i) → ι))
    [Finite X.obj.V] (i : ι) : ℕ :=
  letI := Fintype.ofFinite (X.fiber i)
  Fintype.card (X.fiber i)

/-- The canonical ascending enumeration of a tier fiber. -/
noncomputable def AR.fiberEnum [Finite X.obj.V] (i : ι) :
    Fin (X.tierLength i) ≃o X.fiber i :=
  letI := Fintype.ofFinite (X.fiber i)
  monoEquivOfFin (X.fiber i) rfl

/-- The canonical enumeration of a finite representation's vertex type: tier
    fibers in ascending precedence order, assembled over the tier index. -/
noncomputable def AR.vertexEquiv [Finite X.obj.V] :
    ((i : ι) × Fin (X.tierLength i)) ≃ X.obj.V :=
  letI : ∀ i : ι, Fintype (X.fiber i) := fun _ => Fintype.ofFinite _
  (Equiv.sigmaCongrRight (fun i : ι => (X.fiberEnum i).toEquiv)).trans
    (Equiv.sigmaFiberEquiv (fun v : X.obj.V => (X.obj.label v).1))

/-- The tier-`i` label word: the fiber's labels read off in ascending precedence
    order — the tier content the normal form canonicalizes. -/
noncomputable def AR.tierWord [Finite X.obj.V] (i : ι) : List (τ i) :=
  letI := Fintype.ofFinite (X.fiber i)
  List.ofFn fun p : Fin (X.tierLength i) => X.fiberLabel (X.fiberEnum i p)

@[simp] theorem AR.length_tierWord [Finite X.obj.V] (i : ι) :
    (X.tierWord i).length = X.tierLength i := by
  simp [AR.tierWord]

/-- The link relation in position coordinates: tier-`i` position `p` associates
    to tier-`j` position `q`. With `tierWord`, the complete tuple reading of a
    finite representation. -/
noncomputable def AR.linkRel [Finite X.obj.V] (i j : ι)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) : Prop :=
  X.obj.edges.Adj (X.vertexEquiv ⟨i, p⟩) (X.vertexEquiv ⟨j, q⟩)

theorem AR.linkRel_def [Finite X.obj.V] {i j : ι} {p : Fin (X.tierLength i)}
    {q : Fin (X.tierLength j)} :
    X.linkRel i j p q ↔
      X.obj.edges.Adj (X.vertexEquiv ⟨i, p⟩) (X.vertexEquiv ⟨j, q⟩) := Iff.rfl

/-- The normal form: `X` reindexed onto the canonical vertex type by pulling
    edges, arcs, and labels back along `vertexEquiv`. A `AR` — the
    normal form is not a separate kind of object. -/
noncomputable def AR.normalize
    (X : AR (Sigma.fst : ((i : ι) × τ i) → ι)) [Finite X.obj.V] :
    AR (Sigma.fst : ((i : ι) × τ i) → ι) where
  obj :=
    { V := (i : ι) × Fin (X.tierLength i)
      edges := X.obj.edges.comap X.vertexEquiv
      arcs := ⟨fun v w => X.obj.arcs.Adj (X.vertexEquiv v) (X.vertexEquiv w)⟩
      label := fun v => X.obj.label (X.vertexEquiv v) }
  property :=
    ⟨⟨fun _ _ h => X.property.1.tier_eq h,
      fun _ _ hne htier => X.property.1.total (fun hv => hne (X.vertexEquiv.injective hv)) htier,
      fun _ h => X.property.1.irrefl _ h,
      fun _ _ _ huv hvw => X.property.1.trans huv hvw⟩,
     fun _ _ hadj harc => X.property.2 hadj harc⟩

/-- The normal form is fully isomorphic to the original — definitionally,
    since `normalize` is a pullback along `vertexEquiv`. -/
noncomputable def AR.normalizeFullIso [Finite X.obj.V] :
    Graph.Iso (X.normalize).obj X.obj where
  toEquiv := X.vertexEquiv
  edges_iff _ _ := Iff.rfl
  arcs_iff _ _ := Iff.rfl
  label_comp _ := rfl

/-- The normal form is isomorphic to the original. -/
noncomputable def AR.normalizeIso [Finite X.obj.V] : X.normalize ≅ X :=
  AR.mkIso X.normalizeFullIso

/-- On normal forms the edges are exactly `linkRel` — with `arcs_normalize`,
    the complete tuple reading of the normal form. -/
theorem AR.edges_normalize [Finite X.obj.V] (i j : ι)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) :
    (X.normalize).obj.edges.Adj ⟨i, p⟩ ⟨j, q⟩ ↔ X.linkRel i j p q := Iff.rfl

/-- On normal forms the arcs are the ascending position order — the
    classification content: [jardine-heinz-2015]'s tiered presentation
    recovered as a theorem. -/
theorem AR.arcs_normalize [Finite X.obj.V] (i : ι)
    (p q : Fin (X.tierLength i)) :
    (X.normalize).obj.arcs.Adj ⟨i, p⟩ ⟨i, q⟩ ↔ p < q :=
  (X.fiberEnum i).lt_iff_lt

/-- Normal forms represent their isomorphism class: `normalize` is a section
    of the quotient onto `AR.IsoClass`. -/
theorem AR.cls_normalize [Finite X.obj.V] :
    AR.cls (X.normalize) = AR.cls X :=
  Quotient.sound ⟨AR.fullIsoToWideIso X.normalizeFullIso⟩

end NormalForm

/-! ### Realization of strings

[jardine-2019]'s mapping `g`: each symbol denotes a representation primitive, a
string denotes their concatenation. The monoid-homomorphism content lives on the
skeleton, where concatenation is strictly associative. -/

section Realize
open scoped MonoidalCategory

variable {S : Type*} {ι : Type*} {τ : ι → Type*}

/-- Realize a string as a representation: the iterated tensor of its symbols'
    primitives ([jardine-2019]'s `g`). -/
noncomputable def realize (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι))
    (w : List S) : AR (Sigma.fst : ((i : ι) × τ i) → ι) :=
  (w.map g₀).foldr (· ⊗ ·) (𝟙_ _)

@[simp] theorem realize_nil (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι)) :
    realize g₀ [] = 𝟙_ _ := rfl

@[simp] theorem realize_cons (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι))
    (a : S) (w : List S) : realize g₀ (a :: w) = g₀ a ⊗ realize g₀ w := rfl

/-- The realization as a free-monoid homomorphism into the monoid of
    isomorphism classes — the string→AR monoid hom, with associativity strict
    on classes. -/
noncomputable def realizeHom
    (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι)) :
    FreeMonoid S →* Skeleton (PrecAR ι τ) :=
  FreeMonoid.lift (AR.cls ∘ g₀)

end Realize

/-! ### Tier words of tensors

Concatenation appends tier content: within a tier, the bridge arc puts every
left-factor vertex before every right-factor vertex, so the tensor's fiber is
the lexicographic sum of the factors' fibers and its ascending enumeration is
the two enumerations in sequence (`Subsingleton (Fin n ≃o ·)` — monotone
enumerations are unique). -/

section TierWordTensor
open scoped MonoidalCategory

variable {ι : Type*} {τ : ι → Type*}
variable {X Y : AR (Sigma.fst : ((i : ι) × τ i) → ι)}

instance [Finite X.obj.V] [Finite Y.obj.V] : Finite ((X ⊗ Y).obj.V) :=
  inferInstanceAs (Finite (X.obj.V ⊕ Y.obj.V))

/-- A tensor's tier fiber splits as the sum of the factors' fibers. -/
def AR.fiberTensorEquiv (i : ι) :
    (X ⊗ Y).fiber i ≃ X.fiber i ⊕ Y.fiber i where
  toFun v := match v with
    | ⟨.inl w, h⟩ => .inl ⟨w, h⟩
    | ⟨.inr w, h⟩ => .inr ⟨w, h⟩
  invFun := Sum.elim (fun w => ⟨.inl w.val, w.property⟩) (fun w => ⟨.inr w.val, w.property⟩)
  left_inv := by rintro ⟨w | w, h⟩ <;> rfl
  right_inv := by rintro (w | w) <;> rfl

variable [Finite X.obj.V] [Finite Y.obj.V]

attribute [local instance] Fintype.ofFinite

@[simp] theorem AR.tierLength_tensor (i : ι) :
    (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i := by
  letI := Fintype.ofFinite ((X ⊗ Y).fiber i)
  letI := Fintype.ofFinite (X.fiber i)
  letI := Fintype.ofFinite (Y.fiber i)
  simp only [AR.tierLength]
  rw [Fintype.card_congr (AR.fiberTensorEquiv i), Fintype.card_sum]

open AR in
/-- The blockwise enumeration of a tensor's fiber: left factor first, then
    right — monotone because the bridge arc orders the blocks. -/
noncomputable def AR.tensorEnum (i : ι) :
    Fin (X.tierLength i + Y.tierLength i) ≃o (X ⊗ Y).fiber i := by
  letI := Fintype.ofFinite (X.fiber i)
  letI := Fintype.ofFinite (Y.fiber i)
  refine StrictMono.orderIsoOfSurjective
    (finSumFinEquiv.symm.trans
      (((X.fiberEnum i).toEquiv.sumCongr
        (Y.fiberEnum i).toEquiv).trans
        (fiberTensorEquiv i).symm))
    ?_ (Equiv.surjective _)
  intro p q hpq
  simp only [Equiv.trans_apply]
  induction p using Fin.addCases with
  | left p₁ =>
    rw [finSumFinEquiv_symm_apply_castAdd]
    induction q using Fin.addCases with
    | left q₁ =>
      rw [finSumFinEquiv_symm_apply_castAdd]
      exact (X.fiberEnum i).strictMono
        (by simp only [Fin.lt_def, Fin.val_castAdd] at hpq ⊢; exact hpq)
    | right q₂ =>
      rw [finSumFinEquiv_symm_apply_natAdd]
      exact (X.fiberEnum i p₁).property.trans
        ((Y.fiberEnum i q₂).property).symm
  | right p₂ =>
    induction q using Fin.addCases with
    | left q₁ =>
      exact absurd hpq (by simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]; omega)
    | right q₂ =>
      rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
      exact (Y.fiberEnum i).strictMono
        (by simp only [Fin.lt_def, Fin.val_natAdd] at hpq ⊢; omega)

theorem AR.tensorEnum_apply_castAdd (i : ι) (p : Fin (X.tierLength i)) :
    AR.tensorEnum i (Fin.castAdd (Y.tierLength i) p) =
      (AR.fiberTensorEquiv i).symm
        (.inl (X.fiberEnum i p)) := by
  simp [AR.tensorEnum, finSumFinEquiv_symm_apply_castAdd]

theorem AR.tensorEnum_apply_natAdd (i : ι) (p : Fin (Y.tierLength i)) :
    AR.tensorEnum i (Fin.natAdd (X.tierLength i) p) =
      (AR.fiberTensorEquiv (X := X) i).symm
        (.inr (Y.fiberEnum i p)) := by
  simp [AR.tensorEnum, finSumFinEquiv_symm_apply_natAdd]

omit [Finite X.obj.V] [Finite Y.obj.V] in
theorem AR.fiberLabel_symm_inl {i : ι} (w : X.fiber i) :
    AR.fiberLabel ((AR.fiberTensorEquiv (X := X) (Y := Y) i).symm
      (.inl w)) = X.fiberLabel w := rfl

omit [Finite X.obj.V] [Finite Y.obj.V] in
theorem AR.fiberLabel_symm_inr {i : ι} (w : Y.fiber i) :
    AR.fiberLabel ((AR.fiberTensorEquiv (X := X) (Y := Y) i).symm
      (.inr w)) = Y.fiberLabel w := rfl

/-- Any monotone enumeration computes the tier word. -/
theorem AR.tierWord_eq_ofFn {Z : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite Z.obj.V] {i : ι} {n : ℕ} (e : Fin n ≃o Z.fiber i) :
    Z.tierWord i = List.ofFn fun p => Z.fiberLabel (e p) := by
  have hn : Z.tierLength i = n := by
    simpa [AR.tierLength] using (Fintype.card_congr e.toEquiv).symm
  subst hn
  rw [Subsingleton.elim e (Z.fiberEnum i)]
  rfl

/-- **Concatenation appends tier content**: the tier word of a tensor is the
    factors' tier words in sequence — the tuple presentation of
    [jardine-heinz-2015]'s Definition 2, recovered as a theorem about normal
    forms. -/
@[simp] theorem AR.tierWord_tensor (i : ι) :
    (X ⊗ Y).tierWord i = X.tierWord i ++ Y.tierWord i := by
  rw [AR.tierWord_eq_ofFn (AR.tensorEnum i), List.ofFn_add]
  congr 1
  · rw [AR.tierWord_eq_ofFn (X.fiberEnum i)]
    exact congrArg List.ofFn (funext fun p =>
      (congrArg AR.fiberLabel (AR.tensorEnum_apply_castAdd i p)).trans
        (AR.fiberLabel_symm_inl _))
  · rw [AR.tierWord_eq_ofFn (Y.fiberEnum i)]
    exact congrArg List.ofFn (funext fun p =>
      (congrArg AR.fiberLabel (AR.tensorEnum_apply_natAdd i p)).trans
        (AR.fiberLabel_symm_inr _))

theorem AR.fiberEnum_tensor (i : ι) :
    (X ⊗ Y).fiberEnum i =
      (Fin.castOrderIso (AR.tierLength_tensor i)).trans
        (AR.tensorEnum i) :=
  Subsingleton.elim _ _

theorem AR.vertexEquiv_tensor_of_lt {i : ι} {r : Fin ((X ⊗ Y).tierLength i)}
    (h : (r : ℕ) < X.tierLength i) :
    (X ⊗ Y).vertexEquiv ⟨i, r⟩ = Sum.inl (X.vertexEquiv ⟨i, ⟨r, h⟩⟩) := by
  show ((X ⊗ Y).fiberEnum i r).val = _
  rw [AR.fiberEnum_tensor, OrderIso.trans_apply,
    show Fin.castOrderIso (AR.tierLength_tensor (X := X) (Y := Y) i) r
      = Fin.castAdd (Y.tierLength i) ⟨r, h⟩ from rfl,
    AR.tensorEnum_apply_castAdd]
  rfl

theorem AR.vertexEquiv_tensor_of_ge {i : ι} {r : Fin ((X ⊗ Y).tierLength i)}
    (h : X.tierLength i ≤ (r : ℕ)) :
    (X ⊗ Y).vertexEquiv ⟨i, r⟩ = Sum.inr (Y.vertexEquiv ⟨i,
      ⟨(r : ℕ) - X.tierLength i, by
        have _h1 := r.isLt
        have h2 : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
          AR.tierLength_tensor i
        omega⟩⟩) := by
  show ((X ⊗ Y).fiberEnum i r).val = _
  rw [AR.fiberEnum_tensor, OrderIso.trans_apply,
    show Fin.castOrderIso (AR.tierLength_tensor (X := X) (Y := Y) i) r
      = Fin.natAdd (X.tierLength i) ⟨(r : ℕ) - X.tierLength i, by
          have h1 := r.isLt
          have h2 : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
            AR.tierLength_tensor i
          omega⟩ from
      Fin.ext (by simpa using (Nat.add_sub_cancel' h).symm),
    AR.tensorEnum_apply_natAdd]
  rfl

end TierWordTensor

/-! ### Tier content of realizations -/

section RealizeTierWord
open scoped MonoidalCategory

variable {S : Type*} {ι : Type*} {τ : ι → Type*}
variable (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι))

instance realize.instFinite [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    Finite (realize g₀ w).obj.V := by
  induction w with
  | nil => exact inferInstanceAs (Finite PEmpty)
  | cons a w ih => exact inferInstanceAs (Finite ((g₀ a).obj.V ⊕ (realize g₀ w).obj.V))

instance : Finite ((𝟙_ (AR (Sigma.fst : ((i : ι) × τ i) → ι))).obj.V) :=
  inferInstanceAs (Finite PEmpty)

@[simp] theorem AR.tierWord_unit (i : ι) :
    (𝟙_ (AR (Sigma.fst : ((i : ι) × τ i) → ι))).tierWord i = [] := by
  haveI : IsEmpty ((𝟙_ (AR (Sigma.fst : ((i : ι) × τ i) → ι))).fiber i) :=
    ⟨fun v => v.val.elim⟩
  rw [AR.tierWord_eq_ofFn (OrderIso.ofIsEmpty (Fin 0) _)]
  exact List.ofFn_zero

/-- **Tier content is compositional**: the tier word of a realized string is the
    concatenation of its symbols' tier words — [jardine-2019]'s tier projection
    of `g`, and the bridge that places link-free ASL conditions per tier. -/
theorem AR.tierWord_realize [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    (realize g₀ w).tierWord i = (w.map fun s => (g₀ s).tierWord i).flatten := by
  induction w with
  | nil => simp
  | cons a w ih =>
    calc (realize g₀ (a :: w)).tierWord i
        = (g₀ a ⊗ realize g₀ w).tierWord i := rfl
      _ = ((a :: w).map fun s => (g₀ s).tierWord i).flatten := by simp [ih]

/-- The tier-`i` projection of a realization, as a free-monoid homomorphism:
    each symbol contributes its primitive's tier word. -/
noncomputable def tierProj [∀ s, Finite (g₀ s).obj.V] (i : ι) :
    FreeMonoid S →* FreeMonoid (τ i) :=
  FreeMonoid.lift fun s => FreeMonoid.ofList ((g₀ s).tierWord i)

/-- `realizeHom` packages `realize`: on a word it is the class of the realized
    representation. -/
theorem realizeHom_ofList (w : List S) :
    realizeHom g₀ (FreeMonoid.ofList w) = AR.cls (realize g₀ w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [show FreeMonoid.ofList (a :: w) = FreeMonoid.of a * FreeMonoid.ofList w from rfl,
      map_mul, ih, realize_cons, AR.cls_tensor]
    rfl

/-- `tierProj` packages `tierWord`: on a word it is the realized tier word. -/
theorem tierProj_ofList [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    tierProj g₀ i (FreeMonoid.ofList w) = FreeMonoid.ofList ((realize g₀ w).tierWord i) := by
  induction w with
  | nil => simp [realize_nil]
  | cons a w ih =>
    rw [show FreeMonoid.ofList (a :: w) = FreeMonoid.of a * FreeMonoid.ofList w from rfl,
      map_mul, ih]
    calc FreeMonoid.ofList ((g₀ a).tierWord i) * FreeMonoid.ofList ((realize g₀ w).tierWord i)
        = FreeMonoid.ofList ((g₀ a).tierWord i ++ (realize g₀ w).tierWord i) := rfl
      _ = _ := by rw [← AR.tierWord_tensor i]; rfl

end RealizeTierWord

/-! ### Factors and banned-subgraph grammars

[jardine-2017]'s connected-subgraph embedding in position coordinates: a factor
occurs at per-tier offsets when its tier words are windows of the host's and its
links transport shifted. Banned-subgraph grammars ([jardine-2016-diss] Ch. 5)
are lists of forbidden factors. -/

section Factors

variable {ι : Type*} {τ : ι → Type*}
variable (F X : AR (Sigma.fst : ((i : ι) × τ i) → ι))

/-- Tier-`i` position `p` links to tier-`j` position `q`, in ℕ coordinates
    (out-of-bounds positions link to nothing). -/
def AR.link [Finite X.obj.V] (i j : ι) (p q : ℕ) : Prop :=
  ∃ (hp : p < X.tierLength i) (hq : q < X.tierLength j), X.linkRel i j ⟨p, hp⟩ ⟨q, hq⟩

open scoped Classical in
/-- The two-tier reading of tiers `i` over `j`: each tier-`j` position's label
    with the tier-`i` labels linked to it, in ascending order — the phonetic
    interpretation of a melody tier over its backbone. -/
noncomputable def AR.linearize [Finite X.obj.V] (i j : ι) :
    List (τ j × List (τ i)) :=
  (X.tierWord j).zipIdx.map fun bq =>
    (bq.1, ((X.tierWord i).zipIdx.filter fun ap => X.link i j ap.2 bq.2).map (·.1))

/-- `F` occurs in `X` at per-tier offsets `o`: each tier word of `F` is the
    window of `X`'s at `o i`, and `F`'s links transport shifted. -/
def AR.IsFactorAt [Finite F.obj.V] [Finite X.obj.V] (o : ι → ℕ) : Prop :=
  (∀ i p, p < F.tierLength i → (X.tierWord i)[p + o i]? = (F.tierWord i)[p]?) ∧
    ∀ i j p q, F.link i j p q → X.link i j (p + o i) (q + o j)

/-- `F` **subgraph-embeds** in `X` when some offsets place it as a factor
    ([jardine-2017]'s connected-subgraph embedding). -/
def AR.FactorEmbeds [Finite F.obj.V] [Finite X.obj.V] : Prop :=
  ∃ o : ι → ℕ, F.IsFactorAt X o

/-- Offsets clamp to the host's tier lengths: `FactorEmbeds` is a bounded
    search. On tiers where the factor is nonempty the word-window condition
    already forces the bound; empty factor tiers accept any offset, so `min`
    clamps them harmlessly. -/
theorem AR.factorEmbeds_iff_bounded
    {F X : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite F.obj.V] [Finite X.obj.V] :
    F.FactorEmbeds X ↔
      ∃ o : ι → ℕ, (∀ i, o i ≤ X.tierLength i) ∧ F.IsFactorAt X o := by
  constructor
  · rintro ⟨o, hw, hl⟩
    refine ⟨fun i => min (o i) (X.tierLength i), fun i => min_le_right _ _, fun i p hp => ?_,
      fun i j p q h => ?_⟩
    · have horig := hw i p hp
      show (X.tierWord i)[p + min (o i) (X.tierLength i)]? = (F.tierWord i)[p]?
      rcases le_or_gt (o i) (X.tierLength i) with hle | hgt
      · rwa [Nat.min_eq_left hle]
      · exfalso
        have hnone : (X.tierWord i)[p + o i]? = none := by
          rw [List.getElem?_eq_none_iff]
          simp only [AR.length_tierWord]
          omega
        have hsome : p < (F.tierWord i).length := by
          simpa [AR.length_tierWord] using hp
        rw [hnone, List.getElem?_eq_some_iff.mpr ⟨hsome, rfl⟩] at horig
        simp at horig
    · obtain ⟨hpb, hqb, -⟩ := id (hl i j p q h)
      have h' := hl i j p q h
      have hoi : min (o i) (X.tierLength i) = o i := by
        have := hw i p (by obtain ⟨hp', -, -⟩ := id h; omega)
        rcases le_or_gt (o i) (X.tierLength i) with hle | hgt
        · exact Nat.min_eq_left hle
        · exfalso
          obtain ⟨hpX, -, -⟩ := id h'
          omega
      have hoj : min (o j) (X.tierLength j) = o j := by
        rcases le_or_gt (o j) (X.tierLength j) with hle | hgt
        · exact Nat.min_eq_left hle
        · exfalso
          obtain ⟨-, hqX, -⟩ := id h'
          omega
      show X.link i j (p + min (o i) (X.tierLength i)) (q + min (o j) (X.tierLength j))
      rw [hoi, hoj]
      exact h'
  · rintro ⟨o, -, hfa⟩
    exact ⟨o, hfa⟩

/-- Link conditions are supported on the factor's tier ranges. -/
theorem AR.forall_link_iff_bounded
    {F : AR (Sigma.fst : ((i : ι) × τ i) → ι)} [Finite F.obj.V]
    {C : ι → ι → ℕ → ℕ → Prop} :
    (∀ i j p q, F.link i j p q → C i j p q) ↔
      ∀ i j, ∀ p < F.tierLength i, ∀ q < F.tierLength j,
        F.link i j p q → C i j p q := by
  refine ⟨fun h i j p _ q _ hl => h i j p q hl, fun h i j p q hl => ?_⟩
  obtain ⟨hp, hq, -⟩ := id hl
  exact h i j p hp q hq hl

/-- `X` avoids every forbidden factor of a banned-subgraph grammar
    ([jardine-2016-diss] Ch. 5's `L^NL_G`). -/
def AR.Free [Finite X.obj.V]
    (B : List {F : AR (Sigma.fst : ((i : ι) × τ i) → ι) // Finite F.obj.V}) :
    Prop :=
  ∀ F ∈ B, haveI := F.property; ¬ F.val.FactorEmbeds X

/-- For a link-free factor, embedding reduces to independent per-tier infix
    occurrences ([jardine-2019]'s link-free fragment). -/
theorem AR.factorEmbeds_iff_infix_of_link_free
    {F X : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite F.obj.V] [Finite X.obj.V]
    (hF : ∀ i j p q, ¬ F.link i j p q) :
    F.FactorEmbeds X ↔ ∀ i, F.tierWord i <:+: X.tierWord i := by
  constructor
  · rintro ⟨o, hw, -⟩ i
    rw [List.isInfix_iff_exists_offset]
    rcases Nat.eq_zero_or_pos (F.tierWord i).length with hzero | hpos
    · exact ⟨0, Nat.zero_le _, fun p hp => absurd hp (by omega)⟩
    · have h0 := hw i 0 (by simpa [AR.length_tierWord] using hpos)
      refine ⟨o i, ?_, fun p hp => hw i p
        (by simpa [AR.length_tierWord] using hp)⟩
      rcases List.getElem?_eq_some_iff.mp
        (h0 ▸ (List.getElem?_eq_some_iff.mpr
          ⟨by simpa [AR.length_tierWord] using hpos, rfl⟩ :
            (F.tierWord i)[0]? = some _)) with ⟨hb, -⟩
      omega
  · intro h
    choose o ho using fun i => (List.isInfix_iff_exists_offset _ _).mp (h i)
    refine ⟨o, fun i p hp => ?_, fun i j p q hl => absurd hl (hF i j p q)⟩
    obtain ⟨-, hoff⟩ := ho i
    exact hoff p (by simpa [AR.length_tierWord] using hp)

open scoped MonoidalCategory in
/-- Tensor links are blockwise: within the left factor, or within the right
    factor shifted by the left factor's tier lengths — no cross-factor links. -/
theorem AR.link_tensor {X Y : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite X.obj.V] [Finite Y.obj.V] (i j : ι) (p q : ℕ) :
    (X ⊗ Y).link i j p q ↔
      X.link i j p q ∨ X.tierLength i ≤ p ∧ X.tierLength j ≤ q ∧
        Y.link i j (p - X.tierLength i) (q - X.tierLength j) := by
  have h2i : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
    AR.tierLength_tensor i
  have h2j : (X ⊗ Y).tierLength j = X.tierLength j + Y.tierLength j :=
    AR.tierLength_tensor j
  constructor
  · rintro ⟨hp, hq, hl⟩
    rw [AR.linkRel_def] at hl
    rcases lt_or_ge p (X.tierLength i) with hpi | hpi <;>
      rcases lt_or_ge q (X.tierLength j) with hqj | hqj
    · rw [AR.vertexEquiv_tensor_of_lt (h := hpi),
        AR.vertexEquiv_tensor_of_lt (h := hqj)] at hl
      exact Or.inl ⟨hpi, hqj, by simpa [AR.linkRel_def] using hl⟩
    · rw [AR.vertexEquiv_tensor_of_lt (h := hpi),
        AR.vertexEquiv_tensor_of_ge (h := hqj)] at hl
      simp at hl
    · rw [AR.vertexEquiv_tensor_of_ge (h := hpi),
        AR.vertexEquiv_tensor_of_lt (h := hqj)] at hl
      simp at hl
    · rw [AR.vertexEquiv_tensor_of_ge (h := hpi),
        AR.vertexEquiv_tensor_of_ge (h := hqj)] at hl
      exact Or.inr ⟨hpi, hqj, by omega, by omega,
        by simpa [AR.linkRel_def] using hl⟩
  · rintro (⟨hp, hq, hl⟩ | ⟨hpi, hqj, hp', hq', hl⟩)
    · rw [AR.linkRel_def] at hl
      refine ⟨by omega, by omega, ?_⟩
      rw [AR.linkRel_def, AR.vertexEquiv_tensor_of_lt (h := hp),
        AR.vertexEquiv_tensor_of_lt (h := hq)]
      simpa using hl
    · rw [AR.linkRel_def] at hl
      refine ⟨by omega, by omega, ?_⟩
      rw [AR.linkRel_def,
        AR.vertexEquiv_tensor_of_ge (h := by omega),
        AR.vertexEquiv_tensor_of_ge (h := by omega)]
      simpa using hl

end Factors

/-! ### Classification: the readers determine the representation

Two finite representations with the same tier words and the same links are
isomorphic — `(tierWord, link)` is a complete invariant, [jardine-heinz-2015]'s
tiered tuples as the classification of finite representations. -/

section Classification
open scoped MonoidalCategory

variable {ι : Type*} {τ : ι → Type*}
variable {X : AR (Sigma.fst : ((i : ι) × τ i) → ι)}

/-- The label of a canonical vertex sits on its own tier. -/
theorem AR.label_vertexEquiv [Finite X.obj.V] (i : ι)
    (p : Fin (X.tierLength i)) : (X.obj.label (X.vertexEquiv ⟨i, p⟩)).1 = i :=
  (X.fiberEnum i p).property

theorem AR.linkRel_iff_link [Finite X.obj.V] {i j : ι}
    {p : Fin (X.tierLength i)} {q : Fin (X.tierLength j)} :
    X.linkRel i j p q ↔ X.link i j (p : ℕ) (q : ℕ) :=
  ⟨fun h => ⟨p.isLt, q.isLt, h⟩, fun ⟨_, _, h⟩ => by convert h⟩

theorem AR.tierWord_getElem [Finite X.obj.V] {i : ι}
    (p : Fin (X.tierLength i)) :
    (X.tierWord i)[(p : ℕ)]'(by simp) = X.fiberLabel (X.fiberEnum i p) := by
  simp [AR.tierWord]

theorem AR.label_normalize [Finite X.obj.V] {i : ι}
    (p : Fin (X.tierLength i)) :
    (X.normalize).obj.label ⟨i, p⟩ = ⟨i, X.fiberLabel (X.fiberEnum i p)⟩ :=
  X.label_fiber (X.fiberEnum i p)

theorem AR.arcs_normalize_ne [Finite X.obj.V] {i j : ι} (h : i ≠ j)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) :
    ¬ (X.normalize).obj.arcs.Adj ⟨i, p⟩ ⟨j, q⟩ := fun ha => by
  have h2 := X.property.1.tier_eq ha
  rw [show Graph.tier Sigma.fst X.obj (X.vertexEquiv ⟨i, p⟩) = i from
      X.label_vertexEquiv i p,
    show Graph.tier Sigma.fst X.obj (X.vertexEquiv ⟨j, q⟩) = j from
      X.label_vertexEquiv j q] at h2
  exact h h2

/-- Links are symmetric in coordinates. -/
theorem AR.link_symm [Finite X.obj.V] {i j : ι} {p q : ℕ}
    (h : X.link i j p q) : X.link j i q p := by
  obtain ⟨hp, hq, hl⟩ := h
  exact ⟨hq, hp, hl.symm⟩

/-- Same-tier vertices are never linked: they are arc-comparable (Axioms 1–2),
    and association never follows arcs (Axiom 3). -/
theorem AR.not_link_self_tier [Finite X.obj.V] (i : ι) (p q : ℕ) :
    ¬ X.link i i p q := by
  rintro ⟨hp, hq, hl⟩
  rw [AR.linkRel_def] at hl
  have hlab : X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨p, hp⟩⟩)
      = X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨q, hq⟩⟩) := by
    show (X.obj.label _).1 = (X.obj.label _).1
    rw [AR.label_vertexEquiv, AR.label_vertexEquiv]
  exact (X.property.1.total hl.ne hlab).elim (X.property.2 hl) (X.property.2 hl.symm)

/-- The classification isomorphism, as a full-structure `Graph.Iso` —
    the form that descends to the class monoid. -/
noncomputable def AR.fullIsoOfReaderEq
    {A B : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite A.obj.V] [Finite B.obj.V]
    (hw : ∀ i, A.tierWord i = B.tierWord i)
    (hl : ∀ i j p q, A.link i j p q ↔ B.link i j p q) :
    Graph.Iso A.obj B.obj := by
  have hlen : ∀ i, A.tierLength i = B.tierLength i := fun i => by
    rw [← AR.length_tierWord, hw, AR.length_tierWord]
  refine A.normalizeFullIso.symm.trans (Graph.Iso.trans ?_ B.normalizeFullIso)
  refine
    { toEquiv := Equiv.sigmaCongrRight fun i => finCongr (hlen i)
      edges_iff := fun v w => ?_
      arcs_iff := fun v w => ?_
      label_comp := fun v => ?_ }
  · obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    show B.normalize.obj.edges.Adj ⟨i, Fin.cast (hlen i) p⟩ ⟨j, Fin.cast (hlen j) q⟩
      ↔ A.normalize.obj.edges.Adj ⟨i, p⟩ ⟨j, q⟩
    rw [AR.edges_normalize, AR.edges_normalize,
      AR.linkRel_iff_link, AR.linkRel_iff_link]
    exact (hl i j p q).symm
  · obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    show B.normalize.obj.arcs.Adj ⟨i, Fin.cast (hlen i) p⟩ ⟨j, Fin.cast (hlen j) q⟩
      ↔ A.normalize.obj.arcs.Adj ⟨i, p⟩ ⟨j, q⟩
    rcases eq_or_ne i j with rfl | h
    · rw [AR.arcs_normalize, AR.arcs_normalize]
      exact (Fin.castOrderIso (hlen i)).lt_iff_lt
    · exact iff_of_false (AR.arcs_normalize_ne h _ _)
        (AR.arcs_normalize_ne h _ _)
  · obtain ⟨i, p⟩ := v
    show B.normalize.obj.label ⟨i, Fin.cast (hlen i) p⟩ = A.normalize.obj.label ⟨i, p⟩
    rw [AR.label_normalize, AR.label_normalize]
    congr 1
    rw [← AR.tierWord_getElem, ← AR.tierWord_getElem]
    simp only [hw, Fin.val_cast]

/-- **Classification of finite representations**: equal tier words and equal
    links give an isomorphism — the tuple reading is a complete invariant. -/
noncomputable def AR.isoOfReaderEq
    {A B : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite A.obj.V] [Finite B.obj.V]
    (hw : ∀ i, A.tierWord i = B.tierWord i)
    (hl : ∀ i j p q, A.link i j p q ↔ B.link i j p q) : A ≅ B :=
  AR.mkIso (AR.fullIsoOfReaderEq hw hl)

end Classification

/-! ### Building representations from tuple data

The constructor inverse to the readers: tier words plus a position-coordinate
link relation determine a representation on the canonical carrier. This is the
tiered presentation as a *function* — the essential-surjectivity direction of
the classification. -/

section OfData

variable {ι : Type*} {τ : ι → Type*}

/-- The representation presented by tier words `ws` and cross-tier links `L`
    (positions in ℕ coordinates; same-tier and out-of-bounds pairs are
    ignored, and same-tier links are excluded by construction). Arcs are the
    ascending position order on each tier. -/
def AR.ofData (ws : ∀ i, List (τ i)) (L : ι → ι → ℕ → ℕ → Prop) :
    AR (Sigma.fst : ((i : ι) × τ i) → ι) where
  obj :=
    { V := (i : ι) × Fin (ws i).length
      edges :=
        { Adj := fun v w => v.1 ≠ w.1 ∧
            (L v.1 w.1 v.2 w.2 ∨ L w.1 v.1 w.2 v.2)
          symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
          loopless := ⟨fun _ h => h.1 rfl⟩ }
      arcs := ⟨fun v w => v.1 = w.1 ∧ (v.2 : ℕ) < (w.2 : ℕ)⟩
      label := fun v => ⟨v.1, (ws v.1)[v.2]⟩ }
  property := by
    refine ⟨⟨fun v w h => h.1, fun v w hne htier => ?_, fun v h => lt_irrefl _ h.2,
      fun u v w huv hvw => ⟨huv.1.trans hvw.1, huv.2.trans hvw.2⟩⟩,
      fun v w hadj harc => hadj.1 harc.1⟩
    obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    obtain rfl : i = j := htier
    rcases Nat.lt_trichotomy (p : ℕ) (q : ℕ) with h | h | h
    · exact Or.inl ⟨rfl, h⟩
    · exact absurd (by rw [Fin.ext h]) hne
    · exact Or.inr ⟨rfl, h⟩

variable [Finite ι] {ws : ∀ i, List (τ i)} {L : ι → ι → ℕ → ℕ → Prop}

instance : Finite (AR.ofData ws L).obj.V :=
  inferInstanceAs (Finite ((i : ι) × Fin (ws i).length))

/-- The canonical carrier's fiber at `i` is its position range. -/
noncomputable def AR.ofDataFiberEnum (i : ι) :
    Fin ((ws i).length) ≃o (AR.ofData ws L).fiber i := by
  refine StrictMono.orderIsoOfSurjective (fun p => ⟨⟨i, p⟩, rfl⟩) (fun p q h => ⟨rfl, h⟩)
    fun v => ?_
  obtain ⟨⟨j, q⟩, hp⟩ := v
  obtain rfl : j = i := hp
  exact ⟨q, rfl⟩

theorem AR.tierLength_ofData (i : ι) :
    (AR.ofData ws L).tierLength i = (ws i).length := by
  rw [← AR.length_tierWord,
    AR.tierWord_eq_ofFn (AR.ofDataFiberEnum i), List.length_ofFn]

theorem AR.fiberEnum_ofData (i : ι) :
    (AR.ofData ws L).fiberEnum i =
      (Fin.castOrderIso (AR.tierLength_ofData i)).trans
        (AR.ofDataFiberEnum i) :=
  Subsingleton.elim _ _

theorem AR.vertexEquiv_ofData {i : ι}
    (r : Fin ((AR.ofData ws L).tierLength i)) :
    (AR.ofData ws L).vertexEquiv ⟨i, r⟩ =
      ⟨i, Fin.cast (AR.tierLength_ofData i) r⟩ := by
  show ((AR.ofData ws L).fiberEnum i r).val = _
  rw [AR.fiberEnum_ofData]
  rfl

/-- `ofData` reads back its words. -/
@[simp] theorem AR.tierWord_ofData (i : ι) :
    (AR.ofData ws L).tierWord i = ws i := by
  rw [AR.tierWord_eq_ofFn (AR.ofDataFiberEnum i)]
  exact List.ofFn_getElem

/-- `ofData` reads back its links, symmetrized, on in-bounds cross-tier
    pairs. -/
theorem AR.link_ofData (i j : ι) (p q : ℕ) :
    (AR.ofData ws L).link i j p q ↔
      i ≠ j ∧ p < (ws i).length ∧ q < (ws j).length ∧ (L i j p q ∨ L j i q p) := by
  constructor
  · rintro ⟨hp, hq, hl⟩
    rw [AR.linkRel_def, AR.vertexEquiv_ofData,
      AR.vertexEquiv_ofData] at hl
    obtain ⟨hne, hor⟩ := hl
    have hp' : p < (ws i).length := AR.tierLength_ofData i ▸ hp
    have hq' : q < (ws j).length := AR.tierLength_ofData j ▸ hq
    exact ⟨hne, hp', hq', by simpa using hor⟩
  · rintro ⟨hij, hp, hq, hor⟩
    have hp' : p < (AR.ofData ws L).tierLength i := by
      rw [← AR.length_tierWord, AR.tierWord_ofData]; exact hp
    have hq' : q < (AR.ofData ws L).tierLength j := by
      rw [← AR.length_tierWord, AR.tierWord_ofData]; exact hq
    refine ⟨hp', hq', ?_⟩
    rw [AR.linkRel_def, AR.vertexEquiv_ofData,
      AR.vertexEquiv_ofData]
    exact ⟨hij, by simpa using hor⟩

end OfData

end Autosegmental
