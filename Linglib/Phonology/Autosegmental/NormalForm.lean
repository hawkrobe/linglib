/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Linglib.Phonology.Autosegmental.MixedGraph

/-!
# Normal forms of autosegmental representations

Every finite representation is isomorphic to its **normal form**: the same
representation reindexed onto the canonical vertex type `(i : ι) × Fin nᵢ`,
each tier fiber enumerated in ascending precedence order
(`IsTierOrdered.isStrictTotalOrder` → `linearOrderOfSTO` → `monoEquivOfFin`).
The normal form is a `Representation` — not a separate carrier — and
`normalizeIso` is definitional: `normalize` pulls the graph back along the
enumeration equivalence.

Strictness lives where Mac Lane coherence puts it: on the skeleton. The monoid
of isomorphism classes `Skeleton (Representation t)` carries concatenation with
associativity on the nose (`CategoryTheory.Monoidal.Skeleton`), and
`toSkeleton_normalize` says `normalize` chooses representatives.

## Main definitions

* `Representation.fiber`, `Representation.vertexEquiv`: the tier fibers of a
  finite representation and the canonical enumeration of its vertex type.
* `Representation.normalize`: the normal form, a `Representation` on the
  canonical vertex type.

## Main results

* `Representation.normalizeIso`: `X.normalize ≅ X`.
* `Representation.arcs_normalize`: on normal forms the arcs are the ascending
  position order — the classification content, [jardine-heinz-2015]'s tiered
  presentation recovered as a theorem.
* `Representation.toSkeleton_normalize`: normal forms represent their
  isomorphism class in the skeleton monoid.
-/

namespace Autosegmental

open CategoryTheory

variable {ι : Type*} {τ : ι → Type*}

section NormalForm
open scoped Classical

/-- Fiber of the tier coloring at `i`: vertices of `X.obj` labelled to tier `i`.
    Under `IsTierOrdered` its arcs form a strict total order, and under
    `Finite X.obj.V` it is finite — the two ingredients `monoEquivOfFin`
    needs to enumerate the fiber as `Fin _`. -/
def Representation.fiber (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)) (i : ι) :
    Type _ := {v : X.obj.V // (X.obj.label v).1 = i}

variable {X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)}

/-- The `τ i` component of a fiber element, extracted from the labeling by
    transporting along the fiber's tier-membership witness. -/
def Representation.fiberLabel {i : ι} (v : X.fiber i) : τ i :=
  v.property ▸ (X.obj.label v.val).2

instance Representation.fiber.instFinite [Finite X.obj.V] (i : ι) : Finite (X.fiber i) :=
  Subtype.finite

/-- The arcs restricted to a tier fiber form a strict total order — the classed
    form of Axioms 1–2 applied to the tier coloring `Sigma.fst`. -/
instance Representation.fiber.instIsStrictTotalOrder (i : ι) :
    IsStrictTotalOrder (X.fiber i) (fun a b => X.obj.graph.arcs.Adj a.val b.val) :=
  X.property.1.isStrictTotalOrder i

/-- Classical linear order on the fiber, from `IsStrictTotalOrder` via
    `linearOrderOfSTO`. -/
noncomputable instance Representation.fiber.instLinearOrder (i : ι) :
    LinearOrder (X.fiber i) := by
  classical
  exact linearOrderOfSTO (fun a b : X.fiber i => X.obj.graph.arcs.Adj a.val b.val)

/-- The number of tier-`i` vertices. -/
noncomputable def Representation.tierLen (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι))
    [Finite X.obj.V] (i : ι) : ℕ :=
  letI := Fintype.ofFinite (X.fiber i)
  Fintype.card (X.fiber i)

/-- The canonical enumeration of a finite representation's vertex type: tier
    fibers in ascending precedence order, assembled over the tier index. -/
noncomputable def Representation.vertexEquiv [Finite X.obj.V] :
    ((i : ι) × Fin (X.tierLen i)) ≃ X.obj.V :=
  letI : ∀ i : ι, Fintype (X.fiber i) := fun _ => Fintype.ofFinite _
  (Equiv.sigmaCongrRight
    (fun i : ι => (monoEquivOfFin (X.fiber i) rfl).toEquiv)).trans
    (Equiv.sigmaFiberEquiv (fun v : X.obj.V => (X.obj.label v).1))

/-- The tier-`i` label word: the fiber's labels read off in ascending precedence
    order — the tier content the normal form canonicalizes. -/
noncomputable def Representation.tierWord [Finite X.obj.V] (i : ι) : List (τ i) :=
  letI := Fintype.ofFinite (X.fiber i)
  List.ofFn fun p : Fin (X.tierLen i) => X.fiberLabel (monoEquivOfFin (X.fiber i) rfl p)

/-- The link relation in position coordinates: tier-`i` position `p` associates
    to tier-`j` position `q`. With `tierWord`, the complete tuple reading of a
    finite representation. -/
noncomputable def Representation.linkRel [Finite X.obj.V] (i j : ι)
    (p : Fin (X.tierLen i)) (q : Fin (X.tierLen j)) : Prop :=
  X.obj.graph.edges.Adj (X.vertexEquiv ⟨i, p⟩) (X.vertexEquiv ⟨j, q⟩)

/-- The normal form: `X` reindexed onto the canonical vertex type by pulling
    edges, arcs, and labels back along `vertexEquiv`. A `Representation` — the
    normal form is not a separate kind of object. -/
noncomputable def Representation.normalize
    (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)) [Finite X.obj.V] :
    Representation (Sigma.fst : ((i : ι) × τ i) → ι) where
  obj :=
    { V := (i : ι) × Fin (X.tierLen i)
      graph :=
        { edges := X.obj.graph.edges.comap X.vertexEquiv
          arcs := ⟨fun v w => X.obj.graph.arcs.Adj (X.vertexEquiv v) (X.vertexEquiv w)⟩ }
      label := fun v => X.obj.label (X.vertexEquiv v) }
  property :=
    ⟨⟨fun _ _ h => X.property.1.tier_eq h,
      fun _ _ hne htier => X.property.1.total (fun hv => hne (X.vertexEquiv.injective hv)) htier,
      fun _ h => X.property.1.irrefl _ h,
      fun _ _ _ huv hvw => X.property.1.trans huv hvw⟩,
     fun _ _ hadj harc => X.property.2 hadj harc⟩

/-- The normal form is isomorphic to the original — definitionally, since
    `normalize` is a pullback along `vertexEquiv`. -/
noncomputable def Representation.normalizeIso [Finite X.obj.V] : X.normalize ≅ X :=
  Representation.mkIso
    { toEquiv := X.vertexEquiv
      edges_iff := fun _ _ => Iff.rfl
      arcs_iff := fun _ _ => Iff.rfl
      label_comp := fun _ => rfl }

/-- Normal forms represent their isomorphism class: `normalize` is a section of
    the quotient onto the skeleton, where the monoid of iso classes carries
    strictly associative concatenation (`CategoryTheory.Monoidal.Skeleton`). -/
theorem Representation.toSkeleton_normalize [Finite X.obj.V] :
    toSkeleton (X.normalize) = toSkeleton X :=
  Quotient.sound ⟨X.normalizeIso⟩

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
noncomputable def realize (g₀ : S → Representation (Sigma.fst : ((i : ι) × τ i) → ι))
    (w : List S) : Representation (Sigma.fst : ((i : ι) × τ i) → ι) :=
  (w.map g₀).foldr (· ⊗ ·) (𝟙_ _)

@[simp] theorem realize_nil (g₀ : S → Representation (Sigma.fst : ((i : ι) × τ i) → ι)) :
    realize g₀ [] = 𝟙_ _ := rfl

@[simp] theorem realize_cons (g₀ : S → Representation (Sigma.fst : ((i : ι) × τ i) → ι))
    (a : S) (w : List S) : realize g₀ (a :: w) = g₀ a ⊗ realize g₀ w := rfl

/-- The realization as a free-monoid homomorphism into the skeleton monoid —
    the string→AR monoid hom, with associativity strict on iso classes
    (`CategoryTheory.Monoidal.Skeleton`). -/
noncomputable def realizeHom
    (g₀ : S → Representation (Sigma.fst : ((i : ι) × τ i) → ι)) :
    FreeMonoid S →* Skeleton (Representation (Sigma.fst : ((i : ι) × τ i) → ι)) :=
  FreeMonoid.lift (toSkeleton ∘ g₀)

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
variable {X Y : Representation (Sigma.fst : ((i : ι) × τ i) → ι)}

instance [Finite X.obj.V] [Finite Y.obj.V] : Finite ((X ⊗ Y).obj.V) :=
  inferInstanceAs (Finite (X.obj.V ⊕ Y.obj.V))

/-- A tensor's tier fiber splits as the sum of the factors' fibers. -/
def Representation.fiberTensorEquiv (i : ι) :
    (X ⊗ Y).fiber i ≃ X.fiber i ⊕ Y.fiber i where
  toFun v := match v with
    | ⟨.inl w, h⟩ => .inl ⟨w, h⟩
    | ⟨.inr w, h⟩ => .inr ⟨w, h⟩
  invFun := Sum.elim (fun w => ⟨.inl w.val, w.property⟩) (fun w => ⟨.inr w.val, w.property⟩)
  left_inv := by rintro ⟨w | w, h⟩ <;> rfl
  right_inv := by rintro (w | w) <;> rfl

variable [Finite X.obj.V] [Finite Y.obj.V]

attribute [local instance] Fintype.ofFinite

theorem Representation.tierLen_tensor (i : ι) :
    (X ⊗ Y).tierLen i = X.tierLen i + Y.tierLen i := by
  letI := Fintype.ofFinite ((X ⊗ Y).fiber i)
  letI := Fintype.ofFinite (X.fiber i)
  letI := Fintype.ofFinite (Y.fiber i)
  simp only [Representation.tierLen]
  rw [Fintype.card_congr (Representation.fiberTensorEquiv i), Fintype.card_sum]

open Representation in
/-- The blockwise enumeration of a tensor's fiber: left factor first, then
    right — monotone because the bridge arc orders the blocks. -/
noncomputable def Representation.tensorEnum (i : ι) :
    Fin (X.tierLen i + Y.tierLen i) ≃o (X ⊗ Y).fiber i := by
  letI := Fintype.ofFinite (X.fiber i)
  letI := Fintype.ofFinite (Y.fiber i)
  refine StrictMono.orderIsoOfSurjective
    (finSumFinEquiv.symm.trans
      (((monoEquivOfFin (X.fiber i) (rfl : _ = X.tierLen i)).toEquiv.sumCongr
        (monoEquivOfFin (Y.fiber i) (rfl : _ = Y.tierLen i)).toEquiv).trans
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
      exact (monoEquivOfFin (X.fiber i) (rfl : _ = X.tierLen i)).strictMono
        (by simp only [Fin.lt_def, Fin.val_castAdd] at hpq ⊢; exact hpq)
    | right q₂ =>
      rw [finSumFinEquiv_symm_apply_natAdd]
      exact (monoEquivOfFin (X.fiber i) (rfl : _ = X.tierLen i) p₁).property.trans
        ((monoEquivOfFin (Y.fiber i) (rfl : _ = Y.tierLen i) q₂).property).symm
  | right p₂ =>
    induction q using Fin.addCases with
    | left q₁ =>
      exact absurd hpq (by simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]; omega)
    | right q₂ =>
      rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
      exact (monoEquivOfFin (Y.fiber i) (rfl : _ = Y.tierLen i)).strictMono
        (by simp only [Fin.lt_def, Fin.val_natAdd] at hpq ⊢; omega)

theorem Representation.tensorEnum_apply_castAdd (i : ι) (p : Fin (X.tierLen i)) :
    Representation.tensorEnum i (Fin.castAdd (Y.tierLen i) p) =
      (Representation.fiberTensorEquiv i).symm
        (.inl (monoEquivOfFin (X.fiber i) (rfl : _ = X.tierLen i) p)) := by
  simp [Representation.tensorEnum, finSumFinEquiv_symm_apply_castAdd]

theorem Representation.tensorEnum_apply_natAdd (i : ι) (p : Fin (Y.tierLen i)) :
    Representation.tensorEnum i (Fin.natAdd (X.tierLen i) p) =
      (Representation.fiberTensorEquiv (X := X) i).symm
        (.inr (monoEquivOfFin (Y.fiber i) (rfl : _ = Y.tierLen i) p)) := by
  simp [Representation.tensorEnum, finSumFinEquiv_symm_apply_natAdd]

omit [Finite X.obj.V] [Finite Y.obj.V] in
theorem Representation.fiberLabel_symm_inl {i : ι} (w : X.fiber i) :
    Representation.fiberLabel ((Representation.fiberTensorEquiv (X := X) (Y := Y) i).symm
      (.inl w)) = X.fiberLabel w := rfl

omit [Finite X.obj.V] [Finite Y.obj.V] in
theorem Representation.fiberLabel_symm_inr {i : ι} (w : Y.fiber i) :
    Representation.fiberLabel ((Representation.fiberTensorEquiv (X := X) (Y := Y) i).symm
      (.inr w)) = Y.fiberLabel w := rfl

/-- Any monotone enumeration computes the tier word. -/
theorem Representation.tierWord_eq_ofFn {Z : Representation (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite Z.obj.V] {i : ι} {n : ℕ} (e : Fin n ≃o Z.fiber i) :
    Z.tierWord i = List.ofFn fun p => Z.fiberLabel (e p) := by
  have hn : Z.tierLen i = n := by
    simpa [Representation.tierLen] using (Fintype.card_congr e.toEquiv).symm
  subst hn
  rw [Subsingleton.elim e (monoEquivOfFin (Z.fiber i) rfl)]
  rfl

/-- **Concatenation appends tier content**: the tier word of a tensor is the
    factors' tier words in sequence — the tuple presentation of
    [jardine-heinz-2015]'s Definition 2, recovered as a theorem about normal
    forms. -/
theorem Representation.tierWord_tensor (i : ι) :
    (X ⊗ Y).tierWord i = X.tierWord i ++ Y.tierWord i := by
  rw [Representation.tierWord_eq_ofFn (Representation.tensorEnum i), List.ofFn_add]
  congr 1
  · rw [Representation.tierWord_eq_ofFn (monoEquivOfFin (X.fiber i) (rfl : _ = X.tierLen i))]
    exact congrArg List.ofFn (funext fun p =>
      (congrArg Representation.fiberLabel (Representation.tensorEnum_apply_castAdd i p)).trans
        (Representation.fiberLabel_symm_inl _))
  · rw [Representation.tierWord_eq_ofFn (monoEquivOfFin (Y.fiber i) (rfl : _ = Y.tierLen i))]
    exact congrArg List.ofFn (funext fun p =>
      (congrArg Representation.fiberLabel (Representation.tensorEnum_apply_natAdd i p)).trans
        (Representation.fiberLabel_symm_inr _))

end TierWordTensor

/-! ### Tier content of realizations -/

section RealizeTierWord
open scoped MonoidalCategory

variable {S : Type*} {ι : Type*} {τ : ι → Type*}
variable (g₀ : S → Representation (Sigma.fst : ((i : ι) × τ i) → ι))

instance realize.instFinite [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    Finite (realize g₀ w).obj.V := by
  induction w with
  | nil => exact inferInstanceAs (Finite PEmpty)
  | cons a w ih => exact inferInstanceAs (Finite ((g₀ a).obj.V ⊕ (realize g₀ w).obj.V))

instance : Finite ((𝟙_ (Representation (Sigma.fst : ((i : ι) × τ i) → ι))).obj.V) :=
  inferInstanceAs (Finite PEmpty)

theorem Representation.tierWord_unit (i : ι) :
    (𝟙_ (Representation (Sigma.fst : ((i : ι) × τ i) → ι))).tierWord i = [] := by
  haveI : IsEmpty ((𝟙_ (Representation (Sigma.fst : ((i : ι) × τ i) → ι))).fiber i) :=
    ⟨fun v => v.val.elim⟩
  rw [Representation.tierWord_eq_ofFn (n := 0) ⟨Equiv.equivOfIsEmpty _ _, fun {a} => a.elim0⟩]
  exact List.ofFn_zero

/-- **Tier content is compositional**: the tier word of a realized string is the
    concatenation of its symbols' tier words — [jardine-2019]'s tier projection
    of `g`, and the bridge that places link-free ASL conditions per tier. -/
theorem Representation.tierWord_realize [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    (realize g₀ w).tierWord i = (w.map fun s => (g₀ s).tierWord i).flatten := by
  induction w with
  | nil => exact Representation.tierWord_unit i
  | cons a w ih =>
    calc (realize g₀ (a :: w)).tierWord i
        = (g₀ a ⊗ realize g₀ w).tierWord i := rfl
      _ = (g₀ a).tierWord i ++ (realize g₀ w).tierWord i := Representation.tierWord_tensor i
      _ = ((a :: w).map fun s => (g₀ s).tierWord i).flatten := by rw [ih]; rfl

/-- The tier-`i` projection of a realization, as a free-monoid homomorphism:
    each symbol contributes its primitive's tier word. -/
noncomputable def tierProj [∀ s, Finite (g₀ s).obj.V] (i : ι) :
    FreeMonoid S →* FreeMonoid (τ i) :=
  FreeMonoid.lift fun s => FreeMonoid.ofList ((g₀ s).tierWord i)

end RealizeTierWord

end Autosegmental
