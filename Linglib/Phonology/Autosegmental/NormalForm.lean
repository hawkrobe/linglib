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

* `Representation.fiber`, `Representation.fiberEnum`, `Representation.vertexEquiv`:
  the tier fibers of a finite representation and their canonical enumerations.
* `Representation.tierLength`, `Representation.tierWord`, `Representation.linkRel`:
  the tuple reading — per-tier sizes, label words, and position-coordinate links.
* `Representation.normalize`: the normal form, a `Representation` on the
  canonical vertex type.
* `realize`, `realizeHom`, `tierProj`: [jardine-2019]'s `g` as iterated tensor,
  as a free-monoid hom into the skeleton, and its per-tier projections.

## Main results

* `Representation.normalizeIso`: `X.normalize ≅ X`.
* `Representation.arcs_normalize`, `Representation.edges_normalize`: on normal
  forms the arcs are the ascending position order and the edges are `linkRel` —
  [jardine-heinz-2015]'s tiered presentation recovered as a theorem.
* `Representation.tierWord_tensor`, `Representation.tierWord_realize`:
  concatenation appends tier words; tier content of a realization is
  compositional.
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
noncomputable def Representation.tierLength (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι))
    [Finite X.obj.V] (i : ι) : ℕ :=
  letI := Fintype.ofFinite (X.fiber i)
  Fintype.card (X.fiber i)

/-- The canonical ascending enumeration of a tier fiber. -/
noncomputable def Representation.fiberEnum [Finite X.obj.V] (i : ι) :
    Fin (X.tierLength i) ≃o X.fiber i :=
  letI := Fintype.ofFinite (X.fiber i)
  monoEquivOfFin (X.fiber i) rfl

/-- The canonical enumeration of a finite representation's vertex type: tier
    fibers in ascending precedence order, assembled over the tier index. -/
noncomputable def Representation.vertexEquiv [Finite X.obj.V] :
    ((i : ι) × Fin (X.tierLength i)) ≃ X.obj.V :=
  letI : ∀ i : ι, Fintype (X.fiber i) := fun _ => Fintype.ofFinite _
  (Equiv.sigmaCongrRight (fun i : ι => (X.fiberEnum i).toEquiv)).trans
    (Equiv.sigmaFiberEquiv (fun v : X.obj.V => (X.obj.label v).1))

/-- The tier-`i` label word: the fiber's labels read off in ascending precedence
    order — the tier content the normal form canonicalizes. -/
noncomputable def Representation.tierWord [Finite X.obj.V] (i : ι) : List (τ i) :=
  letI := Fintype.ofFinite (X.fiber i)
  List.ofFn fun p : Fin (X.tierLength i) => X.fiberLabel (X.fiberEnum i p)

@[simp] theorem Representation.length_tierWord [Finite X.obj.V] (i : ι) :
    (X.tierWord i).length = X.tierLength i := by
  simp [Representation.tierWord]

/-- The link relation in position coordinates: tier-`i` position `p` associates
    to tier-`j` position `q`. With `tierWord`, the complete tuple reading of a
    finite representation. -/
noncomputable def Representation.linkRel [Finite X.obj.V] (i j : ι)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) : Prop :=
  X.obj.graph.edges.Adj (X.vertexEquiv ⟨i, p⟩) (X.vertexEquiv ⟨j, q⟩)

theorem Representation.linkRel_def [Finite X.obj.V] {i j : ι} {p : Fin (X.tierLength i)}
    {q : Fin (X.tierLength j)} :
    X.linkRel i j p q ↔
      X.obj.graph.edges.Adj (X.vertexEquiv ⟨i, p⟩) (X.vertexEquiv ⟨j, q⟩) := Iff.rfl

/-- The normal form: `X` reindexed onto the canonical vertex type by pulling
    edges, arcs, and labels back along `vertexEquiv`. A `Representation` — the
    normal form is not a separate kind of object. -/
noncomputable def Representation.normalize
    (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)) [Finite X.obj.V] :
    Representation (Sigma.fst : ((i : ι) × τ i) → ι) where
  obj :=
    { V := (i : ι) × Fin (X.tierLength i)
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

/-- On normal forms the edges are exactly `linkRel` — with `arcs_normalize`,
    the complete tuple reading of the normal form. -/
theorem Representation.edges_normalize [Finite X.obj.V] (i j : ι)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) :
    (X.normalize).obj.graph.edges.Adj ⟨i, p⟩ ⟨j, q⟩ ↔ X.linkRel i j p q := Iff.rfl

/-- On normal forms the arcs are the ascending position order — the
    classification content: [jardine-heinz-2015]'s tiered presentation
    recovered as a theorem. -/
theorem Representation.arcs_normalize [Finite X.obj.V] (i : ι)
    (p q : Fin (X.tierLength i)) :
    (X.normalize).obj.graph.arcs.Adj ⟨i, p⟩ ⟨i, q⟩ ↔ p < q :=
  (X.fiberEnum i).lt_iff_lt

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

@[simp] theorem Representation.tierLength_tensor (i : ι) :
    (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i := by
  letI := Fintype.ofFinite ((X ⊗ Y).fiber i)
  letI := Fintype.ofFinite (X.fiber i)
  letI := Fintype.ofFinite (Y.fiber i)
  simp only [Representation.tierLength]
  rw [Fintype.card_congr (Representation.fiberTensorEquiv i), Fintype.card_sum]

open Representation in
/-- The blockwise enumeration of a tensor's fiber: left factor first, then
    right — monotone because the bridge arc orders the blocks. -/
noncomputable def Representation.tensorEnum (i : ι) :
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

theorem Representation.tensorEnum_apply_castAdd (i : ι) (p : Fin (X.tierLength i)) :
    Representation.tensorEnum i (Fin.castAdd (Y.tierLength i) p) =
      (Representation.fiberTensorEquiv i).symm
        (.inl (X.fiberEnum i p)) := by
  simp [Representation.tensorEnum, finSumFinEquiv_symm_apply_castAdd]

theorem Representation.tensorEnum_apply_natAdd (i : ι) (p : Fin (Y.tierLength i)) :
    Representation.tensorEnum i (Fin.natAdd (X.tierLength i) p) =
      (Representation.fiberTensorEquiv (X := X) i).symm
        (.inr (Y.fiberEnum i p)) := by
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
  have hn : Z.tierLength i = n := by
    simpa [Representation.tierLength] using (Fintype.card_congr e.toEquiv).symm
  subst hn
  rw [Subsingleton.elim e (Z.fiberEnum i)]
  rfl

/-- **Concatenation appends tier content**: the tier word of a tensor is the
    factors' tier words in sequence — the tuple presentation of
    [jardine-heinz-2015]'s Definition 2, recovered as a theorem about normal
    forms. -/
@[simp] theorem Representation.tierWord_tensor (i : ι) :
    (X ⊗ Y).tierWord i = X.tierWord i ++ Y.tierWord i := by
  rw [Representation.tierWord_eq_ofFn (Representation.tensorEnum i), List.ofFn_add]
  congr 1
  · rw [Representation.tierWord_eq_ofFn (X.fiberEnum i)]
    exact congrArg List.ofFn (funext fun p =>
      (congrArg Representation.fiberLabel (Representation.tensorEnum_apply_castAdd i p)).trans
        (Representation.fiberLabel_symm_inl _))
  · rw [Representation.tierWord_eq_ofFn (Y.fiberEnum i)]
    exact congrArg List.ofFn (funext fun p =>
      (congrArg Representation.fiberLabel (Representation.tensorEnum_apply_natAdd i p)).trans
        (Representation.fiberLabel_symm_inr _))

theorem Representation.fiberEnum_tensor (i : ι) :
    (X ⊗ Y).fiberEnum i =
      (Fin.castOrderIso (Representation.tierLength_tensor i)).trans
        (Representation.tensorEnum i) :=
  Subsingleton.elim _ _

theorem Representation.vertexEquiv_tensor_of_lt {i : ι} {r : Fin ((X ⊗ Y).tierLength i)}
    (h : (r : ℕ) < X.tierLength i) :
    (X ⊗ Y).vertexEquiv ⟨i, r⟩ = Sum.inl (X.vertexEquiv ⟨i, ⟨r, h⟩⟩) := by
  show ((X ⊗ Y).fiberEnum i r).val = _
  rw [Representation.fiberEnum_tensor, OrderIso.trans_apply,
    show Fin.castOrderIso (Representation.tierLength_tensor (X := X) (Y := Y) i) r
      = Fin.castAdd (Y.tierLength i) ⟨r, h⟩ from rfl,
    Representation.tensorEnum_apply_castAdd]
  rfl

theorem Representation.vertexEquiv_tensor_of_ge {i : ι} {r : Fin ((X ⊗ Y).tierLength i)}
    (h : X.tierLength i ≤ (r : ℕ)) :
    (X ⊗ Y).vertexEquiv ⟨i, r⟩ = Sum.inr (Y.vertexEquiv ⟨i,
      ⟨(r : ℕ) - X.tierLength i, by
        have _h1 := r.isLt
        have h2 : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
          Representation.tierLength_tensor i
        omega⟩⟩) := by
  show ((X ⊗ Y).fiberEnum i r).val = _
  rw [Representation.fiberEnum_tensor, OrderIso.trans_apply,
    show Fin.castOrderIso (Representation.tierLength_tensor (X := X) (Y := Y) i) r
      = Fin.natAdd (X.tierLength i) ⟨(r : ℕ) - X.tierLength i, by
          have h1 := r.isLt
          have h2 : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
            Representation.tierLength_tensor i
          omega⟩ from
      Fin.ext (by simpa using (Nat.add_sub_cancel' h).symm),
    Representation.tensorEnum_apply_natAdd]
  rfl

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

@[simp] theorem Representation.tierWord_unit (i : ι) :
    (𝟙_ (Representation (Sigma.fst : ((i : ι) × τ i) → ι))).tierWord i = [] := by
  haveI : IsEmpty ((𝟙_ (Representation (Sigma.fst : ((i : ι) × τ i) → ι))).fiber i) :=
    ⟨fun v => v.val.elim⟩
  rw [Representation.tierWord_eq_ofFn (OrderIso.ofIsEmpty (Fin 0) _)]
  exact List.ofFn_zero

/-- **Tier content is compositional**: the tier word of a realized string is the
    concatenation of its symbols' tier words — [jardine-2019]'s tier projection
    of `g`, and the bridge that places link-free ASL conditions per tier. -/
theorem Representation.tierWord_realize [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
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
theorem realizeHom_ofList [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    realizeHom g₀ (FreeMonoid.ofList w) = toSkeleton (realize g₀ w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [show FreeMonoid.ofList (a :: w) = FreeMonoid.of a * FreeMonoid.ofList w from rfl,
      map_mul, ih, realize_cons]
    exact (CategoryTheory.Skeleton.toSkeleton_tensorObj _ _).symm

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
      _ = _ := by rw [← Representation.tierWord_tensor i]; rfl

end RealizeTierWord

/-! ### Factors and banned-subgraph grammars

[jardine-2017]'s connected-subgraph embedding in position coordinates: a factor
occurs at per-tier offsets when its tier words are windows of the host's and its
links transport shifted. Banned-subgraph grammars ([jardine-2016-diss] Ch. 5)
are lists of forbidden factors. -/

section Factors

variable {ι : Type*} {τ : ι → Type*}
variable (F X : Representation (Sigma.fst : ((i : ι) × τ i) → ι))

/-- Tier-`i` position `p` links to tier-`j` position `q`, in ℕ coordinates
    (out-of-bounds positions link to nothing). -/
def Representation.link [Finite X.obj.V] (i j : ι) (p q : ℕ) : Prop :=
  ∃ (hp : p < X.tierLength i) (hq : q < X.tierLength j), X.linkRel i j ⟨p, hp⟩ ⟨q, hq⟩

open scoped Classical in
/-- The two-tier reading of tiers `i` over `j`: each tier-`j` position's label
    with the tier-`i` labels linked to it, in ascending order — the phonetic
    interpretation of a melody tier over its backbone. -/
noncomputable def Representation.linearize [Finite X.obj.V] (i j : ι) :
    List (τ j × List (τ i)) :=
  (X.tierWord j).zipIdx.map fun bq =>
    (bq.1, ((X.tierWord i).zipIdx.filter fun ap => X.link i j ap.2 bq.2).map (·.1))

/-- `F` occurs in `X` at per-tier offsets `o`: each tier word of `F` is the
    window of `X`'s at `o i`, and `F`'s links transport shifted. -/
def Representation.IsFactorAt [Finite F.obj.V] [Finite X.obj.V] (o : ι → ℕ) : Prop :=
  (∀ i p, p < F.tierLength i → (X.tierWord i)[p + o i]? = (F.tierWord i)[p]?) ∧
    ∀ i j p q, F.link i j p q → X.link i j (p + o i) (q + o j)

/-- `F` **subgraph-embeds** in `X` when some offsets place it as a factor
    ([jardine-2017]'s connected-subgraph embedding). -/
def Representation.FactorEmbeds [Finite F.obj.V] [Finite X.obj.V] : Prop :=
  ∃ o : ι → ℕ, F.IsFactorAt X o

/-- `X` avoids every forbidden factor of a banned-subgraph grammar
    ([jardine-2016-diss] Ch. 5's `L^NL_G`). -/
def Representation.Free [Finite X.obj.V]
    (B : List {F : Representation (Sigma.fst : ((i : ι) × τ i) → ι) // Finite F.obj.V}) :
    Prop :=
  ∀ F ∈ B, haveI := F.property; ¬ F.val.FactorEmbeds X

open scoped MonoidalCategory in
/-- Tensor links are blockwise: within the left factor, or within the right
    factor shifted by the left factor's tier lengths — no cross-factor links. -/
theorem Representation.link_tensor {X Y : Representation (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite X.obj.V] [Finite Y.obj.V] (i j : ι) (p q : ℕ) :
    (X ⊗ Y).link i j p q ↔
      X.link i j p q ∨ X.tierLength i ≤ p ∧ X.tierLength j ≤ q ∧
        Y.link i j (p - X.tierLength i) (q - X.tierLength j) := by
  have h2i : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
    Representation.tierLength_tensor i
  have h2j : (X ⊗ Y).tierLength j = X.tierLength j + Y.tierLength j :=
    Representation.tierLength_tensor j
  constructor
  · rintro ⟨hp, hq, hl⟩
    rw [Representation.linkRel_def] at hl
    rcases lt_or_ge p (X.tierLength i) with hpi | hpi <;>
      rcases lt_or_ge q (X.tierLength j) with hqj | hqj
    · rw [Representation.vertexEquiv_tensor_of_lt (h := hpi),
        Representation.vertexEquiv_tensor_of_lt (h := hqj)] at hl
      exact Or.inl ⟨hpi, hqj, by simpa [Representation.linkRel_def] using hl⟩
    · rw [Representation.vertexEquiv_tensor_of_lt (h := hpi),
        Representation.vertexEquiv_tensor_of_ge (h := hqj)] at hl
      simp at hl
    · rw [Representation.vertexEquiv_tensor_of_ge (h := hpi),
        Representation.vertexEquiv_tensor_of_lt (h := hqj)] at hl
      simp at hl
    · rw [Representation.vertexEquiv_tensor_of_ge (h := hpi),
        Representation.vertexEquiv_tensor_of_ge (h := hqj)] at hl
      exact Or.inr ⟨hpi, hqj, by omega, by omega,
        by simpa [Representation.linkRel_def] using hl⟩
  · rintro (⟨hp, hq, hl⟩ | ⟨hpi, hqj, hp', hq', hl⟩)
    · rw [Representation.linkRel_def] at hl
      refine ⟨by omega, by omega, ?_⟩
      rw [Representation.linkRel_def, Representation.vertexEquiv_tensor_of_lt (h := hp),
        Representation.vertexEquiv_tensor_of_lt (h := hq)]
      simpa using hl
    · rw [Representation.linkRel_def] at hl
      refine ⟨by omega, by omega, ?_⟩
      rw [Representation.linkRel_def,
        Representation.vertexEquiv_tensor_of_ge (h := by omega),
        Representation.vertexEquiv_tensor_of_ge (h := by omega)]
      simpa using hl

end Factors

end Autosegmental
