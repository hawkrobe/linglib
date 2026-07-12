/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.RelClasses
import Linglib.Core.CategoryTheory.Monoidal.LabeledTuple
import Linglib.Core.Data.Fin.Tuple.Basic
import Linglib.Phonology.Autosegmental.MixedGraph
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Multi-tier autosegmental graphs and their monoidal category

An autosegmental representation at general tier arity has a family of
heterogeneously-typed ordered tiers, indexed by an arbitrary type, and, for every
ordered tier-pair `(i, j)`, a finite set of association links. This renders
[jardine-heinz-2015]'s labeled graphs over a tier partition fiberwise — their
finite `n`-block partition is the `ι = Fin n` case — and is the home of
[lionnet-2022]'s register-tier tone geometry (subtonal-feature tiers and a mora
tier around a Tonal Root Node hub). This file builds the object, the category of
in-bounds objects, and its concatenation monoidal structure, mirroring the
bipartite `AR.lean` at general arity.

The bipartite `Graph α β` / `AR α β` (`AR.lean`) is the `ι = Fin 2` case, kept
first-class for its `extends`/anonymous-constructor ergonomics and independent
universes; the two are related by `Inclusion.lean`'s monoidal functor `ι` rather
than a defeq view.

## Main definitions

* `MultiGraph τ`: the raw object — tiers `tiers i : LabeledTuple (τ i)` for
  `τ : ι → Type u`, links `links i j : Finset (ℕ × ℕ)` per ordered tier-pair.
* `MultiGraph.IsPlanar` / `MultiGraph.InBounds`: the per-pair No-Crossing
  Constraint and the bounds predicate, decidable over a `Fintype` tier index.
* `MultiGraph.concat` / `MultiGraph.empty`: morpheme concatenation and its unit.
* `MultiAR τ`: the in-bounds object; `MultiAR.Hom` is a family of per-tier
  label-preserving position maps that preserves association lines.
* `MonoidalCategory (MultiAR τ)`: tensor is `concat`, via
  `MonoidalCategory.ofTensorHom` — the dependent tiers add only a `funext i` to
  each of `AR`'s coherence proofs.
* `isNormal` / `MultiAR.Normal`: the orientation-normal form full subcategory
  (links only in the ascending-order bucket, relative to `[LinearOrder ι]`).
* `normalForm`: the functor from `MultiAR.Normal` into the foundational
  `Representation` category, fully faithful (`normalForm.fullyFaithful`).
* `Representation.ofFinite`: the `MultiAR.Normal` object built from a finite
  representation by enumerating each tier fiber; the essential-surjectivity
  witness on the finite-vertex fragment.

## Main results

* `MultiGraph.isPlanar_concat` / `MultiGraph.inBounds_concat`: concatenation
  preserves planarity (given in-bounds) and in-bounds.
* `normalForm.fullyFaithful`: the normal-form embedding of the tiered
  presentation into the labeled-mixed-graph foundation is fully faithful.
* `normalForm.essSurj`: essential surjectivity of `normalForm` on the
  finite-vertex fragment — every finite-vertex `Representation` is isomorphic
  to `normalForm.obj Y` for some `Y : MultiAR.Normal`, packaged with
  `normalForm.fullyFaithful` into an equivalence of the finite-vertex
  subcategories.

## Implementation notes

Links are stored per ordered tier-pair (empty set ⇒ the pair does not associate),
keeping `concat`'s index shift fiberwise; the associating topology is
`{(i, j) | links i j ≠ ∅}`. The tier index is an arbitrary type — none of the
concatenation or categorical theory uses its structure — with `Fintype ι` gating
only the decidability instances; concrete geometries instantiate `ι = Fin n`.
Planarity is per ordered tier-pair — each pair its own
autosegmental plane with crossing defined only within it, the multi-planar model of
[mccarthy-1989]; a cross-plane constraint (two feature tiers non-crossing through a
shared anchor tier) is deliberately inexpressible, declining the common-timeline
tradition of [coleman-local-1991]. The rendering is expressively safe: [oakden-2020]
proves rival tonal geometries (Yip's and Bao's register structures) bi-interpretable,
their arrangement differences notational rather than substantive, and
[jardine-danis-iacoponi-2021] prove Q-theoretic subsegmental representation and
autosegmental association equivalent in expressible constraints.

## TODO

* The planar full monoidal subcategory ([goldsmith-1976]'s NCC as an
  `ObjectProperty.IsMonoidal` over the per-pair `MultiGraph.IsPlanar`) and the
  coproduct universal property (`inl`/`inr`/`coprodDesc`), making the
  `AR`/`MultiAR` pair fully symmetric — both follow `AR.lean`'s pattern.
* Strict-monoidal upgrade: `normalForm` respects `concat` up to a definitional
  isomorphism with `MixedGraphCat.concat`, promoting the fully-faithful
  embedding to a strict monoidal functor (via `Monoidal.transport`).
-/

namespace Autosegmental

open CategoryTheory MonoidalCategory

universe u

/-- A multi-tier autosegmental representation is an indexed family of ordered
    labeled tiers with a finite set of association lines (index pairs) on each
    ordered tier-pair. -/
@[ext]
structure MultiGraph {ι : Type*} (τ : ι → Type u) where
  /-- The heterogeneously-typed ordered tiers. -/
  tiers : (i : ι) → LabeledTuple (τ i)
  /-- Association links per ordered tier-pair; empty ⇒ the pair does not associate. -/
  links : (i j : ι) → Finset (ℕ × ℕ)

namespace MultiGraph

variable {ι : Type*} {τ : ι → Type u}

instance [Fintype ι] [∀ i, DecidableEq (τ i)] : DecidableEq (MultiGraph τ) := fun _ _ =>
  decidable_of_iff _ MultiGraph.ext_iff.symm

/-! ### Well-formedness predicates -/

/-- A multi-tier representation is planar if every tier-pair's link set
    satisfies [goldsmith-1976]'s No-Crossing Constraint. -/
def IsPlanar (G : MultiGraph τ) : Prop := ∀ i j, IsNonCrossing (G.links i j)

instance [Fintype ι] (G : MultiGraph τ) : Decidable G.IsPlanar :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- Every link's indices fall within the respective tier lengths. -/
def InBounds (G : MultiGraph τ) : Prop :=
  ∀ i j, ∀ p ∈ G.links i j, p.1 < (G.tiers i).len ∧ p.2 < (G.tiers j).len

instance [Fintype ι] (G : MultiGraph τ) : Decidable G.InBounds :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-! ### The empty graph -/

/-- The empty multi-tier representation, with every tier empty and no links. -/
def empty : MultiGraph τ where
  tiers _ := LabeledTuple.empty
  links _ _ := ∅

@[simp] theorem tiers_empty (i : ι) : (empty : MultiGraph τ).tiers i = LabeledTuple.empty := rfl
@[simp] theorem links_empty (i j : ι) : (empty : MultiGraph τ).links i j = ∅ := rfl

theorem isPlanar_empty : (empty : MultiGraph τ).IsPlanar := by simp [IsPlanar]

theorem inBounds_empty : (empty : MultiGraph τ).InBounds := by simp [InBounds]

/-! ### Concatenation ([jardine-heinz-2015], fiberwise coproduct) -/

/-- Concatenation concatenates each tier and unions the link sets per pair,
    shifting `B`'s indices past `A`'s tier lengths ([jardine-heinz-2015]). -/
def concat (A B : MultiGraph τ) : MultiGraph τ where
  tiers i := (A.tiers i).concat (B.tiers i)
  links i j := A.links i j ∪ (B.links i j).image (shiftLink (A.tiers i).len (A.tiers j).len)

@[simp] theorem tiers_concat (A B : MultiGraph τ) (i : ι) :
    (A.concat B).tiers i = (A.tiers i).concat (B.tiers i) := rfl

@[simp] theorem links_concat (A B : MultiGraph τ) (i j : ι) :
    (A.concat B).links i j =
      A.links i j ∪ (B.links i j).image (shiftLink (A.tiers i).len (A.tiers j).len) := rfl

/-! #### Monoid laws ([jardine-heinz-2015] Theorems 1, 3) -/

theorem empty_concat (A : MultiGraph τ) : empty.concat A = A := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simpa using LabeledTuple.empty_concat (A.tiers i)
  · funext i j; simp [links_concat, empty, shiftLink_zero]

theorem concat_empty (A : MultiGraph τ) : A.concat empty = A := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simpa using LabeledTuple.concat_empty (A.tiers i)
  · funext i j; simp [links_concat, empty]

theorem concat_assoc (A B C : MultiGraph τ) :
    (A.concat B).concat C = A.concat (B.concat C) := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simp only [tiers_concat, LabeledTuple.concat_assoc]
  · funext i j
    simp only [links_concat, tiers_concat, LabeledTuple.concat_len, Finset.image_union,
      Finset.image_image, shiftLink_comp]
    rw [Finset.union_assoc]

/-! #### Predicate preservation -/

/-- Concatenation preserves planarity, given `A.InBounds`. -/
theorem isPlanar_concat {A B : MultiGraph τ} (hAib : A.InBounds)
    (hA : A.IsPlanar) (hB : B.IsPlanar) : (A.concat B).IsPlanar := by
  intro i j
  grind [IsPlanar, IsNonCrossing, InBounds, MonovaryOn, links_concat, Finset.coe_union,
    monovaryOn_union, isNonCrossing_image_shiftLink, shiftLink]

/-- Concatenation preserves in-bounds. -/
theorem inBounds_concat {A B : MultiGraph τ}
    (hA : A.InBounds) (hB : B.InBounds) : (A.concat B).InBounds := by
  intro i j p hp
  simp only [links_concat, Finset.mem_union, Finset.mem_image, tiers_concat,
    LabeledTuple.concat_len] at hp ⊢
  obtain hp | ⟨q, hq, rfl⟩ := hp
  · have := hA i j p hp; omega
  · have := hB i j q hq; simp only [shiftLink]; omega

end MultiGraph

/-! ## The in-bounds object `MultiAR` and its monoidal category -/

variable {ι : Type*} {τ : ι → Type u}

/-- A multi-tier autosegmental graph whose links are in bounds — the objects of
    the multi-tier autosegmental category. -/
structure MultiAR {ι : Type*} (τ : ι → Type u) extends MultiGraph τ where
  inBounds : toMultiGraph.InBounds

namespace MultiAR

/-! ### Morphisms -/

/-- A morphism of in-bounds multi-tier graphs is a family of label-preserving
    position maps (`LabeledTuple.Hom`s), one per tier, that preserves association
    lines: each link's endpoints route through the maps for its two tiers. -/
@[ext]
structure Hom (A B : MultiAR τ) where
  /-- Per-tier vertex maps. -/
  fT : (i : ι) → LabeledTuple.Hom (A.tiers i) (B.tiers i)
  /-- Association lines are preserved (per tier-pair). -/
  links_preserve : ∀ (i j : ι) {p q : ℕ} (hp : p < (A.tiers i).len) (hq : q < (A.tiers j).len),
    (p, q) ∈ A.links i j → (((fT i).toFun ⟨p, hp⟩ : ℕ), ((fT j).toFun ⟨q, hq⟩ : ℕ)) ∈ B.links i j

namespace Hom
variable {A B C : MultiAR τ}

/-- The identity morphism. -/
def id (A : MultiAR τ) : Hom A A where
  fT i := LabeledTuple.Hom.id (A.tiers i)
  links_preserve _ _ {_ _} _ _ h := h

/-- Composition of morphisms, tier-wise. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  fT i := (f.fT i).comp (g.fT i)
  links_preserve i j {p q} hp hq h := by
    simpa [LabeledTuple.Hom.comp] using
      g.links_preserve i j ((f.fT i).toFun ⟨_, hp⟩).isLt ((f.fT j).toFun ⟨_, hq⟩).isLt
        (f.links_preserve i j hp hq h)

@[simp] theorem id_fT (A : MultiAR τ) (i : ι) :
    (Hom.id A).fT i = LabeledTuple.Hom.id (A.tiers i) := rfl
@[simp] theorem comp_fT (f : Hom A B) (g : Hom B C) (i : ι) :
    (f.comp g).fT i = (f.fT i).comp (g.fT i) := rfl

/-- Morphisms agree if their per-tier maps agree on the underlying `ℕ` indices.
    This collapses the `Hom.ext → LabeledTuple.Hom.ext → funext → Fin.ext` ladder
    used throughout the coherence proofs. -/
theorem ext_fin {f g : Hom A B}
    (h : ∀ (i : ι) (x : Fin (A.tiers i).len),
      ((f.fT i).toFun x : ℕ) = ((g.fT i).toFun x : ℕ)) : f = g :=
  Hom.ext (funext fun i => LabeledTuple.Hom.ext (funext fun x => Fin.ext (h i x)))

end Hom

instance : CategoryStruct (MultiAR τ) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g

instance : Category (MultiAR τ) where
  id_comp _ := by apply Hom.ext; funext i; rfl
  comp_id _ := by apply Hom.ext; funext i; rfl
  assoc _ _ _ := by apply Hom.ext; funext i; rfl

@[simp] theorem id_fT' (A : MultiAR τ) (i : ι) :
    (𝟙 A : Hom A A).fT i = 𝟙 (A.tiers i) := rfl
@[simp] theorem comp_fT' {A B C : MultiAR τ} (f : A ⟶ B) (g : B ⟶ C) (i : ι) :
    (f ≫ g).fT i = (f.fT i).comp (g.fT i) := rfl

/-! ### Concatenation: the tensor object -/

/-- Concatenation of in-bounds multi-tier graphs. -/
def concat (A B : MultiAR τ) : MultiAR τ where
  toMultiGraph := A.toMultiGraph.concat B.toMultiGraph
  inBounds := MultiGraph.inBounds_concat A.inBounds B.inBounds

@[simp] theorem toMultiGraph_concat (A B : MultiAR τ) :
    (A.concat B).toMultiGraph = A.toMultiGraph.concat B.toMultiGraph := rfl

@[simp] theorem tiers_concat (A B : MultiAR τ) (i : ι) :
    (A.concat B).tiers i = (A.tiers i).concat (B.tiers i) := rfl

theorem links_concat (A B : MultiAR τ) (i j : ι) :
    (A.concat B).links i j =
      A.links i j ∪ (B.links i j).image
        (shiftLink (A.tiers i).len (A.tiers j).len) := rfl

/-- The tensor unit. -/
def empty : MultiAR τ where
  toMultiGraph := MultiGraph.empty
  inBounds := MultiGraph.inBounds_empty

@[simp] theorem toMultiGraph_empty :
    (empty : MultiAR τ).toMultiGraph = MultiGraph.empty := rfl

/-- An in-bounds graph is determined by its underlying `MultiGraph`. -/
@[ext] theorem ext_toMultiGraph {A B : MultiAR τ} (h : A.toMultiGraph = B.toMultiGraph) :
    A = B := by
  cases A; cases B; cases h; rfl

theorem toMultiGraph_injective :
    Function.Injective (toMultiGraph : MultiAR τ → MultiGraph τ) :=
  fun _ _ => ext_toMultiGraph

instance [Fintype ι] [∀ i, DecidableEq (τ i)] : DecidableEq (MultiAR τ) := fun _ _ =>
  decidable_of_iff _ ⟨ext_toMultiGraph, congrArg toMultiGraph⟩

instance instMonoid : Monoid (MultiAR τ) where
  mul := concat
  one := empty
  mul_assoc A B C :=
    ext_toMultiGraph (MultiGraph.concat_assoc A.toMultiGraph B.toMultiGraph C.toMultiGraph)
  one_mul A := ext_toMultiGraph (MultiGraph.empty_concat A.toMultiGraph)
  mul_one A := ext_toMultiGraph (MultiGraph.concat_empty A.toMultiGraph)

@[simp] theorem mul_eq_concat (A B : MultiAR τ) : A * B = A.concat B := rfl
@[simp] theorem one_eq_empty : (1 : MultiAR τ) = empty := rfl

/-! ### `tensorHom`: the concatenation bifunctor on morphisms -/

namespace Hom
variable {A A' B B' : MultiAR τ}

/-- The concatenation bifunctor on morphisms (`f ⊗ g`), acting as
    `LabeledTuple.Hom.concatMap` on each tier; a link on `(i, j)` routes its
    endpoints through the maps for tiers `i` and `j`. -/
def concatMap (f : Hom A A') (g : Hom B B') : Hom (A.concat B) (A'.concat B') where
  fT i := LabeledTuple.Hom.concatMap (f.fT i) (g.fT i)
  links_preserve i j {p q} hp hq h := by
    simp only [links_concat, Finset.mem_union, Finset.mem_image, shiftLink,
      Prod.exists, Prod.mk.injEq, LabeledTuple.Hom.concatMap_toFun] at h ⊢
    rcases h with hA | ⟨a, b, hab, hai, hbj⟩
    · obtain ⟨hpi, hqj⟩ := A.inBounds i j (p, q) hA
      left
      rw [Fin.appendMap_val, dif_pos hpi, Fin.appendMap_val, dif_pos hqj]
      exact f.links_preserve i j hpi hqj hA
    · obtain ⟨hau, hbl⟩ := B.inBounds i j (a, b) hab
      subst hai hbj
      right
      refine ⟨((g.fT i).toFun ⟨a, hau⟩ : ℕ), ((g.fT j).toFun ⟨b, hbl⟩ : ℕ),
        g.links_preserve i j hau hbl hab, ?_, ?_⟩
      · rw [Fin.appendMap_val, dif_neg (show ¬ (a + (A.tiers i).len) < (A.tiers i).len by omega)]
        congr 2; apply Fin.ext; simp
      · rw [Fin.appendMap_val, dif_neg (show ¬ (b + (A.tiers j).len) < (A.tiers j).len by omega)]
        congr 2; apply Fin.ext; simp

@[simp] theorem concatMap_fT (f : Hom A A') (g : Hom B B') (i : ι) :
    (concatMap f g).fT i = LabeledTuple.Hom.concatMap (f.fT i) (g.fT i) := rfl

theorem concatMap_id (A B : MultiAR τ) :
    concatMap (Hom.id A) (Hom.id B) = Hom.id (A.concat B) := by
  apply Hom.ext; funext i
  simp only [concatMap_fT, id_fT, LabeledTuple.Hom.concatMap_id, tiers_concat]

theorem concatMap_comp {A A' A'' B B' B'' : MultiAR τ}
    (f : Hom A A') (f' : Hom A' A'') (g : Hom B B') (g' : Hom B' B'') :
    (concatMap f g).comp (concatMap f' g') = concatMap (f.comp f') (g.comp g') := by
  apply Hom.ext; funext i
  simp only [comp_fT, concatMap_fT]
  exact (LabeledTuple.Hom.concatMap_comp (f.fT i) (f'.fT i) (g.fT i) (g'.fT i)).symm

end Hom

/-! ### `eqToHom` algebra -/

/-- The `i`-th tier map of an `eqToHom` is the length-cast `Fin.cast`. -/
@[simp] theorem eqToHom_fT_toFun {A B : MultiAR τ} (h : A = B) (i : ι) :
    ((eqToHom h).fT i).toFun = Fin.cast (congrArg (fun X => (X.tiers i).len) h) := by
  cases h; rfl

@[simp] theorem concatMap_id_eqToHom {W X Y : MultiAR τ} (h : X = Y) :
    Hom.concatMap (𝟙 W) (eqToHom h) = eqToHom (congrArg (W.concat ·) h) := by
  cases h; simp only [eqToHom_refl]; exact Hom.concatMap_id W X

@[simp] theorem concatMap_eqToHom_id {W X Y : MultiAR τ} (h : X = Y) :
    Hom.concatMap (eqToHom h) (𝟙 W) = eqToHom (congrArg (·.concat W) h) := by
  cases h; simp only [eqToHom_refl]; exact Hom.concatMap_id X W

/-! ### Monoidal category -/

@[simps] instance instMonoidalStruct : MonoidalCategoryStruct (MultiAR τ) where
  tensorObj := MultiAR.concat
  tensorUnit := MultiAR.empty
  tensorHom f g := Hom.concatMap f g
  whiskerLeft X _ _ f := Hom.concatMap (Hom.id X) f
  whiskerRight f Y := Hom.concatMap f (Hom.id Y)
  associator A B C := eqToIso (mul_assoc A B C)
  leftUnitor X := eqToIso (one_mul X)
  rightUnitor X := eqToIso (mul_one X)

/-- The monoidal product is the object-monoid multiplication (both are `concat`)
    — the explicit bridge between the categorical `⊗` and the decategorified `*`. -/
@[simp] theorem tensorObj_eq_mul (A B : MultiAR τ) : A ⊗ B = A * B := rfl

instance : MonoidalCategory (MultiAR τ) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := Hom.concatMap_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => Hom.concatMap_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      refine Hom.ext_fin fun i x => ?_
      simp [Fin.appendMap_val, Nat.sub_sub]
      split_ifs <;> omega)
    (leftUnitor_naturality := by
      intro X Y f
      refine Hom.ext_fin fun i x => ?_
      simp [Fin.appendMap_val, empty, MultiGraph.empty]
      rfl)
    (rightUnitor_naturality := by
      intro X Y f
      refine Hom.ext_fin fun i x => ?_
      simp [Fin.appendMap_val, empty, MultiGraph.empty])
    (pentagon := by intros; simp [eqToHom_trans])
    (triangle := by intros; simp [eqToHom_trans])

end MultiAR

/-! ### Interpretation into the labeled mixed graph foundation

The tiered presentation denotes a labeled mixed graph (`MixedGraphCat`,
`MixedGraph.lean`) by construction: vertices are per-tier positions, the alphabet
is the tier-partitioned `Σ i, τ i` with tier assignment `Sigma.fst`, arcs are
within-tier successors, and edges symmetrize the per-pair links. The structural
§4.2 axioms hold as properties of the construction
(`toMixedGraphCat_isTierOrdered`, `toMixedGraphCat_noInternalAssoc`), and the
foundational path-form No-Crossing Constraint agrees with the per-pair `IsPlanar`
exactly on orientation-normalized presentations (`toMixedGraphCat_isPlanar_iff`) —
links between two tiers must be stored in one orientation bucket, since the path
form also sees crossings between an `(i, j)` link and a `(j, i)` link, which the
per-pair check cannot couple. -/

namespace MultiGraph

/-- The labeled mixed graph a tiered presentation denotes: per-tier positions as
    vertices, the within-tier position order as arcs ([jardine-2019]'s reading —
    `A` represents the order, matching `IsTierOrdered`'s path-closure), and
    symmetrized per-pair links as edges. -/
def toMixedGraphCat (M : MultiGraph τ) : MixedGraphCat ((i : ι) × τ i) where
  V := (i : ι) × Fin (M.tiers i).len
  graph :=
    { edges :=
        { Adj := fun v w => v ≠ w ∧
            (((v.2 : ℕ), (w.2 : ℕ)) ∈ M.links v.1 w.1 ∨
              ((w.2 : ℕ), (v.2 : ℕ)) ∈ M.links w.1 v.1)
          symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
          loopless := ⟨fun _ h => h.1 rfl⟩ }
      arcs := ⟨fun v w => v.1 = w.1 ∧ (v.2 : ℕ) < (w.2 : ℕ)⟩ }
  label v := ⟨v.1, (M.tiers v.1).label v.2⟩

variable {M : MultiGraph τ}

@[simp] theorem toMixedGraphCat_tier (v : (i : ι) × Fin (M.tiers i).len) :
    M.toMixedGraphCat.tier Sigma.fst v = v.1 := rfl

/-- Axioms 1–2 hold by construction: the arcs are the tier-internal position
    order, already path-closed. -/
theorem toMixedGraphCat_isTierOrdered :
    IsTierOrdered M.toMixedGraphCat.graph (M.toMixedGraphCat.tier Sigma.fst) := by
  refine ⟨fun v w h => h.1, fun v w hne htier => ?_, fun v h => ?_,
    fun u v w huv hvw => ⟨huv.1.trans hvw.1, by obtain ⟨-, h1⟩ := huv; obtain ⟨-, h2⟩ := hvw; omega⟩⟩
  · obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    obtain rfl : i = j := htier
    rcases Nat.lt_trichotomy (p : ℕ) (q : ℕ) with h | h | h
    · exact Or.inl ⟨rfl, h⟩
    · exact absurd (by simp [Fin.ext h]) hne
    · exact Or.inr ⟨rfl, h⟩
  · obtain ⟨-, h2⟩ := h
    omega

/-- Axiom 3 holds by construction on diagonal-free presentations: edges land
    across tier-pairs, paths stay within a tier. -/
theorem toMixedGraphCat_noInternalAssoc (hdiag : ∀ i, M.links i i = ∅) :
    NoInternalAssoc M.toMixedGraphCat.graph := by
  rintro v w ⟨hne, hmem⟩ harc
  obtain ⟨i, p⟩ := v
  obtain ⟨j, q⟩ := w
  obtain rfl : i = j := harc.1
  rcases hmem with hm | hm <;> simp [hdiag i] at hm

/-- The foundational path-form No-Crossing Constraint agrees with the per-pair
    `IsPlanar` on in-bounds, orientation-normalized presentations (links between
    two tiers stored in one orientation bucket — which also rules out diagonal
    links). Without normalization the path form is strictly stronger: it couples
    an `(i, j)` link with a `(j, i)` link between the same two tiers. -/
theorem toMixedGraphCat_isPlanar_iff (hb : M.InBounds)
    (hor : ∀ i j, M.links i j ≠ ∅ → M.links j i = ∅) :
    Autosegmental.IsPlanar M.toMixedGraphCat.graph ↔ M.IsPlanar := by
  have hdiag : ∀ i, M.links i i = ∅ := fun i => by
    by_contra h
    exact h (hor i i h)
  constructor
  · intro h i j
    rw [isNonCrossing_iff]
    rintro ⟨a, b⟩ h₁ ⟨c, d⟩ h₂ hac
    by_contra hbd
    have hij : i ≠ j := by
      rintro rfl
      simp [hdiag i] at h₁
    obtain ⟨ha, hb'⟩ := hb i j _ h₁
    obtain ⟨hc, hd⟩ := hb i j _ h₂
    exact h (v := ⟨i, ⟨a, ha⟩⟩) (v' := ⟨j, ⟨b, hb'⟩⟩) (w := ⟨i, ⟨c, hc⟩⟩) (w' := ⟨j, ⟨d, hd⟩⟩)
      ⟨by simp [hij], Or.inl h₁⟩ ⟨by simp [hij], Or.inl h₂⟩
      ⟨rfl, hac⟩ ⟨rfl, not_le.mp hbd⟩
  · rintro h v v' w w' ⟨hne₁, hm₁⟩ ⟨hne₂, hm₂⟩ hp hp'
    obtain ⟨i, a⟩ := v
    obtain ⟨j, b⟩ := v'
    obtain ⟨i', c⟩ := w
    obtain ⟨j', d⟩ := w'
    obtain ⟨heq, hac⟩ := hp
    obtain ⟨heq', hdb⟩ := hp'
    obtain rfl : i = i' := heq
    obtain rfl : j = j' := heq'.symm
    rcases hm₁ with hm₁ | hm₁ <;> rcases hm₂ with hm₂ | hm₂
    · exact absurd (isNonCrossing_iff.mp (h i j) _ hm₁ _ hm₂ hac) (by omega)
    · exact absurd hm₂ (by simp [hor i j (Finset.ne_empty_of_mem hm₁)])
    · exact absurd hm₁ (by simp [hor i j (Finset.ne_empty_of_mem hm₂)])
    · exact absurd (isNonCrossing_iff.mp (h j i) _ hm₂ _ hm₁ hdb) (by omega)

end MultiGraph

/-! ### The normal-form functor into the labeled-mixed-graph foundation

Given a `LinearOrder` on the tier index, tiered presentations whose links live
only in the ascending-order bucket per unordered tier-pair embed fully
faithfully into the foundational representation category — this is the
**normal form** for `MultiAR τ` relative to the ambient linear order. The
order canonicalizes an orientation choice `MultiGraph.links` allows and
`MultiGraph.toMixedGraphCat` symmetrizes away: without a normalization, two
tiered graphs storing the same physical link in opposite `(i, j)` vs. `(j, i)`
buckets would carry a foundational identity morphism between their images
that no `MultiAR.Hom` (which is orientation-tracked in `links_preserve`)
realizes. The ordering also subsumes diagonal-freeness — `¬ i < i` forces
`links i i = ∅`, exactly the hypothesis `toMixedGraphCat_noInternalAssoc` needs.

Essential surjectivity and the monoidal upgrade (a strict-monoidal embedding
into `Representation` compatible with `MixedGraphCat.concat`) are follow-ups. -/

section NormalForm

variable [LinearOrder ι]

/-- Orientation-normal form: link storage restricted to the ascending-order
    tier-pair bucket. Includes diagonal-freeness as the `i = j` special case
    (`¬ i < i`), matching `toMixedGraphCat_noInternalAssoc`'s hypothesis. -/
def isNormal : ObjectProperty (MultiAR τ) := fun M => ∀ i j, ¬ i < j → M.links i j = ∅

namespace MultiAR

lemma lt_of_isNormal {M : MultiAR τ} (h : isNormal M) {i j : ι} {p q : ℕ}
    (hmem : (p, q) ∈ M.links i j) : i < j := by
  by_contra hle
  exact Finset.notMem_empty _ (h i j hle ▸ hmem)

lemma diag_empty_of_isNormal {M : MultiAR τ} (h : isNormal M) (i : ι) :
    M.links i i = ∅ :=
  h i i (lt_irrefl i)

/-- The full subcategory of orientation-normalized in-bounds multi-tier graphs
    — the domain of the normal-form functor into `Representation`. -/
abbrev Normal : Type _ := (isNormal (τ := τ)).FullSubcategory

end MultiAR

namespace MultiAR

/-- Forward direction: a per-tier `LabeledTuple.Hom` family gives a
    foundational `MixedGraphCat.Hom` between the images. Source normality
    disambiguates the edge bucket via `i < j`. -/
def toMixedGraphCatHom {A B : MultiAR τ} (hn : isNormal A) (f : Hom A B) :
    MixedGraphCat.Hom A.toMultiGraph.toMixedGraphCat B.toMultiGraph.toMixedGraphCat where
  toFun v := ⟨v.1, (f.fT v.1).toFun v.2⟩
  edge_map := by
    rintro v w ⟨_, hmem⟩
    have h1 : v.1 ≠ w.1 := by
      rcases hmem with hij | hji
      · exact ne_of_lt (lt_of_isNormal hn hij)
      · exact (ne_of_lt (lt_of_isNormal hn hji)).symm
    refine ⟨?_, ?_⟩
    · intro heq
      exact h1 (congrArg (fun (s : (k : ι) × Fin (B.tiers k).len) => s.1) heq)
    · rcases hmem with hij | hji
      · exact Or.inl (f.links_preserve v.1 w.1 v.2.isLt w.2.isLt hij)
      · exact Or.inr (f.links_preserve w.1 v.1 w.2.isLt v.2.isLt hji)
  label_comp v := congrArg (Sigma.mk v.1) (congrFun (f.fT v.1).label_comp v.2)

omit [LinearOrder ι] in
/-- The core existence lemma: label preservation forces `φ` on `⟨i, p⟩` to
    stay in the `i`-tier, and its second component labels `(A.tiers i).label p`. -/
private lemma ofMixedGraphCatHom_exists {A B : MultiAR τ}
    (φ : MixedGraphCat.Hom A.toMultiGraph.toMixedGraphCat B.toMultiGraph.toMixedGraphCat)
    (i : ι) (p : Fin (A.tiers i).len) :
    ∃ q : Fin (B.tiers i).len, φ.toFun ⟨i, p⟩ = ⟨i, q⟩ ∧
      (B.tiers i).label q = (A.tiers i).label p := by
  have hlbl := φ.label_comp ⟨i, p⟩
  generalize hv : φ.toFun ⟨i, p⟩ = v at hlbl ⊢
  obtain ⟨j, q⟩ := v
  have hj : j = i := congrArg (fun (s : (k : ι) × τ k) => s.1) hlbl
  subst hj
  exact ⟨q, rfl, eq_of_heq (Sigma.mk.inj_iff.mp hlbl).2⟩

/-- The per-tier `LabeledTuple.Hom` reconstructed from a foundational morphism. -/
private noncomputable def ofMixedGraphCatHom_fT {A B : MultiAR τ}
    (φ : MixedGraphCat.Hom A.toMultiGraph.toMixedGraphCat B.toMultiGraph.toMixedGraphCat)
    (i : ι) : LabeledTuple.Hom (A.tiers i) (B.tiers i) where
  toFun p := (ofMixedGraphCatHom_exists φ i p).choose
  label_comp := funext fun p => (ofMixedGraphCatHom_exists φ i p).choose_spec.2

omit [LinearOrder ι] in
private lemma ofMixedGraphCatHom_fT_spec {A B : MultiAR τ}
    (φ : MixedGraphCat.Hom A.toMultiGraph.toMixedGraphCat B.toMultiGraph.toMixedGraphCat)
    (i : ι) (p : Fin (A.tiers i).len) :
    φ.toFun ⟨i, p⟩ = ⟨i, (ofMixedGraphCatHom_fT φ i).toFun p⟩ :=
  (ofMixedGraphCatHom_exists φ i p).choose_spec.1

/-- Backward direction as a `MultiAR.Hom`: both source and target normality —
    source to build the edge witness at `i < j`, target to disambiguate the
    image bucket by ruling out the `B.links j i` disjunct. -/
noncomputable def ofMixedGraphCatHom {A B : MultiAR τ}
    (hnA : isNormal A) (hnB : isNormal B)
    (φ : MixedGraphCat.Hom A.toMultiGraph.toMixedGraphCat B.toMultiGraph.toMixedGraphCat) :
    Hom A B where
  fT := ofMixedGraphCatHom_fT φ
  links_preserve i j p q hp hq hmem := by
    have hij : i < j := lt_of_isNormal hnA hmem
    have hne : (⟨i, ⟨p, hp⟩⟩ : (k : ι) × Fin (A.tiers k).len) ≠ ⟨j, ⟨q, hq⟩⟩ := by
      intro heq
      exact (ne_of_lt hij)
        (congrArg (fun (s : (k : ι) × Fin (A.tiers k).len) => s.1) heq)
    have hadj : A.toMultiGraph.toMixedGraphCat.graph.edges.Adj
        ⟨i, ⟨p, hp⟩⟩ ⟨j, ⟨q, hq⟩⟩ := ⟨hne, Or.inl hmem⟩
    have himg := φ.edge_map hadj
    rw [ofMixedGraphCatHom_fT_spec φ i ⟨p, hp⟩,
        ofMixedGraphCatHom_fT_spec φ j ⟨q, hq⟩] at himg
    obtain ⟨_, hmem'⟩ := himg
    rcases hmem' with hij' | hji'
    · exact hij'
    · exact absurd hji' (by simp [hnB j i (not_lt.mpr hij.le)])

end MultiAR

/-! ### The functor and its full faithfulness -/

open CategoryTheory

/-- The normal-form functor from `MultiAR.Normal` into the foundational
    representation category. On objects it takes `X` to `X.toMixedGraphCat`
    with the §4.2 axioms furnished by `toMixedGraphCat_isTierOrdered` and
    `toMixedGraphCat_noInternalAssoc`; on morphisms it lifts a per-tier
    `LabeledTuple.Hom` family through the Sigma vertex encoding. -/
noncomputable def normalForm :
    (isNormal (τ := τ)).FullSubcategory ⥤
      Representation (Sigma.fst : ((i : ι) × τ i) → ι) where
  obj X :=
    ⟨X.obj.toMultiGraph.toMixedGraphCat,
      MultiGraph.toMixedGraphCat_isTierOrdered,
      MultiGraph.toMixedGraphCat_noInternalAssoc (MultiAR.diag_empty_of_isNormal X.property)⟩
  map {X _} f := ObjectProperty.homMk (MultiAR.toMixedGraphCatHom X.property f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply MixedGraphCat.Hom.ext
    funext v
    rcases v with ⟨i, p⟩
    rfl
  map_comp {_ _ _} _ _ := by
    apply ObjectProperty.hom_ext
    apply MixedGraphCat.Hom.ext
    funext v
    rcases v with ⟨i, p⟩
    rfl

/-- `normalForm` is fully faithful: label preservation forces tier
    preservation, so foundational morphisms between image graphs recover
    per-tier `LabeledTuple.Hom` families, and orientation-normality forces
    each preimage link to land in its own storage bucket. -/
noncomputable def normalForm.fullyFaithful : (normalForm (τ := τ)).FullyFaithful where
  preimage {X Y} φ :=
    ObjectProperty.homMk (MultiAR.ofMixedGraphCatHom X.property Y.property φ.hom)
  map_preimage {X Y} φ := by
    apply ObjectProperty.hom_ext
    apply MixedGraphCat.Hom.ext
    funext v
    rcases v with ⟨i, p⟩
    exact (MultiAR.ofMixedGraphCatHom_fT_spec φ.hom i p).symm
  preimage_map {X Y} f := by
    apply ObjectProperty.hom_ext
    show MultiAR.ofMixedGraphCatHom X.property Y.property _ = f.hom
    apply MultiAR.Hom.ext
    funext i
    apply LabeledTuple.Hom.ext
    funext p
    have hspec := MultiAR.ofMixedGraphCatHom_fT_spec
      (MultiAR.toMixedGraphCatHom X.property f.hom) i p
    -- LHS is ⟨i, (f.hom.fT i).toFun p⟩ by rfl; second-components equal via HEq → Eq
    have hheq := (Sigma.mk.inj_iff.mp hspec).2
    exact (eq_of_heq hheq).symm

instance : (normalForm (τ := τ)).Faithful := normalForm.fullyFaithful.faithful

instance : (normalForm (τ := τ)).Full := normalForm.fullyFaithful.full

/-! ### Essential surjectivity on the finite-vertex fragment

Every `Representation` with a `Finite` vertex type is isomorphic to
`normalForm.obj Y` for some orientation-normal `MultiAR`. The construction
enumerates each tier fiber `{v // (X.obj.label v).1 = i}` via
`IsTierOrdered.isStrictTotalOrder` + `linearOrderOfSTO` +
`monoEquivOfFin`, reads off tier labels from the second Sigma component of
the labeling, and records each cross-tier association edge as one link in
the ascending-order bucket per unordered tier-pair. Combined with
`normalForm.fullyFaithful`, this witnesses the finite-vertex subcategories
of `MultiAR.Normal` and `Representation` as equivalent categories.
-/

section EssSurj
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

omit [LinearOrder ι] in
/-- The label of a fiber element decomposes as tier + fiberLabel. -/
theorem Representation.label_fiber {i : ι} (v : X.fiber i) :
    X.obj.label v.val = ⟨i, X.fiberLabel v⟩ := by
  obtain ⟨u, hu⟩ := v
  show X.obj.label u = ⟨i, X.fiberLabel ⟨u, hu⟩⟩
  simp only [Representation.fiberLabel]
  conv_lhs => rw [← Sigma.eta (X.obj.label u)]
  exact Sigma.eq hu rfl

instance Representation.fiber.instFinite [Finite X.obj.V] (i : ι) : Finite (X.fiber i) :=
  Subtype.finite

/-- The arcs restricted to a tier fiber form a strict total order — the classed
    form of Axioms 1–2 applied to the tier coloring `Sigma.fst`. -/
instance Representation.fiber.instIsStrictTotalOrder (i : ι) :
    IsStrictTotalOrder (X.fiber i) (fun a b => X.obj.graph.arcs.Adj a.val b.val) :=
  X.property.1.isStrictTotalOrder i

/-- Classical linear order on the fiber, from `IsStrictTotalOrder` via
    `linearOrderOfSTO`. `noncomputable` because we resolve arc-decidability
    with `Classical.dec`; the essential-surjectivity witness is data-noncomputable
    anyway. -/
noncomputable instance Representation.fiber.instLinearOrder (i : ι) :
    LinearOrder (X.fiber i) := by
  classical
  exact linearOrderOfSTO (fun a b : X.fiber i => X.obj.graph.arcs.Adj a.val b.val)

/-- The tier component of the built `MultiAR` at tier `i`: a length-`n_i`
    `LabeledTuple (τ i)` where `n_i` is the fiber's cardinality, positions
    enumerated by `monoEquivOfFin`, labels read off via `fiberLabel`. -/
noncomputable def Representation.tierAt [Finite X.obj.V] (i : ι) : LabeledTuple (τ i) :=
  letI := Fintype.ofFinite (X.fiber i)
  { len := Fintype.card (X.fiber i)
    label := fun p => X.fiberLabel (monoEquivOfFin (X.fiber i) rfl p) }

omit [LinearOrder ι] in
theorem Representation.tierAt_len [Finite X.obj.V] (i : ι) :
    (X.tierAt i).len = @Fintype.card (X.fiber i) (Fintype.ofFinite _) := rfl

/-- The link storage between tier `i` and tier `j` (only populated when
    `i < j`, matching `isNormal`): all cross-tier association edges in
    `X.obj.graph.edges` between the two fibers, recorded as index pairs
    under the fiber enumeration. -/
noncomputable def Representation.linksAt [Finite X.obj.V] (i j : ι) :
    Finset (ℕ × ℕ) :=
  letI := Fintype.ofFinite (X.fiber i)
  letI := Fintype.ofFinite (X.fiber j)
  if i < j then
    ((Finset.univ (α := X.fiber i × X.fiber j)).filter
      (fun vw => X.obj.graph.edges.Adj vw.1.val vw.2.val)).image
      (fun vw =>
        (((monoEquivOfFin (X.fiber i) rfl).symm vw.1).val,
         ((monoEquivOfFin (X.fiber j) rfl).symm vw.2).val))
  else ∅

/-- The essential-surjectivity witness: a `MultiAR.Normal` object whose image
    under `normalForm` is isomorphic to `X`. -/
noncomputable def Representation.ofFinite [Finite X.obj.V] : MultiAR.Normal (τ := τ) where
  obj :=
    { toMultiGraph :=
        { tiers := fun i => X.tierAt i
          links := fun i j => X.linksAt i j }
      inBounds := by
        intro i j ⟨p, q⟩ hmem
        letI := Fintype.ofFinite (X.fiber i)
        letI := Fintype.ofFinite (X.fiber j)
        simp only [Representation.linksAt] at hmem
        split_ifs at hmem with hij
        · simp only [Finset.mem_image, Finset.mem_filter] at hmem
          obtain ⟨⟨v, w⟩, _, ⟨rfl, rfl⟩⟩ := hmem
          exact ⟨((monoEquivOfFin (X.fiber i) rfl).symm v).isLt,
                 ((monoEquivOfFin (X.fiber j) rfl).symm w).isLt⟩
        · exact absurd hmem (Finset.notMem_empty _)
    }
  property := by
    intro i j hle
    simp only [Representation.linksAt, if_neg hle]

/-- The `MixedGraphCat.Iso` between `X.ofFinite`'s image and `X.obj`: on
    vertices, the fiber-partition + `monoEquivOfFin` composition; on edges,
    arcs and labels, unfolding of `Representation.linksAt`, the fiber
    linear order (`IsTierOrdered.isStrictTotalOrder`), and
    `Representation.label_fiber` respectively. -/
noncomputable def Representation.ofFiniteIso [Finite X.obj.V] :
    MixedGraphCat.Iso (X.ofFinite.obj.toMultiGraph.toMixedGraphCat) X.obj where
  toEquiv :=
    letI : ∀ i : ι, Fintype (X.fiber i) := fun i => Fintype.ofFinite _
    (Equiv.sigmaCongrRight
      (fun i : ι => (monoEquivOfFin (X.fiber i) rfl).toEquiv)).trans
      (Equiv.sigmaFiberEquiv (fun v : X.obj.V => (X.obj.label v).1))
  edges_iff := by
    intro v w
    obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    letI : Fintype (X.fiber i) := Fintype.ofFinite _
    letI : Fintype (X.fiber j) := Fintype.ofFinite _
    show X.obj.graph.edges.Adj (monoEquivOfFin (X.fiber i) rfl p).val
        (monoEquivOfFin (X.fiber j) rfl q).val ↔
      (⟨i, p⟩ : Σ k, Fin (X.tierAt k).len) ≠ ⟨j, q⟩ ∧
      (((p : ℕ), (q : ℕ)) ∈ X.linksAt i j ∨
       ((q : ℕ), (p : ℕ)) ∈ X.linksAt j i)
    constructor
    · intro hadj
      have hne_val : (monoEquivOfFin (X.fiber i) rfl p).val ≠
          (monoEquivOfFin (X.fiber j) rfl q).val := hadj.ne
      have hi : (X.obj.label (monoEquivOfFin (X.fiber i) rfl p).val).1 = i :=
        (monoEquivOfFin (X.fiber i) rfl p).property
      have hj : (X.obj.label (monoEquivOfFin (X.fiber j) rfl q).val).1 = j :=
        (monoEquivOfFin (X.fiber j) rfl q).property
      have hij_ne : i ≠ j := by
        intro heq
        subst heq
        rcases X.property.1.total hne_val (hi.trans hj.symm) with harc | harc
        exacts [X.property.2 hadj harc, X.property.2 hadj.symm harc]
      refine ⟨?_, ?_⟩
      · intro hveq
        exact hij_ne (Sigma.mk.injEq _ _ _ _ |>.mp hveq).1
      · rcases lt_trichotomy i j with hij_lt | hij_eq | hij_lt
        · left
          show ((p : ℕ), (q : ℕ)) ∈ X.linksAt i j
          simp only [Representation.linksAt, if_pos hij_lt, Finset.mem_image,
            Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨(monoEquivOfFin (X.fiber i) rfl p, monoEquivOfFin (X.fiber j) rfl q),
                  hadj, ?_⟩
          simp [OrderIso.symm_apply_apply]
        · exact absurd hij_eq hij_ne
        · right
          show ((q : ℕ), (p : ℕ)) ∈ X.linksAt j i
          simp only [Representation.linksAt, if_pos hij_lt, Finset.mem_image,
            Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨(monoEquivOfFin (X.fiber j) rfl q, monoEquivOfFin (X.fiber i) rfl p),
                  hadj.symm, ?_⟩
          simp [OrderIso.symm_apply_apply]
    · rintro ⟨_, hmem⟩
      rcases hmem with hij | hji
      · simp only [Representation.linksAt] at hij
        split_ifs at hij with hlt
        · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and] at hij
          obtain ⟨⟨a, b⟩, hab, heq⟩ := hij
          obtain ⟨hpa, hqb⟩ := Prod.mk.injEq _ _ _ _ |>.mp heq
          have ha : a = monoEquivOfFin (X.fiber i) rfl p := by
            have h₁ : monoEquivOfFin (X.fiber i) rfl
                ((monoEquivOfFin (X.fiber i) rfl).symm a) =
                monoEquivOfFin (X.fiber i) rfl p := congrArg _ (Fin.ext hpa)
            rwa [OrderIso.apply_symm_apply] at h₁
          have hb : b = monoEquivOfFin (X.fiber j) rfl q := by
            have h₁ : monoEquivOfFin (X.fiber j) rfl
                ((monoEquivOfFin (X.fiber j) rfl).symm b) =
                monoEquivOfFin (X.fiber j) rfl q := congrArg _ (Fin.ext hqb)
            rwa [OrderIso.apply_symm_apply] at h₁
          rw [ha, hb] at hab
          exact hab
        · exact absurd hij (Finset.notMem_empty _)
      · simp only [Representation.linksAt] at hji
        split_ifs at hji with hlt
        · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and] at hji
          obtain ⟨⟨a, b⟩, hab, heq⟩ := hji
          obtain ⟨hqa, hpb⟩ := Prod.mk.injEq _ _ _ _ |>.mp heq
          have ha : a = monoEquivOfFin (X.fiber j) rfl q := by
            have h₁ : monoEquivOfFin (X.fiber j) rfl
                ((monoEquivOfFin (X.fiber j) rfl).symm a) =
                monoEquivOfFin (X.fiber j) rfl q := congrArg _ (Fin.ext hqa)
            rwa [OrderIso.apply_symm_apply] at h₁
          have hb : b = monoEquivOfFin (X.fiber i) rfl p := by
            have h₁ : monoEquivOfFin (X.fiber i) rfl
                ((monoEquivOfFin (X.fiber i) rfl).symm b) =
                monoEquivOfFin (X.fiber i) rfl p := congrArg _ (Fin.ext hpb)
            rwa [OrderIso.apply_symm_apply] at h₁
          rw [ha, hb] at hab
          exact hab.symm
        · exact absurd hji (Finset.notMem_empty _)
  arcs_iff := by
    intro v w
    obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    letI : Fintype (X.fiber i) := Fintype.ofFinite _
    letI : Fintype (X.fiber j) := Fintype.ofFinite _
    show X.obj.graph.arcs.Adj (monoEquivOfFin (X.fiber i) rfl p).val
        (monoEquivOfFin (X.fiber j) rfl q).val ↔ i = j ∧ (p : ℕ) < (q : ℕ)
    constructor
    · intro h
      have htier := X.property.1.tier_eq h
      have hi : (X.obj.label (monoEquivOfFin (X.fiber i) rfl p).val).1 = i :=
        (monoEquivOfFin (X.fiber i) rfl p).property
      have hj : (X.obj.label (monoEquivOfFin (X.fiber j) rfl q).val).1 = j :=
        (monoEquivOfFin (X.fiber j) rfl q).property
      have hij : i = j := hi.symm.trans (htier.trans hj)
      refine ⟨hij, ?_⟩
      subst hij
      -- goal: (p : ℕ) < (q : ℕ)
      -- On the fiber LinearOrder, arcs.Adj (mono p).val (mono q).val = mono p < mono q
      -- and mono is OrderIso so mono p < mono q ↔ p < q
      have hlt : (monoEquivOfFin (X.fiber i) rfl p) < (monoEquivOfFin (X.fiber i) rfl q) := by
        change X.obj.graph.arcs.Adj _ _
        exact h
      exact (monoEquivOfFin (X.fiber i) rfl).lt_iff_lt.mp hlt
    · rintro ⟨rfl, hlt⟩
      have hlt' : (p : Fin _) < (q : Fin _) := hlt
      have : (monoEquivOfFin (X.fiber i) rfl p) < (monoEquivOfFin (X.fiber i) rfl q) :=
        (monoEquivOfFin (X.fiber i) rfl).lt_iff_lt.mpr hlt'
      exact this
  label_comp := by
    intro v
    obtain ⟨i, p⟩ := v
    letI : Fintype (X.fiber i) := Fintype.ofFinite _
    show X.obj.label ((monoEquivOfFin (X.fiber i) rfl p) : X.fiber i).val =
      ⟨i, (X.tierAt i).label p⟩
    rw [X.label_fiber]
    rfl

/-- **Essential surjectivity of `normalForm` on the finite-vertex fragment.**
    For every finite-vertex representation there is an orientation-normal
    `MultiAR` whose image is isomorphic to it. -/
theorem normalForm.essSurj (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι))
    [Finite X.obj.V] :
    ∃ Y : MultiAR.Normal, Nonempty (normalForm.obj Y ≅ X) :=
  ⟨X.ofFinite, ⟨Representation.mkIso X.ofFiniteIso⟩⟩

-- TODO(equivalence): once `normalForm.essSurj` is discharged, package
-- `Functor.EssSurj normalForm` (restricted to the finite-vertex subcategory
-- on both sides) with `normalForm.fullyFaithful` into an `IsEquivalence`
-- instance — the "packaged equivalence" side of task #6. The `Full`,
-- `Faithful` instances above transfer to the restriction automatically.

end EssSurj

end NormalForm

end Autosegmental
