/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Linglib.Core.CategoryTheory.Monoidal.LabeledTuple
import Linglib.Core.Data.Fin.Tuple.Basic
import Linglib.Phonology.Autosegmental.MixedGraph
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Multi-tier autosegmental graphs and their monoidal category

An autosegmental representation at general tier arity has `n` heterogeneously-typed
ordered tiers and, for every ordered tier-pair `(i, j)`, a finite set of association
links. This renders [jardine-heinz-2015]'s labeled graphs over an `n`-block tier
partition fiberwise, and is the home of [lionnet-2022]'s register-tier tone geometry
(subtonal-feature tiers and a mora tier around a Tonal Root Node hub). This file
builds the object, the category of in-bounds objects, and its concatenation monoidal
structure, mirroring the bipartite `AR.lean` at arity `n`.

The bipartite `Graph α β` / `AR α β` (`AR.lean`) is the `n = 2` case, kept
first-class for its `extends`/anonymous-constructor ergonomics and independent
universes; the two are related by `Inclusion.lean`'s monoidal functor `ι` rather
than a defeq view.

## Main definitions

* `MultiGraph τ`: the raw object — tiers `tiers i : LabeledTuple (τ i)` for
  `τ : Fin n → Type u`, links `links i j : Finset (ℕ × ℕ)` per ordered tier-pair.
* `MultiGraph.IsPlanar` / `MultiGraph.InBounds`: the per-pair No-Crossing
  Constraint and the bounds predicate, both decidable.
* `MultiGraph.concat` / `MultiGraph.empty`: morpheme concatenation and its unit.
* `MultiAR τ`: the in-bounds object; `MultiAR.Hom` is a family of per-tier
  label-preserving position maps that preserves association lines.
* `MonoidalCategory (MultiAR τ)`: tensor is `concat`, via
  `MonoidalCategory.ofTensorHom` — the dependent tiers add only a `funext i` to
  each of `AR`'s coherence proofs.

## Main results

* `MultiGraph.isPlanar_concat` / `MultiGraph.inBounds_concat`: concatenation
  preserves planarity (given in-bounds) and in-bounds.

## Implementation notes

Links are stored per ordered tier-pair (empty set ⇒ the pair does not associate),
keeping `concat`'s index shift fiberwise; the associating topology is
`{(i, j) | links i j ≠ ∅}`. Planarity is per ordered tier-pair — each pair its own
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
-/

namespace Autosegmental

open CategoryTheory MonoidalCategory

universe u

/-- A multi-tier autosegmental representation is a family of `n` ordered labeled
    tiers with a finite set of association lines (index pairs) on each ordered
    tier-pair. -/
@[ext]
structure MultiGraph {n : ℕ} (τ : Fin n → Type u) where
  /-- The `n` heterogeneously-typed ordered tiers. -/
  tiers : (i : Fin n) → LabeledTuple (τ i)
  /-- Association links per ordered tier-pair; empty ⇒ the pair does not associate. -/
  links : (i j : Fin n) → Finset (ℕ × ℕ)

namespace MultiGraph

variable {n : ℕ} {τ : Fin n → Type u}

instance [∀ i, DecidableEq (τ i)] : DecidableEq (MultiGraph τ) := fun _ _ =>
  decidable_of_iff _ MultiGraph.ext_iff.symm

/-! ### Well-formedness predicates -/

/-- A multi-tier representation is planar if every tier-pair's link set
    satisfies [goldsmith-1976]'s No-Crossing Constraint. -/
def IsPlanar (G : MultiGraph τ) : Prop := ∀ i j, IsNonCrossing (G.links i j)

instance (G : MultiGraph τ) : Decidable G.IsPlanar :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- Every link's indices fall within the respective tier lengths. -/
def InBounds (G : MultiGraph τ) : Prop :=
  ∀ i j, ∀ p ∈ G.links i j, p.1 < (G.tiers i).len ∧ p.2 < (G.tiers j).len

instance (G : MultiGraph τ) : Decidable G.InBounds :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-! ### The empty graph -/

/-- The empty multi-tier representation, with every tier empty and no links. -/
def empty : MultiGraph τ where
  tiers _ := LabeledTuple.empty
  links _ _ := ∅

@[simp] theorem tiers_empty (i : Fin n) : (empty : MultiGraph τ).tiers i = LabeledTuple.empty := rfl
@[simp] theorem links_empty (i j : Fin n) : (empty : MultiGraph τ).links i j = ∅ := rfl

theorem isPlanar_empty : (empty : MultiGraph τ).IsPlanar := by simp [IsPlanar]

theorem inBounds_empty : (empty : MultiGraph τ).InBounds := by simp [InBounds]

/-! ### Concatenation ([jardine-heinz-2015], fiberwise coproduct) -/

/-- Concatenation concatenates each tier and unions the link sets per pair,
    shifting `B`'s indices past `A`'s tier lengths ([jardine-heinz-2015]). -/
def concat (A B : MultiGraph τ) : MultiGraph τ where
  tiers i := (A.tiers i).concat (B.tiers i)
  links i j := A.links i j ∪ (B.links i j).image (shiftLink (A.tiers i).len (A.tiers j).len)

@[simp] theorem tiers_concat (A B : MultiGraph τ) (i : Fin n) :
    (A.concat B).tiers i = (A.tiers i).concat (B.tiers i) := rfl

@[simp] theorem links_concat (A B : MultiGraph τ) (i j : Fin n) :
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

variable {n : ℕ} {τ : Fin n → Type u}

/-- A multi-tier autosegmental graph whose links are in bounds — the objects of
    the multi-tier autosegmental category. -/
structure MultiAR {n : ℕ} (τ : Fin n → Type u) extends MultiGraph τ where
  inBounds : toMultiGraph.InBounds

namespace MultiAR

/-! ### Morphisms -/

/-- A morphism of in-bounds multi-tier graphs is a family of label-preserving
    position maps (`LabeledTuple.Hom`s), one per tier, that preserves association
    lines: each link's endpoints route through the maps for its two tiers. -/
@[ext]
structure Hom (A B : MultiAR τ) where
  /-- Per-tier vertex maps. -/
  fT : (i : Fin n) → LabeledTuple.Hom (A.tiers i) (B.tiers i)
  /-- Association lines are preserved (per tier-pair). -/
  links_preserve : ∀ (i j : Fin n) {p q : ℕ} (hp : p < (A.tiers i).len) (hq : q < (A.tiers j).len),
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

@[simp] theorem id_fT (A : MultiAR τ) (i : Fin n) :
    (Hom.id A).fT i = LabeledTuple.Hom.id (A.tiers i) := rfl
@[simp] theorem comp_fT (f : Hom A B) (g : Hom B C) (i : Fin n) :
    (f.comp g).fT i = (f.fT i).comp (g.fT i) := rfl

/-- Morphisms agree if their per-tier maps agree on the underlying `ℕ` indices.
    This collapses the `Hom.ext → LabeledTuple.Hom.ext → funext → Fin.ext` ladder
    used throughout the coherence proofs. -/
theorem ext_fin {f g : Hom A B}
    (h : ∀ (i : Fin n) (x : Fin (A.tiers i).len),
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

@[simp] theorem id_fT' (A : MultiAR τ) (i : Fin n) :
    (𝟙 A : Hom A A).fT i = 𝟙 (A.tiers i) := rfl
@[simp] theorem comp_fT' {A B C : MultiAR τ} (f : A ⟶ B) (g : B ⟶ C) (i : Fin n) :
    (f ≫ g).fT i = (f.fT i).comp (g.fT i) := rfl

/-! ### Concatenation: the tensor object -/

/-- Concatenation of in-bounds multi-tier graphs. -/
def concat (A B : MultiAR τ) : MultiAR τ where
  toMultiGraph := A.toMultiGraph.concat B.toMultiGraph
  inBounds := MultiGraph.inBounds_concat A.inBounds B.inBounds

@[simp] theorem toMultiGraph_concat (A B : MultiAR τ) :
    (A.concat B).toMultiGraph = A.toMultiGraph.concat B.toMultiGraph := rfl

@[simp] theorem tiers_concat (A B : MultiAR τ) (i : Fin n) :
    (A.concat B).tiers i = (A.tiers i).concat (B.tiers i) := rfl

theorem links_concat (A B : MultiAR τ) (i j : Fin n) :
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

instance [∀ i, DecidableEq (τ i)] : DecidableEq (MultiAR τ) := fun _ _ =>
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

@[simp] theorem concatMap_fT (f : Hom A A') (g : Hom B B') (i : Fin n) :
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
@[simp] theorem eqToHom_fT_toFun {A B : MultiAR τ} (h : A = B) (i : Fin n) :
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

The tiered presentation denotes a labeled mixed graph (`MixedGraph.lean`) by
construction: vertices are per-tier positions, the alphabet is the
tier-partitioned `Σ i, τ i` with tier assignment `Sigma.fst`, arcs are within-tier
successors, and edges symmetrize the per-pair links. The structural §4.2 axioms
hold as properties of the construction (`toMixedGraph_isTierOrdered`,
`toMixedGraph_noInternalAssoc`), and the foundational path-form No-Crossing
Constraint agrees with the per-pair `IsPlanar` exactly on orientation-normalized
presentations (`toMixedGraph_isPlanar_iff`) — links between two tiers must be
stored in one orientation bucket, since the path form also sees crossings between
an `(i, j)` link and a `(j, i)` link, which the per-pair check cannot couple. -/

namespace MultiGraph

/-- The labeled mixed graph a tiered presentation denotes: per-tier positions as
    vertices, within-tier successor arcs, symmetrized per-pair links as edges. -/
def toMixedGraph (M : MultiGraph τ) :
    MixedGraph ((i : Fin n) × Fin (M.tiers i).len) ((i : Fin n) × τ i) where
  edges :=
    { Adj := fun v w => v ≠ w ∧
        (((v.2 : ℕ), (w.2 : ℕ)) ∈ M.links v.1 w.1 ∨ ((w.2 : ℕ), (v.2 : ℕ)) ∈ M.links w.1 v.1)
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  arcs := ⟨fun v w => v.1 = w.1 ∧ (v.2 : ℕ) + 1 = (w.2 : ℕ)⟩
  label v := ⟨v.1, (M.tiers v.1).label v.2⟩

variable {M : MultiGraph τ}

@[simp] theorem toMixedGraph_tier (v : (i : Fin n) × Fin (M.tiers i).len) :
    M.toMixedGraph.tier Sigma.fst v = v.1 := rfl

/-- Precedence paths in the interpretation are exactly same-tier position order. -/
theorem toMixedGraph_precPath {v w : (i : Fin n) × Fin (M.tiers i).len} :
    M.toMixedGraph.PrecPath v w ↔ v.1 = w.1 ∧ (v.2 : ℕ) < (w.2 : ℕ) := by
  constructor
  · intro h
    induction h with
    | single h => obtain ⟨h1, h2⟩ := h; exact ⟨h1, by omega⟩
    | tail _ h ih =>
        obtain ⟨ih1, ih2⟩ := ih; obtain ⟨h1, h2⟩ := h
        exact ⟨ih1.trans h1, by omega⟩
  · obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    rintro ⟨(rfl : i = j), hlt⟩
    dsimp only at hlt
    obtain ⟨d, hd⟩ : ∃ d, (p : ℕ) + d + 1 = (q : ℕ) := ⟨(q : ℕ) - (p : ℕ) - 1, by omega⟩
    clear hlt
    induction d generalizing q with
    | zero => exact .single ⟨rfl, hd⟩
    | succ d ih =>
        have hm : (p : ℕ) + d + 1 < (M.tiers i).len := by have := q.isLt; omega
        exact .tail (ih ⟨(p : ℕ) + d + 1, hm⟩ rfl) ⟨rfl, by omega⟩

/-- Axioms 1–2 hold by construction: successor arcs are tier-internal chains. -/
theorem toMixedGraph_isTierOrdered : M.toMixedGraph.IsTierOrdered Sigma.fst := by
  refine ⟨fun v w h => h.1, fun v w hne htier => ?_, fun v h => ?_⟩
  · obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    obtain rfl : i = j := htier
    rcases Nat.lt_trichotomy (p : ℕ) (q : ℕ) with h | h | h
    · exact Or.inl (toMixedGraph_precPath.mpr ⟨rfl, h⟩)
    · exact absurd (by simp [Fin.ext h]) hne
    · exact Or.inr (toMixedGraph_precPath.mpr ⟨rfl, h⟩)
  · rw [toMixedGraph_precPath] at h
    omega

/-- Axiom 3 holds by construction on diagonal-free presentations: edges land
    across tier-pairs, paths stay within a tier. -/
theorem toMixedGraph_noInternalAssoc (hdiag : ∀ i, M.links i i = ∅) :
    M.toMixedGraph.NoInternalAssoc := by
  rintro v w ⟨hne, hmem⟩ hpath
  rw [toMixedGraph_precPath] at hpath
  obtain ⟨i, p⟩ := v
  obtain ⟨j, q⟩ := w
  obtain rfl : i = j := hpath.1
  rcases hmem with hm | hm <;> simp [hdiag i] at hm

/-- The foundational path-form No-Crossing Constraint agrees with the per-pair
    `IsPlanar` on in-bounds, orientation-normalized presentations (links between
    two tiers stored in one orientation bucket — which also rules out diagonal
    links). Without normalization the path form is strictly stronger: it couples
    an `(i, j)` link with a `(j, i)` link between the same two tiers. -/
theorem toMixedGraph_isPlanar_iff (hb : M.InBounds)
    (hor : ∀ i j, M.links i j ≠ ∅ → M.links j i = ∅) :
    M.toMixedGraph.IsPlanar ↔ M.IsPlanar := by
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
      (toMixedGraph_precPath.mpr ⟨rfl, hac⟩)
      (toMixedGraph_precPath.mpr ⟨rfl, not_le.mp hbd⟩)
  · rintro h v v' w w' ⟨hne₁, hm₁⟩ ⟨hne₂, hm₂⟩ hp hp'
    rw [toMixedGraph_precPath] at hp hp'
    obtain ⟨i, a⟩ := v
    obtain ⟨j, b⟩ := v'
    obtain ⟨i', c⟩ := w
    obtain ⟨j', d⟩ := w'
    obtain rfl : i = i' := hp.1
    obtain rfl : j = j' := hp'.1.symm
    have hac : (a : ℕ) < (c : ℕ) := hp.2
    have hdb : (d : ℕ) < (b : ℕ) := hp'.2
    rcases hm₁ with hm₁ | hm₁ <;> rcases hm₂ with hm₂ | hm₂
    · exact absurd (isNonCrossing_iff.mp (h i j) _ hm₁ _ hm₂ hac) (by omega)
    · exact absurd hm₂ (by simp [hor i j (Finset.ne_empty_of_mem hm₁)])
    · exact absurd hm₁ (by simp [hor i j (Finset.ne_empty_of_mem hm₂)])
    · exact absurd (isNonCrossing_iff.mp (h j i) _ hm₂ _ hm₁ hdb) (by omega)

end MultiGraph

end Autosegmental
