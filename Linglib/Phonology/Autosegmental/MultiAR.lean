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
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Multi-tier autosegmental graphs and their monoidal category

`MultiGraph τ` is the autosegmental representation at **general tier arity**:
`n` heterogeneously-typed ordered **tiers** (`tiers i : LabeledTuple (τ i)`, with
`τ : Fin n → Type u`) plus, for every ordered tier-pair `(i, j)`, a `Finset (ℕ × ℕ)`
of association **links** (`links i j`; empty ⇒ the pair does not associate). This
renders [jardine-heinz-2015]'s labeled graphs over an `n`-block tier partition
fiberwise, and is the home of [lionnet-2022]'s register-tier tone geometry
(subtonal-feature tiers + a mora tier around a Tonal Root Node hub).

`MultiAR τ` is the category of **in-bounds** multi-tier graphs: an object is a
`MultiGraph τ` whose links are in bounds; a morphism is a family of per-tier
label-preserving position maps (`fT i : LabeledTuple.Hom (A.tiers i) (B.tiers i)`)
that preserves association lines. The monoidal product is morpheme concatenation
(`MultiGraph.concat`, [jardine-heinz-2015]), built via
`MonoidalCategory.ofTensorHom` exactly as the bipartite `AR α β`'s is — the
dependent tiers add only a `funext i` to each coherence proof.

The classical **bipartite** `Graph α β` / `AR α β` (`AR.lean`) is the `n = 2`
case. It stays a *separate first-class structure* (keeping `extends`/`.toGraph`/
anonymous-constructor ergonomics and independent universes); the two are related
by the **monoidal inclusion functor** rather than a defeq view — see
`Inclusion.lean`. The planar full monoidal subcategory (Goldsmith's NCC,
[goldsmith-1976]) would follow `AR.lean`'s `WellFormedAR` pattern via the
per-pair `MultiGraph.IsPlanar`.

## Design

* **Heterogeneous tiers** `τ : Fin n → Type u` — per-tier static typing, fiberwise.
* **Links per ordered tier-pair** `(i j) → Finset (ℕ × ℕ)` — keeps `concat`'s shift
  fiberwise; the associating topology is `{(i,j) | links i j ≠ ∅}`.
* **Planarity stays binary, per pair** (`IsPlanar := ∀ i j, IsNonCrossing (links i j)`):
  the existing `MonovaryOn`-based NCC reused pointwise — no N-ary planarity theory.
-/

namespace Autosegmental

open CategoryTheory MonoidalCategory

universe u

/-- A **multi-tier autosegmental graph**: `n` heterogeneously-typed ordered tiers
    plus a `Finset (ℕ × ℕ)` of association links on each ordered tier-pair. -/
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

/-- **Planarity**: every tier-pair's link set is non-crossing — the binary
    `MonovaryOn` NCC applied pointwise per pair (no N-ary generalization). -/
def IsPlanar (G : MultiGraph τ) : Prop := ∀ i j, IsNonCrossing (G.links i j)

instance (G : MultiGraph τ) : Decidable G.IsPlanar :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- **In-bounds**: every link's endpoints fall within the respective tier lengths. -/
def InBounds (G : MultiGraph τ) : Prop :=
  ∀ i j, ∀ p ∈ G.links i j, p.1 < (G.tiers i).len ∧ p.2 < (G.tiers j).len

instance (G : MultiGraph τ) : Decidable G.InBounds :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-! ### The empty graph -/

/-- The empty multigraph: every tier empty, no links. -/
def empty : MultiGraph τ where
  tiers _ := LabeledTuple.empty
  links _ _ := ∅

@[simp] theorem empty_tiers (i : Fin n) : (empty : MultiGraph τ).tiers i = LabeledTuple.empty := rfl
@[simp] theorem empty_links (i j : Fin n) : (empty : MultiGraph τ).links i j = ∅ := rfl

theorem isPlanar_empty : (empty : MultiGraph τ).IsPlanar := by
  intro i j; simp [empty, isNonCrossing_empty]

theorem inBounds_empty : (empty : MultiGraph τ).InBounds := by
  intro i j p hp; simp at hp

/-! ### Concatenation ([jardine-heinz-2015], fiberwise coproduct) -/

/-- Concatenation: tier-wise `LabeledTuple.concat`, and per-pair link union with
    `B`'s links shifted past `A`'s tier lengths on each coordinate. -/
def concat (A B : MultiGraph τ) : MultiGraph τ where
  tiers i := (A.tiers i).concat (B.tiers i)
  links i j := A.links i j ∪ (B.links i j).image (shiftLink (A.tiers i).len (A.tiers j).len)

@[simp] theorem concat_tiers (A B : MultiGraph τ) (i : Fin n) :
    (A.concat B).tiers i = (A.tiers i).concat (B.tiers i) := rfl

@[simp] theorem concat_links (A B : MultiGraph τ) (i j : Fin n) :
    (A.concat B).links i j =
      A.links i j ∪ (B.links i j).image (shiftLink (A.tiers i).len (A.tiers j).len) := rfl

/-! #### Monoid laws ([jardine-heinz-2015] Theorems 1, 3) -/

theorem empty_concat (A : MultiGraph τ) : empty.concat A = A := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simpa using LabeledTuple.empty_concat (A.tiers i)
  · funext i j; simp [concat_links, empty, shiftLink_zero]

theorem concat_empty (A : MultiGraph τ) : A.concat empty = A := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simpa using LabeledTuple.concat_empty (A.tiers i)
  · funext i j; simp [concat_links, empty]

theorem concat_assoc (A B C : MultiGraph τ) :
    (A.concat B).concat C = A.concat (B.concat C) := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simp only [concat_tiers, LabeledTuple.concat_assoc]
  · funext i j
    simp only [concat_links, concat_tiers, LabeledTuple.concat_len, Finset.image_union,
      Finset.image_image, shiftLink_comp]
    rw [Finset.union_assoc]

/-! #### Predicate preservation -/

/-- Concatenation preserves planarity, given `A.InBounds`. -/
theorem isPlanar_concat {A B : MultiGraph τ} (hAib : A.InBounds)
    (hA : A.IsPlanar) (hB : B.IsPlanar) : (A.concat B).IsPlanar := by
  intro i j
  have hAij := hA i j; have hBij := hB i j; have hAibij := hAib i j
  grind [IsPlanar, IsNonCrossing, InBounds, MonovaryOn, concat_links, Finset.coe_union,
    monovaryOn_union, isNonCrossing_image_shiftLink, shiftLink]

/-- Concatenation preserves in-bounds. -/
theorem inBounds_concat {A B : MultiGraph τ}
    (hA : A.InBounds) (hB : B.InBounds) : (A.concat B).InBounds := by
  intro i j p hp
  simp only [concat_links, Finset.mem_union, Finset.mem_image, concat_tiers,
    LabeledTuple.concat_len] at hp ⊢
  obtain hp | ⟨q, hq, rfl⟩ := hp
  · have := hA i j p hp; omega
  · have := hB i j q hq; simp only [shiftLink]; omega

end MultiGraph

/-! ## The in-bounds object `MultiAR` and its monoidal category -/

variable {n : ℕ} {τ : Fin n → Type u}

/-- An **in-bounds multi-tier autosegmental graph** — the base object. -/
structure MultiAR {n : ℕ} (τ : Fin n → Type u) extends MultiGraph τ where
  inBounds : toMultiGraph.InBounds

namespace MultiAR

/-! ### Morphisms -/

/-- A label- and link-preserving morphism: a family of `LabeledTuple.Hom`s, one per
    tier, plus link preservation routing each link's endpoints through the maps for
    its two tiers. -/
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

/-- Composition (per tier). -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  fT i := (f.fT i).comp (g.fT i)
  links_preserve i j {p q} hp hq h := by
    have hf := f.links_preserve i j hp hq h
    have hg := g.links_preserve i j ((f.fT i).toFun ⟨_, hp⟩).isLt ((f.fT j).toFun ⟨_, hq⟩).isLt hf
    simpa [LabeledTuple.Hom.comp] using hg

@[simp] theorem id_fT (A : MultiAR τ) (i : Fin n) :
    (Hom.id A).fT i = LabeledTuple.Hom.id (A.tiers i) := rfl
@[simp] theorem comp_fT (f : Hom A B) (g : Hom B C) (i : Fin n) :
    (f.comp g).fT i = (f.fT i).comp (g.fT i) := rfl

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

/-- The monoidal product: tier-wise concatenation, preserving in-bounds. -/
def concat (A B : MultiAR τ) : MultiAR τ where
  toMultiGraph := A.toMultiGraph.concat B.toMultiGraph
  inBounds := MultiGraph.inBounds_concat A.inBounds B.inBounds

@[simp] theorem concat_toMultiGraph (A B : MultiAR τ) :
    (A.concat B).toMultiGraph = A.toMultiGraph.concat B.toMultiGraph := rfl

@[simp] theorem concat_tiers (A B : MultiAR τ) (i : Fin n) :
    (A.concat B).tiers i = (A.tiers i).concat (B.tiers i) := rfl

@[simp] theorem concat_links (A B : MultiAR τ) (i j : Fin n) :
    (A.concat B).links i j =
      A.links i j ∪ (B.links i j).image
        (shiftLink (A.tiers i).len (A.tiers j).len) := rfl

/-- The tensor unit. -/
def empty : MultiAR τ where
  toMultiGraph := MultiGraph.empty
  inBounds := MultiGraph.inBounds_empty

/-- An in-bounds graph is determined by its underlying `MultiGraph`. -/
@[ext] theorem ext_toMultiGraph {A B : MultiAR τ} (h : A.toMultiGraph = B.toMultiGraph) :
    A = B := by
  cases A; cases B; simp only at h; subst h; rfl

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

/-- `tensorHom`: per-tier `LabeledTuple.Hom.concatMap`. A link on `(i,j)` routes its
    first endpoint through tier `i`'s map, its second through tier `j`'s map. -/
def concatMap (f : Hom A A') (g : Hom B B') : Hom (A.concat B) (A'.concat B') where
  fT i := LabeledTuple.Hom.concatMap (f.fT i) (g.fT i)
  links_preserve i j {p q} hp hq h := by
    simp only [concat_links, Finset.mem_union, Finset.mem_image, shiftLink,
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
  simp only [concatMap_fT, id_fT, LabeledTuple.Hom.concatMap_id, concat_tiers]

theorem concatMap_comp {A A' A'' B B' B'' : MultiAR τ}
    (f : Hom A A') (f' : Hom A' A'') (g : Hom B B') (g' : Hom B' B'') :
    (concatMap f g).comp (concatMap f' g') = concatMap (f.comp f') (g.comp g') := by
  apply Hom.ext; funext i
  simp only [comp_fT, concatMap_fT]
  exact (LabeledTuple.Hom.concatMap_comp (f.fT i) (f'.fT i) (g.fT i) (g'.fT i)).symm

end Hom

/-! ### `eqToHom` algebra -/

/-- The `i`-th tier map of an `eqToHom`, as a function: a length-cast `Fin.cast`. -/
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

instance : MonoidalCategory (MultiAR τ) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := Hom.concatMap_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => Hom.concatMap_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      apply Hom.ext; funext i; apply LabeledTuple.Hom.ext; funext x; apply Fin.ext
      simp [Fin.appendMap_val, Nat.sub_sub]
      split_ifs <;> omega)
    (leftUnitor_naturality := by
      intro X Y f
      apply Hom.ext; funext i; apply LabeledTuple.Hom.ext; funext x; apply Fin.ext
      simp [Fin.appendMap_val, empty, MultiGraph.empty]
      rfl)
    (rightUnitor_naturality := by
      intro X Y f
      apply Hom.ext; funext i; apply LabeledTuple.Hom.ext; funext x; apply Fin.ext
      simp [Fin.appendMap_val, empty, MultiGraph.empty])
    (pentagon := by intros; simp [eqToHom_trans])
    (triangle := by intros; simp [eqToHom_trans])

end MultiAR

end Autosegmental
