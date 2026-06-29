/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Linglib.Core.CategoryTheory.Monoidal.LabeledTuple
import Linglib.Core.Data.Fin.Tuple.Basic
import Linglib.Phonology.Autosegmental.NonCrossing
import Linglib.Phonology.OCP

/-!
# The monoidal category of autosegmental representations

An **autosegmental representation** (APR; [goldsmith-1976]) of a word is a finite
labeled bipartite graph: an `upper` tier of `α`s (the melody — tones, features), a
`lower` tier of `β`s (the timing/segmental backbone), and a finite set of
**association lines** between their positions. This file builds the object, its
concatenation monoidal category, and the well-formed (planar) subcategory cut out
by the No-Crossing Constraint, following [jardine-heinz-2015].

The arc, in three layers:

* `Graph α β` — the bipartite object. Planarity `IsPlanar` is [goldsmith-1976]'s
  No-Crossing Constraint ([jardine-heinz-2015] Axiom 4) — the sole *structural*
  well-formedness condition ([pulleyblank-1986]); saturation (Goldsmith's original
  WFC) is language-particular, so floating elements are well-formed.
* `AR α β` — the **in-bounds** object (every association line falls within the tier
  lengths) and the base of the category; morphisms are label- and link-preserving
  position maps. `concat` is morpheme concatenation ([jardine-heinz-2015] §5): the
  empty graph is the unit (Theorem 1) and `concat` is associative (Theorem 3). The
  paper calls it "a modification of [the] disjoint union"; its disjoint-union core —
  before the OCP-merging step, modeled separately as `OCP.collapse` — is the
  **categorical coproduct** (`HasBinaryCoproducts`), so the monoidal product is
  cocartesian.
* `WellFormedAR α β` — the full monoidal subcategory of planar ARs. The No-Crossing
  Constraint is **morpheme-modular** (`ncc_isMonoidal`, [jardine-heinz-2015]
  Theorem 4): planarity is stable under `⊗`. The OCP ([mccarthy-1986]) is **not**
  (`ocp_not_isMonoidal`, Axiom 5) — concatenation can abut identical autosegments
  across a morpheme boundary — so it drives a boundary repair (`OCP.collapse`).

## Main definitions

* `Graph` / `AR` / `WellFormedAR` — the three layers of the autosegmental object.
* `Graph.IsPlanar` — the No-Crossing Constraint, via the `MonovaryOn`-based
  `NonCrossing` substrate.
* `AR.concat` / `AR.empty` — concatenation and its unit; `HasBinaryCoproduct`
  exhibits `concat` as the categorical coproduct, `empty` as the initial object.
* `MonoidalCategory (AR α β)` / `MonoidalCategory (WellFormedAR α β)`.

## Main results

* `Graph.isPlanar_concat` — concatenation preserves planarity ([jardine-heinz-2015]
  Theorem 4).
* `ncc_isMonoidal` / `ocp_not_isMonoidal` — the NCC is morpheme-modular, the OCP is
  not; `ncc_modular_ocp_not` is the discriminating dichotomy.
* `collapse_repairs_boundary` — fusion restores OCP-cleanness across a boundary.

## Categorical recognition

`AR α β` is the **Grothendieck construction** `∫ F` of the relation functor
`F : (LabeledTuple α × LabeledTuple β) ⥤ Cat` sending a tier-pair `(U, V)` to the
`⊆`-poset of relations `Finset (Fin U.len × Fin V.len)` and a position-map pair to
image-pushforward. An object is `(tiers, relation)`; the Grothendieck fiber morphism
— a `≤` in the thin poset fiber — is exactly `Hom.links_preserve` (`image ⊆ target`).
So `AR` is the category of **labeled finite bipartite graphs**, and `concat`/`empty`
are the coproduct/initial object it carries as such.

This is realized **concretely**, not via `CategoryTheory.Grothendieck`: the literal
construction inherits only the bare `Category` (recorded here anyway as `HasInitial`
and `HasBinaryCoproduct`), forces the `Fin (m + n)` length-casts that the raw-`ℕ`
`NonCrossing` substrate and the `omega`-based consumers (`Floating`, `LaoideKemp2026`)
are built to avoid, and leaves the monoidal/coproduct layer hand-built regardless —
mathlib has neither a monoidal Grothendieck construction nor a cocartesian
`ofChosenFiniteCoproducts` builder (both upstream TODOs). The choice mirrors
`LabeledTuple`'s and `SimplexCategory`'s `Fin`-skeleton: state the universal
properties as theorems, and keep a definitional `tensorObj := concat` for the
`decide`/`prop_tensor`/`eqToIso`-coherence consumers.

## Implementation notes

Tiers are `LabeledTuple`s; `links : Finset (ℕ × ℕ)` keeps raw natural-number
indexing — matching the `MonovaryOn`-based `NonCrossing` substrate and keeping the
monoid laws free of dependent-type casts — with in-bounds a separable `Prop`
(`Graph.InBounds`) rather than a structural invariant. Because the object-`Monoid`
laws hold as strict equalities, the associator and unitors are `eqToIso` of
`mul_assoc`/`one_mul`/`mul_one`, so `AR` is strict monoidal over its object-monoid.
-/

namespace Autosegmental
open scoped CategoryTheory

/-! ## The autosegmental graph (the bipartite object) -/

/-- A bipartite autosegmental representation: two ordered labeled tiers and a
    finite set of association lines (index pairs) between them. -/
@[ext]
structure Graph (α β : Type*) where
  /-- The upper tier (e.g., tonal tier, melodic tier, root). -/
  upper : LabeledTuple α
  /-- The lower tier (e.g., segmental backbone, skeleton, template). -/
  lower : LabeledTuple β
  /-- Association lines as a finite set of index pairs
      `(upper-index, lower-index)`. -/
  links : Finset (ℕ × ℕ)
  deriving DecidableEq

namespace Graph

variable {α β : Type*} (r : Graph α β)

/-! ### Construction -/

/-- The empty bipartite representation with no tiers and no links. -/
def empty : Graph α β := ⟨LabeledTuple.empty, LabeledTuple.empty, ∅⟩

/-! ### Planarity (no-crossing) -/

/-- **Planar** (no-crossing): the link set satisfies [goldsmith-1976]'s NCC. -/
def IsPlanar : Prop := IsNonCrossing r.links

/-! ### Index predicates -/

/-- Upper index `i` is **linked** to some lower position (no in-bounds check). -/
def IsLinkedUpper (i : ℕ) : Prop :=
  ∃ p ∈ r.links, p.fst = i

/-- Lower index `j` is **linked** to some upper position (no in-bounds check). -/
def IsLinkedLower (j : ℕ) : Prop :=
  ∃ p ∈ r.links, p.snd = j

/-- Upper index `i` is **floating**: in-bounds but unlinked. -/
def IsFloatingUpper (i : ℕ) : Prop :=
  i < r.upper.len ∧ ¬ r.IsLinkedUpper i

/-- Lower index `j` is **floating**: in-bounds but unlinked (*segmentally empty*). -/
def IsFloatingLower (j : ℕ) : Prop :=
  j < r.lower.len ∧ ¬ r.IsLinkedLower j

/-! ### Decidability of index predicates -/

instance (i : ℕ) : Decidable (r.IsLinkedUpper i) :=
  inferInstanceAs (Decidable (∃ p ∈ r.links, p.fst = i))

instance (j : ℕ) : Decidable (r.IsLinkedLower j) :=
  inferInstanceAs (Decidable (∃ p ∈ r.links, p.snd = j))

instance (i : ℕ) : Decidable (r.IsFloatingUpper i) :=
  inferInstanceAs (Decidable (i < r.upper.len ∧ ¬ r.IsLinkedUpper i))

instance (j : ℕ) : Decidable (r.IsFloatingLower j) :=
  inferInstanceAs (Decidable (j < r.lower.len ∧ ¬ r.IsLinkedLower j))

/-- The empty representation is planar (vacuously). -/
theorem isPlanar_empty : (empty : Graph α β).IsPlanar := by simp [IsPlanar, empty]

/-! ### In-bounds predicate -/

/-- Every link's indices fall within the tier lengths. -/
def InBounds : Prop :=
  ∀ p ∈ r.links, p.fst < r.upper.len ∧ p.snd < r.lower.len

instance : Decidable r.InBounds :=
  inferInstanceAs (Decidable (∀ p ∈ r.links, p.fst < r.upper.len ∧ p.snd < r.lower.len))

theorem inBounds_empty : (empty : Graph α β).InBounds := by simp [InBounds, empty]

/-! ### Concatenation ([jardine-heinz-2015]) -/

variable (A B C : Graph α β)

/-- [jardine-heinz-2015] concatenation: tier-concatenation plus
    index-shifted link-set union. -/
def concat : Graph α β where
  upper := A.upper.concat B.upper
  lower := A.lower.concat B.lower
  links := A.links ∪ B.links.image (shiftLink A.upper.len A.lower.len)

@[simp] theorem upper_concat : (A.concat B).upper = A.upper.concat B.upper := rfl
@[simp] theorem lower_concat : (A.concat B).lower = A.lower.concat B.lower := rfl
@[simp] theorem links_concat :
    (A.concat B).links = A.links ∪ B.links.image (shiftLink A.upper.len A.lower.len) := rfl

/-! #### Monoid laws ([jardine-heinz-2015] Theorems 1, 3) -/

/-- `empty` is a left identity for `concat`. -/
theorem empty_concat : empty.concat A = A :=
  Graph.ext (LabeledTuple.empty_concat A.upper) (LabeledTuple.empty_concat A.lower)
    (by simp [empty, shiftLink_zero])

/-- `empty` is a right identity for `concat`. -/
theorem concat_empty : A.concat empty = A :=
  Graph.ext (LabeledTuple.concat_empty A.upper) (LabeledTuple.concat_empty A.lower)
    (by simp [empty])

/-- `concat` is associative. -/
theorem concat_assoc : (A.concat B).concat C = A.concat (B.concat C) :=
  Graph.ext (LabeledTuple.concat_assoc A.upper B.upper C.upper)
    (LabeledTuple.concat_assoc A.lower B.lower C.lower)
    (by grind [links_concat, upper_concat, lower_concat, LabeledTuple.concat_len,
          Finset.image_union, Finset.image_image, shiftLink_comp])

/-! #### Planarity preservation ([jardine-heinz-2015] Theorem 4) -/

/-- Concatenation preserves planarity, given `A.InBounds`: `A.links` and the
    shifted `B.links` are each non-crossing (`monovaryOn_union` +
    `isNonCrossing_image_shiftLink`), and `A` sits entirely before `B`. -/
theorem isPlanar_concat {A B : Graph α β} (hAib : A.InBounds) (hA : A.IsPlanar) (hB : B.IsPlanar) :
    (A.concat B).IsPlanar := by
  grind [IsPlanar, IsNonCrossing, InBounds, MonovaryOn, links_concat, Finset.coe_union,
    monovaryOn_union, isNonCrossing_image_shiftLink, shiftLink]

/-- Concatenation preserves in-bounds. -/
theorem inBounds_concat {A B : Graph α β}
    (hA : A.InBounds) (hB : B.InBounds) : (A.concat B).InBounds := by
  grind [InBounds, links_concat, upper_concat, lower_concat, LabeledTuple.concat_len, shiftLink]

end Graph

/-! ## The in-bounds object `AR` and its monoidal category -/

open Graph CategoryTheory

variable {α β : Type*}

/-- The base object of the autosegmental category: an **in-bounds** autosegmental
    graph (every association line falls within the tier lengths). Planarity is
    *not* carried here — it is the constraint defining the subcategory `WellFormedAR`. -/
structure AR (α β : Type*) extends Graph α β where
  inBounds : toGraph.InBounds

namespace AR

/-! ### Morphisms -/

/-- A label- and link-preserving morphism. The tier maps are `LabeledTuple.Hom`s
    (each bundles a position map with its label-preservation `b.label ∘ f = a.label`);
    link preservation routes a link's (in-bounds) endpoints through those maps. -/
@[ext]
structure Hom (A B : AR α β) where
  /-- Vertex map on the upper tier (a label-preserving `LabeledTuple` morphism). -/
  fU : LabeledTuple.Hom A.upper B.upper
  /-- Vertex map on the lower tier. -/
  fL : LabeledTuple.Hom A.lower B.lower
  /-- Association lines are preserved. -/
  links_preserve : ∀ {i j : ℕ} (hi : i < A.upper.len) (hj : j < A.lower.len),
    (i, j) ∈ A.links → ((fU.toFun ⟨i, hi⟩ : ℕ), (fL.toFun ⟨j, hj⟩ : ℕ)) ∈ B.links

namespace Hom
variable {A B C : AR α β}

/-- The identity morphism. -/
def id (A : AR α β) : Hom A A where
  fU := LabeledTuple.Hom.id A.upper
  fL := LabeledTuple.Hom.id A.lower
  links_preserve _ _ h := h

/-- Composition of morphisms (diagrammatic: `f` then `g`). -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  fU := f.fU.comp g.fU
  fL := f.fL.comp g.fL
  links_preserve hi hj h := by
    simpa [LabeledTuple.Hom.comp] using g.links_preserve (f.fU.toFun ⟨_, hi⟩).isLt
      (f.fL.toFun ⟨_, hj⟩).isLt (f.links_preserve hi hj h)

@[simp] theorem id_fU (A : AR α β) : (Hom.id A).fU = LabeledTuple.Hom.id A.upper := rfl
@[simp] theorem id_fL (A : AR α β) : (Hom.id A).fL = LabeledTuple.Hom.id A.lower := rfl
@[simp] theorem comp_fU (f : Hom A B) (g : Hom B C) : (f.comp g).fU = f.fU.comp g.fU := rfl
@[simp] theorem comp_fL (f : Hom A B) (g : Hom B C) : (f.comp g).fL = f.fL.comp g.fL := rfl

/-- Extensionality at the index level: morphisms agree if their tier maps agree on
    the underlying `ℕ` indices. Collapses the
    `Hom.ext → LabeledTuple.Hom.ext → funext → Fin.ext` ladder used throughout the
    category/coherence proofs. -/
theorem ext_fin {f g : Hom A B} (hU : ∀ i, (f.fU.toFun i : ℕ) = g.fU.toFun i)
    (hL : ∀ j, (f.fL.toFun j : ℕ) = g.fL.toFun j) : f = g :=
  Hom.ext (LabeledTuple.Hom.ext (funext fun i => Fin.ext (hU i)))
    (LabeledTuple.Hom.ext (funext fun j => Fin.ext (hL j)))

end Hom

instance : CategoryStruct (AR α β) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g

instance : Category (AR α β) where
  id_comp _ := by apply Hom.ext <;> rfl
  comp_id _ := by apply Hom.ext <;> rfl
  assoc _ _ _ := by apply Hom.ext <;> rfl

@[simp] theorem id_fU' (A : AR α β) : (𝟙 A : Hom A A).fU = 𝟙 A.upper := rfl
@[simp] theorem id_fL' (A : AR α β) : (𝟙 A : Hom A A).fL = 𝟙 A.lower := rfl
@[simp] theorem comp_fU' {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fU = f.fU.comp g.fU := rfl
@[simp] theorem comp_fL' {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fL = f.fL.comp g.fL := rfl

/-! ### Concatenation: the tensor object -/

/-- Morpheme concatenation ([jardine-heinz-2015]): the tier-concatenated,
    index-shifted graph, in-bounds by `Graph.inBounds_concat`. -/
def concat (A B : AR α β) : AR α β where
  toGraph := A.toGraph.concat B.toGraph
  inBounds := Graph.inBounds_concat A.inBounds B.inBounds

@[simp] theorem concat_toGraph (A B : AR α β) :
    (A.concat B).toGraph = A.toGraph.concat B.toGraph := rfl

@[simp] theorem concat_upper (A B : AR α β) :
    (A.concat B).upper = A.upper.concat B.upper := rfl

@[simp] theorem concat_lower (A B : AR α β) :
    (A.concat B).lower = A.lower.concat B.lower := rfl

theorem links_concat (A B : AR α β) :
    (A.concat B).links =
      A.links ∪ B.links.image (shiftLink A.upper.len A.lower.len) := rfl

/-! ### The concatenation bifunctor `concatMap` (the tensor on morphisms)

The tier action delegates to the keystone `LabeledTuple.Hom.concatMap`; only link
preservation is bespoke, routing the A-block through `f` (unshifted) and the
B-block through `g` (shifted past `A'`) via `Fin.appendMap_val`. -/

namespace Hom
variable {A A' B B' : AR α β}

/-- The concatenation bifunctor on morphisms (`f ⊗ g`): `f` on the A-block,
    `g` (shifted) on the B-block. Tiers via `LabeledTuple.Hom.concatMap`. -/
def concatMap (f : Hom A A') (g : Hom B B') : Hom (A.concat B) (A'.concat B') where
  fU := LabeledTuple.Hom.concatMap f.fU g.fU
  fL := LabeledTuple.Hom.concatMap f.fL g.fL
  links_preserve {i j} hi hj h := by
    simp only [links_concat, Finset.mem_union, Finset.mem_image, shiftLink,
      Prod.exists, Prod.mk.injEq, LabeledTuple.Hom.concatMap_toFun] at h ⊢
    rcases h with hA | ⟨a, b, hab, hai, hbj⟩
    · obtain ⟨hiu, hjl⟩ := A.inBounds (i, j) hA
      left
      rw [Fin.appendMap_val, dif_pos hiu, Fin.appendMap_val, dif_pos hjl]
      exact f.links_preserve hiu hjl hA
    · obtain ⟨hau, hbl⟩ := B.inBounds (a, b) hab
      subst hai hbj
      right
      refine ⟨(g.fU.toFun ⟨a, hau⟩ : ℕ), (g.fL.toFun ⟨b, hbl⟩ : ℕ),
        g.links_preserve hau hbl hab, ?_, ?_⟩
      · rw [Fin.appendMap_val, dif_neg (show ¬ (a + A.upper.len) < A.upper.len by omega)]
        congr 2; apply Fin.ext; simp
      · rw [Fin.appendMap_val, dif_neg (show ¬ (b + A.lower.len) < A.lower.len by omega)]
        congr 2; apply Fin.ext; simp

@[simp] theorem concatMap_fU (f : Hom A A') (g : Hom B B') :
    (concatMap f g).fU = LabeledTuple.Hom.concatMap f.fU g.fU := rfl

@[simp] theorem concatMap_fL (f : Hom A A') (g : Hom B B') :
    (concatMap f g).fL = LabeledTuple.Hom.concatMap f.fL g.fL := rfl

/-- The concat bifunctor preserves identities (`tensor_id`). -/
theorem concatMap_id (A B : AR α β) :
    concatMap (Hom.id A) (Hom.id B) = Hom.id (A.concat B) := by
  apply Hom.ext <;>
    simp only [concatMap_fU, concatMap_fL, id_fU, id_fL, LabeledTuple.Hom.concatMap_id,
      concat_upper, concat_lower]

/-- The concat bifunctor preserves composition (`tensor_comp`). -/
theorem concatMap_comp {A A' A'' B B' B'' : AR α β}
    (f : Hom A A') (f' : Hom A' A'') (g : Hom B B') (g' : Hom B' B'') :
    (concatMap f g).comp (concatMap f' g') = concatMap (f.comp f') (g.comp g') := by
  apply Hom.ext
  · simp only [comp_fU, concatMap_fU]
    exact (LabeledTuple.Hom.concatMap_comp f.fU f'.fU g.fU g'.fU).symm
  · simp only [comp_fL, concatMap_fL]
    exact (LabeledTuple.Hom.concatMap_comp f.fL f'.fL g.fL g'.fL).symm

end Hom

/-! ### Monoid structure on objects -/

/-- The empty (unit) object: no tiers, no links. -/
def empty : AR α β where
  toGraph := Graph.empty
  inBounds := Graph.inBounds_empty

/-- Two ARs are equal iff their underlying graphs are (`inBounds` by proof
    irrelevance). -/
theorem ext_toGraph {A B : AR α β} (h : A.toGraph = B.toGraph) : A = B := by
  cases A; cases B; cases h; rfl

/-- Objects form a `Monoid` under concatenation, with `empty` as unit
    ([jardine-heinz-2015] Theorems 1, 3): the laws lift the `Graph` monoid laws
    through `ext_toGraph`. -/
instance instMonoid : Monoid (AR α β) where
  mul := concat
  one := empty
  mul_assoc A B C := ext_toGraph (Graph.concat_assoc A.toGraph B.toGraph C.toGraph)
  one_mul A := ext_toGraph (Graph.empty_concat A.toGraph)
  mul_one A := ext_toGraph (Graph.concat_empty A.toGraph)

@[simp] theorem mul_eq_concat (A B : AR α β) : A * B = A.concat B := rfl

@[simp] theorem one_eq_empty : (1 : AR α β) = empty := rfl

/-! ### Concatenation is the categorical coproduct

`empty` is the initial object and `concat` the categorical coproduct — the
**disjoint union** of the two labeled bipartite graphs, with coprojections the
tier coprojections (`LabeledTuple.inl`/`inr`) carrying links forward. This is the
autosegmental analogue of `LabeledTuple`'s cocartesian structure (and of
disjoint-union-of-graphs). [jardine-heinz-2015] describes concatenation as "a
modification of [the] disjoint union" (§5) with the empty graph as identity
(Theorem 1); its disjoint-union core — the part before the OCP-merging
modification, modeled separately as `OCP.collapse` — is exactly this coproduct.
So the monoidal product is **cocartesian**.
-/

open CategoryTheory Limits

instance (Y : AR α β) : Subsingleton (empty ⟶ Y) :=
  ⟨fun _ _ => Hom.ext_fin (fun i => i.elim0) (fun j => j.elim0)⟩

instance (Y : AR α β) : Nonempty (empty ⟶ Y) :=
  ⟨{ fU := ⟨Fin.elim0, by funext i; exact i.elim0⟩
     fL := ⟨Fin.elim0, by funext i; exact i.elim0⟩
     links_preserve := fun _ _ h => absurd h (by simp [empty, Graph.empty]) }⟩

instance : HasInitial (AR α β) := hasInitial_of_unique empty

/-- The left coprojection `A ⟶ A.concat B`: tier inclusions plus the identity on
    `A`'s links, which sit unshifted in the first block. -/
def inl (A B : AR α β) : Hom A (A.concat B) where
  fU := LabeledTuple.inl A.upper B.upper
  fL := LabeledTuple.inl A.lower B.lower
  links_preserve _ _ h := by simpa [LabeledTuple.inl, links_concat] using Or.inl h

/-- The right coprojection `B ⟶ A.concat B`: tier inclusions plus `A`'s
    index-shift on `B`'s links (the second block). -/
def inr (A B : AR α β) : Hom B (A.concat B) where
  fU := LabeledTuple.inr A.upper B.upper
  fL := LabeledTuple.inr A.lower B.lower
  links_preserve {i j} _ _ h := by
    simp only [LabeledTuple.inr_toFun, Fin.val_natAdd, links_concat, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨(i, j), h, by simp [shiftLink, Nat.add_comm]⟩)

/-- The copairing of `f : A ⟶ T` and `g : B ⟶ T`: `f` on the first block, `g` on
    the (shifted) second block — `Fin.append` on tiers, case-split on links. -/
def coprodDesc {A B T : AR α β} (f : Hom A T) (g : Hom B T) : Hom (A.concat B) T where
  fU := LabeledTuple.coprodDesc f.fU g.fU
  fL := LabeledTuple.coprodDesc f.fL g.fL
  links_preserve {i j} hi hj h := by
    simp only [LabeledTuple.coprodDesc_toFun, links_concat,
      Finset.mem_union, Finset.mem_image, shiftLink, Prod.exists, Prod.mk.injEq] at h ⊢
    rcases h with hA | ⟨a, b, hab, hai, hbj⟩
    · obtain ⟨hiu, hjl⟩ := A.inBounds (i, j) hA
      rw [Fin.append_val, dif_pos hiu, Fin.append_val, dif_pos hjl]
      exact f.links_preserve hiu hjl hA
    · obtain ⟨hau, hbl⟩ := B.inBounds (a, b) hab
      subst hai hbj
      rw [Fin.append_val, dif_neg (show ¬ a + A.upper.len < A.upper.len by omega),
        Fin.append_val, dif_neg (show ¬ b + A.lower.len < A.lower.len by omega)]
      simpa only [Nat.add_sub_cancel] using g.links_preserve hau hbl hab

@[simp] theorem inl_fU (A B : AR α β) : (inl A B).fU = LabeledTuple.inl A.upper B.upper := rfl
@[simp] theorem inl_fL (A B : AR α β) : (inl A B).fL = LabeledTuple.inl A.lower B.lower := rfl
@[simp] theorem inr_fU (A B : AR α β) : (inr A B).fU = LabeledTuple.inr A.upper B.upper := rfl
@[simp] theorem inr_fL (A B : AR α β) : (inr A B).fL = LabeledTuple.inr A.lower B.lower := rfl
@[simp] theorem coprodDesc_fU {A B T : AR α β} (f : Hom A T) (g : Hom B T) :
    (coprodDesc f g).fU = LabeledTuple.coprodDesc f.fU g.fU := rfl
@[simp] theorem coprodDesc_fL {A B T : AR α β} (f : Hom A T) (g : Hom B T) :
    (coprodDesc f g).fL = LabeledTuple.coprodDesc f.fL g.fL := rfl

/-- `concat` is the categorical coproduct: `inl`/`inr` are the coprojections and
    `coprodDesc` the copairing — the disjoint-union universal property. -/
instance (A B : AR α β) : HasBinaryCoproduct A B :=
  HasColimit.mk
    { cocone := BinaryCofan.mk (inl A B) (inr A B)
      isColimit := BinaryCofan.IsColimit.mk _ (fun f g => coprodDesc f g)
        (fun f g => by apply Hom.ext_fin <;> intro i <;> simp)
        (fun f g => by apply Hom.ext_fin <;> intro i <;> simp)
        (fun f g m h₁ h₂ => by
          refine Hom.ext_fin (fun i => ?_) (fun j => ?_)
          · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
            · simpa using congrArg (fun φ => (φ.fU.toFun k : ℕ)) h₁
            · simpa using congrArg (fun φ => (φ.fU.toFun k : ℕ)) h₂
          · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
            · simpa using congrArg (fun φ => (φ.fL.toFun k : ℕ)) h₁
            · simpa using congrArg (fun φ => (φ.fL.toFun k : ℕ)) h₂) }

instance : HasBinaryCoproducts (AR α β) := hasBinaryCoproducts_of_hasColimit_pair _

/-! ### Monoidal category structure

`(AR α β, concat, empty)` is a monoidal category. Because the object `Monoid`
laws hold as strict equalities, the associator and unitors are `eqToIso` of
`mul_assoc`/`one_mul`/`mul_one`, so the coherence laws reduce to `eqToHom`
algebra (pentagon, triangle) or `Fin`-index arithmetic (naturalities).
-/

open CategoryTheory MonoidalCategory

/-- The upper tier map of an `eqToHom`, as a function: the length-cast `Fin.cast`
    (goes straight to the `len` level, avoiding a nested `LabeledTuple` `eqToHom`). -/
@[simp] theorem eqToHom_fU_toFun {A B : AR α β} (h : A = B) :
    (eqToHom h).fU.toFun = Fin.cast (congrArg (fun X => X.upper.len) h) := by
  cases h; rfl

/-- The lower tier map of an `eqToHom`, as a function. -/
@[simp] theorem eqToHom_fL_toFun {A B : AR α β} (h : A = B) :
    (eqToHom h).fL.toFun = Fin.cast (congrArg (fun X => X.lower.len) h) := by
  cases h; rfl

/-- Tensoring an identity (left) with an `eqToHom` (right) is an `eqToHom`. -/
@[simp] theorem concatMap_id_eqToHom {W X Y : AR α β} (h : X = Y) :
    Hom.concatMap (𝟙 W) (eqToHom h) = eqToHom (congrArg (W.concat ·) h) := by
  cases h; simp only [eqToHom_refl]; exact Hom.concatMap_id W X

/-- Tensoring an `eqToHom` (left) with an identity (right) is an `eqToHom`. -/
@[simp] theorem concatMap_eqToHom_id {W X Y : AR α β} (h : X = Y) :
    Hom.concatMap (eqToHom h) (𝟙 W) = eqToHom (congrArg (·.concat W) h) := by
  cases h; simp only [eqToHom_refl]; exact Hom.concatMap_id X W

/-- The tensor is `concat`; associator and unitors are `eqToIso` of the object
    `Monoid` laws (`AR` is strict monoidal over its object-monoid). -/
@[simps] instance instMonoidalStruct : MonoidalCategoryStruct (AR α β) where
  tensorObj := AR.concat
  tensorUnit := AR.empty
  tensorHom f g := Hom.concatMap f g
  whiskerLeft X _ _ f := Hom.concatMap (Hom.id X) f
  whiskerRight f Y := Hom.concatMap f (Hom.id Y)
  associator A B C := eqToIso (mul_assoc A B C)
  leftUnitor X := eqToIso (one_mul X)
  rightUnitor X := eqToIso (mul_one X)

instance : MonoidalCategory (AR α β) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := Hom.concatMap_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => Hom.concatMap_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      refine Hom.ext_fin ?_ ?_ <;> intro x <;>
        simp [Fin.appendMap_val, Nat.sub_sub] <;> split_ifs <;> omega)
    (leftUnitor_naturality := by
      intro X Y f
      refine Hom.ext_fin ?_ ?_ <;> intro x <;>
        simp [Fin.appendMap_val, empty, Graph.empty] <;> rfl)
    (rightUnitor_naturality := by
      intro X Y f
      refine Hom.ext_fin ?_ ?_ <;> intro x <;> simp [Fin.appendMap_val, empty, Graph.empty])
    (pentagon := by intros; simp [eqToHom_trans])
    (triangle := by intros; simp [eqToHom_trans])

end AR

/-! ## The well-formed (planar) monoidal subcategory -/

open CategoryTheory MonoidalCategory

variable {α β : Type*}

/-! ### Planarity as a monoidal object-property -/

/-- Planarity (Goldsmith's NCC) as a property of the base object `AR`. -/
def isPlanar : ObjectProperty (AR α β) := fun A => A.toGraph.IsPlanar

/-- Planarity is a **monoidal property**: the unit is planar and `concat`
    preserves planarity (using the left factor's in-boundedness via
    `Graph.isPlanar_concat`). This is the categorical content of the NCC's
    morpheme-modularity ([bermudez-otero-2012]). -/
instance instIsMonoidalIsPlanar : (isPlanar (α := α) (β := β)).IsMonoidal where
  prop_unit := Graph.isPlanar_empty
  prop_tensor X₁ _X₂ h₁ h₂ := Graph.isPlanar_concat X₁.inBounds h₁ h₂

/-- The well-formed autosegmental category `WellFormedAR α β`: the full monoidal
    subcategory of `AR` cut out by planarity. Objects are planar in-bounds graphs;
    the `MonoidalCategory` instance is inherited from `AR` via
    `ObjectProperty.fullMonoidalSubcategory`. -/
abbrev WellFormedAR (α β : Type*) := (isPlanar (α := α) (β := β)).FullSubcategory

namespace WellFormedAR

/-- Build a `WellFormedAR` from an in-bounds representation and a planarity proof. -/
abbrev mk (A : AR α β) (h : A.toGraph.IsPlanar) : WellFormedAR α β := ⟨A, h⟩

end WellFormedAR

/-! ### The No-Crossing Constraint is morpheme-modular -/

/-- The No-Crossing Constraint ([goldsmith-1976], [pulleyblank-1986]) is
    **morpheme-modular**: planarity is a monoidal property of `AR`, so the planar
    (well-formed) ARs form the monoidal subcategory `WellFormedAR`. This is the
    linguistic content witnessed by the `MonoidalCategory (WellFormedAR α β)` instance. -/
theorem ncc_isMonoidal : (isPlanar (α := α) (β := β)).IsMonoidal := inferInstance

/-! ### The OCP is not morpheme-modular -/

/-- The OCP ([mccarthy-1986]) as a property of `AR`: the autosegmental (upper)
    tier has no adjacent identical elements. -/
def upperOCPClean : ObjectProperty (AR α β) := fun A => OCP.IsClean A.upper.toList

instance [DecidableEq α] (A : AR α β) : Decidable (upperOCPClean A) :=
  inferInstanceAs (Decidable (OCP.IsClean A.upper.toList))

/-- A single-autosegment representation `⟨[true], [], ∅⟩`; concatenating it with
    itself produces the OCP-violating tier `[true, true]`. `Bool`/`Unit` is the
    smallest label/backbone pair admitting two equal upper elements. -/
private def ocpWitness : AR Bool Unit := ⟨⟨.ofList [true], .empty, ∅⟩, by decide⟩

/-- The OCP is **not** morpheme-modular: concatenation can create an adjacent
    identical autosegment pair at the morpheme boundary — a violation present in
    neither factor. Witnessed by two single-autosegment reps (`⟨[true], [], ∅⟩`)
    whose concatenation has upper tier `[true, true]`. The OCP-clean ARs are
    therefore not closed under `⊗`; the boundary violation is what forces a repair
    (`OCP.collapse`; see `collapse_repairs_boundary`). -/
theorem ocp_not_isMonoidal : ¬ (upperOCPClean (α := Bool) (β := Unit)).IsMonoidal := by
  intro h
  haveI := h.toTensorLE
  have hc : upperOCPClean (ocpWitness ⊗ ocpWitness) :=
    ObjectProperty.prop_tensor (show upperOCPClean ocpWitness by decide)
      (show upperOCPClean ocpWitness by decide)
  revert hc
  decide

/-- The discriminating dichotomy: the monoidal structure of `WellFormedAR` classifies the
    NCC as morpheme-modular (closed under `⊗`) and the OCP as not
    (boundary-spanning). The two halves cannot be interchanged — that is what
    makes the monoidal product load-bearing rather than decorative. -/
theorem ncc_modular_ocp_not :
    (isPlanar (α := Bool) (β := Unit)).IsMonoidal ∧
    ¬ (upperOCPClean (α := Bool) (β := Unit)).IsMonoidal :=
  ⟨ncc_isMonoidal, ocp_not_isMonoidal⟩

/-! ### Fusion as the forced boundary repair -/

/-- Because the OCP is not morpheme-modular, well-formedness must be *restored* at
    the morpheme boundary by a repair. [mccarthy-1986]'s fusion (`OCP.collapse`)
    is exactly such a repair: it maps the autosegmental tier of any concatenation
    back into the OCP-clean set. The non-modularity of the OCP
    (`ocp_not_isMonoidal`) is what makes a repair *necessary*; this theorem
    exhibits one. -/
theorem collapse_repairs_boundary [DecidableEq α] (A B : Graph α β) :
    OCP.IsClean (OCP.collapse (A.concat B).upper.toList) :=
  OCP.collapse_clean _

end Autosegmental
