/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Graph
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The autosegmental category `AR α β`

`AR α β` is the bundled type of **well-formed autosegmental
representations**: a `Graph α β` paired with proofs that the link
set is in-bounds and that the representation is planar (satisfies
[goldsmith-1976]'s No-Crossing Constraint, equivalently
[pulleyblank-1986]'s reformulated Well-Formedness Condition).

In mathlib's pattern (`Group` → `Grp`, `Module` → `ModuleCat`),
`Graph α β` is the underlying object type and `AR α β` is the
*bundled* type that carries the autosegmental well-formedness
invariants — the canonical objects of the category of autosegmental
representations. The bundled name `AR` matches the field's standard
abbreviation across [jardine-2017],
[chandlee-jardine-2019], [burness-mcmullin-2020] and the
broader Heinz-Jardine-Chandlee tradition.

## Main definitions (this file)

* `AR α β` — the bundled well-formed AR type (Graph + InBounds + Planar).
* `AR.empty`, `AR.concat` — lifted from Graph; concat preserves the
  invariants because [jardine-heinz-2015] Theorem 4 + our
  `inBounds_concat` lemma carry both invariants through.
* `AR.Hom A B := Graph.Hom A.toGraph B.toGraph` — morphisms are
  just graph homomorphisms on the underlying graphs.
* `AR.Hom.id`, `AR.Hom.comp` — delegated to `Graph.Hom`.

## What this file does NOT yet define

Sibling files in the same directory will add:

* `AR.tensorHom` and functoriality (via `Graph.Hom.concatMap`) — the
  bifunctor on `Hom` corresponding to concatenation.
* `CategoryTheory.Category (AR α β)` — the formal category instance.
* `CategoryTheory.MonoidalCategory (AR α β)` — with `concat` as the
  tensor product, `empty` as the tensor unit, and the associator /
  unitors built from the strict concatenation equalities (the `Monoid`
  laws `mul_assoc`/`one_mul`/`mul_one`).

These complete "the category of autosegmental representations" as a
formal mathlib monoidal category. They will land as separate commits.
-/

namespace Phonology.Autosegmental

/-! ### The bundled type `AR`

`AR α β` extends `Graph α β` with structural well-formedness
proofs. The Pulleyblank-1986 WFC is **planarity (NCC) alone**;
[goldsmith-1979]'s saturation is language-particular and is
*not* carried as a structural invariant here. `InBounds` is a
substrate-level requirement (Graph doesn't enforce links to fall
within tier lengths structurally; the subtype does).
-/

/-- A well-formed autosegmental representation: a `Graph` whose link
    set is in-bounds (`InBounds`) and which satisfies the No-Crossing
    Constraint (`IsPlanar`). Per [pulleyblank-1986], planarity is
    the sole universal structural well-formedness condition on
    autosegmental representations; [goldsmith-1979]'s additional
    saturation requirements are language-particular and live at the
    consumer level, not in this subtype. -/
@[ext]
structure AR (α β : Type*) extends Graph α β where
  inBounds : toGraph.InBounds
  planar : toGraph.IsPlanar

namespace AR

variable {α β : Type*}

/-! ### Construction -/

/-- The empty AR (no tier elements, no associations). Trivially
    in-bounds (no links to check) and planar. -/
def empty : AR α β where
  toGraph := Graph.empty
  inBounds := Graph.inBounds_empty
  planar := Graph.isPlanar_empty

/-- Concatenation of ARs ([jardine-heinz-2015]): tiers are
    concatenated, link sets are unioned with B's shifted by A's tier
    lengths. The InBounds invariant is preserved by
    `Graph.inBounds_concat`; planarity is preserved by
    `Graph.isPlanar_concat` (using A's `InBounds`). -/
def concat (A B : AR α β) : AR α β where
  toGraph := A.toGraph.concat B.toGraph
  inBounds := Graph.inBounds_concat A.inBounds B.inBounds
  planar := Graph.isPlanar_concat _ _ A.inBounds A.planar B.planar

/-! ### Morphisms -/

/-- A morphism in the autosegmental category is just a graph
    homomorphism on the underlying graphs. The well-formedness
    invariants (`InBounds`, `Planar`) are properties of objects, not
    of morphisms — a graph homomorphism between well-formed ARs
    automatically lands inside a well-formed AR. -/
abbrev Hom (A B : AR α β) := Graph.Hom A.toGraph B.toGraph

namespace Hom

variable {A B C D : AR α β}

/-- Identity morphism on an AR. Delegated to `Graph.Hom.id`. -/
def id (A : AR α β) : Hom A A := Graph.Hom.id A.toGraph

/-- Composition (diagrammatic order: `f.comp g` is "f first, then g").
    Delegated to `Graph.Hom.comp`. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C := Graph.Hom.comp f g

/-! #### Category laws (inherited from Graph) -/

theorem id_comp (f : Hom A B) : (Hom.id A).comp f = f :=
  Graph.Hom.id_comp f

theorem comp_id (f : Hom A B) : f.comp (Hom.id B) = f :=
  Graph.Hom.comp_id f

theorem comp_assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Graph.Hom.comp_assoc f g h

end Hom

/-! ### Tensor on morphisms (the bifunctor underlying `MonoidalCategory`) -/

/-- The concatenation tensor on AR morphisms. Lifts
    `Graph.Hom.concatMap` using the `inBounds` proof carried by the
    AR object — so the `InBounds` hypothesis the underlying
    `Graph.Hom.concatMap` requires is automatically supplied. This is
    the bifunctor `(⊗) : Hom A A' → Hom B B' → Hom (A ⊗ B) (A' ⊗ B')`
    of `MonoidalCategory (AR α β)`. -/
def tensorHom {A A' B B' : AR α β}
    (f : Hom A A') (g : Hom B B') : Hom (A.concat B) (A'.concat B') :=
  Graph.Hom.concatMap A.inBounds f g

/-! #### Functoriality of `tensorHom` -/

/-- `tensorHom (id A) (id B) = id (A ⊗ B)` — the `tensor_id` law of
    mathlib's `MonoidalCategory`. -/
theorem tensorHom_id (A B : AR α β) :
    tensorHom (Hom.id A) (Hom.id B) = Hom.id (A.concat B) :=
  Graph.Hom.concatMap_id A.inBounds

/-- `tensorHom (f₁ ; g₁) (f₂ ; g₂) = tensorHom f₁ f₂ ; tensorHom g₁ g₂`
    — the `tensor_comp` law of mathlib's `MonoidalCategory`. -/
theorem tensorHom_comp {A A' A'' B B' B'' : AR α β}
    (f : Hom A A') (f' : Hom A' A'')
    (g : Hom B B') (g' : Hom B' B'') :
    (tensorHom f g).comp (tensorHom f' g') =
      tensorHom (f.comp f') (g.comp g') :=
  Graph.Hom.concatMap_comp A.inBounds A'.inBounds f f' g g'

/-! ### Monoid structure

`AR α β` is a `Monoid` under concatenation ([jardine-heinz-2015] Theorems 1, 3):
the laws lift the `Graph` monoid laws (`Graph.concat_assoc` etc.) through
`ext_toGraph` — the `inBounds`/`planar` proofs match by proof irrelevance. So
associativity and the unit laws are `mul_assoc`/`one_mul`/`mul_one`, and
`toGraphHom` exhibits `AR` as the in-bounds, planar submonoid of `Graph`.

These are strict equalities, so the `MonoidalCategory`'s associator and unitor
isomorphisms are built directly (as explicit `Graph.Hom` isos below).
-/

/-- Two ARs are equal iff their underlying `Graph`s are equal —
    the `inBounds` and `planar` proofs match by proof irrelevance.
    Cheap helper for lifting Graph-level equalities to AR. -/
theorem ext_toGraph {A B : AR α β} (h : A.toGraph = B.toGraph) : A = B := by
  cases A; cases B
  simp only at h
  subst h
  rfl

/-- ARs form a monoid under concatenation, with the empty AR as unit — the
    well-formed (in-bounds, planar) submonoid of `Graph`'s concatenation monoid
    (see `toGraphHom`). The laws lift the `Graph` monoid laws through
    `ext_toGraph` (the `inBounds`/`planar` proofs match by proof irrelevance);
    [jardine-heinz-2015] Theorems 1, 3. Associativity and the unit laws are the
    `Monoid` API's `mul_assoc`/`one_mul`/`mul_one`. -/
instance instMonoid : Monoid (AR α β) where
  mul := concat
  one := empty
  mul_assoc A B C := ext_toGraph (Graph.concat_assoc A.toGraph B.toGraph C.toGraph)
  one_mul A := ext_toGraph (Graph.empty_concat A.toGraph)
  mul_one A := ext_toGraph (Graph.concat_empty A.toGraph)

@[simp] theorem mul_eq_concat (A B : AR α β) : A * B = A.concat B := rfl

@[simp] theorem one_eq_empty : (1 : AR α β) = empty := rfl

/-- The underlying-graph projection is a monoid homomorphism: `AR α β` is the
    in-bounds, planar submonoid of `Graph α β`. Injective by `ext_toGraph`, so
    it exhibits the autosegmental monoid as a submonoid of all graphs. -/
def toGraphHom : AR α β →* Graph α β where
  toFun A := A.toGraph
  map_one' := rfl
  map_mul' _ _ := rfl

/-! ### Category instance

`AR α β` is a `CategoryTheory.Category`: objects are well-formed
ARs, morphisms are graph homomorphisms. The category laws
(`id_comp`, `comp_id`, `assoc`) are inherited verbatim from
`Graph.Hom`.
-/

instance : CategoryTheory.CategoryStruct (AR α β) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

instance : CategoryTheory.Category (AR α β) where
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-! ### MonoidalCategory instance

`(AR α β, concat, empty)` is a monoidal category. The tensor product
is concatenation; the unit is the empty AR. Because `concat_assoc`,
`empty_concat`, and `concat_empty` hold as *strict equalities* on the
underlying graphs (and lift to AR equalities), the associator and
unitor natural isomorphisms are constructed via `eqToIso`, which
makes the naturality + coherence laws (pentagon, triangle) discharge
mechanically.
-/

/-! #### Explicit unitor and associator isomorphisms

To make the `MonoidalCategory` naturality + pentagon + triangle laws
provable cleanly (without manipulating opaque `eqToHom`-transports), the
unitors and associator are constructed as **explicit `Graph.Hom` Isos**
with identity index maps (`fUpper = id`, `fLower = id`). The underlying
list-level facts `[] ++ X = X`, `X ++ [] = X`, and `(A ++ B) ++ C = A ++ (B ++ C)`
are definitional or near-definitional, so identity maps are well-typed; the
label and link-preservation fields close by `simp` using the relevant List /
Finset lemmas.

This approach mirrors how strict-monoidal categories are usually built:
the unitors and associator are concretely "the identity," not just a
black-box `eqToIso` transport.
-/

/-- Explicit Iso for the left unitor: `empty.concat X ≅ X`. Since
    `[] ++ X.upper = X.upper` (and similarly for `lower`) is definitionally
    true, the identity `Nat → Nat` map is well-typed on both directions. -/
def leftUnitorIso (X : AR α β) : empty.concat X ≅ X where
  hom :=
    { fUpper := _root_.id
      fLower := _root_.id
      upper_label := fun i hi => ⟨hi, rfl⟩
      lower_label := fun j hj => ⟨hj, rfl⟩
      links_preserve := fun p hp => by
        show p ∈ X.toGraph.links
        rw [show (empty.concat X).toGraph = Graph.empty.concat X.toGraph from rfl,
            Graph.links_concat] at hp
        simp [Graph.empty] at hp
        exact hp
      upper_canonical := fun i hi => by
        show i = i - (empty.concat X).toGraph.upper.length + X.toGraph.upper.length
        have h : (empty.concat X).toGraph.upper.length = X.toGraph.upper.length := rfl
        omega
      lower_canonical := fun j hj => by
        show j = j - (empty.concat X).toGraph.lower.length + X.toGraph.lower.length
        have h : (empty.concat X).toGraph.lower.length = X.toGraph.lower.length := rfl
        omega }
  inv :=
    { fUpper := _root_.id
      fLower := _root_.id
      upper_label := fun i hi => ⟨hi, rfl⟩
      lower_label := fun j hj => ⟨hj, rfl⟩
      links_preserve := fun p hp => by
        show p ∈ (empty.concat X).toGraph.links
        rw [show (empty.concat X).toGraph = Graph.empty.concat X.toGraph from rfl,
            Graph.links_concat]
        simp [Graph.empty]
        exact hp
      upper_canonical := fun i hi => by
        show i = i - X.toGraph.upper.length + (empty.concat X).toGraph.upper.length
        have h : (empty.concat X).toGraph.upper.length = X.toGraph.upper.length := rfl
        omega
      lower_canonical := fun j hj => by
        show j = j - X.toGraph.lower.length + (empty.concat X).toGraph.lower.length
        have h : (empty.concat X).toGraph.lower.length = X.toGraph.lower.length := rfl
        omega }
  hom_inv_id := by apply Graph.Hom.ext <;> rfl
  inv_hom_id := by apply Graph.Hom.ext <;> rfl

/-- Explicit Iso for the right unitor: `X.concat empty ≅ X`. The
    underlying list-level facts `X.upper ++ [] = X.upper` are NOT
    definitional (they require induction on `X.upper`), so the field
    proofs use `List.append_nil` to bridge. -/
def rightUnitorIso (X : AR α β) : X.concat empty ≅ X where
  hom :=
    { fUpper := _root_.id
      fLower := _root_.id
      upper_label := fun i hi => by
        have hi' : i < X.upper.length := by
          rw [show (X.concat empty).toGraph.upper = X.upper ++ [] from rfl,
              List.length_append] at hi
          simpa using hi
        refine ⟨hi', ?_⟩
        show X.upper[i]? = (X.concat empty).toGraph.upper[i]?
        rw [show (X.concat empty).toGraph.upper = X.upper ++ [] from rfl,
            List.append_nil]
      lower_label := fun j hj => by
        have hj' : j < X.lower.length := by
          rw [show (X.concat empty).toGraph.lower = X.lower ++ [] from rfl,
              List.length_append] at hj
          simpa using hj
        refine ⟨hj', ?_⟩
        show X.lower[j]? = (X.concat empty).toGraph.lower[j]?
        rw [show (X.concat empty).toGraph.lower = X.lower ++ [] from rfl,
            List.append_nil]
      links_preserve := fun p hp => by
        show p ∈ X.toGraph.links
        rw [show (X.concat empty).toGraph = X.toGraph.concat Graph.empty from rfl,
            Graph.links_concat] at hp
        simp [Graph.empty] at hp
        exact hp
      upper_canonical := fun i hi => by
        show i = i - (X.concat empty).toGraph.upper.length + X.toGraph.upper.length
        have h : (X.concat empty).toGraph.upper.length = X.toGraph.upper.length := by
          show (X.upper ++ []).length = _
          simp
        omega
      lower_canonical := fun j hj => by
        show j = j - (X.concat empty).toGraph.lower.length + X.toGraph.lower.length
        have h : (X.concat empty).toGraph.lower.length = X.toGraph.lower.length := by
          show (X.lower ++ []).length = _
          simp
        omega }
  inv :=
    { fUpper := _root_.id
      fLower := _root_.id
      upper_label := fun i hi => by
        refine ⟨by
          show i < (X.concat empty).toGraph.upper.length
          rw [show (X.concat empty).toGraph.upper = X.upper ++ [] from rfl,
              List.append_nil]
          exact hi, ?_⟩
        show (X.concat empty).toGraph.upper[i]? = X.upper[i]?
        rw [show (X.concat empty).toGraph.upper = X.upper ++ [] from rfl,
            List.append_nil]
      lower_label := fun j hj => by
        refine ⟨by
          show j < (X.concat empty).toGraph.lower.length
          rw [show (X.concat empty).toGraph.lower = X.lower ++ [] from rfl,
              List.append_nil]
          exact hj, ?_⟩
        show (X.concat empty).toGraph.lower[j]? = X.lower[j]?
        rw [show (X.concat empty).toGraph.lower = X.lower ++ [] from rfl,
            List.append_nil]
      links_preserve := fun p hp => by
        show p ∈ (X.concat empty).toGraph.links
        rw [show (X.concat empty).toGraph = X.toGraph.concat Graph.empty from rfl,
            Graph.links_concat]
        simp [Graph.empty]
        exact hp
      upper_canonical := fun i hi => by
        show i = i - X.toGraph.upper.length + (X.concat empty).toGraph.upper.length
        have h : (X.concat empty).toGraph.upper.length = X.toGraph.upper.length := by
          show (X.upper ++ []).length = _
          simp
        omega
      lower_canonical := fun j hj => by
        show j = j - X.toGraph.lower.length + (X.concat empty).toGraph.lower.length
        have h : (X.concat empty).toGraph.lower.length = X.toGraph.lower.length := by
          show (X.lower ++ []).length = _
          simp
        omega }
  hom_inv_id := by apply Graph.Hom.ext <;> rfl
  inv_hom_id := by apply Graph.Hom.ext <;> rfl

/-- The underlying upper-tier equality used by the associator Iso. -/
private theorem assoc_upper (A B C : AR α β) :
    ((A.concat B).concat C).toGraph.upper = (A.concat (B.concat C)).toGraph.upper :=
  List.append_assoc A.toGraph.upper B.toGraph.upper C.toGraph.upper

/-- The underlying lower-tier equality used by the associator Iso. -/
private theorem assoc_lower (A B C : AR α β) :
    ((A.concat B).concat C).toGraph.lower = (A.concat (B.concat C)).toGraph.lower :=
  List.append_assoc A.toGraph.lower B.toGraph.lower C.toGraph.lower

/-- The underlying link-set equality used by the associator Iso. Both
    sides expand to `A.links ∪ B.links.image (shift_AB) ∪ C.links.image (shift_ABC)`. -/
private theorem assoc_links (A B C : AR α β) :
    ((A.concat B).concat C).toGraph.links = (A.concat (B.concat C)).toGraph.links := by
  show (A.toGraph.concat B.toGraph |>.concat C.toGraph).links =
       (A.toGraph.concat (B.toGraph.concat C.toGraph)).links
  rw [Graph.links_concat, Graph.links_concat, Graph.links_concat, Graph.links_concat,
      Finset.image_union]
  simp only [Graph.upper_concat, Graph.lower_concat, List.length_append,
             Finset.image_image, Graph.shiftLink_comp, Finset.union_assoc]

/-- Explicit Iso for the associator: `(A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)`. The
    underlying list-level fact `(A.upper ++ B.upper) ++ C.upper =
    A.upper ++ (B.upper ++ C.upper)` is `List.append_assoc` (not
    definitional). Links transform under `shiftLink`-composition with
    `shiftLink_comp`. -/
def associatorIso (A B C : AR α β) :
    (A.concat B).concat C ≅ A.concat (B.concat C) where
  hom :=
    { fUpper := _root_.id
      fLower := _root_.id
      upper_label := fun i hi => by
        refine ⟨(assoc_upper A B C) ▸ hi, ?_⟩
        rw [(assoc_upper A B C)]; rfl
      lower_label := fun j hj => by
        refine ⟨(assoc_lower A B C) ▸ hj, ?_⟩
        rw [(assoc_lower A B C)]; rfl
      links_preserve := fun p hp => (assoc_links A B C) ▸ hp
      upper_canonical := fun i hi => by
        show i = i - ((A.concat B).concat C).toGraph.upper.length +
                    (A.concat (B.concat C)).toGraph.upper.length
        have h : ((A.concat B).concat C).toGraph.upper.length =
                 (A.concat (B.concat C)).toGraph.upper.length := by
          rw [assoc_upper]
        omega
      lower_canonical := fun j hj => by
        show j = j - ((A.concat B).concat C).toGraph.lower.length +
                    (A.concat (B.concat C)).toGraph.lower.length
        have h : ((A.concat B).concat C).toGraph.lower.length =
                 (A.concat (B.concat C)).toGraph.lower.length := by
          rw [assoc_lower]
        omega }
  inv :=
    { fUpper := _root_.id
      fLower := _root_.id
      upper_label := fun i hi => by
        refine ⟨(assoc_upper A B C).symm ▸ hi, ?_⟩
        rw [(assoc_upper A B C).symm]; rfl
      lower_label := fun j hj => by
        refine ⟨(assoc_lower A B C).symm ▸ hj, ?_⟩
        rw [(assoc_lower A B C).symm]; rfl
      links_preserve := fun p hp => (assoc_links A B C).symm ▸ hp
      upper_canonical := fun i hi => by
        show i = i - (A.concat (B.concat C)).toGraph.upper.length +
                    ((A.concat B).concat C).toGraph.upper.length
        have h : ((A.concat B).concat C).toGraph.upper.length =
                 (A.concat (B.concat C)).toGraph.upper.length := by
          rw [assoc_upper]
        omega
      lower_canonical := fun j hj => by
        show j = j - (A.concat (B.concat C)).toGraph.lower.length +
                    ((A.concat B).concat C).toGraph.lower.length
        have h : ((A.concat B).concat C).toGraph.lower.length =
                 (A.concat (B.concat C)).toGraph.lower.length := by
          rw [assoc_lower]
        omega }
  hom_inv_id := by apply Graph.Hom.ext <;> rfl
  inv_hom_id := by apply Graph.Hom.ext <;> rfl

open CategoryTheory in
instance : MonoidalCategoryStruct (AR α β) where
  tensorObj := AR.concat
  tensorUnit := AR.empty
  tensorHom := AR.tensorHom
  whiskerLeft X _ _ f := AR.tensorHom (Hom.id X) f
  whiskerRight f Y := AR.tensorHom f (Hom.id Y)
  associator := AR.associatorIso
  leftUnitor := AR.leftUnitorIso
  rightUnitor := AR.rightUnitorIso

open CategoryTheory in
instance : MonoidalCategory (AR α β) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := AR.tensorHom_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => AR.tensorHom_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intros X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      apply Graph.Hom.ext
      · funext i
        show (AR.associatorIso Y₁ Y₂ Y₃).hom.fUpper
              ((AR.tensorHom (AR.tensorHom f₁ f₂) f₃).fUpper i) =
            (AR.tensorHom f₁ (AR.tensorHom f₂ f₃)).fUpper
              ((AR.associatorIso X₁ X₂ X₃).hom.fUpper i)
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.associatorIso,
               AR.concat, Graph.concat]
        simp only [List.length_append, Nat.sub_sub]
        split_ifs <;> first | rfl | omega
      · funext j
        show (AR.associatorIso Y₁ Y₂ Y₃).hom.fLower
              ((AR.tensorHom (AR.tensorHom f₁ f₂) f₃).fLower j) =
            (AR.tensorHom f₁ (AR.tensorHom f₂ f₃)).fLower
              ((AR.associatorIso X₁ X₂ X₃).hom.fLower j)
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.associatorIso,
               AR.concat, Graph.concat]
        simp only [List.length_append, Nat.sub_sub]
        split_ifs <;> first | rfl | omega)
    (leftUnitor_naturality := by intros; apply Graph.Hom.ext <;> rfl)
    (rightUnitor_naturality := by
      intros X Y f
      apply Graph.Hom.ext
      · funext i
        show (AR.rightUnitorIso Y).hom.fUpper
              ((AR.tensorHom f (Hom.id empty)).fUpper i) =
            f.fUpper ((AR.rightUnitorIso X).hom.fUpper i)
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.rightUnitorIso,
               AR.empty, Graph.empty, Graph.Hom.id, AR.Hom.id]
        by_cases hi : i < X.toGraph.upper.length
        · simp [hi]
        · simp only [hi, if_false]
          rw [f.upper_canonical i (by omega)]
      · funext j
        show (AR.rightUnitorIso Y).hom.fLower
              ((AR.tensorHom f (Hom.id empty)).fLower j) =
            f.fLower ((AR.rightUnitorIso X).hom.fLower j)
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.rightUnitorIso,
               AR.empty, Graph.empty, Graph.Hom.id, AR.Hom.id]
        by_cases hj : j < X.toGraph.lower.length
        · simp [hj]
        · simp only [hj, if_false]
          rw [f.lower_canonical j (by omega)])
    (pentagon := by
      intros W X Y Z
      apply Graph.Hom.ext
      · funext i
        show (AR.tensorHom (Hom.id W) (AR.associatorIso X Y Z).hom).fUpper
              ((AR.associatorIso W (X.concat Y) Z).hom.fUpper
                ((AR.tensorHom (AR.associatorIso W X Y).hom (Hom.id Z)).fUpper i)) =
            (AR.associatorIso W X (Y.concat Z)).hom.fUpper
              ((AR.associatorIso (W.concat X) Y Z).hom.fUpper i)
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.associatorIso,
               AR.Hom.id, Graph.Hom.id, AR.concat, Graph.concat]
        simp only [List.length_append]
        split_ifs <;> omega
      · funext j
        show (AR.tensorHom (Hom.id W) (AR.associatorIso X Y Z).hom).fLower
              ((AR.associatorIso W (X.concat Y) Z).hom.fLower
                ((AR.tensorHom (AR.associatorIso W X Y).hom (Hom.id Z)).fLower j)) =
            (AR.associatorIso W X (Y.concat Z)).hom.fLower
              ((AR.associatorIso (W.concat X) Y Z).hom.fLower j)
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.associatorIso,
               AR.Hom.id, Graph.Hom.id, AR.concat, Graph.concat]
        simp only [List.length_append]
        split_ifs <;> omega)
    (triangle := by
      intros X Y
      apply Graph.Hom.ext
      · funext i
        show (AR.tensorHom (Hom.id X) (AR.leftUnitorIso Y).hom).fUpper
              ((AR.associatorIso X empty Y).hom.fUpper i) =
            (AR.tensorHom (AR.rightUnitorIso X).hom (Hom.id Y)).fUpper i
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.associatorIso,
               AR.leftUnitorIso, AR.rightUnitorIso, AR.Hom.id, Graph.Hom.id,
               AR.empty, Graph.empty, AR.concat, Graph.concat]
        simp [List.length_append]
      · funext j
        show (AR.tensorHom (Hom.id X) (AR.leftUnitorIso Y).hom).fLower
              ((AR.associatorIso X empty Y).hom.fLower j) =
            (AR.tensorHom (AR.rightUnitorIso X).hom (Hom.id Y)).fLower j
        dsimp [AR.tensorHom, Graph.Hom.concatMap, AR.associatorIso,
               AR.leftUnitorIso, AR.rightUnitorIso, AR.Hom.id, Graph.Hom.id,
               AR.empty, Graph.empty, AR.concat, Graph.concat]
        simp [List.length_append])

end AR

end Phonology.Autosegmental
