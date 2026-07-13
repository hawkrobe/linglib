/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Monoidal.Widesubcategory
import Linglib.Phonology.Autosegmental.Graph

/-!
# Autosegmental representations: the §4.2 axioms and their category

The well-formedness axioms of [jardine-2016-diss] §4.2 as predicates on
exactly the components each axiom reads — the order arcs (`Digraph`), the
association edges (`SimpleGraph`), and for the tier-relative axioms a vertex
coloring `c : V → ι`; on a labeled mixed graph they are read at the tier
coloring `X.tier t`. The class they carve out of `Graph S` is `AR t`, the
category of autosegmental representations, monoidal under `Graph.concat`.

## Main definitions

* `IsTierOrdered`, `NoInternalAssoc`, `IsSaturated`, `IsPlanar`, `IsOCPClean`:
  the §4.2 axioms (1–2, 3, 4, 5, 6; [jardine-heinz-2015] numbers the NCC and OCP
  as 4 and 5 and has no saturation axiom). Saturation ([goldsmith-1976]'s
  original well-formedness condition) is stated but not imposed; tier-orderedness
  includes path-closure — the arcs are transitively closed, [jardine-2019]'s
  reading that `A` represents the order; the OCP reads adjacency as the covering
  relation of the arcs, since order-closed arcs relate all comparable pairs.
  Axiom 6's word-level form is `AR.IsCleanAt`, bridged by
  `AR.isCleanAt_iff_isOCPClean` (`OCP.lean`) through the shared hub
  `OCP.IsClean`; connecting Axiom 5 to the coordinate `IsNonCrossing`
  (`NonCrossing.lean`) is the TODO below.
* `AR t`: the category of autosegmental representations — the full
  subcategory of labeled mixed graphs on Axioms 1–3, monoidal under `concat`.

## Main results

* `isTierOrdered_concat`, `noInternalAssoc_concat`, `isPlanar_concat`:
  concatenation preserves the axioms ([jardine-heinz-2015] Theorem 4's
  structural half); `isPlanar_concat` is [jardine-2019]'s NCC-preservation.
* `not_isTierOrdered_sum`: the bridge-free coproduct leaves the axiom class
  whenever the factors share a tier — Axiom 2 forces `concat`'s bridges.
* `AR.tierColoring`: the tier map properly colors the association
  graph, so tier arity bounds its chromatic number (`edges_colorable`).

## TODO

* Package `AR.ofData` and `AR.isoOfReaderEq` (`NormalForm.lean`) as a
  `CategoryTheory.Equivalence` between the strict tuple category and the
  finite representations, and reduce `IsPlanar` on normal forms to the
  per-pair `IsNonCrossing` of the link relation.
-/

namespace Autosegmental

variable {V S ι : Type*}

section Axioms
variable (E : SimpleGraph V) (A : Digraph V)

/-- The arcs `A` are tier-internal and strictly totally order each fiber of `c` (Axioms 1–2). -/
structure IsTierOrdered (c : V → ι) : Prop extends IsStrictOrder V A.Adj where
  /-- Arcs never leave a tier. -/
  tier_eq : ∀ ⦃v w⦄, A.Adj v w → c v = c w
  /-- Distinct same-tier vertices are arc-comparable. -/
  total : ∀ ⦃v w⦄, v ≠ w → c v = c w → A.Adj v w ∨ A.Adj w v

/-- No association edge links arc-related vertices (Axiom 3). -/
def NoInternalAssoc : Prop := ∀ ⦃v w⦄, E.Adj v w → ¬ A.Adj v w

/-- Every vertex meets an association edge (Axiom 4, full specification). -/
def IsSaturated : Prop := ∀ v, ∃ w, E.Adj v w

/-- No two association edges straddle in opposite precedence order (Axiom 5, the NCC). -/
def IsPlanar : Prop :=
  ∀ ⦃v v' w w'⦄, E.Adj v v' → E.Adj w w' → A.Adj v w → ¬ A.Adj w' v'

/-- Precedence-adjacent vertices on melody tier `m` bear distinct labels (Axiom 6, the OCP). -/
def IsOCPClean (ℓ : V → S) (t : S → ι) (m : ι) : Prop :=
  ∀ ⦃v w⦄, A.Adj v w → (∀ u, ¬ (A.Adj v u ∧ A.Adj u w)) → t (ℓ v) = m → ℓ v ≠ ℓ w

end Axioms

/-! ### Axiom preservation under the graph operations -/

namespace Graph

variable {X Y : Graph S}

theorem isTierOrdered_empty (t : S → ι) : IsTierOrdered (empty S).arcs ((empty S).tier t) :=
  { irrefl := (·.elim), trans := (·.elim), tier_eq := (·.elim), total := (·.elim) }

theorem noInternalAssoc_empty : NoInternalAssoc (empty S).edges (empty S).arcs := (·.elim)

section Concat
variable (t : S → ι)

/-- Concatenation preserves Axioms 1–2; seam transitivity holds because arcs are
    tier-internal. -/
theorem isTierOrdered_concat
    (h₁ : IsTierOrdered X.arcs (X.tier t)) (h₂ : IsTierOrdered Y.arcs (Y.tier t)) :
    IsTierOrdered (concat t X Y).arcs ((concat t X Y).tier t) where
  tier_eq := by rintro (v | v) (w | w) h; exacts [h₁.tier_eq h, h, h.elim, h₂.tier_eq h]
  total := by
    rintro (v | v) (w | w) hne htier
    exacts [h₁.total (Sum.inl_injective.ne_iff.mp hne) htier, Or.inl htier,
      Or.inr htier.symm, h₂.total (Sum.inr_injective.ne_iff.mp hne) htier]
  irrefl := by rintro (v | v) h; exacts [h₁.irrefl v h, h₂.irrefl v h]
  trans := by
    rintro (u | u) (v | v) (w | w) huv hvw
    exacts [h₁.trans _ _ _ huv hvw, (h₁.tier_eq huv).trans hvw, (hvw : False).elim,
      huv.trans (h₂.tier_eq hvw), (huv : False).elim, (huv : False).elim,
      (hvw : False).elim, h₂.trans _ _ _ huv hvw]

/-- Concatenation preserves Axiom 3: the disjoint edge sum adds no cross edges. -/
theorem noInternalAssoc_concat (h₁ : NoInternalAssoc X.edges X.arcs)
    (h₂ : NoInternalAssoc Y.edges Y.arcs) :
    NoInternalAssoc (concat t X Y).edges (concat t X Y).arcs := by
  rintro (v | v) (w | w) hadj harc
  exacts [h₁ hadj harc, absurd hadj (by simp), absurd hadj (by simp), h₂ hadj harc]

/-- Concatenation preserves the No-Crossing Constraint ([jardine-2019]'s headline
    [jardine-heinz-2015] result): factor planarity suffices — a straddle needs both
    edges in one block, or a return arc `inr → inl` that does not exist. -/
theorem isPlanar_concat (h₁ : IsPlanar X.edges X.arcs) (h₂ : IsPlanar Y.edges Y.arcs) :
    IsPlanar (concat t X Y).edges (concat t X Y).arcs := by
  rintro (v | v) (v' | v') (w | w) (w' | w') hvv' hww' hvw hw'v' <;>
    first
      | exact h₁ hvv' hww' hvw hw'v'
      | exact h₂ hvv' hww' hvw hw'v'
      | exact (hvw : False).elim
      | exact (hw'v' : False).elim
      | simp_all

end Concat

/-- **Axiom 2 forces the bridges**: the bridge-free sum of two graphs occupying a
    common tier is never tier-ordered — same-tier vertices from the two factors
    are precedence-unrelated across the seam. -/
theorem not_isTierOrdered_sum (t : S → ι) (v : X.V) (w : Y.V)
    (htier : X.tier t v = Y.tier t w) :
    ¬ IsTierOrdered (sum X Y).arcs ((sum X Y).tier t) := fun h => by
  simpa using h.total (v := .inl v) (w := .inr w) Sum.inl_ne_inr htier

end Graph

/-! ### The category of autosegmental representations -/

open CategoryTheory

/-- The category of **autosegmental representations** over a tier assignment:
    the full subcategory of labeled mixed graphs satisfying the structural
    axioms ([jardine-2016-diss] §4.2, Axioms 1–3) — the formal literature's
    ARs ([jardine-2019], [chandlee-jardine-2019]). -/
abbrev AR (t : S → ι) :=
  ObjectProperty.FullSubcategory
    fun X : Graph S => IsTierOrdered X.arcs (X.tier t) ∧ NoInternalAssoc X.edges X.arcs

/-! ### The monoidal structure: morpheme concatenation -/

namespace AR

open Graph MonoidalCategory

variable {t : S → ι}

/-- Under the structural axioms the tier map properly colors the association
    graph: same-tier vertices are precedence-related (Axioms 1–2) and associated
    vertices never are (Axiom 3), so associated vertices lie on distinct tiers.
    Goldsmith's bipartite two-tier geometry is the two-colorable case. -/
def tierColoring (X : AR t) : X.obj.edges.Coloring ι :=
  SimpleGraph.Coloring.mk (X.obj.tier t) fun {_ _} hadj htier =>
    (X.property.1.total hadj.ne htier).elim (X.property.2 hadj) (X.property.2 hadj.symm)

/-- A representation's association graph is colorable by its tiers: tier arity
    bounds the chromatic number of the association pattern. -/
theorem edges_colorable [Fintype ι] (X : AR t) :
    X.obj.edges.Colorable (Fintype.card ι) :=
  (tierColoring X).colorable

/-- A graph isomorphism as an isomorphism of representations. -/
def mkIso {X Y : AR t} (e : Graph.Iso X.obj Y.obj) : X ≅ Y :=
  InducedCategory.isoMk
    ⟨e.toHom, e.symm.toHom,
      Graph.Hom.ext (funext fun v => e.toEquiv.symm_apply_apply v),
      Graph.Hom.ext (funext fun v => e.toEquiv.apply_symm_apply v)⟩

/-- Componentwise extensionality for representation morphisms. -/
theorem hom_ext {X Y : AR t} {f g : X ⟶ Y}
    (h : ∀ v, f.hom.toFun v = g.hom.toFun v) : f = g :=
  InducedCategory.hom_ext (Graph.Hom.ext (funext h))

universe u₁ u₂ u₃

/-- Monoidal structure: morpheme concatenation as tensor, the empty
    representation as unit; the axiom class is closed under both by
    `isTierOrdered_concat`/`noInternalAssoc_concat`. Universes pinned so the
    unit's vertex type shares the objects' universe — autobinding would split
    the instance head into an unusable `max`; `@[simps]` feeds the tensor
    rewrites in `NormalForm.lean`. -/
@[simps] instance instMonoidalStruct {S : Type u₁} {ι : Type u₂} {t : S → ι} :
    MonoidalCategoryStruct (AR.{u₁, u₂, u₃} t) where
  tensorObj X Y :=
    ⟨concat t X.obj Y.obj, isTierOrdered_concat t X.property.1 Y.property.1,
      noInternalAssoc_concat t X.property.2 Y.property.2⟩
  tensorUnit := ⟨empty S, isTierOrdered_empty t, noInternalAssoc_empty⟩
  tensorHom f g := InducedCategory.homMk (Hom.concatMap t f.hom g.hom)
  whiskerLeft X _ _ f := InducedCategory.homMk (Hom.concatMap t (Hom.id X.obj) f.hom)
  whiskerRight f Y := InducedCategory.homMk (Hom.concatMap t f.hom (Hom.id Y.obj))
  associator X Y Z := mkIso (concatAssocIso t X.obj Y.obj Z.obj)
  leftUnitor X := mkIso (emptyConcatIso t X.obj)
  rightUnitor X := mkIso (concatEmptyIso t X.obj)

/-- The category of autosegmental representations is monoidal under morpheme
    concatenation — [jardine-heinz-2015] Theorems 1 and 3 packaged as coherence,
    with every proof a componentwise `rfl` over the concrete sum maps. -/
instance : MonoidalCategory (AR t) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => hom_ext (congrFun Sum.map_id_id))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => hom_ext (congrFun (Sum.map_comp_map _ _ _ _)))
    (associator_naturality := fun _ _ _ => hom_ext fun v => by
      repeat' rcases (v : _ ⊕ _) with v | v
      all_goals rfl)
    (leftUnitor_naturality := fun _ => hom_ext fun v => by
      rcases (v : _ ⊕ _) with v | v <;> first | rfl | exact v.elim)
    (rightUnitor_naturality := fun _ => hom_ext fun v => by
      rcases (v : _ ⊕ _) with v | v <;> first | rfl | exact v.elim)
    (pentagon := fun _ _ _ _ => hom_ext fun v => by
      repeat' rcases (v : _ ⊕ _) with v | v
      all_goals rfl)
    (triangle := fun _ _ => hom_ext fun v => by
      repeat' rcases (v : _ ⊕ _) with v | v
      all_goals first | rfl | exact v.elim)

/-- Precedence preservation on representations: the classical morphisms of the
    theory, as a monoidally-stable wide subcategory of the broad category. -/
def precPreserving : MorphismProperty (AR t) := fun _ _ f => Graph.precPreserving f.hom

instance : (precPreserving (t := t)).IsMonoidalStable where
  id_mem _ := fun _ _ h => h
  comp_mem _ _ hf hg := fun _ _ h => hg (hf h)
  whiskerLeft _ _ _ _ hg := Graph.Hom.concatMap_precPreserving t (fun _ _ h => h) hg
  whiskerRight _ hf _ := Graph.Hom.concatMap_precPreserving t hf (fun _ _ h => h)
  associator_hom_mem A B C := (Graph.concatAssocIso t A.obj B.obj C.obj).toHom_precPreserving
  associator_inv_mem A B C := (Graph.concatAssocIso t A.obj B.obj C.obj).symm.toHom_precPreserving
  leftUnitor_hom_mem A := (Graph.emptyConcatIso t A.obj).toHom_precPreserving
  leftUnitor_inv_mem A := (Graph.emptyConcatIso t A.obj).symm.toHom_precPreserving
  rightUnitor_hom_mem A := (Graph.concatEmptyIso t A.obj).toHom_precPreserving
  rightUnitor_inv_mem A := (Graph.concatEmptyIso t A.obj).symm.toHom_precPreserving

end AR

end Autosegmental
