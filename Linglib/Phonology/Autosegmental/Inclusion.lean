/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.Monoidal.Functor
import Linglib.Phonology.Autosegmental.AR
import Linglib.Phonology.Autosegmental.MultiAR

/-!
# The bipartite-to-multi-tier inclusion functor

The strong monoidal functor `ι : AR α β ⥤ MultiAR (biTier α β)` realising the
bipartite autosegmental category as the `n = 2` case: a bipartite graph is the
2-tier multigraph associating only the `(0,1)` melody↔skeleton pair. Unit and
tensor coherences are the object equalities `toMultiGraph_empty`/`toMultiGraph_concat`
as `eqToIso`. ([goldsmith-1976], [jardine-heinz-2015])

## Main definitions

* `Graph.toMultiGraph`, `AR.toMultiAR` — the inclusion on objects.
* `ι` — the inclusion functor; the `ι.Monoidal` instance makes it strong monoidal.
-/

namespace Autosegmental

open CategoryTheory MonoidalCategory

universe u

variable {α β : Type u}

/-- The two-tier family `![α, β]` indexing the bipartite case. -/
abbrev biTier (α β : Type u) : Fin 2 → Type u := ![α, β]

/-- **The inclusion on objects**: a bipartite `Graph α β` as the 2-tier
    `MultiGraph ![α,β]` that associates only the `(0,1)` tier-pair (melody↔skeleton).
    The dependent `Fin 2` tier-tuple is built with `Fin.cons` (`![·,·]` is
    non-dependent and cannot host the heterogeneous `LabeledTuple α`/`LabeledTuple β`). -/
def Graph.toMultiGraph (G : Graph α β) : MultiGraph (biTier α β) where
  tiers := Fin.cons G.upper (Fin.cons G.lower finZeroElim)
  links i j := if i = 0 ∧ j = 1 then G.links else ∅

@[simp] theorem toMultiGraph_tiers_zero (G : Graph α β) : G.toMultiGraph.tiers 0 = G.upper := rfl
@[simp] theorem toMultiGraph_tiers_one (G : Graph α β) : G.toMultiGraph.tiers 1 = G.lower := rfl
@[simp] theorem toMultiGraph_links_01 (G : Graph α β) : G.toMultiGraph.links 0 1 = G.links := rfl

/-- The inclusion sends a planar bipartite graph to a planar multigraph (and back):
    the only nonempty pair is `(0,1)`, carrying `G.links`. -/
@[simp] theorem toMultiGraph_isPlanar (G : Graph α β) :
    G.toMultiGraph.IsPlanar ↔ G.IsPlanar := by
  constructor
  · intro h; exact h 0 1
  · intro h i j
    fin_cases i <;> fin_cases j <;> simp_all [Graph.toMultiGraph, Graph.IsPlanar, isNonCrossing_empty]

/-- The inclusion preserves the empty graph (monoidal unit coherence). -/
theorem toMultiGraph_empty : (Graph.empty : Graph α β).toMultiGraph = MultiGraph.empty := by
  refine MultiGraph.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
  · fin_cases i <;> rfl
  · fin_cases i <;> fin_cases j <;> simp [Graph.toMultiGraph, Graph.empty]

/-- **The inclusion preserves concatenation** — the monoidal-functor coherence on
    objects: `(A ⋆ B)` maps to `(toMultiGraph A) ⋆ (toMultiGraph B)`. -/
theorem toMultiGraph_concat (A B : Graph α β) :
    (A.concat B).toMultiGraph = A.toMultiGraph.concat B.toMultiGraph := by
  refine MultiGraph.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
  · fin_cases i <;> rfl
  · fin_cases i <;> fin_cases j <;> rfl

/-! ### The inclusion functor on objects (in-bounds lift) -/

/-- The bipartite `InBounds` lifts to the multigraph: the only nonempty link-pair of
    `toMultiGraph` is `(0,1)`, where it carries `G.links` and the tier lengths are
    `upper`/`lower`. -/
theorem toMultiGraph_inBounds {A : AR α β} : A.toGraph.toMultiGraph.InBounds := by
  intro i j p hp
  simp only [Graph.toMultiGraph] at hp ⊢
  split_ifs at hp with h
  · obtain ⟨hi, hj⟩ := h; subst hi; subst hj
    exact A.inBounds p hp
  · simp at hp

/-- **The inclusion on objects.** -/
def AR.toMultiAR (A : AR α β) : MultiAR (biTier α β) where
  toMultiGraph := A.toGraph.toMultiGraph
  inBounds := toMultiGraph_inBounds

@[simp] theorem AR.toMultiAR_toMultiGraph (A : AR α β) :
    A.toMultiAR.toMultiGraph = A.toGraph.toMultiGraph := rfl

/-! ### The inclusion on morphisms -/

/-- The `Fin 2`-tuple of tier maps mirroring how `toMultiGraph.tiers` is built. -/
def AR.Hom.toMultiFT {A B : AR α β} (f : AR.Hom A B) :
    (i : Fin 2) → LabeledTuple.Hom (A.toMultiAR.tiers i) (B.toMultiAR.tiers i) :=
  Fin.cons f.fU (Fin.cons f.fL finZeroElim)

@[simp] theorem AR.Hom.toMultiFT_zero {A B : AR α β} (f : AR.Hom A B) :
    f.toMultiFT 0 = f.fU := rfl

@[simp] theorem AR.Hom.toMultiFT_one {A B : AR α β} (f : AR.Hom A B) :
    f.toMultiFT 1 = f.fL := rfl

/-- **The inclusion on morphisms.** -/
def AR.Hom.toMultiAR {A B : AR α β} (f : AR.Hom A B) :
    MultiAR.Hom A.toMultiAR B.toMultiAR where
  fT := f.toMultiFT
  links_preserve i j {p q} hp hq h := by
    simp only [AR.toMultiAR, Graph.toMultiGraph] at h ⊢
    split_ifs at h with hc
    · obtain ⟨hi, hj⟩ := hc; subst hi; subst hj
      rw [if_pos ⟨rfl, rfl⟩]
      exact f.links_preserve hp hq h
    · simp at h

/-! ### The plain functor -/

/-- **The inclusion functor** `AR α β ⥤ MultiAR (biTier α β)`. -/
def ι : AR α β ⥤ MultiAR (biTier α β) where
  obj A := A.toMultiAR
  map f := f.toMultiAR
  map_id A := by apply MultiAR.Hom.ext; funext i; fin_cases i <;> rfl
  map_comp f g := by apply MultiAR.Hom.ext; funext i; fin_cases i <;> rfl

@[simp] theorem ι_obj (A : AR α β) : ι.obj A = A.toMultiAR := rfl
@[simp] theorem ι_map {A B : AR α β} (f : A ⟶ B) : ι.map f = f.toMultiAR := rfl

/-! ### Monoidal coherence on objects (lifting to in-bounds `MultiAR`) -/

/-- The inclusion preserves the tensor unit (monoidal unit object coherence). -/
theorem toMultiAR_empty : (AR.empty : AR α β).toMultiAR = MultiAR.empty :=
  MultiAR.ext_toMultiGraph toMultiGraph_empty

/-- Every tier of the included unit is empty (length 0). -/
@[simp] theorem toMultiAR_empty_tiers_len (i : Fin 2) :
    ((AR.empty : AR α β).toMultiAR.tiers i).len = 0 := by
  rw [toMultiAR_empty]; rfl

/-- The inclusion preserves the tensor (monoidal tensor object coherence). -/
theorem toMultiAR_concat (A B : AR α β) :
    (A.concat B).toMultiAR = A.toMultiAR.concat B.toMultiAR :=
  MultiAR.ext_toMultiGraph (toMultiGraph_concat A.toGraph B.toGraph)

@[simp] theorem toMultiAR_fT {A B : AR α β} (f : AR.Hom A B) :
    (f.toMultiAR).fT = f.toMultiFT := rfl

/-! ### The strong monoidal upgrade

Via `Functor.CoreMonoidal` — `εIso`/`μIso` are the `eqToIso` of the object
coherences — and `CoreMonoidal.toMonoidal`. -/

/-- **The monoidal-functoriality bridge** (the `μ`-naturality crux): `ι` of a tensor
    of morphisms is the tensor of the `ι`-images, conjugated by the object
    coherence `eqToHom`s. -/
theorem toMultiAR_concatMap {A A' B B' : AR α β} (f : AR.Hom A A') (g : AR.Hom B B') :
    (AR.Hom.concatMap f g).toMultiAR =
      eqToHom (toMultiAR_concat A B) ≫ MultiAR.Hom.concatMap f.toMultiAR g.toMultiAR
        ≫ eqToHom (toMultiAR_concat A' B').symm := by
  refine MultiAR.Hom.ext_fin fun i x => ?_
  fin_cases i <;>
    simp only [MultiAR.comp_fT', MultiAR.Hom.concatMap_fT, AR.Hom.toMultiFT,
      AR.Hom.toMultiAR, LabeledTuple.Hom.comp_toFun, LabeledTuple.Hom.concatMap_toFun,
      MultiAR.eqToHom_fT_toFun, Function.comp_apply] <;>
    rfl

/-- The `Functor.CoreMonoidal` data for the inclusion: `εIso`/`μIso` are the
    `eqToIso`s of the object coherences. -/
def ι.coreMonoidal : (ι (α := α) (β := β)).CoreMonoidal where
  εIso := eqToIso toMultiAR_empty.symm
  μIso X Y := eqToIso (toMultiAR_concat X Y).symm
  μIso_hom_natural_left {X Y} f X' := by
    refine MultiAR.Hom.ext_fin fun i x => ?_
    fin_cases i <;>
      simp only [ι_obj, ι_map, eqToIso.hom, MonoidalCategoryStruct.whiskerRight,
        MultiAR.comp_fT', MultiAR.Hom.concatMap_fT, MultiAR.eqToHom_fT_toFun,
        AR.Hom.toMultiFT, AR.Hom.toMultiAR, LabeledTuple.Hom.comp_toFun,
        LabeledTuple.Hom.concatMap_toFun, Function.comp_apply] <;>
      rfl
  μIso_hom_natural_right {X Y} X' f := by
    refine MultiAR.Hom.ext_fin fun i x => ?_
    fin_cases i <;>
      simp only [ι_obj, ι_map, eqToIso.hom, MonoidalCategoryStruct.whiskerLeft,
        MultiAR.comp_fT', MultiAR.Hom.concatMap_fT, MultiAR.eqToHom_fT_toFun,
        AR.Hom.toMultiFT, AR.Hom.toMultiAR, LabeledTuple.Hom.comp_toFun,
        LabeledTuple.Hom.concatMap_toFun, Function.comp_apply] <;>
      rfl
  associativity X Y Z := by
    refine MultiAR.Hom.ext_fin fun i x => ?_
    fin_cases i <;>
      simp only [ι_obj, eqToIso.hom, MonoidalCategoryStruct.whiskerRight,
        MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.associator,
        MonoidalCategoryStruct.tensorObj, MultiAR.comp_fT', MultiAR.Hom.concatMap_fT,
        MultiAR.eqToHom_fT_toFun, eqToHom_map, MultiAR.Hom.id_fT, LabeledTuple.Hom.id_toFun,
        LabeledTuple.Hom.comp_toFun, LabeledTuple.Hom.concatMap_toFun, Function.comp_apply,
        Fin.val_cast, Fin.appendMap_val, id_eq,
        toMultiAR_concat, MultiAR.tiers_concat, LabeledTuple.concat_len] <;>
      (split_ifs <;> omega)
  left_unitality X := by
    refine MultiAR.Hom.ext_fin fun i x => ?_
    fin_cases i <;>
      · simp only [ι_obj, eqToIso.hom, MonoidalCategoryStruct.leftUnitor,
          MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.tensorUnit,
          MultiAR.comp_fT', MultiAR.Hom.concatMap_fT,
          MultiAR.eqToHom_fT_toFun, eqToHom_map, MultiAR.Hom.id_fT, LabeledTuple.Hom.id_toFun,
          LabeledTuple.Hom.comp_toFun, LabeledTuple.Hom.concatMap_toFun, Function.comp_apply,
          Fin.val_cast, Fin.appendMap_val, id_eq,
          MultiAR.empty, MultiGraph.empty, LabeledTuple.empty_len, toMultiAR_empty_tiers_len]
        have hx := x.isLt
        simp only [MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit,
          MultiAR.tiers_concat, LabeledTuple.concat_len, MultiAR.empty, MultiGraph.empty,
          LabeledTuple.empty_len, Nat.zero_add] at hx
        split_ifs <;> omega
  right_unitality X := by
    refine MultiAR.Hom.ext_fin fun i x => ?_
    fin_cases i <;>
      · simp only [ι_obj, eqToIso.hom, MonoidalCategoryStruct.rightUnitor,
          MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.tensorUnit,
          MultiAR.comp_fT', MultiAR.Hom.concatMap_fT,
          MultiAR.eqToHom_fT_toFun, eqToHom_map, MultiAR.Hom.id_fT, LabeledTuple.Hom.id_toFun,
          LabeledTuple.Hom.comp_toFun, LabeledTuple.Hom.concatMap_toFun, Function.comp_apply,
          Fin.val_cast, Fin.appendMap_val, id_eq,
          MultiAR.empty, MultiGraph.empty, LabeledTuple.empty_len]
        have hx := x.isLt
        simp only [MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit,
          MultiAR.tiers_concat, LabeledTuple.concat_len, MultiAR.empty, MultiGraph.empty,
          LabeledTuple.empty_len, Nat.add_zero] at hx
        split_ifs <;> omega

/-- **The strong monoidal functor** `AR α β ⥤ MultiAR (biTier α β)`. -/
instance : (ι (α := α) (β := β)).Monoidal := ι.coreMonoidal.toMonoidal

end Autosegmental
