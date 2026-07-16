import Linglib.Semantics.Dynamic.DRS.Indexed
import Linglib.Semantics.Dynamic.Category

/-!
# DRT's category of contexts

Well-formed DRSs are the morphisms of a category whose objects are
contexts (bases of discourse referents): a morphism `X ⟶ Y` is a DRS
whose free referents are supplied by `X` (the referential
presupposition), whose occurring referents are *visible* — declared in
the context or introduced by the DRS itself — and whose introductions
are fresh for the context, growing `X` to `Y`. Composition is `merge`;
identity is the empty DRS.

The visibility invariant is what makes composition unconditional: it
*derives* the Merging Lemma's capture-freshness side condition, so
`merge` needs no hypotheses here. Interpretation (`Ctx.sem`) is then an
identity-on-objects functor into the semantic category of contexts
`DynamicSemantics.Ctx`, and its functoriality on composition *is* the
Merging Lemma (`DRS.transition_merge`).

"Category of contexts" is the field's name for this structure: it is a
syntactic category in the sense of categorical logic (objects are
contexts — declarations of variables, type theory's *bases*, cf.
[visser-1998] — and arrows are syntax), and the diachronic information
ordering of [visser-vermeulen-1996]'s bracketing approach, in which
contexts under merge form a category
([muskens-van-benthem-visser-2011]'s m-categories). `DRT.Ctx` and
`DynamicSemantics.Ctx` name the two levels of DRT's architecture, not
rival theories: DRT's distinctive *representation* level, where contexts
compose by merging boxes, and the framework-neutral semantic level,
where they compose transitions relationally — the level other dynamic
frameworks interpret into as well.

## Main definitions

- `DRT.Ctx L V`: contexts, with well-formed DRSs as morphisms and
  `merge` as composition.
- `DRT.Ctx.sem`: interpretation as a functor into
  `DynamicSemantics.Ctx W M V`, given a model of the language.

## References

- [visser-vermeulen-1996], [visser-1998], [muskens-1996] (the merge
  algebra and context typing)
- [kamp-vangenabith-reyle-2011], [kamp-reyle-1993]
-/

namespace DRT

open CategoryTheory DynamicSemantics FirstOrder

universe u v w

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V]

/-- An object of DRT's category of contexts: a base of discourse
referents available in the context. -/
@[ext] structure Ctx (L : Language.{u, v}) (V : Type w) where
  /-- The available discourse referents. -/
  base : Finset V

namespace Ctx

/-- A morphism `X ⟶ Y`: a DRS whose free referents are supplied by `X`,
whose occurring referents are visible, and whose fresh introductions grow
`X` to `Y`. -/
@[ext] structure Hom (X Y : Ctx L V) where
  /-- The underlying DRS. -/
  drs : DRS L V
  /-- The referential presupposition: free referents are supplied by the
  context. -/
  presup : drs.fv ⊆ X.base
  /-- Visibility: every occurring referent is contextual or introduced. -/
  occ_le : Condition.occL drs.conditions ⊆ X.base ∪ drs.referents
  /-- Introductions are fresh for the context. -/
  fresh : Disjoint X.base drs.referents
  /-- The context grows by the introduced referents. -/
  target : X.base ∪ drs.referents = Y.base

instance : Category (Ctx L V) where
  Hom := Hom
  id X :=
    ⟨DRS.empty, by simp [DRS.empty], by simp [DRS.empty, Condition.occL],
      by simp [DRS.empty], by simp [DRS.empty]⟩
  comp {X Y Z} u v :=
    { drs := u.drs.merge v.drs
      presup := DRS.fv_merge_subset u.presup (by rw [u.target]; exact v.presup)
      occ_le := by
        rw [DRS.conditions_merge, Condition.occL_append, DRS.referents_merge,
          ← Finset.union_assoc]
        exact Finset.union_subset
          (u.occ_le.trans Finset.subset_union_left)
          (by rw [u.target]; exact v.occ_le)
      fresh := by
        rw [DRS.referents_merge, Finset.disjoint_union_right]
        refine ⟨u.fresh, ?_⟩
        have : Disjoint Y.base v.drs.referents := v.fresh
        rw [← u.target] at this
        exact this.mono_left Finset.subset_union_left
      target := by
        rw [DRS.referents_merge, ← Finset.union_assoc, u.target, v.target] }
  id_comp u := Hom.ext (DRS.empty_merge u.drs)
  comp_id u := Hom.ext (DRS.merge_empty u.drs)
  assoc u v w := Hom.ext (DRS.merge_assoc u.drs v.drs w.drs)

@[simp] theorem drs_id (X : Ctx L V) : Hom.drs (𝟙 X) = DRS.empty := rfl

@[simp] theorem drs_comp {X Y Z : Ctx L V} (u : X ⟶ Y) (v : Y ⟶ Z) :
    (u ≫ v).drs = u.drs.merge v.drs := rfl

/-- **Interpretation is a functor**: a model of `L` sends DRT's category
of contexts to the semantic one, identically on objects and a DRS to its
transition — and functoriality on composition is the Merging Lemma, its
capture-freshness side condition derived from the visibility invariant. -/
def sem (W M : Type*) [L.Structure M] [Nonempty M] :
    Ctx L V ⥤ DynamicSemantics.Ctx W M V where
  obj X := ⟨X.base⟩
  map {X Y} u := ⟨(u.drs.transition W X.base u.presup).copy rfl u.target⟩
  map_id X := by
    apply DynamicSemantics.Ctx.Hom.ext
    exact DRS.transition_empty W X.base _ _
  map_comp {X Y Z} u v := by
    apply DynamicSemantics.Ctx.Hom.ext
    have hocc : Condition.occL u.drs.conditions ⊆ Y.base := by
      rw [← u.target]; exact u.occ_le
    have hfresh : Disjoint v.drs.referents (Condition.occL u.drs.conditions) :=
      v.fresh.symm.mono_right hocc
    have hv : v.drs.fv ⊆ X.base ∪ u.drs.referents := by
      rw [u.target]; exact v.presup
    show ((u ≫ v).drs.transition W X.base (u ≫ v).presup).copy rfl (u ≫ v).target =
      ((u.drs.transition W X.base u.presup).copy rfl u.target).comp
        ((v.drs.transition W Y.base v.presup).copy rfl v.target)
    rw [← DRS.transition_copy (M := M) W v.drs u.target hv v.presup,
      Transition.copy_copy, Transition.copy_comp_copy,
      DRS.transition_merge (M := M) W u.drs v.drs u.presup hv hfresh,
      Transition.copy_copy]
    rfl

end Ctx

end DRT
