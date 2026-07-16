import Linglib.Semantics.Dynamic.Transition
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Functor

/-!
# The category of contexts

Indexed dynamic semantics is a category: objects are contexts (bases of
live discourse referents), morphisms are `Transition`s, composition is
world-pointwise relational composition. The identity and associativity
laws are `Transition.lean`'s `id_comp`/`comp_id`/`comp_assoc`.

The category locates the module's inhabitants. States over a context are
not an independent structure: `State.presheaf` is the powerset functor
applied fiberwise to the presheaf of environments
(`presheafIsoEnvironments`), so level 1 is the `Set` effect read over
the category of contexts, exactly as `Collapse.lean`'s level 0 is the
same effect read over a point — and `Partial.lean`'s partial CCPs are
the `Part` column. Under the identification, `State.restrict` is direct
image along environment projections (`fiberOrderIsoProd_restrict`), the
left adjoint of mathlib's `Set.image_preimage`/`Set.preimage_kernImage`
triple: [lawvere-1969]'s quantifiers as adjoints, in [jacobs-1999]'s
fibrational reading of contexts — the "indexed" picture `State.lean`
cites via [visser-1998]. Syntax categories interpret into `Ctx`
(`DRS/Category.lean`'s `sem`); the degenerate fiber at `∅` is
[veltman-1996]'s update semantics (`State.fiberEmptyOrderIso`).

## Main definitions

- `Ctx W M V`: bundled contexts, with a `Category` instance whose
  morphisms are `Transition`s between the bases.
- `State.presheaf`: information states as a presheaf on the poset of
  bases — the fiber over `X` is the states indexed at `X`, restriction is
  `State.restrict`. Precedent: [abramsky-sadrzadeh-2014]'s presheaf of
  basic DRSs over vocabulary–variable contexts, whose base category
  additionally has relabelling morphisms; ours is the inclusions-only
  fragment with model-theoretic fibers.
- `environments`: the presheaf of world–assignment pairs at each
  granularity — a model read over the category of contexts.
- `State.presheafIsoEnvironments`: `State.presheaf` is the composite of
  `environments` with the powerset functor.

## Main results

- `State.fiberOrderIsoProd_restrict`: under the fiber classification,
  restriction is direct image along the environment projection.

## Implementation notes

Morphisms are a one-field structure wrapping `Transition` (the
`RelCat.Hom` pattern): an unbundled `Hom` field breaks dot-notation on
morphisms. The collapse functor to `RelCat` lives in `Collapse.lean`,
because importing `RelCat` interferes with instance resolution for the
functions category on `Type u`, which `State.presheaf` needs.

## References

- [kamp-vangenabith-reyle-2011]
- [muskens-van-benthem-visser-2011], [abramsky-sadrzadeh-2014]
- [lawvere-1969], [jacobs-1999]
- [groenendijk-stokhof-1991], [muskens-1996]
-/

namespace DynamicSemantics

open CategoryTheory

/-- A context: a base of live discourse referents, bundled as an object of
the category whose morphisms are `Transition W M X Y`. -/
@[ext] structure Ctx (W M : Type*) (V : Type*) where
  /-- The live discourse referents. -/
  base : Finset V

namespace Ctx

variable {W M V : Type*}

/-- Morphisms of contexts: transitions between the bases. -/
@[ext] structure Hom (X Y : Ctx W M V) where
  /-- The underlying transition. -/
  t : Transition W M X.base Y.base

instance : Category (Ctx W M V) where
  Hom := Hom
  id X := ⟨Transition.id X.base⟩
  comp u v := ⟨u.t.comp v.t⟩
  id_comp u := Hom.ext (Transition.id_comp u.t)
  comp_id u := Hom.ext (Transition.comp_id u.t)
  assoc u v w := Hom.ext (Transition.comp_assoc u.t v.t w.t)

@[simp] theorem t_id (X : Ctx W M V) : Hom.t (𝟙 X) = Transition.id X.base := rfl

@[simp] theorem t_comp {X Y Z : Ctx W M V} (u : X ⟶ Y) (v : Y ⟶ Z) :
    (u ≫ v).t = u.t.comp v.t := rfl

end Ctx

/-! ### The state presheaf -/

universe u v w

/-- Information states form a presheaf on the poset of bases: the fiber
over `X` is the states indexed at `X`, and restriction along `Y ⊆ X` is
`State.restrict` — the presheaf laws are `restrict_base` and
`restrict_restrict`. -/
def State.presheaf (W : Type u) (M : Type v) (V : Type w) :
    (Finset V)ᵒᵖ ⥤ Type (max u v w) where
  obj X := State.fiber W M X.unop
  map {X Y} f := TypeCat.ofHom
    fun I => ⟨I.val.restrict Y.unop, State.base_restrict I.val Y.unop⟩
  map_id X := by
    ext I : 3
    apply Subtype.ext
    obtain ⟨J, hJ⟩ := I
    show J.restrict X.unop = J
    rw [← hJ]
    exact J.restrict_base
  map_comp {X Y Z} h k := by
    ext I : 3
    exact Subtype.ext (I.val.restrict_restrict (leOfHom k.unop)).symm

/-! ### The presheaf is a composite -/

/-- The presheaf of environments: over `X`, world–assignment pairs at
granularity `X`; restriction precomposes with the inclusion. A model read
over the category of contexts ([jacobs-1999]). -/
def environments (W : Type u) (M : Type v) (V : Type w) :
    (Finset V)ᵒᵖ ⥤ Type (max u v w) where
  obj X := W × ((↑X.unop : Set V) → M)
  map {X Y} f := TypeCat.ofHom fun p =>
    ⟨p.1, fun v => p.2 ⟨v.1, leOfHom f.unop v.2⟩⟩

section Classified
variable {W : Type u} {M : Type v} {V : Type w} [Nonempty M]

open scoped Classical in
/-- Under the fiber classification, restriction is direct image along the
environment projection — the left adjoint of mathlib's
`Set.image_preimage`/`Set.preimage_kernImage` triple: [lawvere-1969]'s
quantifiers as adjoints, over the category of contexts. -/
theorem State.fiberOrderIsoProd_restrict {X Y : Finset V} (hYX : Y ⊆ X)
    (I : State.fiber W M X) :
    OrderDual.ofDual (State.fiberOrderIsoProd Y
        ⟨I.val.restrict Y, State.base_restrict I.val Y⟩) =
      (fun p : W × ((↑X : Set V) → M) =>
        (p.1, fun v : (↑Y : Set V) => p.2 ⟨v.1, hYX v.2⟩)) ''
        OrderDual.ofDual (State.fiberOrderIsoProd X I) := by
  ext ⟨w, h⟩
  constructor
  · intro hmem
    have hg : (↑Y : Set V).restrict (fun v => if hv : v ∈ (↑Y : Set V) then
        h ⟨v, hv⟩ else Classical.arbitrary M) = h :=
      funext fun v => dif_pos v.2
    rw [← hg] at hmem
    obtain ⟨k, hk, hkg⟩ := State.mem_restrict.mp
      (State.mem_fiberOrderIsoProd.mp hmem)
    refine ⟨(w, (↑X : Set V).restrict k),
      State.mem_fiberOrderIsoProd.mpr hk, ?_⟩
    refine Prod.ext rfl ?_
    rw [← hg]
    funext v
    exact hkg v.2
  · rintro ⟨⟨w', e⟩, hmem, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
    have hk : (↑X : Set V).restrict (fun v => if hv : v ∈ (↑X : Set V) then
        e ⟨v, hv⟩ else Classical.arbitrary M) = e :=
      funext fun v => dif_pos v.2
    rw [← hk] at hmem
    have hYk : (↑Y : Set V).restrict (fun v => if hv : v ∈ (↑X : Set V) then
        e ⟨v, hv⟩ else Classical.arbitrary M) =
        fun v : (↑Y : Set V) => e ⟨v.1, hYX v.2⟩ :=
      funext fun v => dif_pos (hYX v.2)
    rw [← hYk]
    exact State.mem_fiberOrderIsoProd.mpr
      (State.mem_restrict.mpr
        ⟨_, State.mem_fiberOrderIsoProd.mp hmem, Set.eqOn_refl _ _⟩)

/-- `State.presheaf` is not primitive: it is the composite of the
environments presheaf with the powerset functor — the fiber
classification `State.fiberOrderIsoProd`, naturally in the base. The
`Set` here is the same monad whose Kleisli category is level 0
(`Collapse.lean`): the presheaf face and the monadic face of dynamic
semantics are one structure. -/
noncomputable def State.presheafIsoEnvironments
    (W : Type u) (M : Type v) (V : Type w) [Nonempty M] :
    State.presheaf W M V ≅ environments W M V ⋙ ofTypeFunctor Set :=
  NatIso.ofComponents
    (fun X => ((State.fiberOrderIsoProd X.unop).toEquiv.trans
      OrderDual.ofDual).toIso)
    (by
      intro X Y f
      ext I : 3
      show OrderDual.ofDual (State.fiberOrderIsoProd Y.unop
          ⟨I.val.restrict Y.unop, State.base_restrict I.val Y.unop⟩) = _
      rw [State.fiberOrderIsoProd_restrict (leOfHom f.unop) I]
      show _ = Functor.map _ (OrderDual.ofDual (State.fiberOrderIsoProd X.unop I))
      rw [Set.fmap_eq_image]
      rfl)

end Classified

end DynamicSemantics
