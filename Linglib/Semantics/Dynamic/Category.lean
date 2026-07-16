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

The presheaf of state fibers is the composite of the environments
presheaf with the powerset functor — definitionally, in this
formulation: the predecessor proved the isomorphism
(`presheafIsoEnvironments`); typing states at their environments makes
it the definition (`State.presheaf`). Restriction is `Set.image` along
environment weakening, the ∃-leg of mathlib's
`Set.image_preimage`/`Set.preimage_kernImage` triple ([lawvere-1969]'s
quantifiers as adjoints to weakening, as retold by [jacobs-1999]).
Syntax categories interpret into `Ctx` (`DRS/Category.lean`); the fiber
at `∅` is [veltman-1996]'s update semantics.

## Main definitions

- `Ctx W M V`: bundled contexts, with a `Category` instance whose
  morphisms are `Transition`s between the bases.
- `environments`: the presheaf of world–assignment pairs at each
  granularity — a set-valued indexed category in [jacobs-1999]'s sense,
  its maps the semantic face of *weakening*. Precedent for the
  states-as-presheaf reading: [abramsky-sadrzadeh-2014].
- `State.presheaf`: the state fibers — `environments ⋙ Set`.

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

/-! ### The environments presheaf and the state fibers -/

universe u v w

/-- The presheaf of environments: over `X`, world–assignment pairs at
granularity `X`; restriction precomposes with the inclusion. A model read
over the category of contexts — a set-valued *indexed category* in
[jacobs-1999]'s sense, whose maps are the semantic face of *weakening*
(the functor "which adds an extra dummy" variable, in the book's own
gloss). -/
def environments (W : Type u) (M : Type v) (V : Type w) :
    (Finset V)ᵒᵖ ⥤ Type (max u v w) where
  obj X := W × ((↑X.unop : Set V) → M)
  map {X Y} f := TypeCat.ofHom fun p =>
    ⟨p.1, fun v => p.2 ⟨v.1, leOfHom f.unop v.2⟩⟩

/-- The state fibers as a presheaf on the poset of bases: the powerset
functor applied fiberwise to the environments — by definition, in this
formulation. The fiber over `X` is `Set (W × (↑X → M))`; restriction is
direct image along environment weakening. -/
def State.presheaf (W : Type u) (M : Type v) (V : Type w) :
    (Finset V)ᵒᵖ ⥤ Type (max u v w) :=
  environments W M V ⋙ ofTypeFunctor Set

end DynamicSemantics
