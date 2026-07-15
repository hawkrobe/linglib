import Linglib.Semantics.Dynamic.Transition
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic

/-!
# The category of contexts

Indexed dynamic semantics is a category: objects are contexts (bases of
live discourse referents), morphisms are `Transition`s, composition is
world-pointwise relational composition. The identity and associativity
laws are `Transition.lean`'s `id_comp`/`comp_id`/`comp_assoc`.

## Main definitions

- `Ctx W M V`: bundled contexts, with a `Category` instance whose
  morphisms are `Transition`s between the bases.
- `State.presheaf`: information states as a presheaf on the poset of
  bases — the fiber over `X` is the states indexed at `X`, restriction is
  `State.restrict`.

## Implementation notes

Morphisms are a one-field structure wrapping `Transition` (the
`RelCat.Hom` pattern): an unbundled `Hom` field breaks dot-notation on
morphisms. The collapse functor to `RelCat` lives in `Collapse.lean`,
because importing `RelCat` interferes with instance resolution for the
functions category on `Type u`, which `State.presheaf` needs.

## References

- [kamp-vangenabith-reyle-2011]
- [muskens-van-benthem-visser-2011]
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

end DynamicSemantics
