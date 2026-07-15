import Linglib.Semantics.Dynamic.Transition
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic

/-!
# The category of contexts
[kamp-vangenabith-reyle-2011], [groenendijk-stokhof-1991], [muskens-1996]

Based dynamic semantics is a category: objects are contexts (bases of live
discourse referents), morphisms are `Transition`s, composition is
world-pointwise relational composition. The identity and associativity laws
are `Transition.lean`'s `id_comp`/`comp_id`/`comp_assoc`.

Two structures make the levels of the spine mathematically precise:

* `State.presheaf` — information states form a presheaf on the poset of
  bases: the fiber over `X` is the states based at `X`, restriction along
  `Y ⊆ X` is `State.restrict`.
* `Ctx.collapse` — the *one-object collapse* to level 0 is a functor to
  mathlib's `RelCat` sending a context to its possibilities *up to
  agreement on the base* and a transition to its `toUpdate` relation.
  The quotient is forced: `toUpdate` sends `𝟙 X` to agreement-on-`X`, not
  to equality, so the collapse is only lawful on base-agreement classes —
  `supported_left`/`supported_right` are exactly the congruence
  conditions. The collapse is faithful (`Ctx.collapse_faithful`): a
  transition loses nothing under it; what the collapse forgets is the
  base-indexing of the objects.

## Main declarations

* `Ctx` — bundled contexts; `Category (Ctx W M V)` with `Transition` homs.
* `State.presheaf` — the fibered states, contravariant along `⊆`.
* `Ctx.agreeSetoid` / `Ctx.collapse` — the collapse functor to `RelCat`.
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

/-- The states based at `X`: the fiber of the presheaf of states. -/
abbrev State.fiber (W M : Type*) {V : Type*} (X : (Finset V)ᵒᵖ) : Type _ :=
  {I : State W V M // I.base = X.unop}

/-- Information states form a presheaf on the poset of bases: the fiber
over `X` is the states based at `X`, and restriction along `Y ⊆ X` is
`State.restrict` — the presheaf laws are `restrict_base` and
`restrict_restrict`. -/
def State.presheaf (W : Type u) (M : Type v) (V : Type w) :
    (Finset V)ᵒᵖ ⥤ Type (max u v w) where
  obj := State.fiber W M
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
