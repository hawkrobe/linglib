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
- `environments_glue`, `environments_beck_chevalley`: the context-lattice
  square is a pullback of environments, so quantification commutes with
  weakening — the fibers are a hyperdoctrine.

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

/-! ### Gluing and Beck–Chevalley

`environments` sends each square of the context lattice to a pullback
(`environments_glue`), so quantification and weakening cohere: the
existential legs (`Set.image`, which is `State.presheaf`'s own action)
commute with reindexing (`Set.preimage`) across the square
(`environments_beck_chevalley`). Together with mathlib's
`Set.image_subset_iff` (`∃ ⊣ weakening`), `Set.preimage_kernImage`
(`weakening ⊣ ∀`), and `Set.image_inter_preimage` (Frobenius), the
fibers form a hyperdoctrine over the context lattice ([lawvere-1969],
[jacobs-1999]). -/

section Gluing

open Opposite

variable {W M V : Type*} {X Y : Finset V}

/-- The action of `environments` on a lattice inequality, elementwise. -/
@[simp] theorem environments_map_apply (h : X ≤ Y)
    (p : (environments W M V).obj (op Y)) :
    (environments W M V).map (homOfLE h).op p =
      (p.1, fun v => p.2 ⟨v.1, h v.2⟩) := rfl

variable [DecidableEq V]

/-- Environments glue: a pair of environments over `X` and `Y` whose
weakenings to `X ⊓ Y` agree is jointly the weakening of a unique
environment over `X ⊔ Y` — `environments` sends the lattice square to a
pullback of types. The piecewise witness is the environment face of
`Possibility.union`. -/
theorem environments_glue
    (a : (environments W M V).obj (op X)) (b : (environments W M V).obj (op Y))
    (hab : (environments W M V).map (homOfLE inf_le_left).op a =
      (environments W M V).map (homOfLE inf_le_right).op b) :
    ∃! c : (environments W M V).obj (op (X ⊔ Y)),
      (environments W M V).map (homOfLE le_sup_left).op c = a ∧
        (environments W M V).map (homOfLE le_sup_right).op c = b := by
  simp only [environments_map_apply] at hab ⊢
  have hw : a.1 = b.1 := congrArg Prod.fst hab
  have hagree : ∀ (v : V) (hX : v ∈ X) (hY : v ∈ Y),
      a.2 ⟨v, hX⟩ = b.2 ⟨v, hY⟩ := fun v hX hY =>
    congrFun (congrArg Prod.snd hab) ⟨v, Finset.mem_inter.mpr ⟨hX, hY⟩⟩
  refine ⟨(a.1, fun v => if h : v.1 ∈ X then a.2 ⟨v.1, h⟩
      else b.2 ⟨v.1, (Finset.mem_union.mp v.2).resolve_left h⟩),
    ⟨Prod.ext rfl (funext fun v => dif_pos v.2),
      Prod.ext hw (funext fun v => ?_)⟩, fun c' hc' => ?_⟩
  · by_cases h : v.1 ∈ X
    · exact (dif_pos h).trans (hagree v.1 h v.2)
    · exact dif_neg h
  · obtain ⟨rfl, rfl⟩ := hc'
    exact Prod.ext rfl (funext fun v => by by_cases h : v.1 ∈ X <;> simp [h])

/-- Beck–Chevalley for the context-lattice square: existential image
along `X ⊓ Y ≤ X` then weakening to `Y` is weakening to `X ⊔ Y` then
existential image along `Y ≤ X ⊔ Y` — quantifying and reindexing
commute. The image legs are `State.presheaf`'s own action on the
square's arrows. -/
theorem environments_beck_chevalley (X Y : Finset V)
    (S : Set ((environments W M V).obj (op X))) :
    (environments W M V).map (homOfLE (inf_le_right : X ⊓ Y ≤ Y)).op ⁻¹'
      ((environments W M V).map (homOfLE (inf_le_left : X ⊓ Y ≤ X)).op '' S) =
    (environments W M V).map (homOfLE (le_sup_right : Y ≤ X ⊔ Y)).op ''
      ((environments W M V).map (homOfLE (le_sup_left : X ≤ X ⊔ Y)).op ⁻¹' S) := by
  ext b
  constructor
  · rintro ⟨a, ha, hab⟩
    obtain ⟨c, ⟨hcX, hcY⟩, -⟩ := environments_glue a b hab
    exact ⟨c, show _ ∈ S by rw [hcX]; exact ha, hcY⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨(environments W M V).map (homOfLE le_sup_left).op c, hc, ?_⟩
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, homOfLE_comp, homOfLE_comp]

end Gluing

end DynamicSemantics
