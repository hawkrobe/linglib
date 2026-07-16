import Linglib.Semantics.Dynamic.Update
import Mathlib.Data.Set.Functor
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.Order.Hom.CompleteLattice

/-!
# The update algebra is the Kleisli construction
[charlow-2014] [muskens-van-benthem-visser-2011]

The two faces of `Update.lean`'s algebra are canonical, not a design
choice. An update
`S → S → Prop` is a Kleisli arrow `S → Set S` of the powerset monad —
definitionally — and under that reading sequencing is Kleisli
composition, the trivial test is `pure`, and `lift` is `bind`:
[charlow-2014]'s monadic view of dynamic semantics, as theorems. `lift`
is then an equivalence onto the completely-join-preserving transformers
(`sSupHom`), so the transformer algebra is the suplattice completion of
the relational one and the non-distributive tests (`might`, `must`) are
exactly the residue. Categorically, `RelCat ≌ KleisliCat Set`; with
`Ctx.collapse` landing in `RelCat`, the indexed tower reads
`Ctx ⥤ RelCat ≌ KleisliCat Set ↪ suplattice endomaps`, every arrow
canonical.

## Main results

- `dseq_eq_kleisliComp`, `test_top_eq_pure`, `lift_eq_bind`: the monadic
  reading of the update algebra.
- `isDistributive_iff_map_sSup`, `liftEquiv`, `liftEquiv_dseq`:
  distributive CCPs are exactly the completely-join-preserving maps, and
  `lift`/`lower` is an equivalence onto them, sending sequencing to
  composition.
- `relCatEquivKleisli`: `RelCat ≌ KleisliCat Set`. [UPSTREAM] candidate —
  pure category theory, absent from mathlib.
-/

namespace DynamicSemantics

attribute [local instance] Set.monad

universe u

variable {S : Type*}

/-! ### The Set-monad reading -/

/-- Sequencing is Kleisli composition for the powerset monad: an update
is a Kleisli arrow `S → Set S`, definitionally. -/
theorem dseq_eq_kleisliComp (D₁ D₂ : S → Set S) :
    (dseq D₁ D₂ : S → Set S) = D₁ >=> D₂ :=
  funext fun i => Set.ext fun j => by
    rw [Bind.kleisliRight, Set.bind_def, Set.mem_iUnion₂]
    exact exists_congr fun k => exists_prop.symm

/-- The trivial test is `pure`. -/
theorem test_top_eq_pure :
    (test (fun _ => True) : Update S) = fun i => (pure i : Set S) :=
  funext fun _ => Set.ext fun _ => (and_iff_left trivial).trans eq_comm

/-- `lift` is `bind`: the relational image is the monad's extension
operator. -/
theorem lift_eq_bind (R : Update S) (σ : Set S) :
    lift R σ = σ >>= (R : S → Set S) :=
  Set.ext fun j => by
    rw [Set.bind_def, Set.mem_iUnion₂]
    exact exists_congr fun i => exists_prop.symm

/-! ### Distributivity is complete join preservation -/

/-- A CCP is distributive iff it preserves arbitrary joins of states. -/
theorem isDistributive_iff_map_sSup (φ : CCP S) :
    CCP.IsDistributive φ ↔ ∀ T : Set (Set S), φ (sSup T) = sSup (φ '' T) := by
  simp only [Set.sSup_eq_sUnion]
  constructor
  · intro h T
    ext j
    constructor
    · intro hj
      rw [h] at hj
      obtain ⟨i, ⟨t, ht, hit⟩, hji⟩ := hj
      refine ⟨φ t, ⟨t, ht, rfl⟩, ?_⟩
      rw [h t]
      exact ⟨i, hit, hji⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, hjt⟩
      rw [h t] at hjt
      obtain ⟨i, hit, hji⟩ := hjt
      rw [h]
      exact ⟨i, ⟨t, ht, hit⟩, hji⟩
  · intro h s
    have hs : s = ⋃₀ ((fun i => ({i} : Set S)) '' s) := by
      ext i
      simp
    ext j
    constructor
    · intro hj
      rw [hs, h] at hj
      obtain ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, hji⟩ := hj
      exact ⟨i, hi, hji⟩
    · rintro ⟨i, hi, hji⟩
      rw [hs, h]
      exact ⟨φ {i}, ⟨{i}, ⟨i, hi, rfl⟩, rfl⟩, hji⟩

/-- The relational algebra is exactly the completely-join-preserving
fragment of the transformer algebra: `lift`/`lower` as an equivalence
onto `sSupHom`. -/
def liftEquiv : Update S ≃ sSupHom (Set S) (Set S) where
  toFun R := ⟨lift R, (isDistributive_iff_map_sSup _).mp (lift_isDistributive R)⟩
  invFun f := lower f
  left_inv := lower_lift
  right_inv f := sSupHom.ext fun σ =>
    congrFun (lift_lower _ ((isDistributive_iff_map_sSup _).mpr f.map_sSup')) σ

/-- The equivalence sends sequencing to composition (diagrammatic order):
the transformer monoid restricts to the relational one. -/
theorem liftEquiv_dseq (D₁ D₂ : Update S) :
    (liftEquiv (D₁ ⨟ D₂) : Set S → Set S) =
      (liftEquiv D₂ : Set S → Set S) ∘ (liftEquiv D₁ : Set S → Set S) :=
  lift_dseq D₁ D₂

/-! ### `RelCat ≌ KleisliCat Set` -/

open CategoryTheory

/-- [UPSTREAM] Relations to Kleisli arrows of the powerset monad: curry. -/
def relCatToKleisli : RelCat.{u} ⥤ KleisliCat Set where
  obj X := X
  map f := fun x => {y | (x, y) ∈ f.rel}
  map_id X := funext fun x => by
    ext y
    show (x, y) ∈ SetRel.id ↔ y ∈ ({x} : Set X)
    simp [SetRel.id, eq_comm]
  map_comp {X Y Z} f g := funext fun x => by
    ext z
    show (x, z) ∈ SetRel.comp f.rel g.rel ↔ _
    simp only [SetRel.comp, KleisliCat.comp_def,
      Set.bind_def, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

/-- [UPSTREAM] Kleisli arrows of the powerset monad to relations:
uncurry. -/
def kleisliToRelCat : KleisliCat Set ⥤ RelCat.{u} where
  obj X := X
  map f := .ofRel {p | p.2 ∈ f p.1}
  map_id X := by
    apply RelCat.Hom.ext
    ext ⟨x, y⟩
    show y ∈ ({x} : Set X) ↔ (x, y) ∈ SetRel.id
    simp [SetRel.id, eq_comm]
  map_comp {X Y Z} f g := by
    apply RelCat.Hom.ext
    ext ⟨x, z⟩
    simp only [KleisliCat.comp_def, Set.bind_def, Set.mem_iUnion,
      Set.mem_setOf_eq, exists_prop]
    rfl

/-- [UPSTREAM] The category of relations is the Kleisli category of the
powerset monad. -/
def relCatEquivKleisli : RelCat.{u} ≌ KleisliCat Set :=
  CategoryTheory.Equivalence.mk relCatToKleisli kleisliToRelCat
  (NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    apply RelCat.Hom.ext
    ext ⟨x, y⟩
    simp only [relCatToKleisli, kleisliToRelCat, Functor.id_map,
      Functor.comp_map, Iso.refl_hom, RelCat.Hom.rel_comp, RelCat.Hom.rel_id]
    constructor
    · rintro ⟨b, hb, he⟩
      obtain rfl : b = y := he
      exact ⟨x, rfl, hb⟩
    · rintro ⟨b, he, hb⟩
      obtain rfl : x = b := he
      exact ⟨y, hb, rfl⟩))
  (NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    funext x
    ext y
    simp only [relCatToKleisli, kleisliToRelCat, Functor.id_map,
      Functor.comp_map, Iso.refl_hom, KleisliCat.comp_def, KleisliCat.id_def,
      Set.bind_def, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨x, rfl, hi⟩
    · rintro ⟨i, hi, hyf⟩
      obtain rfl : i = x := hi
      exact ⟨y, hyf, rfl⟩))

end DynamicSemantics
