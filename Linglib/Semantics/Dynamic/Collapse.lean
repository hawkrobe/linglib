import Linglib.Semantics.Dynamic.Category
import Mathlib.Data.Set.Functor
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.Order.Hom.CompleteLattice

/-!
# The one-object collapse and the Kleisli reading

The descent from indexed dynamic semantics to level 0 — the relational
algebra of procedures over a single state space
([muskens-van-benthem-visser-2011]'s "Dynamic Constants as Operators in
Relational Algebra") — and the canonicity of level 0 itself. An update
`S → S → Prop` is a Kleisli arrow `S → Set S` of the powerset monad —
definitionally — so sequencing is Kleisli composition, the trivial test is
`pure`, and `lift` is `bind` ([charlow-2014]'s monadic view of dynamic
semantics, as theorems); `lift` is then an equivalence onto the
completely-join-preserving transformers (`sSupHom`), so the transformer
algebra is the suplattice completion of the relational one and the
non-distributive tests (`might`, `must`) are exactly the residue.
Categorically, `RelCat ≌ KleisliCat Set`, and the indexed tower reads
`Ctx ⥤ RelCat ≌ KleisliCat Set ↪ suplattice endomaps`, every arrow
canonical.

The powerset monad is one column of the effect view of dynamic semantics
([moggi-1991], [shan-2001], [bumford-charlow-2024]): a framework's update
algebra is the Kleisli algebra of its chosen effect. Partiality is the
`Part` column (`Partial.lean`'s `seq_eq_kleisliComp`); probabilistic and
continuation-based systems choose further effects.

## Main definitions

- `Ctx.agreeSetoid`: `Possibility.agreeSetoid` at the context's base.
- `Ctx.collapse`: the functor `Ctx W M V ⥤ RelCat` sending a context to
  its possibilities up to base-agreement and a transition to its
  `toUpdate` relation.
- `liftEquiv`: `Update S ≃ sSupHom (Set S) (Set S)`.
- `relCatEquivKleisli`: `RelCat ≌ KleisliCat Set`. [UPSTREAM] candidate —
  pure category theory, absent from mathlib.

## Main results

- `Ctx.collapseRel_id`, `Ctx.collapseRel_comp`: identity and sequencing
  collapse to equality and relational composition on agreement classes.
- `Ctx.collapse_faithful`: a transition is recoverable from its collapsed
  relation; what the collapse forgets is the base-indexing of objects.
- `seq_eq_kleisliComp`, `test_top_eq_pure`, `lift_eq_bind`: the monadic
  reading of the update algebra.
- `isDistributive_iff_map_sSup`, `liftEquiv_seq`: distributive CCPs are
  exactly the completely-join-preserving maps, and `lift`/`lower` is an
  equivalence onto them, sending sequencing to composition.

## Implementation notes

The quotient is forced: `toUpdate` sends `𝟙 X` to agreement-on-`X`, not
to equality, so the collapse is lawful only on base-agreement classes —
`supported_left`/`supported_right` are exactly the congruence conditions.
This file is separate from `Category.lean` because importing `RelCat` (a
type synonym for `Type u` carrying the relations category) interferes
with instance resolution for the functions category on `Type u`.

## References

- [muskens-van-benthem-visser-2011], [charlow-2014]
- [moggi-1991], [shan-2001], [bumford-charlow-2024]
- [muskens-1996], [groenendijk-stokhof-1991]
-/

namespace DynamicSemantics

open CategoryTheory

/-! ### The collapse to `RelCat` -/

namespace Ctx

variable {W M V : Type*} {X Y Z : Ctx W M V}

/-- Agreement on the context's base: `Possibility.agreeSetoid` at `↑X.base`. -/
abbrev agreeSetoid (X : Ctx W M V) : Setoid (Possibility W V M) :=
  Possibility.agreeSetoid ↑X.base

/-- `toUpdate` descends to base-agreement classes: `supported_left` and
`supported_right` are precisely the congruence conditions. -/
def collapseRel (u : X ⟶ Y) :
    Quotient X.agreeSetoid → Quotient Y.agreeSetoid → Prop :=
  Quotient.lift₂ (fun p q => u.t.toUpdate p q)
    fun p₁ q₁ p₂ q₂ hp hq => propext <| by
      simp only [Transition.toUpdate]
      rw [hp.1, hq.1]
      exact and_congr Iff.rfl
        ((u.t.supported_left hp.2).trans (u.t.supported_right hq.2))

@[simp] theorem collapseRel_mk (u : X ⟶ Y)
    (p q : Possibility W V M) :
    collapseRel u (⟦p⟧) (⟦q⟧) ↔ u.t.toUpdate p q := Iff.rfl

/-- On base-agreement classes the identity transition collapses to
equality — the unitality the raw `toUpdate` lacks. -/
theorem collapseRel_id (X : Ctx W M V) (p q : Quotient X.agreeSetoid) :
    collapseRel (𝟙 X) p q ↔ p = q := by
  induction p using Quotient.ind
  induction q using Quotient.ind
  rename_i p q
  constructor
  · rintro ⟨hw, ha⟩
    exact Quotient.sound ⟨hw, ha⟩
  · intro h
    obtain ⟨hw, ha⟩ := Quotient.exact h
    exact ⟨hw, ha⟩

/-- On base-agreement classes sequencing collapses to relational
composition. -/
theorem collapseRel_comp (u : X ⟶ Y) (v : Y ⟶ Z)
    (p : Quotient X.agreeSetoid) (r : Quotient Z.agreeSetoid) :
    collapseRel (u ≫ v) p r ↔
      ∃ q, collapseRel u p q ∧ collapseRel v q r := by
  induction p using Quotient.ind
  induction r using Quotient.ind
  rename_i p r
  constructor
  · intro h
    have h' : Update.seq u.t.toUpdate v.t.toUpdate p r := by
      rw [← Transition.toUpdate_comp, ← t_comp]
      exact h
    obtain ⟨k, hk₁, hk₂⟩ := h'
    exact ⟨(⟦k⟧), hk₁, hk₂⟩
  · rintro ⟨q, hq₁, hq₂⟩
    induction q using Quotient.ind
    rename_i k
    show (u ≫ v).t.toUpdate p r
    rw [t_comp, Transition.toUpdate_comp]
    exact ⟨k, hq₁, hq₂⟩

/-- **The one-object collapse**: forget the bases, keeping possibilities up
to base-agreement. Functoriality on composition is `toUpdate_comp`; on
identities it is `Quotient.sound`/`exact` — which is why the quotient is
forced: on raw possibilities `toUpdate (𝟙 X)` is agreement-on-`X`, not
equality. -/
def collapse (W M V : Type*) : Ctx W M V ⥤ RelCat where
  obj X := Quotient X.agreeSetoid
  map u := .ofRel {pq | collapseRel u pq.1 pq.2}
  map_id X := by
    apply RelCat.Hom.ext
    ext ⟨p, q⟩
    rw [Set.mem_setOf_eq, RelCat.Hom.rel_id]
    exact (collapseRel_id X p q).trans SetRel.mem_id.symm
  map_comp {X Y Z} u v := by
    apply RelCat.Hom.ext
    ext ⟨p, r⟩
    rw [Set.mem_setOf_eq, RelCat.Hom.rel_comp, collapseRel_comp]
    constructor
    · rintro ⟨q, h₁, h₂⟩
      exact SetRel.prodMk_mem_comp h₁ h₂
    · rintro ⟨q, h₁, h₂⟩
      exact ⟨q, h₁, h₂⟩

/-- The collapse is faithful: a transition is recoverable from its relation
on base-agreement classes. What the collapse forgets is only the
base-indexing of the objects. -/
instance collapse_faithful : (collapse W M V).Faithful where
  map_injective {X Y} {u v} h := by
    have hs : ∀ p q : Possibility W V M, u.t.toUpdate p q ↔ v.t.toUpdate p q :=
      fun p q => Set.ext_iff.mp (congrArg RelCat.Hom.rel h) (⟦p⟧, ⟦q⟧)
    refine Hom.ext (Transition.ext ?_)
    funext w f g
    exact propext (by simpa [Transition.toUpdate] using hs ⟨w, f⟩ ⟨w, g⟩)

end Ctx

/-! ### The Set-monad reading -/

open Update

attribute [local instance] Set.monad

universe u

variable {S : Type*}

/-- Sequencing is Kleisli composition for the powerset monad: an update
is a Kleisli arrow `S → Set S`, definitionally. -/
theorem seq_eq_kleisliComp (D₁ D₂ : S → Set S) :
    (seq D₁ D₂ : S → Set S) = D₁ >=> D₂ :=
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
theorem liftEquiv_seq (D₁ D₂ : Update S) :
    (liftEquiv (seq D₁ D₂) : Set S → Set S) =
      (liftEquiv D₂ : Set S → Set S) ∘ (liftEquiv D₁ : Set S → Set S) :=
  lift_seq D₁ D₂

/-! ### `RelCat ≌ KleisliCat Set` -/

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
