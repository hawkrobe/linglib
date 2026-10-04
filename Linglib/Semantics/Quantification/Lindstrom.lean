module

public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Core.ModelTheory.Lindstrom
public import Linglib.Core.ModelTheory.Monadic
public import Linglib.Semantics.Quantification.Basic

/-!
# Realizing Lindström quantifiers as GQ denotations

A `FirstOrder.Language.LindstromQuantifier` is an isomorphism-invariant class of `L`-structures,
Mostowski's quantifiers with the invariance built into the type. Over the monadic language
`L_UV`, with two unary predicates `U` and `V`, such a class is a determiner, and `Det.toGQ`
realizes it as a generalized-quantifier denotation `GQ α`: a pair of predicates `(A, B)` becomes
the structure `(α, A, B)`, and the quantifier holds of `(A, B)` when that structure is in the
class. Quantity invariance is then a theorem about every realized determiner rather than a side
condition, and the determiners for *every*, *some* and *no* realize the denotations of
`Quantification/Basic.lean`.

## Main definitions

* `L_UV`: the monadic language with two unary relation symbols `U`, `V`.
* `structOfAB A B`: the `L_UV`-structure `(α, A, B)`.
* `Det`, `Det.toGQ`: determiners and their realization as `GQ α` denotations.
* `everyDet`, `someDet`, `noDet`: the determiners of the square of opposition.

## Main results

* `Det.realize_quantityInvariant`: every realized determiner satisfies
  `Quantifier.GQ.QuantityInvariant`, the type-`⟨1,1⟩` form of Mostowski's permutation
  invariance.
* `everyDet_toGQ`, `someDet_toGQ`, `noDet_toGQ`: the realizations are `every`, `GQ.some`, `no`.
* `toGQ_compl`: realization carries the complement of a class to GQ outer negation.
* `someDet_holds_eq_compl`, `noDet_toGQ_eq_innerNeg`, `someDet_toGQ_eq_dual`: the `no` and
  `some` corners as the complement, inner negation and dual of `every`.
* `nEquiv_structOfAB_iff`: two models agree on the sentences of quantifier rank `≤ t` iff their
  Venn regions agree in size up to `t`.

## References

* [barwise-cooper-1981]
* [demey-frijters-2023]
* [mostowski-1957]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

universe u v

namespace Quantifier.Lindstrom

open Quantifier.GQ

open FirstOrder Language
open CategoryTheory (Bundled)

/-! ### The monadic language `L_UV` -/

/-- The two unary relation symbols of `L_UV`, the restrictor `U` and the scope `V`. -/
inductive uvRel : ℕ → Type
  | U : uvRel 1
  | V : uvRel 1
  deriving DecidableEq

/-- The monadic language of generalized determiners, with no function symbols and the two unary
relation symbols `U` and `V`. -/
def L_UV : Language :=
  { Functions := fun _ => Empty
    Relations := uvRel }

/-- The restrictor symbol `U`. -/
abbrev uRel : L_UV.Relations 1 := .U

/-- The scope symbol `V`. -/
abbrev vRel : L_UV.Relations 1 := .V

/-- The `L_UV`-structure `(α, A, B)` interprets `U` as `A` and `V` as `B`. -/
@[reducible] def structOfAB {α : Type u} (A B : α → Prop) : L_UV.Structure α where
  funMap := fun f _ => f.elim
  RelMap {n} r v :=
    match r, v with
    | .U, v => A (v 0)
    | .V, v => B (v 0)

@[simp] theorem structOfAB_relMap_U {α : Type u} (A B : α → Prop) (v : Fin 1 → α) :
    (structOfAB A B).RelMap uRel v ↔ A (v 0) := Iff.rfl

@[simp] theorem structOfAB_relMap_V {α : Type u} (A B : α → Prop) (v : Fin 1 → α) :
    (structOfAB A B).RelMap vRel v ↔ B (v 0) := Iff.rfl

/-! ### The realization functor -/

/-- A *determiner*, a Lindström quantifier of type `⟨1,1⟩`, is an iso-invariant class of
`L_UV`-structures. -/
abbrev Det := LindstromQuantifier.{0, 0, u} L_UV

namespace Det

/-- A determiner realized as a `GQ α` denotation, which holds of `(A, B)` iff the structure
`(α, A, B)` is in the quantifier's class. -/
def toGQ (Q : Det.{u}) (α : Type u) : GQ α :=
  fun A B => (⟨α, structOfAB A B⟩ : Bundled.{u} L_UV.Structure) ∈ Q.holds

@[simp] theorem toGQ_apply (Q : Det.{u}) {α : Type u} (A B : α → Prop) :
    Q.toGQ α A B ↔ (⟨α, structOfAB A B⟩ : Bundled.{u} L_UV.Structure) ∈ Q.holds := Iff.rfl

/-- The `L_UV`-isomorphism `(α, A, B) ≃[L_UV] (α, A', B')` induced by a bijection `f`
matching the predicates pointwise. The underlying map is `f⁻¹`, since `map_rel'` for `U`
needs `A' (f⁻¹ z) ↔ A z`, which is `hA` read at `f⁻¹ z`. -/
private noncomputable def equivOfBij {α : Type u} {A B A' B' : α → Prop} {f : α → α}
    (hBij : Function.Bijective f) (hA : ∀ x, A (f x) ↔ A' x) (hB : ∀ x, B (f x) ↔ B' x) :
    @FirstOrder.Language.Equiv L_UV α α (structOfAB A B) (structOfAB A' B') :=
  @FirstOrder.Language.Equiv.mk L_UV α α (structOfAB A B) (structOfAB A' B')
    (Equiv.ofBijective f hBij).symm (fun {n} g _ => g.elim) (by
      intro n r v
      cases r with
      | U =>
        change A' ((Equiv.ofBijective f hBij).symm (v 0)) ↔ A (v 0)
        have := hA ((Equiv.ofBijective f hBij).symm (v 0))
        rw [Equiv.ofBijective_apply_symm_apply f hBij] at this
        exact this.symm
      | V =>
        change B' ((Equiv.ofBijective f hBij).symm (v 0)) ↔ B (v 0)
        have := hB ((Equiv.ofBijective f hBij).symm (v 0))
        rw [Equiv.ofBijective_apply_symm_apply f hBij] at this
        exact this.symm)

/-- Every realized Lindström quantifier satisfies `QuantityInvariant`, so `q A B` is invariant
under a bijective relabelling of the domain. This is the type-`⟨1,1⟩` form of Mostowski's
permutation invariance, derived from `iso_inv` rather than stipulated on the denotation. -/
theorem realize_quantityInvariant (Q : Det.{u}) {α : Type u} :
    Quantifier.GQ.QuantityInvariant (Q.toGQ α) := by
  intro A B A' B' f hBij hA hB
  exact Q.iso_inv ⟨equivOfBij hBij hA hB⟩

end Det

/-! ### The Aristotelian determiner classes -/

/-- A `RelMap` fact for `U` transfers across `e.symm`. -/
private theorem relMap_symm_U {M N : Bundled.{u} L_UV.Structure} (e : M ≃[L_UV] N) (y : N) :
    N.str.RelMap uRel ![y] ↔ M.str.RelMap uRel ![e.symm y] := by
  have h := e.map_rel uRel ![e.symm y]
  rwa [Matrix.comp_vecCons, Matrix.comp_vecEmpty, e.apply_symm_apply] at h

/-- Transfer a `RelMap` fact for `V` across `e.symm`. -/
private theorem relMap_symm_V {M N : Bundled.{u} L_UV.Structure} (e : M ≃[L_UV] N) (y : N) :
    N.str.RelMap vRel ![y] ↔ M.str.RelMap vRel ![e.symm y] := by
  have h := e.map_rel vRel ![e.symm y]
  rwa [Matrix.comp_vecCons, Matrix.comp_vecEmpty, e.apply_symm_apply] at h

/-- The determiner *every*, holding when `∀ x, U x → V x`. -/
def everyDet : Det.{u} where
  holds := {M | ∀ x : M, M.str.RelMap uRel ![x] → M.str.RelMap vRel ![x]}
  iso_inv {M N} h := by
    obtain ⟨e⟩ := h
    have key : ∀ {P Q : Bundled.{u} L_UV.Structure} (g : P ≃[L_UV] Q),
        (∀ x : P, P.str.RelMap uRel ![x] → P.str.RelMap vRel ![x]) →
        (∀ y : Q, Q.str.RelMap uRel ![y] → Q.str.RelMap vRel ![y]) := by
      intro P Q g hP y hu
      exact (relMap_symm_V g y).mpr (hP (g.symm y) ((relMap_symm_U g y).mp hu))
    exact ⟨key e, key e.symm⟩

/-- The determiner *some*, holding when `∃ x, U x ∧ V x`. -/
def someDet : Det.{u} where
  holds := {M | ∃ x : M, M.str.RelMap uRel ![x] ∧ M.str.RelMap vRel ![x]}
  iso_inv {M N} h := by
    obtain ⟨e⟩ := h
    have key : ∀ {P Q : Bundled.{u} L_UV.Structure} (g : P ≃[L_UV] Q),
        (∃ x : P, P.str.RelMap uRel ![x] ∧ P.str.RelMap vRel ![x]) →
        (∃ y : Q, Q.str.RelMap uRel ![y] ∧ Q.str.RelMap vRel ![y]) := by
      rintro P Q g ⟨x, hu, hv⟩
      refine ⟨g x, ?_, ?_⟩
      · have := (g.map_rel uRel ![x]).mpr hu
        rwa [Matrix.comp_vecCons, Matrix.comp_vecEmpty] at this
      · have := (g.map_rel vRel ![x]).mpr hv
        rwa [Matrix.comp_vecCons, Matrix.comp_vecEmpty] at this
    exact ⟨key e, key e.symm⟩

/-- The determiner *no*, holding when `∀ x, U x → ¬ V x`. -/
def noDet : Det.{u} where
  holds := {M | ∀ x : M, M.str.RelMap uRel ![x] → ¬ M.str.RelMap vRel ![x]}
  iso_inv {M N} h := by
    obtain ⟨e⟩ := h
    have key : ∀ {P Q : Bundled.{u} L_UV.Structure} (g : P ≃[L_UV] Q),
        (∀ x : P, P.str.RelMap uRel ![x] → ¬ P.str.RelMap vRel ![x]) →
        (∀ y : Q, Q.str.RelMap uRel ![y] → ¬ Q.str.RelMap vRel ![y]) := by
      intro P Q g hP y hu hv
      exact hP (g.symm y) ((relMap_symm_U g y).mp hu) ((relMap_symm_V g y).mp hv)
    exact ⟨key e, key e.symm⟩

/-! ### Theory-hub tie-ins

The GQ denotations the codebase already uses (`every`, `GQ.some`, `no`) are
exactly the realizations of the Lindström classes above. -/

/-- `everyDet` realizes `every`. -/
theorem everyDet_toGQ (α : Type u) : everyDet.toGQ α = (every : GQ α) := by
  funext A B
  simp only [Det.toGQ, everyDet, Set.mem_ofPred_eq, structOfAB_relMap_U, structOfAB_relMap_V,
    Matrix.cons_val_fin_one, every]

/-- `someDet` realizes `GQ.some`. -/
theorem someDet_toGQ (α : Type u) : someDet.toGQ α = (GQ.some : GQ α) := by
  funext A B
  simp only [Det.toGQ, someDet, Set.mem_ofPred_eq, structOfAB_relMap_U, structOfAB_relMap_V,
    Matrix.cons_val_fin_one, GQ.some]

/-- `noDet` realizes `no`. -/
theorem noDet_toGQ (α : Type u) : noDet.toGQ α = (no : GQ α) := by
  funext A B
  simp only [Det.toGQ, noDet, Set.mem_ofPred_eq, structOfAB_relMap_U, structOfAB_relMap_V,
    Matrix.cons_val_fin_one, no]

/-! ### The square of opposition

The relations of the square live on `GQ α` in `Quantification/Basic.lean`:
`every_contradicts_notEvery` and `no_contradicts_some`, and `a_e_contrary` and
`subalternation_a_i`, which need a non-empty restrictor, an instance of the logic-sensitivity
Demey and Frijters describe. This section shows that realization carries the class-level
structure to the GQ duality operators. Outer negation is the complement of the class
(`toGQ_compl`), the corners `no` and `some` are the inner negation and the dual of `every`
(`noDet_toGQ_eq_innerNeg`, `someDet_toGQ_eq_dual`), and the contradictory diagonal between `no`
and `some` is the class-level fact `some = ¬ no` (`someDet_holds_eq_compl`). -/

/-- As iso-invariant classes, `some` is the complement of `no`, since `∃x. Ux ∧ Vx` is the
negation of `∀x. Ux → ¬Vx`. Its image under `toGQ` is `Quantifier.GQ.no_contradicts_some`. -/
theorem someDet_holds_eq_compl : (someDet.{u}).holds = (noDet.{u}).holdsᶜ := by
  ext M
  simp only [someDet, noDet, Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_not,
    exists_prop]

/-- Realization carries the complement of an iso-invariant class to GQ outer negation. With
`everyDet` this realizes the contradictory diagonal between `A` and `O` as
`Quantifier.GQ.every_contradicts_notEvery`. -/
theorem toGQ_compl (Q : Det.{u}) (α : Type u) : Det.toGQ Qᶜ α = (Q.toGQ α)ᶜ := by
  funext A B
  simp only [Det.toGQ, LindstromQuantifier.holds_compl, Set.mem_compl_iff, compl_apply]

/-- At the `E` corner, `no` realizes the inner negation of `every`. -/
theorem noDet_toGQ_eq_innerNeg (α : Type u) :
    noDet.toGQ α = innerNeg (everyDet.toGQ α) := by
  rw [noDet_toGQ, everyDet_toGQ, innerNeg_every]

/-- At the `I` corner, `some` realizes the dual of `every`. -/
theorem someDet_toGQ_eq_dual (α : Type u) :
    someDet.toGQ α = dual (everyDet.toGQ α) := by
  rw [someDet_toGQ, everyDet_toGQ, dual_every]

/-! ### Finite-rank equivalence of `L_UV`-models

`L_UV` is monadic, so the Ehrenfeucht–Fraïssé game on its models is decided by counting: two
models `(α, A, B)` and `(β, A', B')` agree on every sentence of quantifier rank `≤ t` iff each of
the four Venn regions of the two predicates has the same size in both or at least `t` elements in
both. The four unary types of `L_UV` are these regions, so `foDefinable_iff_exists_min_encard_eq`
is van Benthem's characterization of the first-order definable determiners as those invariant
under agreement of the four region sizes up to a threshold. -/

instance : L_UV.IsMonadic :=
  ⟨fun _ => inferInstanceAs (IsEmpty Empty), fun _ hl => ⟨fun r => by cases r <;> exact hl rfl⟩⟩

private theorem unaryType_structOfAB_eq {α : Type u} (A B : α → Prop) (x : α)
    (S : L_UV.Relations 1 → Prop) :
    @unaryType L_UV α (structOfAB A B) x = S ↔ ((A x ↔ S uRel) ∧ (B x ↔ S vRel)) := by
  refine ⟨fun h => h ▸ ⟨Iff.rfl, Iff.rfl⟩, fun ⟨hA, hB⟩ => funext fun R => ?_⟩
  cases R
  exacts [propext hA, propext hB]

instance : Finite L_UV.Symbols := by
  refine Finite.of_injective (β := Bool) (fun s => match s with
    | .inl ⟨_, f⟩ => (f : Empty).elim
    | .inr ⟨_, .U⟩ => false
    | .inr ⟨_, .V⟩ => true) ?_
  rintro (⟨_, ⟨⟩⟩ | ⟨_, r₁⟩) (⟨_, ⟨⟩⟩ | ⟨_, r₂⟩) h
  cases r₁ <;> cases r₂ <;> first | rfl | cases h

/-- Two `L_UV`-models are `t`-equivalent iff each Venn region of `U` and `V` has the same size in
both or at least `t` elements in both ([peters-westerstahl-2006] Theorem 13 for type `⟨1, 1⟩`,
first-order case). -/
theorem nEquiv_structOfAB_iff {α β : Type u} {A B : α → Prop} {A' B' : β → Prop} {t : ℕ} :
    @NEquiv L_UV t α β (structOfAB A B) (structOfAB A' B') ↔
      min (t : ℕ∞) {x | A x ∧ B x}.encard = min (t : ℕ∞) {y | A' y ∧ B' y}.encard ∧
      min (t : ℕ∞) {x | A x ∧ ¬ B x}.encard = min (t : ℕ∞) {y | A' y ∧ ¬ B' y}.encard ∧
      min (t : ℕ∞) {x | ¬ A x ∧ B x}.encard = min (t : ℕ∞) {y | ¬ A' y ∧ B' y}.encard ∧
      min (t : ℕ∞) {x | ¬ A x ∧ ¬ B x}.encard = min (t : ℕ∞) {y | ¬ A' y ∧ ¬ B' y}.encard := by
  have key : ∀ {γ : Type u} (C D : γ → Prop) (S : L_UV.Relations 1 → Prop),
      @unaryType L_UV γ (structOfAB C D) ⁻¹' {S} = {c | (C c ↔ S uRel) ∧ (D c ↔ S vRel)} :=
    fun C D S => Set.ext fun c => unaryType_structOfAB_eq C D c S
  rw [@nEquiv_iff_min_encard_eq L_UV α β (structOfAB A B) (structOfAB A' B') _ _ t]
  simp only [key]
  refine ⟨fun h => ⟨?_, ?_, ?_, ?_⟩, fun ⟨h₁, h₂, h₃, h₄⟩ S => ?_⟩
  · simpa using h fun R => match R with | .U => True | .V => True
  · simpa using h fun R => match R with | .U => True | .V => False
  · simpa using h fun R => match R with | .U => False | .V => True
  · simpa using h fun R => match R with | .U => False | .V => False
  · by_cases hU : S uRel <;> by_cases hV : S vRel <;> simpa [hU, hV]

end Quantifier.Lindstrom
