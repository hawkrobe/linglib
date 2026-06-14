import Linglib.Core.Logic.FirstOrder.Lindstrom
import Linglib.Semantics.Quantification.Basic
import Linglib.Core.Logic.Aristotelian.Basic

/-!
# Realizing Lindström quantifiers as GQ denotations
[barwise-cooper-1981] [mostowski-1957] [van-benthem-1984] [deklerck-vignero-demey-2024]
[demey-frijters-2023]

A `FirstOrder.Language.LindstromQuantifier` is an isomorphism-invariant class of
`L`-structures (Mostowski's QUANT built into the type). This file *realizes* one over
the monadic language `L_UV` (two unary predicates `U`, `V`) as a linguistic
generalized-quantifier denotation `GQ α = (α → Prop) → (α → Prop) → Prop`: a pair of
predicates `(A, B)` becomes the structure `(α, A, B)`, and the quantifier holds of
`(A, B)` iff it holds of that structure (`Det.toGQ`).

The headline is `Det.realize_quantityInvariant`: the project's existing predicate
`Quantification.QuantityInvariant` — invariance of `q A B` under a bijective relabelling
of the domain — is a *theorem* about every realized Lindström quantifier, not a side
condition. It falls straight out of `iso_inv`, because a bijection `f` with
`A (f x) ↔ A' x` and `B (f x) ↔ B' x` is exactly an `L_UV`-isomorphism
`(α, A, B) ≃[L_UV] (α, A', B')` (with the map `f⁻¹`). This is the general-form
(Lindström/van Benthem, type `⟨1,1⟩`) of Mostowski's permutation invariance.

`everyDet`/`someDet`/`noDet` are the determiner classes for the Aristotelian core, and
`everyDet_toGQ`/`someDet_toGQ`/`noDet_toGQ` show the GQ denotations the codebase already
uses (`every_sem`, `some_sem`, `no_sem`) are precisely their realizations.

The final section *derives the square of opposition from the model theory*: the four
corners are iso-invariant classes, the contradictory relations are `IsCompl` on those
classes (`Aristotelian.IsContradictory`, not stipulated), and `toGQ` carries the class-level
square to the GQ duality operators — an Aristotelian morphism [deklerck-vignero-demey-2024].
Contrariety and subalternation need existential import: they degenerate over arbitrary
structures (logic-sensitivity, [demey-frijters-2023]).

The general `LindstromQuantifier` layer is `[UPSTREAM]`-adjacent; this file is the
linguistic realization functor on top of it.

## Main definitions

* `L_UV` — the monadic language with two unary relation symbols `U`, `V`.
* `structOfAB A B` — the `L_UV`-structure `(α, A, B)`.
* `Det := LindstromQuantifier L_UV` and `Det.toGQ` — the realization functor.
* `everyDet`/`someDet`/`noDet` — the Aristotelian determiner classes.

## Main results

* `Det.realize_quantityInvariant` — every realized Lindström quantifier satisfies
  `Quantification.QuantityInvariant`.
* `everyDet_toGQ`/`someDet_toGQ`/`noDet_toGQ` — realizations are `every_sem`/`some_sem`/
  `no_sem`.
* `isContradictory_every_notEvery`/`isContradictory_no_some` — the square's diagonals as
  `IsCompl` of iso-invariant classes.
* `compl_toGQ`/`noDet_toGQ_eq_innerNeg`/`someDet_toGQ_eq_dualQ` — `toGQ` realizes the
  class-level square as the GQ duality operators.
* `not_isContrary_every_no`/`not_isSubaltern_every_some` — the existential-import
  degeneracy (logic-sensitivity).

`L_UV`/`uvRel`/`uRel`/`vRel` are re-derived in `Studies.BarwiseCooper1981` (its
Appendix-C Fraïssé argument predates this substrate); that copy will be deduped against
this one in a follow-up.
-/

universe u v

namespace Quantification

open FirstOrder Language
open CategoryTheory (Bundled)

/-! ### The monadic language `L_UV` -/

/-- The two unary relation symbols of `L_UV`: restrictor `U` and scope `V`. -/
inductive uvRel : ℕ → Type
  | U : uvRel 1
  | V : uvRel 1
  deriving DecidableEq

/-- The monadic language of generalized determiners: no function symbols, two unary
relation symbols `U`, `V`. -/
def L_UV : Language :=
  { Functions := fun _ => Empty
    Relations := uvRel }

/-- The restrictor symbol `U`. -/
abbrev uRel : L_UV.Relations 1 := .U

/-- The scope symbol `V`. -/
abbrev vRel : L_UV.Relations 1 := .V

/-- The `L_UV`-structure `(α, A, B)`: `U` is interpreted as `A`, `V` as `B`, and there
are no function symbols. -/
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

/-- A *determiner* (type-`⟨1,1⟩` Lindström quantifier): an iso-invariant class of
`L_UV`-structures. -/
abbrev Det := LindstromQuantifier.{0, 0, u} L_UV

namespace Det

/-- Realize a determiner as a `GQ α` denotation: `(A, B)` holds iff the structure
`(α, A, B)` is in the quantifier's class. -/
def toGQ (Q : Det.{u}) (α : Type u) : GQ α :=
  fun A B => (⟨α, structOfAB A B⟩ : Bundled.{u} L_UV.Structure) ∈ Q.holds

@[simp] theorem toGQ_apply (Q : Det.{u}) {α : Type u} (A B : α → Prop) :
    Q.toGQ α A B ↔ (⟨α, structOfAB A B⟩ : Bundled.{u} L_UV.Structure) ∈ Q.holds := Iff.rfl

/-- The `L_UV`-isomorphism `(α, A, B) ≃[L_UV] (α, A', B')` induced by a bijection `f`
matching the predicates pointwise. The underlying map is `f⁻¹`: `map_rel'` for `U`
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

/-- **Headline.** Every realized Lindström quantifier satisfies the project's
`QuantityInvariant` predicate: `q A B` is invariant under a bijective relabelling of the
domain. This is the type-`⟨1,1⟩` Mostowski/Lindström permutation invariance
([mostowski-1957] [van-benthem-1984]), recovered here as a consequence of `iso_inv` —
not stipulated on the denotation. -/
theorem realize_quantityInvariant (Q : Det.{u}) {α : Type u} :
    Quantification.QuantityInvariant (Q.toGQ α) := by
  intro A B A' B' f hBij hA hB
  exact Q.iso_inv ⟨equivOfBij hBij hA hB⟩

end Det

/-! ### The Aristotelian determiner classes -/

/-- `g ∘ ![z] = ![g z]` for a single-element tuple. -/
private theorem comp_cons_fin_one {β γ : Type*} (g : β → γ) (z : β) :
    g ∘ ![z] = ![g z] := by
  funext i; simp only [Function.comp_apply, Matrix.cons_val_fin_one]

/-- Transfer a `RelMap` fact for `U` across `e.symm`: `RelMap_N U ![y] ↔ RelMap_M U ![e.symm y]`. -/
private theorem relMap_symm_U {M N : Bundled.{u} L_UV.Structure} (e : M ≃[L_UV] N) (y : N) :
    N.str.RelMap uRel ![y] ↔ M.str.RelMap uRel ![e.symm y] := by
  have h := e.map_rel uRel ![e.symm y]
  rwa [comp_cons_fin_one, e.apply_symm_apply] at h

/-- Transfer a `RelMap` fact for `V` across `e.symm`. -/
private theorem relMap_symm_V {M N : Bundled.{u} L_UV.Structure} (e : M ≃[L_UV] N) (y : N) :
    N.str.RelMap vRel ![y] ↔ M.str.RelMap vRel ![e.symm y] := by
  have h := e.map_rel vRel ![e.symm y]
  rwa [comp_cons_fin_one, e.apply_symm_apply] at h

/-- `every`: `∀ x, U x → V x`. -/
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

/-- `some`: `∃ x, U x ∧ V x`. -/
def someDet : Det.{u} where
  holds := {M | ∃ x : M, M.str.RelMap uRel ![x] ∧ M.str.RelMap vRel ![x]}
  iso_inv {M N} h := by
    obtain ⟨e⟩ := h
    have key : ∀ {P Q : Bundled.{u} L_UV.Structure} (g : P ≃[L_UV] Q),
        (∃ x : P, P.str.RelMap uRel ![x] ∧ P.str.RelMap vRel ![x]) →
        (∃ y : Q, Q.str.RelMap uRel ![y] ∧ Q.str.RelMap vRel ![y]) := by
      rintro P Q g ⟨x, hu, hv⟩
      refine ⟨g x, ?_, ?_⟩
      · have := (g.map_rel uRel ![x]).mpr hu; rwa [comp_cons_fin_one] at this
      · have := (g.map_rel vRel ![x]).mpr hv; rwa [comp_cons_fin_one] at this
    exact ⟨key e, key e.symm⟩

/-- `no`: `∀ x, U x → ¬ V x`. -/
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

The GQ denotations the codebase already uses (`every_sem`, `some_sem`, `no_sem`) are
exactly the realizations of the Lindström classes above. -/

/-- `everyDet` realizes `every_sem`: `⟦every⟧ = λR S. ∀x. R x → S x`. -/
theorem everyDet_toGQ (α : Type u) : everyDet.toGQ α = (every_sem : GQ α) := by
  funext A B
  simp only [Det.toGQ, everyDet, Set.mem_setOf_eq, structOfAB_relMap_U, structOfAB_relMap_V,
    Matrix.cons_val_fin_one, every_sem]

/-- `someDet` realizes `some_sem`: `⟦some⟧ = λR S. ∃x. R x ∧ S x`. -/
theorem someDet_toGQ (α : Type u) : someDet.toGQ α = (some_sem : GQ α) := by
  funext A B
  simp only [Det.toGQ, someDet, Set.mem_setOf_eq, structOfAB_relMap_U, structOfAB_relMap_V,
    Matrix.cons_val_fin_one, some_sem]

/-- `noDet` realizes `no_sem`: `⟦no⟧ = λR S. ∀x. R x → ¬ S x`. -/
theorem noDet_toGQ (α : Type u) : noDet.toGQ α = (no_sem : GQ α) := by
  funext A B
  simp only [Det.toGQ, noDet, Set.mem_setOf_eq, structOfAB_relMap_U, structOfAB_relMap_V,
    Matrix.cons_val_fin_one, no_sem]

/-! ### The square of opposition, derived from the model theory

The Aristotelian square's four corners are iso-invariant classes — `everyDet` (A),
`someDet` (I), `noDet` (E), and `everyDet.compl` (O, *not-every*) — and the relations
among them are *Boolean-algebra facts on those classes*: `Aristotelian.IsContradictory`
is `IsCompl` on `Set (Bundled L_UV.Structure)`, the genuine complement of an iso-invariant
class. The realization functor `toGQ` carries the class-level square down to the GQ-level
duality operators (`outerNeg`/`innerNeg`/`dualQ`), so the GQ square is the *image* of the
model-theoretic one — an Aristotelian morphism in the sense of [deklerck-vignero-demey-2024]
— not an independent stipulation.

Only the **contradictory** (diagonal) relations hold unconditionally. **Contrariety** and
**subalternation** require *existential import* (a non-empty restrictor) and degenerate over
arbitrary structures, where `every` and `no` are jointly vacuously true: this is the
logic-sensitivity of [demey-frijters-2023], the gap between the `(𝓕, FOL)` and `(𝓕, SYL)`
readings of one fragment. `not_isContrary_every_no` and `not_isSubaltern_every_some` exhibit
the degeneracy concretely. -/

/-- `some` is the (Boolean) complement of `no` as iso-invariant classes: `∃x. Ux ∧ Vx` is
the negation of `∀x. Ux → ¬Vx`. The model-theoretic source of the `no`/`some` diagonal. -/
theorem someDet_holds_eq_compl : (someDet.{u}).holds = (noDet.{u}).holdsᶜ := by
  ext M
  simp only [someDet, noDet, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_not,
    exists_prop]

/-- **A–O diagonal.** `every` and `not-every` (`everyDet.compl`) are contradictory: the
Boolean complement of an iso-invariant class, by construction (not stipulated). -/
theorem isContradictory_every_notEvery :
    Aristotelian.IsContradictory (everyDet.{u}).holds (everyDet.{u}).compl.holds := by
  rw [LindstromQuantifier.compl_holds]; exact isCompl_compl

/-- **E–I diagonal.** `no` and `some` are contradictory: `some = ¬ no` as classes. -/
theorem isContradictory_no_some :
    Aristotelian.IsContradictory (noDet.{u}).holds (someDet.{u}).holds := by
  rw [someDet_holds_eq_compl]; exact isCompl_compl

/-- Outer negation realizes: `(¬Q).toGQ = outerNeg Q.toGQ`. The realization functor is a
homomorphism for outer negation — the [deklerck-vignero-demey-2024] Aristotelian morphism
carrying the class-level square to the GQ duality square. -/
theorem compl_toGQ (Q : Det.{u}) (α : Type u) : Det.toGQ Q.compl α = outerNeg (Q.toGQ α) := by
  funext A B
  simp only [Det.toGQ, LindstromQuantifier.compl_holds, Set.mem_compl_iff, outerNeg]

/-- `no` realizes the inner negation of `every` (`every…not = no`): the E corner is the
inner-negation image of the A corner. -/
theorem noDet_toGQ_eq_innerNeg (α : Type u) :
    noDet.toGQ α = innerNeg (everyDet.toGQ α) := by
  rw [noDet_toGQ, everyDet_toGQ, innerNeg_every_eq_no]

/-- `some` realizes the dual of `every` (`every̌ = some`): the I corner is the dual image
of the A corner. -/
theorem someDet_toGQ_eq_dualQ (α : Type u) :
    someDet.toGQ α = dualQ (everyDet.toGQ α) := by
  rw [someDet_toGQ, everyDet_toGQ, dualQ_every_eq_some]

/-! #### Logic-sensitivity: the classical square needs existential import -/

/-- Empty-restrictor witness: `U` (restrictor) holds of nothing, so over this structure
`every` and `no` are *both* vacuously true. -/
@[reducible] def emptyRestrictor : Bundled.{0} L_UV.Structure :=
  ⟨PUnit, structOfAB (fun _ => False) (fun _ => True)⟩

private theorem emptyRestrictor_mem_every : emptyRestrictor ∈ (everyDet.{0}).holds := by
  intro x hu; exact (hu : False).elim

private theorem emptyRestrictor_mem_no : emptyRestrictor ∈ (noDet.{0}).holds := by
  intro x hu; exact (hu : False).elim

private theorem emptyRestrictor_not_mem_some : emptyRestrictor ∉ (someDet.{0}).holds := by
  rintro ⟨x, hu, -⟩; exact (hu : False)

/-- **Logic-sensitivity (contrariety).** Over arbitrary `L_UV`-structures `every` and `no`
are *not* contrary — both hold vacuously when the restrictor is empty. Classical contrariety
is the `(𝓕, SYL)` reading (existential import), not the `(𝓕, FOL)` one [demey-frijters-2023]. -/
theorem not_isContrary_every_no :
    ¬ Aristotelian.IsContrary (everyDet.{0}).holds (noDet.{0}).holds := by
  rintro ⟨hdisj, -⟩
  exact Set.disjoint_left.mp hdisj emptyRestrictor_mem_every emptyRestrictor_mem_no

/-- **Logic-sensitivity (subalternation).** Over arbitrary `L_UV`-structures `every` does
*not* entail `some`: the empty-restrictor model satisfies `every` but not `some`. -/
theorem not_isSubaltern_every_some :
    ¬ Aristotelian.IsSubaltern (everyDet.{0}).holds (someDet.{0}).holds := by
  intro hlt
  exact emptyRestrictor_not_mem_some (hlt.le emptyRestrictor_mem_every)

end Quantification
