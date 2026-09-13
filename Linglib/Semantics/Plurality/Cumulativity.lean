import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Linglib.Semantics.Mereology

/-!
# Cumulative Predication
[krifka-1986] [krifka-1989] [sternefeld-1998] [beck-sauerland-2000]

Formalises the cumulative operator `**` in its two forms. The closure form of [krifka-1986],
adopted by [sternefeld-1998], takes the smallest relation containing `R` and closed under
componentwise sum: Link's `*` on the product semilattice (`Cumulation`). The
bidirectional-coverage form of [beck-sauerland-2000] asks that every atom of `x` be `R`-related
to some atom of `y` and conversely (`Cumulative`). On finite sets of individuals the two agree
away from the empty pair (`cumulation_map_singleton`).

## Main declarations

* `Cumulative R x y` — bidirectional-coverage cumulative predication.
* `LeftCoverage`, `RightCoverage` — the two conjuncts; their conjunction
  IS `Cumulative` (`cumulative_iff_coverages`).
* `Cumulative.union` — coverage is closed under componentwise union.
* `singleton_right_cumulative` — `**` on a singleton right argument
  collapses to universal distribution.
* `Cumulation R x y` — the closure form `**R` on any pair of join-semilattices.
* `cumulation_map_singleton` — the closure and coverage forms agree on nonempty finite sets.

## Implementation notes

Link's `CUM` (`Mereology.CUM`) is a *property* of denotations:
`P(x) ∧ P(y) → P(x ⊔ y)`. The `**` operator here takes a two-place
predicate and returns a new predicate with cumulative truth conditions;
the output of `**` applied to a non-cumulative predicate is itself
cumulative (`cumulation_iff_of_cum` is the fixed-point statement).

## Todo

* n-ary `***` ([sternefeld-1998] §3.1) is not formalised.
* Schein (1993) *Plurals and Events* (bib entry pending) — the
  event-quantification alternative to the `**`-relational treatment
  of cumulativity — is not yet formalised.
-/

namespace Plurality.Cumulativity

variable {A B : Type*}

/-! ### Bidirectional-coverage `**` -/

/--
The cumulative operator `**` in [beck-sauerland-2000]'s
bidirectional-coverage form.

Given a two-place predicate R and two pluralities x : Finset A, y : Finset B:

  **(R)(x, y) = [∀a ∈ x. ∃b ∈ y. R(a, b)] ∧ [∀b ∈ y. ∃a ∈ x. R(a, b)]

Both argument pluralities must be "covered": every atom in x is
R-related to some atom in y, and vice versa.

Heterogeneous: A and B may be different types (e.g., Elephant × Continent).
-/
def Cumulative (R : A → B → Prop) (x : Finset A) (y : Finset B) : Prop :=
  (∀ a ∈ x, ∃ b ∈ y, R a b) ∧ (∀ b ∈ y, ∃ a ∈ x, R a b)

instance Cumulative.instDecidable
    [DecidableEq A] [DecidableEq B] (R : A → B → Prop)
    [DecidableRel R] (x : Finset A) (y : Finset B) :
    Decidable (Cumulative R x y) := by
  unfold Cumulative; infer_instance

/--
Left coverage: every atom in x is R-related to some atom in y.
-/
def LeftCoverage (R : A → B → Prop) (x : Finset A) (y : Finset B) : Prop :=
  ∀ a ∈ x, ∃ b ∈ y, R a b

/--
Right coverage: every atom in y is R-related to some atom in x.
-/
def RightCoverage (R : A → B → Prop) (x : Finset A) (y : Finset B) : Prop :=
  ∀ b ∈ y, ∃ a ∈ x, R a b

/-- `**` is the conjunction of left and right coverage. -/
theorem cumulative_iff_coverages (R : A → B → Prop) (x : Finset A) (y : Finset B) :
    Cumulative R x y ↔ LeftCoverage R x y ∧ RightCoverage R x y := Iff.rfl

/-- `**` entails DIST on the left argument: if `**(R)(x, y)` then every
    atom in x is R-related to *something* in y (left universality). -/
theorem cumulative_left_universal (R : A → B → Prop) (x : Finset A) (y : Finset B)
    (h : Cumulative R x y) (a : A) (ha : a ∈ x) :
    ∃ b ∈ y, R a b :=
  h.1 a ha

/-- `**` entails DIST on the right argument: if `**(R)(x, y)` then every
    atom in y is R-related to *something* in x (right universality). -/
theorem cumulative_right_universal (R : A → B → Prop) (x : Finset A) (y : Finset B)
    (h : Cumulative R x y) (b : B) (hb : b ∈ y) :
    ∃ a ∈ x, R a b :=
  h.2 b hb

@[simp]
theorem cumulative_singleton (R : A → B → Prop) (a : A) (b : B) :
    Cumulative R {a} {b} ↔ R a b := by
  simp [Cumulative]

/-- Bidirectional coverage is closed under componentwise union. -/
theorem Cumulative.union [DecidableEq A] [DecidableEq B] {R : A → B → Prop}
    {x x' : Finset A} {y y' : Finset B} (h : Cumulative R x y) (h' : Cumulative R x' y') :
    Cumulative R (x ∪ x') (y ∪ y') := by
  refine ⟨λ a ha => ?_, λ b hb => ?_⟩
  · rcases Finset.mem_union.1 ha with ha | ha
    · obtain ⟨b, hb, hab⟩ := h.1 a ha
      exact ⟨b, Finset.mem_union_left _ hb, hab⟩
    · obtain ⟨b, hb, hab⟩ := h'.1 a ha
      exact ⟨b, Finset.mem_union_right _ hb, hab⟩
  · rcases Finset.mem_union.1 hb with hb | hb
    · obtain ⟨a, ha, hab⟩ := h.2 b hb
      exact ⟨a, Finset.mem_union_left _ ha, hab⟩
    · obtain ⟨a, ha, hab⟩ := h'.2 b hb
      exact ⟨a, Finset.mem_union_right _ ha, hab⟩

/-- Left coverage with singleton right argument reduces to universal quantification.

    When the right plurality has exactly one element y, left coverage
    becomes: ∀a ∈ x. R(a, y).

    This is one half of [johnston-2023]'s "number effect": with a
    singular object DP, the cumulative reading collapses to universal
    distribution, eliminating the pairing uncertainty that motivates
    over-informative elaboration. -/
theorem singleton_right_left_coverage (R : A → B → Prop) (x : Finset A) (y : B) :
    LeftCoverage R x {y} ↔ ∀ a ∈ x, R a y := by
  unfold LeftCoverage
  constructor
  · intro h a ha
    obtain ⟨b, hb, hR⟩ := h a ha
    rw [Finset.mem_singleton.mp hb] at hR; exact hR
  · intro h a ha
    exact ⟨y, Finset.mem_singleton.mpr rfl, h a ha⟩

/-- Full `**` with singleton right argument and nonempty left argument.

    When `|Y| = 1` and `X` is nonempty, `**(R)(X, {y}) = ∀a ∈ X. R(a, y)`.
    Right coverage is trivially satisfied by any witness from X. -/
theorem singleton_right_cumulative (R : A → B → Prop) (x : Finset A) (y : B)
    (hne : x.Nonempty) :
    Cumulative R x {y} ↔ ∀ a ∈ x, R a y := by
  rw [cumulative_iff_coverages, singleton_right_left_coverage]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  intro b hb
  rw [Finset.mem_singleton.mp hb]
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, ha, h a ha⟩

/-! ### Closure form

Krifka's `**R` is Link's `*` applied to `R` as a predicate on the product semilattice: the
smallest relation containing `R` and closed under componentwise sum. -/

section Closure

open Mereology

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β] {R S : α → β → Prop}
  {x x' : α} {y y' : β}

/-- The cumulation `**R` of a relation ([krifka-1986]; [sternefeld-1998]): the closure of `R`
under componentwise sum, `Mereology.AlgClosure` on the product semilattice. -/
def Cumulation (R : α → β → Prop) (x : α) (y : β) : Prop :=
  AlgClosure (Function.uncurry R) (x, y)

theorem Cumulation.of_rel (h : R x y) : Cumulation R x y := AlgClosure.base h

theorem Cumulation.sup (h : Cumulation R x y) (h' : Cumulation R x' y') :
    Cumulation R (x ⊔ x') (y ⊔ y') :=
  AlgClosure.sum h h'

theorem Cumulation.mono (hRS : ∀ x y, R x y → S x y) (h : Cumulation R x y) :
    Cumulation S x y :=
  algClosure_mono (P := Function.uncurry R) (λ p => hRS p.1 p.2) _ h

/-- A cumulative relation is its own cumulation. -/
theorem cumulation_iff_of_cum (hR : CUM (Function.uncurry R)) : Cumulation R x y ↔ R x y :=
  algClosure_of_cum hR

end Closure

/-! ### Sets of individuals -/

section Finset

open Mereology

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- On finite sets, `**` of a relation between individuals, taken as singletons, is
bidirectional coverage of a nonempty pair: the closure form of [krifka-1986] and the coverage
form of [beck-sauerland-2000] agree away from the empty pair. -/
theorem cumulation_map_singleton (R : A → B → Prop) (x : Finset A) (y : Finset B) :
    Cumulation (Relation.Map R ({·}) ({·})) x y ↔ x.Nonempty ∧ Cumulative R x y := by
  constructor
  · suffices ∀ p : Finset A × Finset B,
        AlgClosure (Function.uncurry (Relation.Map R ({·}) ({·}))) p →
          p.1.Nonempty ∧ Cumulative R p.1 p.2 from this (x, y)
    intro p h
    induction h with
    | @base p h =>
      obtain ⟨x, y⟩ := p
      change ∃ a b, R a b ∧ ({a} : Finset A) = x ∧ ({b} : Finset B) = y at h
      obtain ⟨a, b, hab, rfl, rfl⟩ := h
      exact ⟨Finset.singleton_nonempty a, (cumulative_singleton R a b).2 hab⟩
    | sum _ _ ih ih' => exact ⟨ih.1.mono Finset.subset_union_left, ih.2.union ih'.2⟩
  · rintro ⟨hx, hl, hr⟩
    have : Nonempty B := hx.elim λ a ha => (hl a ha).elim λ b _ => ⟨b⟩
    have : Nonempty A := hx.elim λ a _ => ⟨a⟩
    choose! f hf hRf using hl
    choose! g hg hRg using hr
    have hy : y.Nonempty := hx.elim λ a ha => ⟨f a, hf a ha⟩
    have key : x.sup' hx (λ a => ({a}, {f a})) ⊔ y.sup' hy (λ b => ({g b}, {b})) = (x, y) := by
      refine le_antisymm (sup_le ((Finset.sup'_le_iff _ _).2 λ a ha => ?_)
        ((Finset.sup'_le_iff _ _).2 λ b hb => ?_))
        (Prod.le_def.2 ⟨Finset.subset_iff.2 λ a ha => ?_, Finset.subset_iff.2 λ b hb => ?_⟩)
      · exact Prod.le_def.2
          ⟨Finset.singleton_subset_iff.2 ha, Finset.singleton_subset_iff.2 (hf a ha)⟩
      · exact Prod.le_def.2
          ⟨Finset.singleton_subset_iff.2 (hg b hb), Finset.singleton_subset_iff.2 hb⟩
      · have hle :=
          Prod.le_def.1 (Finset.le_sup' (λ a => (({a} : Finset A), ({f a} : Finset B))) ha)
        rw [Prod.fst_sup, Finset.sup_eq_union]
        exact Finset.mem_union_left _ (Finset.singleton_subset_iff.1 hle.1)
      · have hle :=
          Prod.le_def.1 (Finset.le_sup' (λ b => (({g b} : Finset A), ({b} : Finset B))) hb)
        rw [Prod.snd_sup, Finset.sup_eq_union]
        exact Finset.mem_union_right _ (Finset.singleton_subset_iff.1 hle.2)
    show AlgClosure _ (x, y)
    rw [← key]
    exact AlgClosure.sum (algClosure_finsetSup' hx λ a ha => .base ⟨a, f a, hRf a ha, rfl, rfl⟩)
      (algClosure_finsetSup' hy λ b hb => .base ⟨g b, b, hRg b hb, rfl, rfl⟩)

end Finset

end Plurality.Cumulativity
