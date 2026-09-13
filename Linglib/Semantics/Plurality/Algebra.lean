import Linglib.Semantics.Mereology

/-!
# Link's algebra of plurals

This file defines the operators of [link-1983] on a join-semilattice `E` of individuals: the
plural closure `*P` of a predicate, the proper plural `⊕P`, distributivity and invariance of
predicates, the distributive operator `D` and reciprocal operator `DJR` of [link-1987], and the
materialization homomorphism from individuals to portions of matter with its material part and
material equivalence. It proves Link's theorems relating them, and the collapse of `*` on finite
sets of individuals to distribution over members.

## Definitions

* `Plurality.Algebra.star P`: the closure of `P` under sum, an abbreviation for
  `Mereology.AlgClosure P`.
* `Plurality.Algebra.properPlural P`: the non-atomic elements of `*P`.
* `Plurality.Algebra.IsDistr P`: `P` holds of atoms only.
* `Plurality.Algebra.Inv h P`: `P` does not distinguish `h`-equivalent individuals.
* `Plurality.Algebra.D P x`, `Plurality.Algebra.DJR R x`: every atomic part of `x` satisfies
  `P`; every two distinct atomic parts of `x` are `R`-related.
* `Plurality.Algebra.Materialization E M`: a `SupHom E M`, with `Plurality.Algebra.mPart` and
  `Plurality.Algebra.mEquiv` the preorder and equivalence it induces on `E`.
* `Plurality.Algebra.AtomJoinPrime E`: an atom below a sum lies below a summand.

## Main results

* `Plurality.Algebra.star_iff_of_atom`: on an atom, `*P` and `P` agree.
* `Plurality.Algebra.IsDistr.of_star_of_atom_le`: Link's distributive inference, for join-prime
  atoms.
* `Plurality.Algebra.IsDistr.properPlural_sup`, `Plurality.Algebra.cum_properPlural`: the sum
  of two distinct atoms of a distributive predicate is a proper plural, and proper plurals are
  closed under sum.
* `Plurality.Algebra.star_image_singleton`: on finite sets of individuals, taken as singletons,
  `*` holds of exactly the nonempty subsets.

## Implementation notes

Link's carrier is a complete join-semilattice with atoms and without a bottom; only
`SemilatticeSup E` and `Mereology.Atom` are used here. The complete atomic Boolean algebra of
later presentations ([landman-2000], [champollion-2017]) is a stronger assumption, entering only
through `AtomJoinPrime`. The set-based ontology of [schwarzschild-1996], where an individual is
its singleton and sum is union, is the `Finset α` instance of the last section.

## References

* [G. Link, *The logical analysis of plurals and mass terms* (1983)][link-1983]
* [G. Link, *Generalized quantifiers and plurals* (1987)][link-1987]
* [M. Krifka, *Nominal reference, temporal constitution and quantification in event semantics*
  (1989)][krifka-1989]
* [F. Landman, *Events and plurality* (2000)][landman-2000]
* [L. Champollion, *Parts of a whole* (2017)][champollion-2017]
* [L. Champollion, *Distributivity in formal semantics* (2019)][champollion-2019]
* [R. Schwarzschild, *Pluralities* (1996)][schwarzschild-1996]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
-/

namespace Plurality.Algebra

open _root_.Mereology

variable {E : Type*} [SemilatticeSup E] {P Q : E → Prop} {x y : E}

/-! ### Predicate operators -/

/-- The plural closure `*P`: the closure of `P` under sum. -/
abbrev star (P : E → Prop) : E → Prop := AlgClosure P

/-- The proper plural `⊕P`: the non-atomic elements of `*P` (D.12). -/
def properPlural (P : E → Prop) (x : E) : Prop :=
  star P x ∧ ¬ Atom x

/-- A distributive predicate holds of atoms only (D.19). -/
def IsDistr (P : E → Prop) : Prop :=
  ∀ x, P x → Atom x

/-- An invariant predicate does not distinguish individuals that `h` identifies (D.21). -/
def Inv {M : Type*} (h : E → M) (P : E → Prop) : Prop :=
  ∀ x y, h x = h y → (P x ↔ P y)

/-- The distributive operator `D`: every atomic part of `x` satisfies `P` ([link-1987];
[champollion-2019]). -/
def D (P : E → Prop) (x : E) : Prop :=
  ∀ y ≤ x, Atom y → P y

theorem D_of_atom (hx : Atom x) (hP : P x) : D P x :=
  λ _ hle hy => (hx.eq hle hy.not_isBot) ▸ hP

theorem D_mono (h : ∀ x, P x → Q x) (hD : D P x) : D Q x :=
  λ y hle hy => h y (hD y hle hy)

/-- The reciprocal operator `DJR`: every two distinct atomic parts of `x` are `R`-related
([link-1987]); on finite sets this is `Reciprocal.StrongReciprocity`. -/
def DJR (R : E → E → Prop) (x : E) : Prop :=
  ∀ y ≤ x, ∀ z ≤ x, Atom y → Atom z → y ≠ z → R y z

theorem DJR_mono {R S : E → E → Prop} (h : ∀ y z, R y z → S y z) (hR : DJR R x) : DJR S x :=
  λ y hy z hz ha hb hne => h y z (hR y hy z hz ha hb hne)

theorem DJR_and {R S : E → E → Prop} :
    DJR (λ y z => R y z ∧ S y z) x ↔ DJR R x ∧ DJR S x := by
  simp only [DJR, imp_and, forall_and]

/-! ### Materialization -/

section Constitution

variable {M : Type*} [SemilatticeSup M]

/-- Materialization (D.22): a sum-preserving map from individuals to their portions of
matter, a `SupHom`. -/
abbrev Materialization (E M : Type*) [SemilatticeSup E] [SemilatticeSup M] :=
  SupHom E M

/-- Material part (D.23): the matter of `x` is part of the matter of `y`. -/
def mPart (h : Materialization E M) (x y : E) : Prop :=
  h x ≤ h y

/-- Material equivalence (D.24): `x` and `y` are made of the same matter. -/
def mEquiv (h : Materialization E M) (x y : E) : Prop :=
  h x = h y

/-- An individual part is a material part (T.2). -/
theorem mPart_of_le (h : Materialization E M) (hxy : x ≤ y) : mPart h x y :=
  OrderHomClass.mono h hxy

theorem equivalence_mEquiv (h : Materialization E M) : Equivalence (mEquiv h) :=
  ⟨λ _ => rfl, Eq.symm, Eq.trans⟩

theorem mEquiv_iff (h : Materialization E M) : mEquiv h x y ↔ mPart h x y ∧ mPart h y x :=
  le_antisymm_iff

theorem Inv.iff_of_mEquiv {h : Materialization E M} (hP : Inv (⇑h) P) (hxy : mEquiv h x y) :
    P x ↔ P y :=
  hP x y hxy

end Constitution

/-! ### Link's theorems -/

/-- On an atom, `*P` and `P` agree (T.8). -/
theorem star_iff_of_atom (hx : Atom x) : star P x ↔ P x :=
  ⟨(of_algClosure_of_atom · hx), .base⟩

/-- No element of a distributive predicate is a proper plural (T.6). -/
theorem IsDistr.not_properPlural (hP : IsDistr P) (hx : P x) : ¬ properPlural P x :=
  λ h => h.2 (hP x hx)

/-- The sum of two distinct atoms of a distributive predicate is a proper plural. -/
theorem IsDistr.properPlural_sup (hP : IsDistr P) (hx : P x) (hy : P y) (hne : x ≠ y) :
    properPlural P (x ⊔ y) :=
  ⟨.sum (.base hx) (.base hy), not_atom_sup_of_ne (hP x hx) (hP y hy) hne⟩

/-- Proper plurals are closed under sum. -/
theorem cum_properPlural : CUM (properPlural P) := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩
  refine ⟨.sum hx hy, λ h => ?_⟩
  by_cases hx0 : IsBot x
  · rw [sup_eq_right.mpr (hx0 _)] at h
    exact hy' h
  · exact hx' ((h.eq le_sup_left hx0) ▸ h)

/-- Atoms are join-prime: an atom below a sum lies below a summand, as in a Boolean algebra. -/
def AtomJoinPrime (E : Type*) [SemilatticeSup E] : Prop :=
  ∀ (a : E), Atom a → ∀ (x y : E), a ≤ x ⊔ y → a ≤ x ∨ a ≤ y

/-- Link's distributive inference: with join-prime atoms, every atomic part of an element of
`*P` satisfies a distributive `P`. -/
theorem IsDistr.of_star_of_atom_le (hP : IsDistr P) (hJP : AtomJoinPrime E) (h : star P x)
    (hy : Atom y) (hle : y ≤ x) : P y := by
  induction h with
  | base hp => exact ((hP _ hp).eq hle hy.not_isBot) ▸ hp
  | @sum a b _ _ iha ihb => exact (hJP y hy a b hle).elim iha ihb

/-! ### Sets of individuals

On the set-based ontology of [schwarzschild-1996], pluralities are finite sets of individuals,
an individual is its singleton, and sum is union. -/

section Finset
variable {α : Type*} [DecidableEq α]

/-- `*` of a set of individuals, taken as singletons, holds of exactly its nonempty subsets;
this is [sternefeld-1998]'s identification of `*P` with `D P` for a `P` true of individuals
only (15). -/
theorem star_image_singleton (S : Set α) (x : Finset α) :
    star (· ∈ ({·} : α → Finset α) '' S) x ↔ x.Nonempty ∧ ↑x ⊆ S := by
  constructor
  · intro h
    induction h with
    | base h => obtain ⟨a, ha, rfl⟩ := h; exact ⟨Finset.singleton_nonempty a, by simpa⟩
    | sum _ _ ih ih' =>
      refine ⟨ih.1.mono Finset.subset_union_left, ?_⟩
      rw [Finset.sup_eq_union, Finset.coe_union]
      exact Set.union_subset ih.2 ih'.2
  · rintro ⟨hx, hS⟩
    have key : x.sup' hx (λ a => ({a} : Finset α)) = x :=
      le_antisymm ((Finset.sup'_le_iff _ _).2 λ a ha => Finset.singleton_subset_iff.2 ha)
        (Finset.subset_iff.2 λ a ha =>
          Finset.singleton_subset_iff.1 (Finset.le_sup' (λ a => ({a} : Finset α)) ha))
    rw [← key]
    exact algClosure_finsetSup' hx λ a ha => .base ⟨a, hS ha, rfl⟩

/-- `*` of a predicate true of individuals only holds of the nonempty pluralities all of
whose members satisfy it. -/
theorem star_iff_of_subset_range_singleton {P : Finset α → Prop}
    (hP : {x | P x} ⊆ Set.range ({·} : α → Finset α)) (x : Finset α) :
    star P x ↔ x.Nonempty ∧ ∀ a ∈ x, P {a} := by
  have : P = (· ∈ ({·} : α → Finset α) '' {a | P {a}}) := by
    ext s
    constructor
    · intro hs
      obtain ⟨a, rfl⟩ := hP hs
      exact ⟨a, hs, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  conv_lhs => rw [this]
  rw [star_image_singleton]
  exact Iff.rfl

end Finset

end Plurality.Algebra
