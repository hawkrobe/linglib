import Mathlib.Data.Fintype.Powerset
import Linglib.Features.Number.Basic
import Linglib.Features.Number.Interp
import Linglib.Features.ContainmentPair

/-!
# The feature decomposition of number

This file defines Harbour's `[±atomic, ±minimal]` feature bundle for the
three basic number values, its presentation as a containment pair shared
with person, and the classification of lattice elements by the regions of
`Number.interp`.

## Main definitions

* `Number.Features`: the `[±atomic, ±minimal]` bundle, with
  `Features.toNumber`/`Features.ofNumber` relating it to `Number`.
* `Number.featuresEquiv`: the bundle as a `ContainmentPair`, `outer` the
  minimality and `inner` the atomicity feature; `Features.WellFormed` is the
  containment `[+atomic] → [+minimal]`.
* `Number.latticeToFeatures`: the bundle a lattice element realizes in a
  region, singular on its atoms, dual on its minimal non-atoms, plural
  otherwise.
* `Number.dualPredOnLattice`: the dual as a predicate modifier.

## Main results

* `Number.card_wellFormed`: exactly three well-formed bundles.
* `Number.toNumber_isSome_iff`, `Number.ofNumber_toNumber`,
  `Number.toNumber_ofNumber`: the bundles and the values correspond on the
  well-formed cells.
* `Number.latticeToFeatures_wellFormed`: classification never produces the
  ill-formed cell — the containment is a theorem of the lattice semantics,
  not a stipulation.
* `Number.dualPredOnLattice_iff`: the dual predicate modifier is the
  restriction to elements classified `dualF`.

## Implementation notes

For number the containment filter follows from the semantics (an atom is
minimal in every region that excludes the null individual,
`Number.singular_subset_minimal`); for person it is a convention. The
examples use the powerset lattice `Finset (Fin n)` on its nonempty subsets,
where the atoms are the singletons.

## References

* [harbour-2014], (11), (12), §3, §4.4
* [harbour-2016], §9.5
* [link-1983]
* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025], §4.2.1, §8
-/

namespace Number

open _root_.Features (ContainmentPair ContainmentPairLike)
open Mereology (Atom CUM Null atomize null)

/-! ### The feature bundle -/

/-- Harbour's binary number features `[±atomic, ±minimal]`. -/
structure Features where
  /-- `[+atomic]`: the referent is an atom. -/
  isAtomic : Bool
  /-- `[+minimal]`: the referent is minimal in its region. -/
  isMinimal : Bool
  deriving DecidableEq, Repr, Fintype

/-- Singular: `[+atomic, +minimal]`. -/
def singularF : Features := ⟨true, true⟩

/-- Dual: `[−atomic, +minimal]`. -/
def dualF : Features := ⟨false, true⟩

/-- Plural: `[−atomic, −minimal]`. -/
def pluralF : Features := ⟨false, false⟩

/-- The number value a bundle realizes; the ill-formed `[+atomic, −minimal]`
realizes none. -/
def Features.toNumber : Features → Option Number
  | ⟨true, true⟩ => some .singular
  | ⟨false, true⟩ => some .dual
  | ⟨false, false⟩ => some .plural
  | ⟨true, false⟩ => none

/-- The bundle of a basic number value; the values that need feature
recursion or additivity have none. -/
def Features.ofNumber : Number → Option Features
  | .singular => some singularF
  | .dual => some dualF
  | .plural => some pluralF
  | _ => none

/-! ### The containment-pair presentation -/

/-- The bundle as a containment pair: `outer` is minimality and `inner`
atomicity, so `[+atomic] → [+minimal]` is `[+inner] → [+outer]`, the shape
shared with person. -/
def featuresEquiv : Features ≃ ContainmentPair where
  toFun f := ⟨f.isMinimal, f.isAtomic⟩
  invFun p := ⟨p.inner, p.outer⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

@[simp] theorem singular_is_maximal :
    ContainmentPairLike.toPair singularF = .maximal := rfl
@[simp] theorem dual_is_intermediate :
    ContainmentPairLike.toPair dualF = .intermediate := rfl
@[simp] theorem plural_is_minimal :
    ContainmentPairLike.toPair pluralF = .minimal := rfl

/-- A bundle is well-formed if `[+atomic]` entails `[+minimal]`. -/
abbrev Features.WellFormed (nf : Features) : Prop :=
  ContainmentPairLike.WellFormed nf

theorem atomic_implies_minimal :
    ∀ f : Features, f.WellFormed → f.isAtomic = true → f.isMinimal = true := by
  decide

/-- Exactly three well-formed bundles, the three basic number values. -/
theorem card_wellFormed : Fintype.card {nf : Features // nf.WellFormed} = 3 := by
  decide

theorem toNumber_isSome_iff : ∀ f : Features, f.toNumber.isSome ↔ f.WellFormed := by
  decide

theorem ofNumber_toNumber :
    ∀ f : Features, f.WellFormed → f.toNumber.bind Features.ofNumber = some f := by
  decide

theorem toNumber_ofNumber : ∀ (n : Number) (f : Features),
    Features.ofNumber n = some f → f.toNumber = some n := by
  decide

/-! ### Classification by lattice position -/

section Lattice

variable {D : Type*} [SemilatticeSup D] [Null D] [Fintype D] [DecidableLE D]
  [DecidablePred (null : D → Prop)]

/-- The bundle a lattice element realizes in the region `P`: singular on the
atoms of `P`, dual on its minimal non-atoms, plural on the rest — the decidable
mirror of `Number.interp`. -/
def latticeToFeatures (P : D → Prop) [DecidablePred P] (x : D) : Features :=
  if atomsOf P x then singularF else if dualOf P x then dualF else pluralF

/-- Classification never produces the ill-formed cell. -/
theorem latticeToFeatures_wellFormed (P : D → Prop) [DecidablePred P] (x : D) :
    (latticeToFeatures P x).WellFormed := by
  unfold latticeToFeatures
  split_ifs <;> decide

/-- The dual as a predicate modifier: `P x` and `x` has exactly two atomic
parts, i.e. is a minimal non-atom of the region `domain`
([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025] (39)). -/
abbrev dualPredOnLattice (domain P : D → Prop) (x : D) : Prop :=
  P x ∧ dualOf domain x

/-- The dual predicate modifier is the restriction of `P` to the elements
classified `dualF`. -/
theorem dualPredOnLattice_iff (domain : D → Prop) [DecidablePred domain] (P : D → Prop)
    (x : D) : dualPredOnLattice domain P x ↔ P x ∧ latticeToFeatures domain x = dualF := by
  unfold latticeToFeatures
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [if_neg fun ha => h.1.2 ha.2, if_pos h]
  · intro h
    by_contra hd
    split_ifs at h with ha <;> exact absurd h (by decide)

end Lattice

/-! ### The powerset lattice -/

/-- The nonempty subsets of `Fin 3`, a lattice with three atoms. -/
def ps3 (s : Finset (Fin 3)) : Prop := s.Nonempty

instance : DecidablePred ps3 := fun s => inferInstanceAs (Decidable s.Nonempty)

example : latticeToFeatures ps3 {0} = singularF := by decide
example : latticeToFeatures ps3 {0, 1} = dualF := by decide
example : latticeToFeatures ps3 {0, 1, 2} = pluralF := by decide

example : dualPredOnLattice ps3 (fun _ => True) {0, 2} := by decide
example : ¬ dualPredOnLattice ps3 (fun _ => True) ({0, 1, 2} : Finset (Fin 3)) := by decide

/-- With three atoms the non-atomic region is cumulative, so `[±additive]`
cannot split it; the paucal/plural contrast needs a larger lattice. -/
example : CUM (fun s : Finset (Fin 3) => 2 ≤ s.card) := by decide

/-- A paucal region of two to three atoms is not cumulative: `{0, 1} ⊔ {2, 3}`
has four. Complement completeness ([harbour-2014] (11)) holds of the plural
region of four or more atoms. -/
example :
    ¬ CUM (fun s : Finset (Fin 5) => 2 ≤ s.card ∧ s.card ≤ 3) ∧
      CUM (fun s : Finset (Fin 5) => 4 ≤ s.card) := by
  decide

end Number
