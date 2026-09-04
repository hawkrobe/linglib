import Linglib.Semantics.Quantification.Counting

/-!
# Generic quantifiers as generalized-quantifier schemas

Rival semantics for the silent generic operator Gen, expressed as instances of the
existing `Quantification.GQ α` generalized-quantifier interface rather than as bespoke
per-paper types. The competing theories then differ by a property of the `GQ`, not by an
incompatible signature: all are `Conservative`, and only the majority schema is
`Proportional`. The traditional schema is a normalcy-restricted universal — the kind's
normal members satisfy the scope; Nickel's replaces the single normalcy predicate by ways
of being normal, some one of which makes all of its normal members satisfy the scope. The
third schema, Cohen's majority reading, is the existing `Quantification.most_sem`, and
`most_proportional` records that it alone is proportional — its truth is a function of the
|R ∩ S| : |R ∖ S| ratio. That is the precise "generics as majority quantification"
characterization the later genericity literature rejects as a theory of generics; it is
true of this operator, not of generics in general.

The per-paper operators are shown equal to these schemas in the study files
(`Cohen1999.gen_univ_eq_most_sem`, `Nickel2009.nickelGEN_univ_eq_genWays`), so the
unification subsumes them rather than paralleling them. Those bridges are to the operators
as linglib formalizes them, inheriting their documented simplifications: Cohen's operator
enters at the absolute reading with the alternative set at its extensional disjunction,
and the ways schema takes Nickel's modal ways at their actual extensions.

## Main definitions

* `genNormalcy normal : GQ α` — normalcy-restricted universal generic.
* `genWays normalIn ways : GQ α` — ways-of-normality generic.

## Main results

* `genNormalcy_conservative`, `genWays_conservative` — the generic schemas are
  conservative.
* `genWays_singleton` — one way of normality reduces `genWays` to `genNormalcy`.
* `genNormalcy_not_ratio_determined` — equal cardinality ratio, opposite generic verdict,
  so the normalcy schema is not `Proportional`.

## Implementation notes

`GQ α` is whole-carrier (`Fintype`); the study operators take an explicit `Finset` domain
and bridge at `Finset.univ`. `most_sem` and `Proportional` are stated over the
noncomputable classical `count`, so the proportionality contrast is witnessed by a
decidable cardinality example rather than a `Proportional` counterexample.

## References

* [J. Barwise and R. Cooper, *Generalized Quantifiers and Natural Language*
  (1981)][barwise-cooper-1981]
* [M. Krifka, F. J. Pelletier, G. N. Carlson, A. ter Meulen, G. Chierchia and G. Link,
  *Genericity: An Introduction* (1995)][krifka-etal-1995]
* [A. Cohen, *Think Generic! The Meaning and Use of Generic Sentences* (1999)][cohen-1999a]
* [B. Nickel, *Generics and the Ways of Normality* (2009)][nickel-2009]
* [S.-J. Leslie, *Generics: Cognition and Acquisition* (2008)][leslie-2008]
-/

namespace Quantification

variable {α : Type*} [Fintype α]

/-! ### The generic schemas as generalized quantifiers -/

/-- The traditional Gen as a generalized quantifier ([krifka-etal-1995]): the
    restrictor's normal members all satisfy the scope — a restricted universal
    with a hidden normalcy parameter. -/
def genNormalcy (normal : α → Prop) : GQ α :=
  fun R S => everyOn Finset.univ (fun x => normal x ∧ R x) S

/-- The ways-of-normality Gen as a generalized quantifier ([nickel-2009]): some
    way of being normal makes all of its normal members satisfy the scope, with
    the ways taken at their actual extensions. -/
def genWays {ι : Type*} (normalIn : α → ι → Prop) (ways : Finset ι) : GQ α :=
  fun R S => ∃ w ∈ ways, everyOn Finset.univ (fun x => normalIn x w ∧ R x) S

/-! ### Conservativity -/

/-- The normalcy-restricted generic is conservative ([barwise-cooper-1981]). -/
theorem genNormalcy_conservative (normal : α → Prop) :
    Conservative (genNormalcy normal) := by
  intro R S
  simp only [genNormalcy, everyOn]
  exact ⟨fun h x hx hpre => ⟨hpre.2, h x hx hpre⟩, fun h x hx hpre => (h x hx hpre).2⟩

/-- The ways-of-normality generic is conservative ([barwise-cooper-1981]). -/
theorem genWays_conservative {ι : Type*} (normalIn : α → ι → Prop) (ways : Finset ι) :
    Conservative (genWays normalIn ways) := by
  intro R S
  simp only [genWays, everyOn]
  constructor
  · rintro ⟨w, hw, h⟩; exact ⟨w, hw, fun x hx hpre => ⟨hpre.2, h x hx hpre⟩⟩
  · rintro ⟨w, hw, h⟩; exact ⟨w, hw, fun x hx hpre => (h x hx hpre).2⟩

/-- A single way of being normal reduces `genWays` to `genNormalcy`: [nickel-2009]'s
    account is the traditional one when there is only one respect of normality. -/
theorem genWays_singleton {ι : Type*} (normalIn : α → ι → Prop) (w : ι) :
    genWays normalIn {w} = genNormalcy (fun x => normalIn x w) := by
  funext R S
  simp only [genWays, genNormalcy, Finset.mem_singleton, exists_eq_left]

/-! ### Proportionality separates majority from normalcy

The majority operator is `Proportional` (`most_proportional`, in `Counting`); the
normalcy schema is not. -/

/-- The normalcy generic is not ratio-determined, hence not `Proportional`: over
    `Fin 2` with only `0` normal, `{0}`-in-scope is generic-true while
    `{1}`-in-scope is generic-false, yet both have |R ∩ S| : |R ∖ S| = 1 : 1. -/
theorem genNormalcy_not_ratio_determined :
    genNormalcy (α := Fin 2) (· = 0) (fun _ => True) (· = 0) ∧
    ¬ genNormalcy (α := Fin 2) (· = 0) (fun _ => True) (· = 1) := by
  refine ⟨?_, ?_⟩ <;> simp only [genNormalcy, everyOn] <;> decide

end Quantification
