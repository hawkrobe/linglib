import Linglib.Semantics.Reference.Iota
import Linglib.Semantics.Degree.Quantifier
import Linglib.Semantics.Quantification.NP
import Mathlib.Data.Fintype.EquivFin

/-!
# Bylinina and Nouwen (2020): Numeral semantics

This file formalizes the type landscape of [bylinina-nouwen-2020]. A bare numeral has been taken
to denote a number, a predicate counting the atoms of a plurality, or a quantifier over degree
properties, and the survey's point is that the three are notational variants related by
type-shifts: the counting operator `MANY` takes the number to the predicate ((22), (23)), the
survey's `CARD` takes the predicate back to the number ((24), (25)), and [partee-1987]'s `BE` and
`iota`, the Russellian `russellIota`, lower [kennedy-2015]'s degree quantifier, `λP. max(P) = n`,
to the number ((49), (50)). The survey then fills the empty slot in the landscape with a lower-bound
degree quantifier, the Montague lift of the number ((52)), and an operator `MAX` sending a
quantifier to the properties whose maximum lies in every member of it ((53)), which turns the
lower-bound quantifier into the exactly-reading one ((54)) while keeping the lower bound basic, as
the polarity behaviour of *zero* argues it should ([bylinina-nouwen-2018]).

## Main definitions

* `MANY d`: the pluralities with `d` atoms, the cardinality instance of `Comparison.eq.over`.
* `CARD P`: the degrees `d` with `Finset.card '' P = {d}`, the graph of `ιd. ∀x[P(x) → #x = d]`.
* `MAX D`: `Degree.maxIn (⋂₀ D)`, the properties whose maximum lies in every member of `D`.

## Main results

* `CARD_MANY`, `MANY_injective_iff`: `CARD` inverts `MANY` at every numeral some plurality
  realizes, so the modifier view determines the numeral exactly when the atoms are infinite.
* `BE_maxIn_singleton`, `russellIota_BE_maxIn_singleton`: lowering the exactly-reading
  quantifier gives the number back.
* `MAX_individual`, `maxIn_singleton_lt_individual`: `MAX` takes the lower-bound quantifier to the
  exactly-reading one, which is strictly stronger.
* `maxIn_singleton_injective`: the exactly-reading quantifier determines the numeral, as the
  lower-bound one does by `Quantifier.NP.individual_injective`.

## Implementation notes

Degrees are natural numbers, a degree property is a `Set ℕ` and a degree quantifier a predicate
on them, so Kennedy's numeral is the substrate's `Degree.maxIn {n}` and a property without a
maximum falsifies it rather than leaving it undefined. Pluralities are the finite sets of atoms of
any type and `#` is `Finset.card`; the identity `CARD (MANY n) = {n}` needs a plurality of `n`
atoms to exist, which the survey's unbounded domain supplies and a finite one does not.

## References

* [bylinina-nouwen-2020]
* [bylinina-nouwen-2018]
* [kennedy-2015]
* [partee-1987]
-/
namespace BylininaNouwen2020

open Reference Degree Quantifier Quantifier.GQ Quantifier.NP Set

variable {α : Type*}

/-! ### The number and the modifier views

Pluralities are finite sets of atoms and `#` is cardinality. The modifier meaning of a numeral is
the counting operator at its number, so the two views differ only in whether the counting is built
into the numeral or supplied by an operator. -/

/-- `MANY d` is the property of pluralities with `d` atoms, `λx. #x = d`. -/
def MANY (d : ℕ) : Set (Finset α) := Comparison.eq.over Finset.card d

theorem mem_MANY {d : ℕ} {x : Finset α} : x ∈ MANY d ↔ x.card = d := Iff.rfl

/-- `CARD P` is the number of atoms every plurality in `P` has, the degree `ιd. ∀x[P(x) → #x = d]`
as the relation holding of `d` when the image of `P` under `#` is `{d}`. -/
def CARD (P : Set (Finset α)) : Set ℕ := {d | Finset.card '' P = {d}}

/-- `CARD` recovers the number a modifier meaning counts, given a plurality of that size. -/
theorem CARD_MANY {n : ℕ} (hn : ∃ x : Finset α, x.card = n) : CARD (MANY (α := α) n) = {n} := by
  ext d
  simp only [CARD, MANY, Comparison.over, Comparison.interval, mem_ofPred_eq,
    image_preimage_eq_of_subset (singleton_subset_iff.2 (hn : n ∈ range Finset.card)),
    singleton_eq_singleton_iff, mem_singleton_iff]
  exact eq_comm

/-- The modifier view determines the numeral exactly when there are pluralities of every size: on
a finite domain of atoms every numeral beyond its size denotes the empty property. -/
theorem MANY_injective_iff : Function.Injective (MANY (α := α)) ↔ Infinite α := by
  refine ⟨fun h => not_finite_iff_infinite.1 fun _ => ?_, fun _ => ?_⟩
  · have := Fintype.ofFinite α
    have key : ∀ k, MANY (α := α) (Fintype.card α + 1 + k) = ∅ := fun k =>
      eq_empty_of_forall_notMem fun x hx => by
        have := Finset.card_le_univ x; have := mem_MANY.1 hx; omega
    exact absurd (h ((key 0).trans (key 1).symm)) (by omega)
  · exact (preimage_injective.2 (Infinite.exists_subset_card_eq α)).comp singleton_injective

/-! ### The degree-quantifier views

A numeral may instead denote a quantifier over degree properties: Kennedy's, holding of the
properties whose greatest element it is, `maxIn {n}`, or the lower-bound one holding of the
properties containing it, `individual n`. -/

/-- `BE` lowers the exactly-reading quantifier to the number ((49)): the properties whose greatest
element is `n` share the single degree `n`. -/
theorem BE_maxIn_singleton (n : ℕ) : BE (maxIn {n}) = ident n := by
  funext x
  exact propext ⟨fun h => ((maxIn_singleton.1 h).1 : n = x).symm, fun h => by
    subst h; exact maxIn_singleton.2 isGreatest_singleton⟩

/-- Lowering with `BE` and then `iota` recovers the number ((50)). -/
theorem russellIota_BE_maxIn_singleton (n : ℕ) : russellIota (BE (maxIn {n})) = some n := by
  rw [BE_maxIn_singleton]; exact russellIota_ident n

/-- The exactly-reading quantifier determines the numeral, since `BE` recovers it. -/
theorem maxIn_singleton_injective : Function.Injective fun n : ℕ => maxIn {n} :=
  fun a b (h : maxIn {a} = maxIn {b}) =>
    ident_injective (by rw [← BE_maxIn_singleton, ← BE_maxIn_singleton, h])

/-! ### The survey's proposal

The empty slot in the landscape is a lower-bound degree quantifier, the Montague lift
`individual n` of the number ((52)); the operator `MAX` recovers the exactly reading from it
((53), (54)), so the lower bound stays basic and the exactly reading is derived, the direction the
polarity behaviour of *zero* requires ([bylinina-nouwen-2018]). -/

/-- `MAX D` holds of the degree properties whose maximum lies in every member of `D`:
`λD λP. max(P) ∈ ∩D`. -/
def MAX (D : Set (Set ℕ)) : Set ℕ → Prop := maxIn (⋂₀ D)

/-- `MAX` takes the lower-bound quantifier to the exactly-reading one ((54)), since the properties
containing `n` intersect to `{n}`. -/
theorem MAX_individual (n : ℕ) : MAX (individual n) = maxIn {n} := by
  rw [MAX, sInter_individual]

/-- The exactly-reading quantifier is strictly stronger than the lower-bound one, so `MAX` does
real work: a property with greatest element `n` contains `n`, and `{n, n + 1}` contains `n`
without `n` being its greatest element. -/
theorem maxIn_singleton_lt_individual (n : ℕ) : maxIn {n} < (individual n : Set ℕ → Prop) :=
  lt_of_le_not_ge (fun _ h => (maxIn_singleton.1 h).1) fun h =>
    absurd ((maxIn_singleton.1 (h {n, n + 1} (Or.inl rfl))).2 (Or.inr rfl)) (by omega)

end BylininaNouwen2020
