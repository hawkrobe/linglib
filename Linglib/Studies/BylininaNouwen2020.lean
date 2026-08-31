import Linglib.Semantics.Composition.TypeShifting
import Mathlib.Order.Bounds.Basic

/-!
# Bylinina and Nouwen 2020: numeral semantics

A bare numeral has been given three kinds of denotation: a number, a modifier counting the atoms of
a plurality, and a quantifier over degree properties. The survey's point is that the three are not
rival analyses of the same data but notational variants related by type-shifts, with equivalent
empirical coverage, and this file proves the equivalences it gives: composing the number view with
a counting operator yields the modifier view and an operator taking cardinalities recovers the
number from the modifier, while lowering the degree quantifier with the shifts of the Partee
triangle lands on the number again.

The survey then fills the gap the three leave: a numeral denoting the degree properties that hold
of it — a lower-bound meaning, which is the Montague lift of the number view — together with an
operator taking maxima, which recovers the exactly-reading quantifier from it. That keeps the
lower bound basic, as the polarity behaviour of *zero* argues it should be, and the operator does
real work: the two quantifiers differ before it applies.

Degrees are natural numbers, maxima are `IsGreatest`, and pluralities are finite sets with
`Finset.card` for the cardinality.

## Main definitions

* `MANY`, `CARD` — the counting operator and the operator recovering a cardinality from a modifier
  meaning
* `exactly` — the quantifier holding of the degree properties the numeral is the maximum of
* `MAX` — the survey's operator, taking a quantifier to the properties whose maximum satisfies it

## Main results

* `CARD_MANY` — the number and modifier views are interderivable
* `BE_exactly`, `iota_BE_exactly` — lowering the degree quantifier gives the number back
* `MAX_individual` — the maximum operator takes the lower-bound quantifier, which is the Montague
  lift of the number, to the exactly-reading one
* `individual_ne_exactly` — the two quantifiers are not the same, so the operator is not idle
* `MANY_injective`, `exactly_injective`, `individual_injective` — each view determines the
  numeral

## References

* [bylinina-nouwen-2020]
* [bylinina-nouwen-2018]
* [kennedy-2015]
* [partee-1987]
-/
namespace BylininaNouwen2020

open Semantics.Composition.TypeShifting Quantification

/-! ### The number and the modifier views

Pluralities are finite sets of atoms and `#` is cardinality. The modifier view of a numeral is the
counting operator applied to its number (their (11), (22), (23)): the two views differ only in
whether the counting is built into the numeral or supplied by an operator, which is why the survey
can state their equivalence as an identity. -/

/-- `MANY d` is the property of pluralities with `d` atoms: `MANY d = λx. #x = d`. -/
def MANY (d : ℕ) : Finset ℕ → Prop := fun x => x.card = d

/-- `CARD P d` holds when `P` is satisfiable and every plurality satisfying it has `d` atoms —
the relation `d = ιd'. ∀x[P(x) → #x = d']`, its presupposition the first conjunct. -/
def CARD (P : Finset ℕ → Prop) : ℕ → Prop :=
  fun d => (∃ x, P x) ∧ ∀ x, P x → x.card = d

/-- `CARD` recovers the number a modifier meaning counts. -/
theorem CARD_MANY (n : ℕ) : CARD (MANY n) = ident n := by
  funext d
  refine propext ⟨fun ⟨⟨x, hx⟩, hall⟩ => ?_, fun h => ?_⟩
  · exact (hall x hx).symm.trans hx ▸ (hall x hx ▸ rfl)
  · obtain rfl : n = d := h
    exact ⟨⟨Finset.range n, Finset.card_range n⟩, fun x hx => hx⟩

/-! ### The degree-quantifier views

A numeral may instead denote a quantifier over degree properties, either those whose maximum it is
(the exactly reading) or those that simply hold of it (the lower-bound reading). Maxima are
`IsGreatest`. -/

/-- `exactly n` holds of the degree properties whose greatest element is `n`. -/
def exactly (n : ℕ) : (ℕ → Prop) → Prop := fun P => IsGreatest {d | P d} n

/-- `BE` lowers the exactly-reading quantifier to the degree itself. -/
theorem BE_exactly (n : ℕ) : BE (exactly n) = ident n := by
  funext x
  refine propext ⟨fun h => h.1, fun h => ⟨h, fun d hd => ?_⟩⟩
  exact ((hd : d = x).trans (h : n = x).symm).le

/-- Lowering with `BE` and then `IOTA` recovers the number. -/
theorem iota_BE_exactly [DecidableEq ℕ] (domain : List ℕ) (n : ℕ)
    (hmem : n ∈ domain) (hnd : domain.Nodup) :
    iota domain (BE (exactly n)) = some n := by
  rw [BE_exactly]
  exact iota_ident domain n hmem hnd

/-! ### The survey's proposal (their (52)–(54))

The gap the three views leave is a numeral denoting the degree properties that merely hold of it —
`individual n`, the Montague lift of the number view, which is the survey's (52). An operator
taking maxima then recovers the exactly reading from it, so the lower bound can stay basic, as the
polarity behaviour of *zero* argues it should ([bylinina-nouwen-2018]). -/

/-- `MAX D P` holds when `P` has a greatest element satisfying every property in `D`:
`MAX = λD λP. max(P) ∈ ∩D`. -/
def MAX (D : (ℕ → Prop) → Prop) : (ℕ → Prop) → Prop :=
  fun P => ∃ m, IsGreatest {d | P d} m ∧ ∀ Q, D Q → Q m

/-- `MAX` takes the lower-bound quantifier to the exactly-reading one. -/
theorem MAX_individual (n : ℕ) : MAX (individual n) = exactly n := by
  funext P
  refine propext ⟨fun ⟨m, hm, hall⟩ => ?_, fun h => ⟨n, h, fun Q hQ => hQ⟩⟩
  · have : m = n := hall (fun d => d = n) rfl
    exact this ▸ hm

/-- The two quantifiers differ: `{n, n+1}` holds of the numeral without having it as greatest
element. -/
theorem individual_ne_exactly (n : ℕ) : individual (α := ℕ) n ≠ exactly n := by
  intro h
  have := congrFun h (fun d => d = n ∨ d = n + 1)
  rw [individual] at this
  have hk : exactly n (fun d => d = n ∨ d = n + 1) := this.mp (Or.inl rfl)
  exact absurd (hk.2 (Or.inr rfl : (n+1) ∈ {d | d = n ∨ d = n + 1})) (by omega)

/-! ### Each view determines the numeral

The shifts above are left inverses of the views, so no two numerals share a modifier meaning or a
degree quantifier: the views encode the number faithfully, which is what equivalent empirical
coverage comes to. -/

private theorem ident_injective : Function.Injective (ident (E := ℕ)) := fun a b h => by
  simpa [ident, eq_comm] using congrFun h a

/-- Distinct numerals have distinct modifier meanings. -/
theorem MANY_injective : Function.Injective MANY := fun a b h =>
  ident_injective (by rw [← CARD_MANY, ← CARD_MANY, h])

/-- Distinct numerals have distinct exactly-reading quantifiers. -/
theorem exactly_injective : Function.Injective exactly := fun a b h =>
  ident_injective (by rw [← BE_exactly, ← BE_exactly, h])

/-- Distinct numerals have distinct lower-bound quantifiers. -/
theorem individual_injective : Function.Injective (individual (α := ℕ)) := fun a b h =>
  exactly_injective (by rw [← MAX_individual, ← MAX_individual, h])

end BylininaNouwen2020
