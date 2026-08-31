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

* `numModifier`, `MANY`, `CARD` — the modifier view, the counting operator and the operator
  recovering a cardinality from a modifier meaning
* `kennedyNum` — the degree quantifier whose degree properties have the numeral as maximum
* `MAX` — the survey's operator, taking a quantifier to the properties whose maximum it holds of

## Main results

* `many_number`, `card_numModifier` — the number and modifier views are interderivable
* `BE_kennedy`, `iota_BE_kennedy` — lowering the degree quantifier gives the number back
* `lowerBounded_eq_lift`, `MAX_lift_eq_kennedy` — the survey's lower-bound quantifier is the
  Montague lift of the number, and its maximum operator recovers the exactly reading
* `lift_ne_kennedy` — the two quantifiers are not the same, so the operator is not idle

## References

* [bylinina-nouwen-2020]
* [bylinina-nouwen-2018]
* [kennedy-2015]
* [partee-1987]
-/
namespace BylininaNouwen2020

open Semantics.Composition.TypeShifting
open Quantification (BE individual)

/-! ### The number and modifier views (their (11), (18), (22)–(25))

Pluralities are finite sets of atoms; `#` is cardinality. -/

/-- The modifier view (their (11)): `⟦twelveₘ⟧ = λx. #x = 12`. -/
def numModifier (n : ℕ) : Finset ℕ → Prop := fun x => x.card = n

/-- The counting operator `MANY` (their (22)): `⟦MANY⟧ = λd λx. #x = d`. -/
def MANY (d : ℕ) : Finset ℕ → Prop := fun x => x.card = d

/-- Their (23): `⟦twelveₙ MANY⟧ = ⟦twelveₘ⟧` — the number view composed
with `MANY` is definitionally the modifier meaning. -/
theorem many_number (n : ℕ) : MANY n = numModifier n := rfl

/-- The survey's own `CARD` operator (their (24)):
`⟦CARD⟧ = λP ιd. ∀x[P(x) → #x = d]`, rendered as the relation "`d` is the
degree `CARD(P)` denotes" — the ι-presupposition is the existence-and-
uniqueness conjunct. -/
def CARD (P : Finset ℕ → Prop) : ℕ → Prop :=
  fun d => (∃ x, P x) ∧ ∀ x, P x → x.card = d

/-- Their (25): `CARD(⟦twelveₘ⟧) = ⟦twelveₙ⟧` — `CARD` maps the modifier
meaning back to the number meaning (`ident n` is the singleton property of
the degree `n`). -/
theorem card_numModifier (n : ℕ) : CARD (numModifier n) = ident n := by
  funext d
  refine propext ⟨fun ⟨⟨x, hx⟩, hall⟩ => ?_, fun h => ?_⟩
  · exact (hall x hx).symm.trans hx ▸ (hall x hx ▸ rfl)
  · obtain rfl : n = d := h
    exact ⟨⟨Finset.range n, Finset.card_range n⟩, fun x hx => hx⟩

/-! ### The degree-quantifier view (their (43), (47)–(50))

[kennedy-2015]'s *exactly* numeral: the degree properties whose maximal
value is `n`. `max(P) = n` is mathlib's `IsGreatest P n`. -/

/-- Kennedy's degree quantifier (their (43)): `⟦twelve⟧ = λP. max(P) = 12`. -/
def kennedyNum (n : ℕ) : (ℕ → Prop) → Prop := fun P => IsGreatest {d | P d} n

/-- Their (49): `BE(⟦twelve⟧) = {12}` — [partee-1987]'s BE lowers Kennedy's
quantifier to the singleton degree property. -/
theorem BE_kennedy (n : ℕ) : BE (kennedyNum n) = ident n := by
  funext x
  refine propext ⟨fun h => h.1, fun h => ⟨h, fun d hd => ?_⟩⟩
  exact ((hd : d = x).trans (h : n = x).symm).le

/-- Their (50): `IOTA(BE(⟦twelve⟧)) = 12` — the BE/IOTA chain recovers the
number meaning, via the substrate's `iota_ident` roundtrip. -/
theorem iota_BE_kennedy [DecidableEq ℕ] (domain : List ℕ) (n : ℕ)
    (hmem : n ∈ domain) (hnd : domain.Nodup) :
    iota domain (BE (kennedyNum n)) = some n := by
  rw [BE_kennedy]
  exact iota_ident domain n hmem hnd

/-! ### The survey's proposal: at-least quantifier + MAX (their (52)–(54)) -/

/-- The survey's *at least* degree quantifier (their (52)):
`⟦twelve⟧ = λP. P(12)` — exactly the Montague lift `individual` of the
number view. -/
theorem lowerBounded_eq_lift (n : ℕ) :
    (fun P : ℕ → Prop => P n) = individual n := rfl

/-- The survey's `MAX` operator (their (53)):
`⟦MAX⟧ = λD λP. max(P) ∈ ∩D`. -/
def MAX (D : (ℕ → Prop) → Prop) : (ℕ → Prop) → Prop :=
  fun P => ∃ m, IsGreatest {d | P d} m ∧ ∀ Q, D Q → Q m

/-- Their (54): `⟦MAX twelve⟧` on the *at least* quantifier is Kennedy's
*exactly* quantifier — the survey's account keeps the lower-bound meaning
basic and derives the *exactly* reading by `MAX`, preserving the
Heim–Kennedy scope explanation. -/
theorem MAX_lift_eq_kennedy (n : ℕ) : MAX (individual n) = kennedyNum n := by
  funext P
  refine propext ⟨fun ⟨m, hm, hall⟩ => ?_, fun h => ⟨n, h, fun Q hQ => hQ⟩⟩
  · have : m = n := hall (fun d => d = n) rfl
    exact this ▸ hm

/-- The lower-bound and *exactly* quantifiers genuinely differ before
`MAX` applies (witness `P = {n, n+1}`): `MAX` does real work. -/
theorem lift_ne_kennedy (n : ℕ) : individual (α := ℕ) n ≠ kennedyNum n := by
  intro h
  have := congrFun h (fun d => d = n ∨ d = n + 1)
  rw [individual] at this
  have hk : kennedyNum n (fun d => d = n ∨ d = n + 1) := this.mp (Or.inl rfl)
  exact absurd (hk.2 (Or.inr rfl : (n+1) ∈ {d | d = n ∨ d = n + 1})) (by omega)

end BylininaNouwen2020
