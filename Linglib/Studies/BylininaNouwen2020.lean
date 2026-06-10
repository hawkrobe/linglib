import Linglib.Semantics.Composition.TypeShifting
import Mathlib.Order.Bounds.Basic

/-!
# [bylinina-nouwen-2020] — Numeral semantics: the type-shift landscape

[bylinina-nouwen-2020] survey the semantics of bare numerals: three views —
numerals as number-denoting (type `d`, their (18)), as cardinality
modifiers (`⟨e,t⟩`, their (11)), and as degree quantifiers
(`⟨⟨d,t⟩,t⟩`, [kennedy-2015], their (43)) — and argue the views are
related by type-shifts and operators, "end[ing] up with equivalent
empirical coverage". This file formalises the equivalences the survey
itself contributes:

* their (23): the number view composed with `MANY` (their (22)) *is* the
  modifier meaning — `many_number`;
* their (25): `CARD` — an operator the authors define themselves, "for
  illustration of the equivalence of the modifier and number views" —
  maps the modifier meaning back to the number meaning —
  `card_numModifier`;
* their (49)–(50): [partee-1987]'s BE/IOTA lower [kennedy-2015]'s
  *exactly* degree quantifier to the number meaning — `BE_kennedy` and
  `iota_BE_kennedy`, on the Partee-triangle substrate
  (`Semantics/Composition/TypeShifting.lean`);
* their (52)–(54): the survey's own proposal, "fill[ing] in an empty slot
  in the available types of numeral semantic analyses" — an *at least*
  degree quantifier (their (52), which is exactly the Montague `lift` of
  the number view) together with a `MAX` operator (their (53)) that
  recovers Kennedy's *exactly* quantifier — `MAX_lift_eq_kennedy` — while
  keeping the lower-bound meaning basic (their argument from the polarity
  profile of "zero", [bylinina-nouwen-2018]).

Degrees are modelled as `ℕ`; `max(P)` is mathlib's `IsGreatest`;
pluralities are `Finset ℕ` with `#` as `Finset.card`. The survey's other
threads — exhaustification (§5, deferring to [spector-2013]), the
Heim–Kennedy generalization, lower-bound semantics ([horn-1972],
`atLeastMeaning` in `Semantics/Numerals/Basic.lean`) — live with their
primary anchors.
-/

set_option autoImplicit false

namespace BylininaNouwen2020

open Semantics.Composition.TypeShifting

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
`⟦twelve⟧ = λP. P(12)` — exactly the Montague `lift` of the number view. -/
theorem lowerBounded_eq_lift (n : ℕ) : (fun P : ℕ → Prop => P n) = lift n := rfl

/-- The survey's `MAX` operator (their (53)):
`⟦MAX⟧ = λD λP. max(P) ∈ ∩D`. -/
def MAX (D : (ℕ → Prop) → Prop) : (ℕ → Prop) → Prop :=
  fun P => ∃ m, IsGreatest {d | P d} m ∧ ∀ Q, D Q → Q m

/-- Their (54): `⟦MAX twelve⟧` on the *at least* quantifier is Kennedy's
*exactly* quantifier — the survey's account keeps the lower-bound meaning
basic and derives the *exactly* reading by `MAX`, preserving the
Heim–Kennedy scope explanation. -/
theorem MAX_lift_eq_kennedy (n : ℕ) : MAX (lift n) = kennedyNum n := by
  funext P
  refine propext ⟨fun ⟨m, hm, hall⟩ => ?_, fun h => ⟨n, h, fun Q hQ => hQ⟩⟩
  · have : m = n := hall (fun d => d = n) rfl
    exact this ▸ hm

/-- The lower-bound and *exactly* quantifiers genuinely differ before
`MAX` applies (witness `P = {n, n+1}`): `MAX` does real work. -/
theorem lift_ne_kennedy (n : ℕ) : lift (E := ℕ) n ≠ kennedyNum n := by
  intro h
  have := congrFun h (fun d => d = n ∨ d = n + 1)
  rw [lift] at this
  have hk : kennedyNum n (fun d => d = n ∨ d = n + 1) := this.mp (Or.inl rfl)
  exact absurd (hk.2 (Or.inr rfl : (n+1) ∈ {d | d = n ∨ d = n + 1})) (by omega)

end BylininaNouwen2020
