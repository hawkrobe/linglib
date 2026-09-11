import Linglib.Pragmatics.Implicature.SomeAll
import Linglib.Semantics.Quantification.Numerals.Basic

/-!
# Huang, Spelke and Snedeker (2013): What exactly do numbers mean?

This file formalizes the covered-box task of [huang-spelke-snedeker-2013], which asks whether
number words have exact or lower-bounded semantics by cancelling the scalar implicature that
would otherwise supply the upper bound. A trial offers two visible boxes and a covered one, and
the instruction is a definite description, *the box with two fish*; under a reading `R` of the
term the referent is the visible box satisfying `R` when exactly one does, the covered box when
none does, and no box at all when both do (`choice`). In the critical trials a lower-bounded
match is visible and an exact one is not: an exact *two* sends the participant to the covered
box and a lower-bounded *two* to the visible box (`choice_bareMeaning_covered`,
`choice_atLeastMeaning_visible`), while for *some* the literal meaning picks the box where
Cookie Monster has all of the cookies and the strengthened meaning the covered box. Adults and
two- to three-year-olds took the total set for *some* and the covered box for *two*.

Two-knowers, children who give one and two but a handful for larger numerals in Wynn's Give-N
task ([wynn-1992]), are the population for which the lower-bounded account has no implicature
to offer, the developmental strategy of [musolino-2004]: exhaustifying *two* against the count
list a child knows leaves the lower bound untouched when *two* is its top (`exhKnown_last`),
and only a known stronger numeral makes it exact (`exhKnown_of_lt`). Section 6.1's residual
route, an implicit alternative *more than two*, does recover exactness
(`atLeast_not_moreThan_iff_bare`).

## Implementation notes

* Scalar trials are typed by the shared `SomeAllWorld`, a box showing Cookie Monster's share of
  the cookies; number trials by the cardinality of a box.
* The choice proportions and the statistics stay in prose: the paradigm's predictions are
  categorical, and the paper's argument is that the majority choice identifies the reading.

## References

* [huang-spelke-snedeker-2013]
* [wynn-1992]
* [musolino-2004]
-/

namespace HuangSpelkeSnedeker2013

open Numerals

/-! ### The covered-box task -/

/-- A covered-box trial: two visible boxes with contents of type `α`, and a covered box. -/
structure Trial (α : Type*) where
  left : α
  right : α

/-- What the participant hands over. -/
inductive Choice (α : Type*) where
  | visible (x : α)
  | covered
  deriving DecidableEq

variable {α : Type*} (R : α → Prop) [DecidablePred R] (t : Trial α)

/-- The referent of the definite description under a reading `R` of the term: the visible box
satisfying `R` when exactly one does, the covered box when none does, and no box when both do,
since the description presupposes a unique referent. -/
def choice : Option (Choice α) :=
  if R t.left then if R t.right then none else some (.visible t.left)
  else if R t.right then some (.visible t.right) else some .covered

theorem choice_eq_none_iff : choice R t = none ↔ R t.left ∧ R t.right := by
  unfold choice; split_ifs <;> simp_all

/-- The covered box is chosen exactly when no visible box satisfies the description. -/
theorem choice_eq_covered_iff : choice R t = some .covered ↔ ¬ R t.left ∧ ¬ R t.right := by
  unfold choice; split_ifs <;> simp_all

theorem choice_eq_visible_left_iff :
    choice R t = some (.visible t.left) ↔ R t.left ∧ ¬ R t.right := by
  unfold choice
  split_ifs with h₁ h₂ h₂ <;> simp only [h₁, h₂, Option.some.injEq, Choice.visible.injEq,
    reduceCtorEq, not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, iff_false]
  exact λ h => h₁ (h ▸ h₂)

theorem choice_eq_visible_right_iff :
    choice R t = some (.visible t.right) ↔ ¬ R t.left ∧ R t.right := by
  unfold choice
  split_ifs with h₁ h₂ h₂ <;> simp only [h₁, h₂, Option.some.injEq, Choice.visible.injEq,
    reduceCtorEq, not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, iff_false]
  exact λ h => h₂ (h ▸ h₁)

/-- Strengthening the reading can only move the referent to the covered box or resolve a tie:
the design of Section 1.4. -/
theorem choice_covered_of_le {R' : α → Prop} [DecidablePred R'] (h : ∀ x, R' x → R x)
    (hc : choice R t = some .covered) : choice R' t = some .covered := by
  rw [choice_eq_covered_iff] at hc ⊢
  exact ⟨mt (h _) hc.1, mt (h _) hc.2⟩

/-! ### Number trials -/

/-- The critical trials show a smaller and a larger set: an exact numeral has no visible
referent, so the covered box is chosen. -/
theorem choice_bareMeaning_covered {m a b : ℕ} (ha : a < m) (hb : m < b) :
    choice (bareMeaning m) ⟨a, b⟩ = some .covered :=
  (choice_eq_covered_iff _ _).2 ⟨by simp; omega, by simp; omega⟩

/-- A lower-bounded numeral refers to the larger set. -/
theorem choice_atLeastMeaning_visible {m a b : ℕ} (ha : a < m) (hb : m ≤ b) :
    choice (atLeastMeaning m) ⟨a, b⟩ = some (.visible b) :=
  (choice_eq_visible_right_iff _ _).2 ⟨by simp; omega, by simp; omega⟩

/-- The lower-bounded numeral strengthened against the full number scale chooses like the exact
one, so the critical trials separate the two semantics only where the implicature is
cancelled. -/
theorem choice_exhNumeral_covered {m a b : ℕ} (ha : a < m) (hb : m < b) :
    choice (exhNumeral m) ⟨a, b⟩ = some .covered :=
  (choice_eq_covered_iff _ _).2
    ⟨by simp only [exhNumeral_iff_bare, bareMeaning_def]; omega,
      by simp only [exhNumeral_iff_bare, bareMeaning_def]; omega⟩

/-- two(1,2): with an exact match visible against a smaller set, both readings pick it. -/
theorem choice_one_two_bare : choice (bareMeaning 2) ⟨1, 2⟩ = some (.visible 2) := by decide

theorem choice_one_two_atLeast : choice (atLeastMeaning 2) ⟨1, 2⟩ = some (.visible 2) := by
  decide

/-- two(2,3∨5): against a larger set the lower-bounded reading leaves the description without
a unique referent, and it is the implicature that restores the exact match. -/
theorem choice_two_three_bare : choice (bareMeaning 2) ⟨2, 3⟩ = some (.visible 2) := by decide

theorem choice_two_three_atLeast : choice (atLeastMeaning 2) ⟨2, 3⟩ = none := by decide

theorem choice_two_three_exh : choice (exhNumeral 2) ⟨2, 3⟩ = some (.visible 2) := by decide

/-- two(1,3∨5), the critical trials: adults and two-knowers chose the covered box. -/
theorem choice_one_three_bare : choice (bareMeaning 2) ⟨1, 3⟩ = some .covered :=
  choice_bareMeaning_covered (by omega) (by omega)

theorem choice_one_three_atLeast : choice (atLeastMeaning 2) ⟨1, 3⟩ = some (.visible 3) :=
  choice_atLeastMeaning_visible (by omega) (by omega)

theorem choice_one_five_atLeast : choice (atLeastMeaning 2) ⟨1, 5⟩ = some (.visible 5) :=
  choice_atLeastMeaning_visible (by omega) (by omega)

/-! ### Scalar trials -/

open SomeAllWorld

/-- *Some* strengthened by its implicature: some but not all. -/
def someStrengthened (w : SomeAllWorld) : Prop := atLeastOne w ∧ notUniversal w

instance : DecidablePred someStrengthened := λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- some(NONE,SOME): the subset under either reading. -/
theorem some_none_some : choice atLeastOne ⟨.none, .someNotAll⟩ = some (.visible .someNotAll) := by
  decide

/-- some(SOME,ALL): the literal meaning fits both visible boxes and the implicature selects
the subset, which adults chose and children split on. -/
theorem some_some_all_literal : choice atLeastOne ⟨.someNotAll, .all⟩ = Option.none := by decide

theorem some_some_all_strengthened :
    choice someStrengthened ⟨.someNotAll, .all⟩ = some (.visible .someNotAll) := by decide

/-- some(NONE,ALL), the control for implicature cancellation: the literal meaning picks the
total set, which adults and children chose, and the strengthened meaning the covered box. -/
theorem some_none_all_literal : choice atLeastOne ⟨.none, .all⟩ = some (.visible .all) := by
  decide

theorem some_none_all_strengthened : choice someStrengthened ⟨.none, .all⟩ = some .covered := by
  decide

/-- Experiment 3: *all* selects the total set when visible and the covered box otherwise, so
the children's choices tracked the quantifier rather than the character. -/
theorem all_none_all : choice universal ⟨.none, .all⟩ = some (.visible .all) := by decide

theorem all_some_all : choice universal ⟨.someNotAll, .all⟩ = some (.visible .all) := by decide

theorem all_some_none : choice universal ⟨.someNotAll, .none⟩ = some .covered := by decide

/-! ### Two-knowers -/

/-- A child at knower level `k` has the numerals up to `k` as a count list; the numeral `i` of
that list exhaustified against its known stronger alternatives. -/
def exhKnown (k : ℕ) (i : Fin (k + 1)) (n : ℕ) : Prop :=
  Exhaustification.exhChain (λ j : Fin (k + 1) => atLeastMeaning j) i n

instance (k : ℕ) (i : Fin (k + 1)) : DecidablePred (exhKnown k i) := λ _ =>
  inferInstanceAs (Decidable (Exhaustification.exhChain _ _ _))

/-- The top of the count list has no stronger known alternative, so exhaustification leaves its
lower-bounded meaning as it is. -/
theorem exhKnown_last (k n : ℕ) : exhKnown k (Fin.last k) n ↔ atLeastMeaning k n :=
  ⟨λ h => h.1, λ h => ⟨h, λ j hj => absurd hj (not_lt.2 (Fin.le_last j))⟩⟩

/-- A numeral below the top is exhaustified to its exact meaning. -/
theorem exhKnown_of_lt {k : ℕ} {i : Fin (k + 1)} (hi : i < Fin.last k) (n : ℕ) :
    exhKnown k i n ↔ bareMeaning i n := by
  have hs : (i : ℕ) + 1 < k + 1 := by have := Fin.lt_def.1 hi; simp at this; omega
  rw [exhKnown, Exhaustification.exhChain_iff_succ (s := ⟨i + 1, hs⟩)
    (λ j k hjk n hk => by simp only [atLeastMeaning_def] at hk ⊢; exact le_trans hjk hk)
    (Fin.lt_def.2 (Nat.lt_succ_self _))
    (λ j hj => Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hj)))]
  simp only [atLeastMeaning_def, bareMeaning_def]
  omega

/-- A two-knower's count list is *one*, *two*: under lower-bounded semantics, *two* stays
lower-bounded and the child should hand over the visible box with three fish, contrary to the
covered-box choices of Experiments 2 and 4. -/
theorem twoKnower_lowerBounded : choice (exhKnown 2 (Fin.last 2)) ⟨1, 3⟩ = some (.visible 3) := by
  decide

/-- A three-knower could reach the covered box through the implicature. -/
theorem threeKnower_exact : choice (exhKnown 3 2) ⟨1, 3⟩ = some .covered := by decide

/-- Section 6.1: an implicit alternative *more than two* would exhaustify *two* to its exact
meaning, the route the paper leaves logically open. -/
theorem atLeast_not_moreThan_iff_bare (m n : ℕ) :
    atLeastMeaning m n ∧ ¬ moreThanMeaning m n ↔ bareMeaning m n := by
  simp only [atLeastMeaning_def, moreThanMeaning_def, bareMeaning_def]; omega

end HuangSpelkeSnedeker2013
