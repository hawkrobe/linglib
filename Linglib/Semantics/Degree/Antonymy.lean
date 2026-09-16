import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.Aristotelian
import Linglib.Semantics.Degree.Boundedness
import Linglib.Semantics.Degree.Discrete

/-!
# Antonymy

This file defines the vocabulary of an antonym pair of gradable adjectives, *tall* and *short*
or *happy* and *unhappy*. The two members measure on the same degrees under inverse orderings
([kennedy-2007] (60) and fn. 29, [kennedy-mcnally-2005] fn. 7): `Degree.Polarity` is which
member an adjective is, as a sign in `ℤˣ`, `positive` for the unmarked member (*tall*) and
`negative` for the inverted one (*short*). Inverting twice restores the ordering, so
`negative * p` is the polarity of the antonym of a `p` adjective, and the sign acts on scale
boundedness through the order dual. `Degree.AntonymRelation` is the opposition between the
members' positive forms, contradictory (*clean* and *dirty*) or contrary (*tall* and *short*,
which leave a gap), a cell of the Aristotelian square ([cruse-1986], [horn-1989]).

The contrary case is modelled by a `Degree.ThresholdPair` on a finite degree scale, the
positive form true above its upper threshold and the negative form below its lower one, and
`Degree.AntonymForm` is the quadruplet *happy*, *not happy*, *unhappy*, *not unhappy* that
sentential negation generates from a pair, with a contradictory denotation on one threshold,
where *not unhappy* collapses to *happy*, and a strengthened denotation on a pair, where the gap
keeps them apart ([krifka-2007b]).

## Main definitions

* `Polarity`, the sign group `ℤˣ`, with the members `Polarity.positive` and `Polarity.negative`
  and its action `p • b` on `Boundedness`.
* `AntonymRelation`, contradictory or contrary, embedded in `Aristotelian.OppositionRel`.
* `ThresholdPair` and the two-threshold meanings `positiveMeaning'`, `contraryNegMeaning`,
  `notContraryNegMeaning`, `inGapRegion`; `contradictoryNeg` and `contraryNeg`.
* `AntonymForm` with `AntonymForm.contradictoryDenot`, `AntonymForm.strengthenedDenot` and
  `AntonymForm.complexity`.

## Main results

* `contradictoryNeg_iff`, `not_contradictoryNeg_iff`: contradictory negation is the complement
  and double negation eliminates.
* `ThresholdPair.exists_notContraryNegMeaning_not_positiveMeaning'`,
  `ThresholdPair.exists_inGapRegion`: a strict pair leaves a gap.
* `isContradictory_contradictoryDenot`, `isContrary_strengthenedDenot`: the two denotations
  realize the two cells of the Aristotelian square.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [cruse-1986]
* [horn-1989]
* [krifka-2007b]
* [tessler-franke-2019]
-/

namespace Degree

/-! ### Polarity -/

/-- Which member of an antonym pair an adjective is, as a sign: `positive` measures in the
unmarked direction (*tall*, *hot*), `negative` in the inverted one (*short*, *cold*). -/
abbrev Polarity := ℤˣ

namespace Polarity

/-- The member of an antonym pair measuring in the scale's increasing direction (*tall*, *hot*);
markedness is a separate matter, since equipollent pairs like *hot*/*cold* have no unmarked
member. -/
def positive : Polarity := 1

/-- The member of an antonym pair measuring on the dual scale (*short*, *cold*). -/
def negative : Polarity := -1

theorem positive_eq_one : positive = 1 := rfl

theorem negative_eq_neg_one : negative = -1 := rfl

@[simp] theorem negative_ne_positive : negative ≠ positive := by decide

@[simp] theorem positive_ne_negative : positive ≠ negative := by decide

theorem eq_positive_or_eq_negative (p : Polarity) : p = positive ∨ p = negative :=
  Int.units_eq_one_or p

@[simp] theorem positive_mul (p : Polarity) : positive * p = p := one_mul p

@[simp] theorem mul_positive (p : Polarity) : p * positive = p := mul_one p

/-- Two inversions restore the ordering: the antonym of *short* is *tall*, and *less short than*
is *taller than*. Sentential negation is not a polarity: *not short* is the contradictory of
*short* and does not entail *tall* (`contradictoryNeg`). -/
@[simp] theorem negative_mul_negative : negative * negative = positive := by decide

@[simp] theorem mul_self (p : Polarity) : p * p = positive := by
  rcases eq_positive_or_eq_negative p with rfl | rfl <;> decide

@[simp] theorem inv_eq_self (p : Polarity) : p⁻¹ = p := by
  rcases eq_positive_or_eq_negative p with rfl | rfl <;> decide

@[simp] theorem positive_smul {M : Type*} [MulAction Polarity M] (x : M) : positive • x = x :=
  one_smul _ x

end Polarity

/-- The negative member of an antonym pair measures on the dual scale. -/
instance : MulAction Polarity Boundedness where
  smul p b := if p = .positive then b else b.dual
  one_smul _ := rfl
  mul_smul p q b := by
    rcases Polarity.eq_positive_or_eq_negative p with rfl | rfl <;>
      rcases Polarity.eq_positive_or_eq_negative q with rfl | rfl <;> simp [HSMul.hSMul, SMul.smul]

@[simp] theorem Boundedness.negative_smul (b : Boundedness) : Polarity.negative • b = b.dual :=
  rfl

/-! ### The relation between the members -/

/-- The opposition between the positive forms of an antonym pair: contradictories (*clean* and
*dirty*) cannot both be false, contraries (*tall* and *short*) can, leaving a gap between the
two standards. An antonym pair is never subcontrary or unconnected, so the type has two
members, embedded in `Aristotelian.OppositionRel` by `toOpposition`. -/
inductive AntonymRelation where
  | contradictory
  | contrary
  deriving Repr, DecidableEq, Fintype

/-- The cell of the Aristotelian square an antonym pair occupies. -/
def AntonymRelation.toOpposition : AntonymRelation → Aristotelian.OppositionRel
  | .contradictory => .contradictory
  | .contrary      => .contrary

instance : Coe AntonymRelation Aristotelian.OppositionRel := ⟨AntonymRelation.toOpposition⟩

theorem AntonymRelation.toOpposition_injective :
    Function.Injective AntonymRelation.toOpposition := by
  intro a b h; cases a <;> cases b <;> simp_all [AntonymRelation.toOpposition]

/-- The image of `toOpposition` is exactly the two antonym cells of `OppositionRel`. -/
theorem AntonymRelation.range_toOpposition (r : Aristotelian.OppositionRel) :
    (∃ n : AntonymRelation, n.toOpposition = r) ↔ r = .contradictory ∨ r = .contrary := by
  constructor
  · rintro ⟨n, rfl⟩; cases n <;> simp [AntonymRelation.toOpposition]
  · rintro (rfl | rfl)
    exacts [⟨.contradictory, rfl⟩, ⟨.contrary, rfl⟩]

/-! ### The two-threshold model of a contrary pair -/

/-- The two thresholds of a contrary antonym pair (*happy* and *unhappy*): `pos` for the
positive form, true above it, and `neg` for the negative form, true below it. When `neg < pos`
the gap `[neg, pos]` is the region that is neither; that strict inequality is a hypothesis where
a gap is needed, not a stored invariant. -/
structure ThresholdPair (max : Nat) where
  pos : Threshold max
  neg : Threshold max
  deriving Repr, DecidableEq, BEq

section TwoThreshold
variable {max : Nat} (d : Bounded max)

/-- Contradictory negation *not happy*, `d ≤ θ` (`notPositiveMeaning`). -/
abbrev contradictoryNeg (θ : Threshold max) : Prop := notPositiveMeaning d θ

/-- Contrary negation *unhappy*, `d < θ_neg` (`negativeMeaning`). -/
abbrev contraryNeg (θ_neg : Threshold max) : Prop := negativeMeaning d θ_neg

/-- The gap: `d` is neither positive nor negative, `neg ≤ d ≤ pos`. -/
abbrev inGapRegion (tp : ThresholdPair max) : Prop :=
  (tp.neg : Bounded max) ≤ d ∧ d ≤ (tp.pos : Bounded max)

/-- The positive form *happy* at the pair's upper threshold, `d > pos`. -/
abbrev positiveMeaning' (tp : ThresholdPair max) : Prop := positiveMeaning d tp.pos

/-- The negative form *unhappy* at the pair's lower threshold, `d < neg`. -/
abbrev contraryNegMeaning (tp : ThresholdPair max) : Prop := negativeMeaning d tp.neg

/-- *not unhappy*, the complement of the negative form, `neg ≤ d`. -/
abbrev notContraryNegMeaning (tp : ThresholdPair max) : Prop := (tp.neg : Bounded max) ≤ d

/-- Contradictory negation is the complement of the positive form. -/
@[simp] theorem contradictoryNeg_iff (θ : Threshold max) :
    contradictoryNeg d θ ↔ ¬ positiveMeaning d θ := by
  simp only [contradictoryNeg, notPositiveMeaning, positiveMeaning, Comparison.mem_over,
    Comparison.rel, id_eq, not_lt]

/-- Double contradictory negation eliminates: *not [not happy]* is *happy*. Under a
contradictory reading of the pair *not unhappy* is therefore synonymous with *happy*, the
puzzle [krifka-2007b] solves pragmatically. -/
theorem not_contradictoryNeg_iff (θ : Threshold max) :
    ¬ contradictoryNeg d θ ↔ positiveMeaning d θ := by
  rw [contradictoryNeg_iff, not_not]

/-- A contradictory pair exhausts the scale: every degree is positive or negated. -/
theorem positiveMeaning_or_contradictoryNeg (θ : Threshold max) :
    positiveMeaning d θ ∨ contradictoryNeg d θ :=
  (em _).imp_right (contradictoryNeg_iff d θ).2

/-- The gap is exactly *not unhappy* and *not happy*. -/
@[simp] theorem inGapRegion_iff (tp : ThresholdPair max) :
    inGapRegion d tp ↔ notContraryNegMeaning d tp ∧ ¬ positiveMeaning' d tp := by
  simp only [inGapRegion, notContraryNegMeaning, positiveMeaning', positiveMeaning,
    Comparison.mem_over, Comparison.rel, id_eq, not_lt]

end TwoThreshold

namespace ThresholdPair
variable {max : Nat} (tp : ThresholdPair max)

/-- A strict pair has a degree, its lower threshold, that is *not unhappy* but not *happy*:
double negation through a contrary fails. -/
theorem exists_notContraryNegMeaning_not_positiveMeaning'
    (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    ∃ d : Bounded max, notContraryNegMeaning d tp ∧ ¬ positiveMeaning' d tp := by
  refine ⟨↑tp.neg, le_refl _, ?_⟩
  simp only [positiveMeaning', positiveMeaning, Comparison.mem_over, Comparison.rel, id_eq,
    not_lt]
  exact le_of_lt h

/-- A strict pair leaves a gap. -/
theorem exists_inGapRegion (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    ∃ d : Bounded max, inGapRegion d tp := by
  obtain ⟨d, h1, h2⟩ := tp.exists_notContraryNegMeaning_not_positiveMeaning' h
  exact ⟨d, (inGapRegion_iff d tp).mpr ⟨h1, h2⟩⟩

end ThresholdPair

/-! ### The quadruplet -/

/-- The four surface forms sentential negation generates from an antonym pair: *happy*,
*not happy*, *unhappy*, *not unhappy* ([horn-1989], [krifka-2007b]). The type carries no
semantics; a contradictory account collapses the four to two denotations and a contrary
account keeps four, and each is a function on it. -/
inductive AntonymForm where
  | positive       -- *happy*
  | notPositive    -- *not happy*
  | negative       -- *unhappy*
  | notNegative    -- *not unhappy*
  deriving Repr, DecidableEq, Fintype

namespace AntonymForm

/-- Exchange the two poles of the quadruplet: *happy* with *unhappy* and *not happy* with
*not unhappy*. -/
def flip : AntonymForm → AntonymForm
  | .positive    => .negative
  | .negative    => .positive
  | .notPositive => .notNegative
  | .notNegative => .notPositive

theorem flip_involutive : Function.Involutive flip := λ f => by cases f <;> rfl

@[simp] theorem flip_flip (f : AntonymForm) : f.flip.flip = f := flip_involutive f

/-- The sign acts on the quadruplet by exchanging its poles. -/
instance : MulAction Polarity AntonymForm where
  smul p f := if p = .positive then f else f.flip
  one_smul _ := rfl
  mul_smul p q f := by
    rcases Polarity.eq_positive_or_eq_negative p with rfl | rfl <;>
      rcases Polarity.eq_positive_or_eq_negative q with rfl | rfl <;> simp [HSMul.hSMul, SMul.smul]

@[simp] theorem negative_smul (f : AntonymForm) : Polarity.negative • f = f.flip := rfl

/-- The morphosyntactic complexity of a form, the number of negations counted as
[krifka-2007b] orders them, `0 < 2 < 3 < 5`, matching [tessler-franke-2019]'s utterance cost. -/
def complexity : AntonymForm → Nat
  | .positive    => 0
  | .negative    => 2
  | .notPositive => 3
  | .notNegative => 5

theorem complexity_strictMono :
    complexity .positive < complexity .negative ∧
    complexity .negative < complexity .notPositive ∧
    complexity .notPositive < complexity .notNegative := by
  decide

/-- The contradictory denotation of a form on a single threshold `θ`: both poles share `θ`, so
the four forms collapse to two, *happy* and *not unhappy* above it, *not happy* and *unhappy*
at or below it. This is the literal semantics [krifka-2007b] attributes to a pair before
pragmatic strengthening. -/
abbrev contradictoryDenot {max : Nat} (θ : Threshold max) (q : AntonymForm) (d : Bounded max) :
    Prop :=
  match q with
  | .positive    => positiveMeaning d θ
  | .notPositive => ¬ positiveMeaning d θ
  | .negative    => ¬ positiveMeaning d θ
  | .notNegative => positiveMeaning d θ

/-- The strengthened denotation of a form on a threshold pair: the gap `[neg, pos]` lifts *not
unhappy* away from *happy* and *not happy* away from *unhappy*, the effective semantics after
strengthening ([krifka-2007b]) or the lexical one ([alexandropoulou-gotzner-2024a]). -/
abbrev strengthenedDenot {max : Nat} (tp : ThresholdPair max) (q : AntonymForm)
    (d : Bounded max) : Prop :=
  match q with
  | .positive    => positiveMeaning' d tp
  | .notPositive => contradictoryNeg d tp.pos
  | .negative    => contraryNegMeaning d tp
  | .notNegative => notContraryNegMeaning d tp

/-- Under the contradictory denotation *unhappy* is *not happy* and *not unhappy* is *happy*. -/
theorem contradictoryDenot_synonymy {max : Nat} (θ : Threshold max) (d : Bounded max) :
    (contradictoryDenot θ .negative d ↔ contradictoryDenot θ .notPositive d) ∧
    (contradictoryDenot θ .notNegative d ↔ contradictoryDenot θ .positive d) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Under the strengthened denotation of a strict pair, *not unhappy* and *happy* come apart at
the lower threshold. -/
theorem strengthenedDenot_breaks_synonymy {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    ∃ d : Bounded max, strengthenedDenot tp .notNegative d ∧ ¬ strengthenedDenot tp .positive d :=
  tp.exists_notContraryNegMeaning_not_positiveMeaning' h

open Aristotelian in
/-- With one threshold the negative form is the complement of the positive form, so the pair is
contradictory in the Boolean algebra `Bounded max → Prop`. -/
theorem isContradictory_contradictoryDenot {max : Nat} (θ : Threshold max) :
    IsContradictory (λ d : Bounded max => contradictoryDenot θ .positive d)
      (λ d => contradictoryDenot θ .negative d) :=
  isCompl_compl

open Aristotelian in
/-- With a strict pair the positive and negative forms are disjoint but, by the gap, not
exhaustive, so the pair is contrary. -/
theorem isContrary_strengthenedDenot {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    IsContrary (λ d : Bounded max => strengthenedDenot tp .positive d)
      (λ d => strengthenedDenot tp .negative d) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    funext d
    simp only [strengthenedDenot, positiveMeaning', contraryNegMeaning, positiveMeaning,
      negativeMeaning, Pi.inf_apply, Pi.bot_apply, inf_Prop_eq]
    exact eq_false (λ ⟨h1, h2⟩ => absurd (h1.trans h2) (lt_asymm h))
  · rw [codisjoint_iff]
    obtain ⟨d, hd1, hd2⟩ := tp.exists_notContraryNegMeaning_not_positiveMeaning' h
    intro hco
    have hd := congrFun hco d
    simp only [strengthenedDenot, positiveMeaning', contraryNegMeaning, notContraryNegMeaning,
      positiveMeaning, negativeMeaning, Pi.sup_apply, Pi.top_apply, sup_Prop_eq] at hd hd1 hd2
    rcases of_eq_true hd with hp | hn
    · exact hd2 hp
    · exact absurd hn (not_lt.mpr hd1)

end AntonymForm

end Degree
