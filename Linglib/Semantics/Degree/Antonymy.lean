module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.Aristotelian
public import Linglib.Semantics.Degree.Boundedness
public import Mathlib.Order.Interval.Set.Disjoint

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

The contrary case is modelled by a `Degree.ThresholdPair` on a linearly ordered scale, the
positive form true above its upper threshold and the negative form below its lower one, and
`Degree.AntonymForm` is the quadruplet *happy*, *not happy*, *unhappy*, *not unhappy* that
sentential negation generates from a pair, with a contradictory denotation on one threshold,
where *not unhappy* collapses to *happy*, and a strengthened denotation on a pair, where the gap
keeps them apart ([krifka-2007b]).

## Main definitions

* `Polarity`, the sign group `ℤˣ`, with the members `Polarity.positive` and `Polarity.negative`
  and its action `p • b` on `Boundedness`.
* `AntonymRelation`, contradictory or contrary, embedded in `Aristotelian.OppositionRel`.
* `ThresholdPair` and its `ThresholdPair.gap`, the interval between the two thresholds.
* `AntonymForm` with `AntonymForm.contradictoryDenot`, `AntonymForm.strengthenedDenot` and
  `AntonymForm.complexity`.

## Main results

* `AntonymForm.contradictoryDenot_notPositive`: contradictory negation is the complement, so
  double negation eliminates.
* `ThresholdPair.gap_nonempty_iff`, `AntonymForm.strengthenedDenot_notNegative_diff_positive`,
  `AntonymForm.strengthenedDenot_notPositive_diff_negative`: a pair leaves a gap when its lower
  threshold does not exceed its upper one, and the gap is what each negated form adds to the
  opposite simple form.
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

@[expose] public section

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
*short* and does not entail *tall* (`AntonymForm.strengthenedDenot`). -/
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

/-- The two thresholds of a contrary antonym pair (*happy* and *unhappy*) are `pos` for the
positive form, true above it, and `neg` for the negative form, true below it. That the lower
threshold does not exceed the upper is a hypothesis where a gap is needed, not a stored
invariant. -/
structure ThresholdPair (D : Type*) where
  pos : D
  neg : D
  deriving Repr, DecidableEq

namespace ThresholdPair
variable {D : Type*} [Preorder D] (tp : ThresholdPair D)

/-- The gap of a pair is the region that is neither positive nor negative, from the lower
threshold to the upper. -/
def gap : Set D := Set.Icc tp.neg tp.pos

theorem mem_gap {d : D} : d ∈ tp.gap ↔ tp.neg ≤ d ∧ d ≤ tp.pos := Iff.rfl

/-- A pair leaves a gap exactly when its lower threshold does not exceed its upper one. -/
theorem gap_nonempty_iff : tp.gap.Nonempty ↔ tp.neg ≤ tp.pos := Set.nonempty_Icc

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

theorem flip_involutive : Function.Involutive flip := fun f ↦ by cases f <;> rfl

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

section Denotation
variable {D : Type*}

/-- The contradictory denotation of a form on a single threshold `θ`, which both poles share, so
that the four forms collapse to two, *happy* and *not unhappy* above it, *not happy* and
*unhappy* at or below it. This is the literal semantics [krifka-2007b] attributes to a pair
before pragmatic strengthening. -/
def contradictoryDenot [Preorder D] (θ : D) : AntonymForm → Set D
  | .positive | .notNegative => Set.Ioi θ
  | .notPositive | .negative => Set.Iic θ

/-- The strengthened denotation of a form on a threshold pair, whose gap lifts *not unhappy*
away from *happy* and *not happy* away from *unhappy*. This is the effective semantics after
strengthening ([krifka-2007b]) or the lexical one ([alexandropoulou-gotzner-2024a]). -/
def strengthenedDenot [Preorder D] (tp : ThresholdPair D) : AntonymForm → Set D
  | .positive => Set.Ioi tp.pos
  | .notPositive => Set.Iic tp.pos
  | .negative => Set.Iio tp.neg
  | .notNegative => Set.Ici tp.neg

variable [LinearOrder D] (θ : D) (tp : ThresholdPair D)

/-- Under the contradictory denotation *unhappy* is *not happy* and *not unhappy* is *happy*. -/
theorem contradictoryDenot_synonymy :
    contradictoryDenot θ .negative = contradictoryDenot θ .notPositive ∧
      contradictoryDenot θ .notNegative = contradictoryDenot θ .positive :=
  ⟨rfl, rfl⟩

/-- Contradictory negation is the complement of the positive form, so double negation
eliminates: *not unhappy* is *happy*, the puzzle [krifka-2007b] solves pragmatically. -/
theorem contradictoryDenot_notPositive :
    contradictoryDenot θ .notPositive = (contradictoryDenot θ .positive)ᶜ :=
  Set.compl_Ioi.symm

/-- What *not unhappy* adds to *happy* under the strengthened denotation is the gap. -/
theorem strengthenedDenot_notNegative_diff_positive :
    strengthenedDenot tp .notNegative \ strengthenedDenot tp .positive = tp.gap := by
  rw [strengthenedDenot, strengthenedDenot, Set.sdiff_eq, Set.compl_Ioi, Set.Ici_inter_Iic,
    ThresholdPair.gap]

/-- What *not happy* adds to *unhappy* under the strengthened denotation is the gap too. -/
theorem strengthenedDenot_notPositive_diff_negative :
    strengthenedDenot tp .notPositive \ strengthenedDenot tp .negative = tp.gap := by
  rw [strengthenedDenot, strengthenedDenot, Set.sdiff_eq, Set.compl_Iio, Set.inter_comm,
    Set.Ici_inter_Iic, ThresholdPair.gap]

open Aristotelian in
/-- With one threshold the negative form is the complement of the positive form, so the pair is
contradictory. -/
theorem isContradictory_contradictoryDenot :
    IsContradictory (contradictoryDenot θ .positive) (contradictoryDenot θ .negative) :=
  contradictoryDenot_notPositive θ ▸ isCompl_compl

open Aristotelian in
/-- With a pair that leaves a gap the positive and negative forms are disjoint but not
exhaustive, so the pair is contrary. -/
theorem isContrary_strengthenedDenot (h : tp.neg ≤ tp.pos) :
    IsContrary (strengthenedDenot tp .positive) (strengthenedDenot tp .negative) :=
  ⟨Set.Ioi_disjoint_Iio_of_le h, fun hco ↦ by
    have hmem : tp.neg ∈ strengthenedDenot tp .positive ⊔ strengthenedDenot tp .negative := by
      rw [hco.eq_top]; trivial
    exact hmem.elim (fun hp ↦ h.not_gt hp) (lt_irrefl _)⟩

end Denotation

end AntonymForm

end Degree
