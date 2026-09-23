module

public import Linglib.Fragments.English.PolarityItems
public import Mathlib.Order.Monotone.Basic

/-!
# Israel (2001): Minimizers, Maximizers and the Rhetoric of Scalar Reasoning

This file formalizes the Scalar Model of polarity sensitivity of [israel-2001]. A scalar model,
after [fillmore-kay-oconnor-1988], is a propositional function over an ordered scale whose
values pragmatically entail one another;
a polarity item encodes a quantity relative to the scalar norm and a rhetorical force, emphatic
when the proposition it expresses entails the norm's and attenuating when it is entailed by it
(`Emphatic`, `Attenuating`). Scale preserving contexts are the strictly monotone maps on
propositions and scale reversing ones the strictly antitone maps, the positive and negative
directions of `Polarity.StrictMonoBy`, and the direction of the expressed propositional
function decides which quantities are emphatic (`felicitous_iff_of_strictMonoBy`). The four cells of Figure 1 follow: emphatic items with low values and attenuating
items with high values need reversing contexts, the negative polarity items, the other two cells
preserving contexts. The inverted items of Section 3, maximizing NPIs like *wild horses* and
minimizing PPIs like *for peanuts*, follow from the thematic logic of Section 4: a propositional
role either impedes the eventuality, so that the function is antitone in quantity, or
facilitates it, so that it is monotone (`Role`). Directions compose as polarities multiply, so
that the licensing context of any item is the product of the signs of its force, quantity and
role (`licensingContext`, `felicitous_iff`). The pecuniary paradox
dissolves because a resource is impeding and a reward facilitating, and the ambiguous
superlatives of Section 6 are the same composition with an existential and a
perceptual-ability scale.

## Implementation notes

* Pragmatic entailment between the propositions of a scalar model is modelled as inclusion of
  sets of worlds; the paper's point that the relevant inferences may be pragmatic rather than
  logical is not represented.
* The paper's classifications of the English items of `Fragments/English/PolarityItems.lean`
  by quantity and role live here (`classified`); the force comes from the fragment's scalar
  direction, and the derived licensing context is checked against the fragment's record of
  each item as an NPI or PPI.

## References

* [israel-2001]
* [israel-1996]
* [fillmore-kay-oconnor-1988]
* [fauconnier-1975]
* [ladusaw-1979]
-/

@[expose] public section

namespace Israel2001

open Polarity English.PolarityItems

variable {α W : Type*} [LinearOrder α]

/-- Rhetorical force: the expressed proposition is more informative than the scalar norm, or
less. -/
inductive Force
  | emphatic
  | attenuating
  deriving DecidableEq

/-- The sign of a force: emphatic items are negative, attenuating ones positive. -/
def Force.sign : Force → Polarity
  | .emphatic => .negative
  | .attenuating => .positive

/-- The force of a fragment entry, from its scalar direction. -/
def Force.ofDirection : ScalarDirection → Option Force
  | .strengthening => some .emphatic
  | .attenuating => some .attenuating
  | .nonScalar => none

/-- Quantity relative to the norm: the size, amount or degree the item denotes. -/
inductive Quantity
  | small
  | large
  deriving DecidableEq

/-- The sign of a quantity relative to the norm: small is negative, large positive. -/
def Quantity.sign : Quantity → Polarity
  | .small => .negative
  | .large => .positive

/-- A quantity `x` stands to the norm `n` as the item's quantity says. -/
def Quantity.Rel : Quantity → α → α → Prop
  | .small, x, n => x < n
  | .large, x, n => n < x

/-- The effect of a propositional role on the likelihood of the eventuality (Section 4): a
patient, theme, increment, expense or duration impedes it, the bigger the less likely, and an
agent, stimulus, reward, instrument or interval facilitates it. -/
inductive Role
  | impeding
  | facilitating
  deriving DecidableEq

/-- The direction of the propositional function of a role: strictly antitone in quantity for an
impeding role, so that bigger values entail smaller ones, strictly monotone for a facilitating
one. -/
def Role.sign : Role → Polarity
  | .impeding => .negative
  | .facilitating => .positive

/-- The proposition expressed with quantity `x` is emphatic when it pragmatically entails the
proposition at the norm. -/
def Emphatic (Q : α → Set W) (n x : α) : Prop := Q x < Q n

/-- It is attenuating when the proposition at the norm entails it. -/
def Attenuating (Q : α → Set W) (n x : α) : Prop := Q n < Q x

/-- An item of a given force is felicitous when the proposition expressed has that force. -/
def Felicitous : Force → (α → Set W) → α → α → Prop
  | .emphatic, Q, n, x => Emphatic Q n x
  | .attenuating, Q, n, x => Attenuating Q n x

variable {Q : α → Set W} {n x : α}

/-- When the expressed function is strictly monotone, inferences run from low values to high
ones and the emphatic propositions are the ones below the norm. -/
theorem emphatic_iff_of_strictMono (h : StrictMono Q) (hx : x ≠ n) : Emphatic Q n x ↔ x < n :=
  ⟨λ hE => (lt_or_gt_of_ne hx).resolve_right λ hn => lt_asymm (h hn) hE, λ hxn => h hxn⟩

/-- When it is strictly antitone, inferences run from high values to low ones and the emphatic
propositions are the ones above the norm. -/
theorem emphatic_iff_of_strictAnti (h : StrictAnti Q) (hx : x ≠ n) : Emphatic Q n x ↔ n < x :=
  ⟨λ hE => (lt_or_gt_of_ne hx).resolve_left λ hn => lt_asymm (h hn) hE, λ hxn => h hxn⟩

theorem attenuating_iff_of_strictMono (h : StrictMono Q) (hx : x ≠ n) :
    Attenuating Q n x ↔ n < x :=
  ⟨λ hA => (lt_or_gt_of_ne hx).resolve_left λ hn => lt_asymm (h hn) hA, λ hxn => h hxn⟩

theorem attenuating_iff_of_strictAnti (h : StrictAnti Q) (hx : x ≠ n) :
    Attenuating Q n x ↔ x < n :=
  ⟨λ hA => (lt_or_gt_of_ne hx).resolve_right λ hn => lt_asymm (h hn) hA, λ hxn => h hxn⟩

/-- Under a strictly monotone expressed function an emphatic item needs a low value and an
attenuating one a high value. -/
theorem felicitous_iff_of_strictMono (h : StrictMono Q) (hx : x ≠ n) (d : Force) :
    Felicitous d Q n x ↔ (d = .emphatic ↔ x < n) := by
  cases d
  · simp [Felicitous, emphatic_iff_of_strictMono h hx]
  · rw [Felicitous, attenuating_iff_of_strictMono h hx]
    simp only [reduceCtorEq, false_iff, not_lt]
    exact ⟨le_of_lt, λ h => lt_of_le_of_ne h hx.symm⟩

/-- Under a strictly antitone one the values are reversed. -/
theorem felicitous_iff_of_strictAnti (h : StrictAnti Q) (hx : x ≠ n) (d : Force) :
    Felicitous d Q n x ↔ (d = .emphatic ↔ n < x) := by
  cases d
  · simp [Felicitous, emphatic_iff_of_strictAnti h hx]
  · rw [Felicitous, attenuating_iff_of_strictAnti h hx]
    simp only [reduceCtorEq, false_iff, not_lt]
    exact ⟨le_of_lt, λ h => lt_of_le_of_ne h hx⟩

/-- The direction of the context in which an item of a given force, quantity and role is
felicitous, scale preserving (positive) or scale reversing (negative), the scalar logic of
Sections 1 and 4: the product of the three signs. Emphatic small items in impeding roles and
emphatic large items in facilitating roles are NPIs, needing scale reversal, as are attenuating
items of the opposite quantities; the remaining cells are PPIs. -/
def licensingContext (d : Force) (q : Quantity) (r : Role) : Polarity := d.sign * q.sign * r.sign

/-- A quantity standing to the norm as the item says is below it exactly for a small item. -/
theorem Quantity.lt_iff_of_rel {q : Quantity} (hq : q.Rel x n) : x < n ↔ q = .small := by
  cases q
  · exact iff_of_true hq rfl
  · exact iff_of_false (lt_asymm hq) (by decide)

/-- And above it exactly for a large item. -/
theorem Quantity.gt_iff_of_rel {q : Quantity} (hq : q.Rel x n) : n < x ↔ q = .large := by
  cases q
  · exact iff_of_false (lt_asymm hq) (by decide)
  · exact iff_of_true hq rfl

/-- An item is felicitous exactly when its force has the sign of the direction of the expressed
function times that of its quantity. -/
theorem felicitous_iff_of_strictMonoBy {δ : Polarity} {q : Quantity} (h : δ.StrictMonoBy Q)
    (hq : q.Rel x n) (d : Force) : Felicitous d Q n x ↔ d.sign = δ * q.sign := by
  have hx : x ≠ n := by
    cases q
    · exact ne_of_lt (hq : x < n)
    · exact (ne_of_lt (hq : n < x)).symm
  cases δ
  · rw [felicitous_iff_of_strictMono h hx, Quantity.lt_iff_of_rel hq]
    cases d <;> cases q <;> decide
  · rw [felicitous_iff_of_strictAnti h hx, Quantity.gt_iff_of_rel hq]
    cases d <;> cases q <;> decide

/-- Figures 1 and 3: an item is felicitous exactly in contexts of its licensing direction, for
any scalar model of its role and any quantity standing to the norm as the item says. -/
theorem felicitous_iff {P : α → Set W} {f : Set W → Set W} {r : Role} {c : Polarity}
    {d : Force} {q : Quantity} (hr : r.sign.StrictMonoBy P) (hc : c.StrictMonoBy f)
    (hq : q.Rel x n) : Felicitous d (f ∘ P) n x ↔ c = licensingContext d q r := by
  rw [felicitous_iff_of_strictMonoBy (hc.comp hr) hq, licensingContext]
  cases c <;> cases d <;> cases q <;> cases r <;> decide

/-- The pecuniary paradox, (15) and (16): the same small amount is emphatic under negation as a
resource, *a red cent*, and not as a reward, *for peanuts*, which is emphatic in the affirmative
instead. -/
theorem pecuniary_paradox {res rew : α → Set W} {f : Set W → Set W} (hres : StrictAnti res)
    (hrew : StrictMono rew) (hf : StrictAnti f) (hx : x < n) :
    Emphatic (f ∘ res) n x ∧ ¬ Emphatic (f ∘ rew) n x ∧ Emphatic rew n x ∧ ¬ Emphatic res n x :=
  ⟨(emphatic_iff_of_strictMono (hf.comp hres) (ne_of_lt hx)).2 hx,
    λ h => lt_asymm hx ((emphatic_iff_of_strictAnti (hf.comp_strictMono hrew) (ne_of_lt hx)).1 h),
    (emphatic_iff_of_strictMono hrew (ne_of_lt hx)).2 hx,
    λ h => lt_asymm hx ((emphatic_iff_of_strictAnti hres (ne_of_lt hx)).1 h)⟩

/-- Ambiguous superlatives, (22): under negation the same frame is emphatic at the bottom of an
existential scale, *the faintest noise*, and at the top of a perceptual-ability scale, *the
loudest noise*, the stimulus impeding its own existence and facilitating its perception. -/
theorem superlative_ambiguity {exist ability : α → Set W} {f : Set W → Set W}
    (hex : StrictAnti exist) (hab : StrictMono ability) (hf : StrictAnti f) {lo hi : α}
    (hlo : lo < n) (hhi : n < hi) : Emphatic (f ∘ exist) n lo ∧ Emphatic (f ∘ ability) n hi :=
  ⟨(emphatic_iff_of_strictMono (hf.comp hex) (ne_of_lt hlo)).2 hlo,
    (emphatic_iff_of_strictAnti (hf.comp_strictMono hab) (ne_of_lt hhi).symm).2 hhi⟩

/-! ### The classified lexicon -/

/-- A fragment entry with the paper's classification by quantity and role. -/
structure Classified where
  item : Item
  quantity : Quantity
  role : Role

/-- The paper's classifications of the fragment's items: the canonical minimizers of Section 4
and the degree items of Figure 1 in impeding roles, the maximizing NPIs and minimizing PPIs of
Section 3 in facilitating roles. -/
def classified : List Classified :=
  [⟨atAll, .small, .impeding⟩, ⟨liftAFinger, .small, .impeding⟩,
   ⟨budgeAnInch, .small, .impeding⟩, ⟨somewhat, .small, .impeding⟩,
   ⟨rather, .small, .impeding⟩, ⟨tonsOf, .large, .impeding⟩, ⟨utterly, .large, .impeding⟩,
   ⟨wildHorses, .large, .facilitating⟩, ⟨allTheTeaInChina, .large, .facilitating⟩,
   ⟨aTenFootPole, .large, .facilitating⟩, ⟨inAMillionYears, .large, .facilitating⟩,
   ⟨atTheDropOfAHat, .small, .facilitating⟩, ⟨inAJiffy, .small, .facilitating⟩,
   ⟨forAPittance, .small, .facilitating⟩, ⟨forASong, .small, .facilitating⟩]

/-- The direction of the context the fragment records an item as sensitive to: preserving for a
PPI, reversing for an NPI. -/
def Item.contextType (e : Item) : Option Polarity :=
  if e.ppi then some .positive else if e.licensor.isSome then some .negative else none

/-- Every classified item's derived licensing context is the one the fragment records. -/
theorem classified_licensingContext :
    ∀ c ∈ classified, ∀ d, c.item.scalarDirection.bind Force.ofDirection = some d →
      Item.contextType c.item = some (licensingContext d c.quantity c.role) := by
  decide

end Israel2001
