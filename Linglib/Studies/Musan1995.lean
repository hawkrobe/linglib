import Mathlib.Order.Nat

/-!
# Musan (1995): On the Temporal Interpretation of Noun Phrases

This file formalizes the pragmatic account of life-time effects in the second chapter of
[musan-1995]. Out of the blue, *Gregory was from America* suggests that Gregory is dead
while *Gregory was silent* does not. Tenses quantify existentially over times, every
predicate carries a life-time presupposition that its argument exists at the predication
time (`holdsAt`), and an individual-level predicate holds of an individual at every time of
its life if at any (`IndividualLevel`). The present-tense sentence is then more informative
than the past-tense one, entailing it without being entailed by it (`present_entails_past`,
`past_not_entails_present`), so a speaker choosing the past tense implicates that the
property is over, and for an individual-level predicate that is to implicate that the
individual no longer exists (`lifetime_effect`); a stage-level predicate supports the first
implicature but not the second (`no_lifetime_effect_of_stage_level`).

## Implementation notes

Times are the points of a linear order and the present tense is evaluation at the utterance
time, where the dissertation quantifies over intervals surrounding it. The neutralization of
life-time effects in temporally specific contexts, the existence-independent predicates, and
the third chapter's account of the predication times of noun phrases are not represented.

## References

* [musan-1995]
-/

namespace Musan1995

variable {T : Type*} [LinearOrder T]

/-- A predicate with its life-time presupposition: it holds at a time only of an individual
alive at that time. -/
def holdsAt (alive P : T → Prop) (t : T) : Prop := alive t ∧ P t

/-- The past tense: the proposition held at some earlier time. -/
def past (φ : T → Prop) (t : T) : Prop := ∃ t' < t, φ t'

/-- An individual-level predicate holds throughout the individual's life if it holds at all. -/
def IndividualLevel (alive P : T → Prop) : Prop :=
  (∃ t, holdsAt alive P t) → ∀ t, alive t → P t

variable {alive P : T → Prop} {now : T}

/-- For an individual-level predicate of an individual alive before now, the present-tense
sentence entails the past-tense one. -/
theorem present_entails_past (hP : IndividualLevel alive P) (hborn : ∃ t < now, alive t)
    (h : holdsAt alive P now) : past (holdsAt alive P) now :=
  let ⟨t, ht, hat⟩ := hborn
  ⟨t, ht, hat, hP ⟨now, h⟩ t hat⟩

/-- The past-tense sentence does not entail the present-tense one: the individual may have
died. -/
theorem past_not_entails_present :
    ∃ alive P : ℕ → Prop,
      IndividualLevel alive P ∧ past (holdsAt alive P) 1 ∧ ¬ holdsAt alive P 1 :=
  ⟨(· = 0), λ _ => True, λ _ _ _ => trivial, ⟨0, Nat.zero_lt_one, rfl, trivial⟩,
    λ h => Nat.one_ne_zero h.1⟩

/-- The life-time effect: the past-tense sentence together with the implicature that the
property is over yields, for an individual-level predicate, that the individual no longer
exists. -/
theorem lifetime_effect (hP : IndividualLevel alive P) (h : past (holdsAt alive P) now)
    (hover : ¬ P now) : ¬ alive now :=
  λ hnow => hover (hP (let ⟨t, _, ht⟩ := h; ⟨t, ht⟩) now hnow)

/-- Without the individual-level property the same implicature leaves existence open: an
individual who was silent and is silent no longer is still alive. -/
theorem no_lifetime_effect_of_stage_level :
    ∃ alive P : ℕ → Prop, past (holdsAt alive P) 1 ∧ ¬ P 1 ∧ alive 1 :=
  ⟨λ _ => True, (· = 0), ⟨0, Nat.zero_lt_one, trivial, rfl⟩, Nat.one_ne_zero, trivial⟩

end Musan1995
