import Mathlib.Data.Set.Insert

/-!
# Klinedinst and Rothschild (2012): Connectives without Truth Tables

This file formalizes [klinedinst-rothschild-2012]'s parameter treatment of the dynamic effects
of *and* and *or*. Truth is relative to a world and to an information parameter, the set of
worlds that epistemic modals quantify over, (46) and (47), and the connectives shift that
parameter for their second clause: *a and b* evaluates *b* against the parameter updated with
*a*, (49), and *a or b* against the parameter updated with the negation of *a*, (50)
(`Sentence.conj`, `Sentence.disj`). This is what lets an epistemic modal sit in a disjunct:
*the dog is in the backyard or it must be in the kitchen*, (36), says that the dog is in the
backyard or that the information, given that it is not, puts it in the kitchen
(`disj_must_iff`), disjunctive syllogism fails for it, (38)–(40)
(`not_disjunctive_syllogism`), and so does commutation, (104) (`disj_not_comm`). The
non-truth-tabular uses of §1 are the assertion forms of (60) that keep only the dynamic effect:
*and* with its first clause shifting the parameter alone is the conditional of (52), (61) and
(62), and *or* with both clauses entailed asserts its first disjunct and the second under the
negation of the first, (66) and (67) (`Use.interpret`); the other two forms collapse into the
normal connectives (`doubleEntailment_and`, `shift_disj`). A normal conjunction whose second
conjunct needs worlds where the first fails is a contradiction, (68) (`not_conj_might_neg`).

## Implementation notes

* The context parameter and the presuppositional definedness of (48) are omitted, as is the
  inner and outer sphere refinement of §4.2 for counterfactual morphology; a sentence is a
  function of the information parameter and the world.

## References

* [klinedinst-rothschild-2012]
* [yalcin-2007]
-/

namespace KlinedinstRothschild2012

variable {W : Type*}

/-- Truth relative to an information parameter and a world, §4. -/
abbrev Sentence (W : Type*) := Set W → W → Prop

namespace Sentence

variable (a b : Sentence W)

/-- A factual sentence ignores the information parameter, (45). -/
def ofProp (p : Set W) : Sentence W := λ _ w => w ∈ p

/-- Epistemic possibility quantifies over the information parameter, (46). -/
def might : Sentence W := λ s _ => ∃ w' ∈ s, a s w'

/-- Epistemic necessity, (47). -/
def must : Sentence W := λ s _ => ∀ w' ∈ s, a s w'

def neg : Sentence W := λ s w => ¬ a s w

/-- The information parameter updated with `a`, the `sᵃ` of §4. -/
def update (s : Set W) : Set W := {w' ∈ s | a s w'}

/-- Conjunction, (49): the second conjunct is evaluated against the parameter updated with
the first. -/
def conj : Sentence W := λ s w => a s w ∧ b (a.update s) w

/-- Disjunction, (50): the second disjunct is evaluated against the parameter updated with
the negation of the first. -/
def disj : Sentence W := λ s w => a s w ∨ b (a.neg.update s) w

/-- The conditional, (52): the antecedent shifts the parameter, and a modal in the consequent
quantifies over the result. -/
def ifThen : Sentence W := λ s w => b (a.update s) w

/-- The premises entail the conclusion when the conclusion holds wherever they all do. -/
def Entails (Γ : List (Sentence W)) (c : Sentence W) : Prop :=
  ∀ (s : Set W) (w : W), (∀ γ ∈ Γ, γ s w) → c s w

end Sentence

open Sentence

/-! ### Epistemic modals under *or*, §3.2 -/

/-- (36): *the dog is in the backyard or it must be in the kitchen* is a disjunction of the
first disjunct with the report that the information, given that the dog is not in the
backyard, puts it in the kitchen. -/
theorem disj_must_iff (p q : Set W) (s : Set W) (w : W) :
    (ofProp p).disj (ofProp q).must s w ↔ w ∈ p ∨ ∀ w' ∈ s, w' ∉ p → w' ∈ q := by
  simp [disj, must, ofProp, update, neg]

/-- Disjunctive syllogism holds for factual disjuncts. -/
theorem disjunctive_syllogism (p q : Set W) :
    Entails [(ofProp p).disj (ofProp q), (ofProp q).neg] (ofProp p) := by
  intro s w h
  rcases h _ (List.mem_cons_self) with hp | hq
  · exact hp
  · exact absurd hq (h _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- (38)–(40): disjunctive syllogism fails with the modal disjunct. On the two-world model,
the dog inside in one world and outside in the other, the disjunction *the dog is inside or it
must be outside* and *it's not the case that it must be outside* both hold at the outside
world, where the dog is not inside. -/
theorem not_disjunctive_syllogism :
    ¬ Entails [(ofProp {true}).disj (ofProp {false}).must, (ofProp {false}).must.neg]
      (ofProp ({true} : Set Bool)) := by
  intro h
  have := h Set.univ false (by simp [disj, must, ofProp, update, neg, Set.mem_singleton_iff])
  simp [ofProp, Set.mem_singleton_iff] at this

/-- (104): the dynamic effect is asymmetric, so the disjuncts do not commute: with the modal
disjunct first, the same model falsifies the disjunction. -/
theorem disj_not_comm :
    ¬ ∀ (a b : Sentence Bool) (s : Set Bool) (w : Bool), a.disj b s w ↔ b.disj a s w := by
  intro h
  have := (h (ofProp {true}) (ofProp {false}).must Set.univ false).1
    (by simp [disj, must, ofProp, update, neg, Set.mem_singleton_iff])
  simp [disj, must, ofProp, Set.mem_singleton_iff] at this

/-! ### The assertion forms of (60), §5 -/

/-- The connective whose dynamic effect is kept. -/
inductive Connective
  | and
  | or
  deriving DecidableEq, Repr

/-- The three assertion forms of `a ∗ b`, (60): the normal connective, both clauses entailed
with the second under the shifted parameter, or the first clause used only to shift the
parameter of the second. -/
inductive Use
  | normal
  | doubleEntailment
  | shift
  deriving DecidableEq, Repr

/-- The parameter the second clause is evaluated under, (49) and (50). -/
def Connective.shift : Connective → Sentence W → Set W → Set W
  | .and, a, s => a.update s
  | .or, a, s => a.neg.update s

/-- The content of `a ∗ b` on each assertion form, the table of (60). -/
def Use.interpret : Use → Connective → Sentence W → Sentence W → Sentence W
  | .normal, .and, a, b => a.conj b
  | .normal, .or, a, b => a.disj b
  | .doubleEntailment, c, a, b => λ s w => a s w ∧ b (c.shift a s) w
  | .shift, c, a, b => λ s w => b (c.shift a s) w

variable (a b : Sentence W)

/-- Double entailment of *and* reproduces the normal conjunction. -/
theorem doubleEntailment_and : Use.doubleEntailment.interpret .and a b = a.conj b := rfl

/-- The parameter-shifting *or* is the conditional on the negation of its first disjunct. -/
theorem shift_disj : Use.shift.interpret .or a b = a.neg.ifThen b := rfl

/-- The non-truth-tabular *and*, (1): the first conjunct only shifts the parameter, which is
the conditional of (52). -/
theorem shift_and : Use.shift.interpret .and a b = a.ifThen b := rfl

/-- The non-truth-tabular *or*, (2) and (66): the first disjunct is asserted, and the second
under the parameter updated with its negation, (67). -/
theorem doubleEntailment_disj :
    Use.doubleEntailment.interpret .or a b = λ s w => a s w ∧ b (a.neg.update s) w := rfl

/-- (61) and (62): *the police show up, and there might be trouble* is true when some world
of the parameter in which the police show up is one with trouble. -/
theorem cond_might_iff (p t : Set W) (s : Set W) (w : W) :
    (ofProp p).ifThen (ofProp t).might s w ↔ ∃ w' ∈ s, w' ∈ p ∧ w' ∈ t := by
  simp [ifThen, might, ofProp, update, and_assoc]

/-- (68): *John is here and he might not be* is a contradiction, the second conjunct needing
a parameter with worlds in which the first fails. -/
theorem not_conj_might_neg (p : Set W) (s : Set W) (w : W) :
    ¬ (ofProp p).conj (ofProp p).neg.might s w := by
  simp [conj, might, ofProp, update, neg]

end KlinedinstRothschild2012
