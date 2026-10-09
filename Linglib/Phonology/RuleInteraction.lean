module

public import Mathlib.Tactic.TypeStar

/-!
# Feeding and bleeding

Kiparsky classifies how one rule bears on another by what applying the first does to the second's
conditions: the first feeds the second when it creates them and bleeds it when it destroys them.
Over any rules, each with a condition under which it fires and an effect on the state it applies
to, the two notions need only a firing predicate and an application map, so they serve
phonological rules, postsyntactic impoverishment, and syntactic operations alike. The rules may
come from different modules, as when impoverishment of a structure feeds metathesis of its
linearization.

## Main definitions

* `RuleInteraction.Feeds`, `RuleInteraction.Bleeds`: applying one rule creates, or destroys, the
  conditions under which another fires.

## Main results

* `RuleInteraction.feeds_iff_bleeds_not`: feeding a rule is bleeding the rule that fires where it
  does not.

## References

* [kiparsky-1968]
-/

@[expose] public section

namespace RuleInteraction

variable {R R' S : Type*} (apply : R → S → S) (fires : R' → S → Prop)

/-- Applying `a` feeds `b` at `s` when `b` does not fire at `s` but fires once `a` has applied. -/
def Feeds (a : R) (b : R') (s : S) : Prop := ¬ fires b s ∧ fires b (apply a s)

/-- Applying `a` bleeds `b` at `s` when `b` fires at `s` but not once `a` has applied. -/
def Bleeds (a : R) (b : R') (s : S) : Prop := fires b s ∧ ¬ fires b (apply a s)

variable {apply fires} {a : R} {b : R'} {s : S}

instance [∀ b s, Decidable (fires b s)] : Decidable (Feeds apply fires a b s) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [∀ b s, Decidable (fires b s)] : Decidable (Bleeds apply fires a b s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem feeds_iff_bleeds_not :
    Feeds apply fires a b s ↔ Bleeds apply (fun b s ↦ ¬ fires b s) a b s := by
  simp [Feeds, Bleeds, and_comm]

end RuleInteraction
