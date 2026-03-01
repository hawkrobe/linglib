import Mathlib.Data.Rat.Defs

/-!
# Relevance — Sperber & Wilson (1986/95)

Relevance is a comparative notion defined along two dimensions:
- **Cognitive effects**: greater effects → more relevant
- **Processing effort**: less effort → more relevant

## The Two Principles (2nd ed, Postface)

**First (Cognitive) Principle**: Human cognition tends to be geared to the
maximisation of relevance. (Descriptive cognitive universal, not a norm.)

**Second (Communicative) Principle**: Every act of ostensive communication
communicates a presumption of its own optimal relevance.

## Optimal Relevance (revised, 2nd ed, p. 270)

(a) Relevant enough to be worth the addressee's effort to process
(b) The most relevant stimulus compatible with the communicator's abilities
    and preferences

Clause (b) does the work of Grice's maxim of Quantity without a cooperative
principle — it derives implicatures about the speaker's knowledge and goals.

## References

Sperber, D. & Wilson, D. (1986/95). Relevance. Ch. 3 §4; Postface pp. 260-272.
-/

set_option autoImplicit false

namespace Theories.Pragmatics.RelevanceTheory

/-- Relevance assessment: the two independent dimensions.

    NOT a ratio or single number. Relevance is comparative: an input is
    more relevant to the extent that effects are greater and effort is
    smaller. Some inputs are incomparable (more effects AND more effort). -/
structure RelevanceAssessment where
  /-- Magnitude of positive cognitive effects -/
  effects : ℕ
  /-- Processing effort required -/
  effort : ℕ
  deriving DecidableEq, BEq, Repr

/-- Comparative relevance: `a` is strictly more relevant than `b`.

    Strict partial order — some inputs are incomparable (more effects
    but also more effort). This partiality is deliberate: RT does not
    claim all inputs can be ranked on relevance. -/
def RelevanceAssessment.moreRelevant (a b : RelevanceAssessment) : Prop :=
  (b.effects ≤ a.effects ∧ a.effort ≤ b.effort) ∧
  (b.effects < a.effects ∨ a.effort < b.effort)

/-- Nothing is more relevant than itself. -/
theorem RelevanceAssessment.moreRelevant_irrefl (a : RelevanceAssessment) :
    ¬a.moreRelevant a := by
  intro ⟨_, h⟩
  rcases h with h | h <;> exact absurd h (Nat.lt_irrefl _)

/-- Comparative relevance is transitive. -/
theorem RelevanceAssessment.moreRelevant_trans {a b c : RelevanceAssessment}
    (hab : a.moreRelevant b) (hbc : b.moreRelevant c) :
    a.moreRelevant c := by
  have h1 := hab.1.1; have h2 := hab.1.2
  have h4 := hbc.1.1; have h5 := hbc.1.2
  constructor
  · exact ⟨Nat.le_trans h4 h1, Nat.le_trans h2 h5⟩
  · rcases hab.2 with h | h
    · exact Or.inl (Nat.lt_of_le_of_lt h4 h)
    · rcases hbc.2 with h' | h'
      · exact Or.inl (Nat.lt_of_lt_of_le h' h1)
      · exact Or.inr (Nat.lt_trans h h')

/-- Optimal relevance: the presumption created by ostensive communication.

    The hearer assumes the stimulus satisfies BOTH clauses:
    (a) Worth processing — effects exceed the hearer's expectations
    (b) Most relevant compatible — the communicator couldn't easily have
        been more relevant

    These two clauses are independent — (a) sets a floor on relevance,
    (b) is an optimality condition on the communicator's choices. -/
structure OptimalRelevance where
  /-- Clause (a): the stimulus achieves enough effects to justify the
      processing effort. -/
  worthProcessing : Prop
  /-- Clause (b): the stimulus is the most relevant one compatible with
      the communicator's abilities and preferences. -/
  mostRelevantCompatible : Prop

end Theories.Pragmatics.RelevanceTheory
