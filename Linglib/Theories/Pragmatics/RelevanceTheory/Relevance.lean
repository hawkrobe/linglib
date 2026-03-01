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

-- ============================================================================
-- Optimal Relevance (Postface p. 270)
-- ============================================================================

/-- Clause (a) of optimal relevance: the stimulus is worth processing.
    Its cognitive effects justify the processing effort.

    S&W (Postface p. 270): "The set of assumptions {I} which the
    communicator intends to make manifest to the addressee is relevant
    enough to make it worth the addressee's while to process the
    ostensive stimulus." -/
def RelevanceAssessment.worthProcessing (r : RelevanceAssessment)
    (minEffects : ℕ) : Prop :=
  minEffects ≤ r.effects

/-- Clause (b) of optimal relevance: no available alternative is strictly
    more relevant than the stimulus actually used.

    S&W (Postface p. 270): "The ostensive stimulus is the most relevant
    one the communicator could have used to communicate {I}."

    Implicatures about the speaker's knowledge and goals derive from this
    clause: if a more relevant alternative existed, the speaker COULDN'T
    or DIDN'T WANT TO use it. -/
def RelevanceAssessment.mostRelevantCompatible (r : RelevanceAssessment)
    (alternatives : List RelevanceAssessment) : Prop :=
  ∀ alt ∈ alternatives, ¬alt.moreRelevant r

/-- Optimal relevance: both clauses (a) and (b) hold jointly.

    Clause (a) sets a floor on the relevance of the stimulus.
    Clause (b) is an optimality condition on the communicator's choice. -/
def RelevanceAssessment.optimallyRelevant (r : RelevanceAssessment)
    (minEffects : ℕ) (alternatives : List RelevanceAssessment) : Prop :=
  r.worthProcessing minEffects ∧ r.mostRelevantCompatible alternatives

/-- If a stimulus is optimally relevant with no available alternatives,
    clause (b) is trivially satisfied — only clause (a) matters. -/
theorem RelevanceAssessment.optimal_no_alternatives (r : RelevanceAssessment)
    (minEffects : ℕ) (ha : r.worthProcessing minEffects) :
    r.optimallyRelevant minEffects [] :=
  ⟨ha, fun _ h => nomatch h⟩

/-- More effects with the same effort → more relevant. -/
theorem RelevanceAssessment.more_effects_more_relevant
    (e1 e2 eff : ℕ) (h : e1 < e2) :
    (⟨e2, eff⟩ : RelevanceAssessment).moreRelevant ⟨e1, eff⟩ :=
  ⟨⟨Nat.le_of_lt h, Nat.le_refl _⟩, Or.inl h⟩

/-- Less effort with the same effects → more relevant. -/
theorem RelevanceAssessment.less_effort_more_relevant
    (eff1 eff2 e : ℕ) (h : eff2 < eff1) :
    (⟨e, eff2⟩ : RelevanceAssessment).moreRelevant ⟨e, eff1⟩ :=
  ⟨⟨Nat.le_refl _, Nat.le_of_lt h⟩, Or.inr h⟩

end Theories.Pragmatics.RelevanceTheory
