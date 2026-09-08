import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Copular
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-!
# Degen and Tonhauser (2021): Prior beliefs modulate projection

This file formalizes the finding of [degen-tonhauser-2021] that a listener's prior belief in
the content of a clausal complement modulates how strongly that content projects, the
listener's inference about the speaker's commitment to it under a question. The hypothesis
came from the by-item variability of [tonhauser-beaver-degen-2018] and had conflicting support,
[mahler-2020] finding modulation for politically charged contents and [lorson-2018] none for
the pre-state of *stop*. Across twenty clause-embedding predicates and twenty contents each
paired with a fact raising or lowering its prior, projection was higher under the higher-prior
fact for every predicate, and the participant's own prior predicted projection better than
the group's or the categorical manipulation. The account the paper sketches is Bayesian, in the
spirit of [goodman-frank-2016] and [qing-goodman-lassiter-2016]: projection is the posterior
credence in the content, which by Bayes' rule is strictly increasing in the prior at fixed
likelihoods, so a more likely content is taken to be more strongly committed to. The
predicates are the Fragment's clause-embedding verbs and adjectives, all of which take a
finite clause complement, and the by-predicate means of Experiment 1 are recorded.

## Implementation notes

The Experiment 1 means come from the cd.csv data file of the paper's repository, averaged by
predicate and rounded to two decimals, the prior means over the contents each predicate was
paired with. The regression coefficients are not encoded: the prior manipulation raised
ratings (β = 0.45), projection rose with the categorical fact (β = 0.14), with the group-level
prior (β = 0.31) and with the participant's own prior (β = 0.28), the individual-level model
winning by BIC, and Experiment 2 replicated the effect between participants.

## References

* [degen-tonhauser-2021]
* [tonhauser-beaver-degen-2018]
* [mahler-2020]
* [lorson-2018]
* [goodman-frank-2016]
* [qing-goodman-lassiter-2016]
-/

namespace DegenTonhauser2021

/-! ### Projection as posterior credence -/

/-- The posterior credence in a content of prior `p` after an utterance the speaker produces
with likelihood `a` when the content holds and `b` when it does not. -/
noncomputable def posterior (a b p : ℝ) : ℝ := p * a / (p * a + (1 - p) * b)

/-- Bayes' rule makes projection prior-sensitive: at fixed positive likelihoods the posterior
credence is strictly increasing in the prior, so a content that is more likely a priori is
more likely a posteriori. -/
theorem posterior_lt_posterior {a b p q : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 ≤ p)
    (hq : q ≤ 1) (hpq : p < q) : posterior a b p < posterior a b q := by
  unfold posterior
  have h1 : 0 < p * a + (1 - p) * b := by nlinarith
  have h2 : 0 < q * a + (1 - q) * b := by nlinarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) (sub_pos.2 hpq)]

/-! ### The predicates and the means of Experiment 1 -/

/-- The twenty clause-embedding predicates of Figure 1c. -/
inductive Predicate where
  | acknowledge | admit | announce | beAnnoyed | beRight
  | confess | confirm | demonstrate | discover | establish
  | hear | inform | know | pretend | prove
  | reveal | say | see | suggest | think
  deriving DecidableEq, Fintype, Repr

/-- A predicate's Experiment 1 means: the prior probability rating of its contents under the
lower- and the higher-probability fact, and the certainty rating, the projection measure, under
each. -/
structure Means where
  priorLow : ℚ
  priorHigh : ℚ
  certaintyLow : ℚ
  certaintyHigh : ℚ
  deriving DecidableEq, Repr

/-- The by-predicate means of Experiment 1, the certainty means those of Figure 3 and the prior
means those of the contents each predicate was paired with; the main-clause control projected
at a mean certainty of 0.21. -/
def means : Predicate → Means
  | .acknowledge => ⟨0.24, 0.67, 0.49, 0.65⟩
  | .admit => ⟨0.24, 0.68, 0.43, 0.60⟩
  | .announce => ⟨0.26, 0.72, 0.41, 0.53⟩
  | .beAnnoyed => ⟨0.23, 0.71, 0.68, 0.80⟩
  | .beRight => ⟨0.26, 0.69, 0.20, 0.34⟩
  | .confess => ⟨0.20, 0.69, 0.45, 0.58⟩
  | .confirm => ⟨0.21, 0.68, 0.28, 0.37⟩
  | .demonstrate => ⟨0.26, 0.62, 0.33, 0.48⟩
  | .discover => ⟨0.26, 0.72, 0.55, 0.69⟩
  | .establish => ⟨0.23, 0.69, 0.27, 0.43⟩
  | .hear => ⟨0.24, 0.69, 0.57, 0.72⟩
  | .inform => ⟨0.25, 0.72, 0.57, 0.76⟩
  | .know => ⟨0.25, 0.68, 0.68, 0.74⟩
  | .pretend => ⟨0.20, 0.70, 0.21, 0.31⟩
  | .prove => ⟨0.24, 0.67, 0.25, 0.41⟩
  | .reveal => ⟨0.25, 0.69, 0.47, 0.62⟩
  | .say => ⟨0.22, 0.69, 0.22, 0.38⟩
  | .see => ⟨0.21, 0.67, 0.60, 0.69⟩
  | .suggest => ⟨0.22, 0.69, 0.24, 0.32⟩
  | .think => ⟨0.19, 0.66, 0.20, 0.40⟩

/-- For every predicate the manipulation raised the prior and, with it, projection, the pattern
of Figure 3 that a prior-sensitive account predicts. -/
theorem prior_modulates_projection (p : Predicate) :
    (means p).priorLow < (means p).priorHigh ∧
      (means p).certaintyLow < (means p).certaintyHigh := by
  cases p <;> exact ⟨by norm_num [means], by norm_num [means]⟩

/-! ### The Fragment's predicates -/

section Fragment

open English.Predicates.Verbal English.Predicates.Copular

/-- The verb of a predicate, the semantic spine the verbal and copular entries share. -/
def toPredicateCore : Predicate → Verb
  | .know => know.toVerb
  | .think => think.toVerb
  | .discover => discover.toVerb
  | .see => see.toVerb
  | .say => say.toVerb
  | .hear => hear.toVerb
  | .reveal => reveal.toVerb
  | .acknowledge => acknowledge.toVerb
  | .admit => admit.toVerb
  | .announce => announce.toVerb
  | .confess => confess.toVerb
  | .inform => inform.toVerb
  | .suggest => suggest.toVerb
  | .pretend => pretend.toVerb
  | .confirm => confirm.toVerb
  | .demonstrate => demonstrate.toVerb
  | .establish => establish.toVerb
  | .prove => prove.toVerb
  | .beAnnoyed => beAnnoyed.toVerb
  | .beRight => beRight.toVerb

/-- Every predicate takes a finite clause complement, as the polar questions of the stimuli
require. -/
theorem all_predicates_take_clause_complement (p : Predicate) :
    (toPredicateCore p).complementType = .finiteClause ∨
      (toPredicateCore p).altComplementType = some .finiteClause := by
  cases p <;>
    simp [toPredicateCore, ClauseEmbeddingAdjective.toVerb, beAnnoyed, beRight] <;>
    first | left; rfl | right; rfl

end Fragment

end DegenTonhauser2021
