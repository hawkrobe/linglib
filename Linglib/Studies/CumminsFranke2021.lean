import Linglib.Pragmatics.DecisionTheoretic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# [cummins-franke-2021]: Rational Interpretation of Numerical Quantity
[cummins-franke-2021] [merin-1999-relevance]

[cummins-franke-2021] applies [merin-1999-relevance]'s log-likelihood-ratio measure of
argumentative strength to numerical quantity expressions: the strength of utterance u toward
goal G is log (P(u∣G) / P(u∣¬G)) (eq. 17), and a pragmatic variant replaces truth with
felicitous assertability (eq. 25). The §5 worked example: a conference succeeds iff more than
120 people register, registrations are uniform on [0, 200], and the speaker chooses between
*more than 100* and *more than 110*.

## Main results

- `strength_reversal`: semantically *more than 110* is the stronger argument for success
  (Bayes factor 12 vs 6), but under assertability with a 90%-enriching listener the ordering
  *reverses* (21/8 vs 6/5) — the paper's central demonstration (§5.2) that pragmatic
  interpretation can penalize the semantically optimal argument.
- `bayesFactor_moreThan100` …: the §5.1–5.2 Bayes factors, computed from a `DTS.DTSContext`
  rather than stipulated; the `example`s certify the paper's printed conditional
  probabilities (1/6, 1/12, 35/80, 1/10).

The measure `strength` is `Real.log` (nats) of `DTS.bayesFactor`; the paper leaves the log
base unspecified (its printed values are base 10) and uses it only ordinally.

Deviation: for *more than 110* the paper prints log 11, computed from "the probability that
*more than 100* is true given that *more than 110* is false equals 1/11" — the Bayes factor
of *more than 100* toward the goal *more than 110* (`bayesFactor_moreThan100_toward110`).
Toward the example's stated goal (*more than 120*) the factor is 12
(`bayesFactor_moreThan110`); the semantic ordering is the same either way.

Not formalized: the §5.4 rational-hearer conditions (eqs. 27–28), which compare an
utterance's strength against the alternatives assertable in ¬G-worlds and are stated but not
computed with in the paper; and the §6 corpus study of research-ranking reports.
-/

namespace CumminsFranke2021

open DTS

/-! ### The §5 example -/

/-- Registration totals in bands of width 10: band k covers (10k, 10(k+1)]. Every threshold
in the §5 example (100, 110, 120, 150) is a band boundary, so the paper's continuous uniform
distribution on [0, 200] is represented exactly by a uniform prior over the 20 bands. -/
abbrev Band := Fin 20

/-- The extension of *more than n*, for thresholds n that are multiples of 10: every total in
band k exceeds n iff n ≤ 10k. -/
def moreThan (n : ℕ) : Set Band := {k | n ≤ 10 * k.val}

instance (n : ℕ) : DecidablePred (· ∈ moreThan n) := fun k =>
  inferInstanceAs (Decidable (n ≤ 10 * k.val))

/-- §5.1: the goal is S = *more than 120* (conference success), with the uniform prior. -/
def successContext : DTSContext Band := ⟨moreThan 120, inferInstance, λ _ => 1/20⟩

example : ∑ k : Band, successContext.prior k = 1 := by decide +kernel

/-! ### Semantic argumentative strength (§5.1) -/

-- The paper's printed conditional probabilities: P(u∣¬S) for the two utterances.
example : condProb successContext.prior (moreThan 100) successContext.topicᶜ = 1/6 := by
  decide +kernel
example : condProb successContext.prior (moreThan 110) successContext.topicᶜ = 1/12 := by
  decide +kernel

/-- §5.1: the Bayes factor of *more than 100* toward success is 1 / (1/6) = 6 (the paper's
log 6 ≈ 0.78). -/
theorem bayesFactor_moreThan100 : bayesFactor successContext (moreThan 100) = 6 := by
  decide +kernel

/-- The Bayes factor of *more than 110* toward success is 1 / (1/12) = 12. The paper instead
prints log 11 (see `bayesFactor_moreThan100_toward110`); the ordering against
`bayesFactor_moreThan100` is the same. -/
theorem bayesFactor_moreThan110 : bayesFactor successContext (moreThan 110) = 12 := by
  decide +kernel

/-- The quantity behind the paper's printed log 11: the Bayes factor of *more than 100*
toward the goal *more than 110* ("the probability that *more than 100* is true given that
*more than 110* is false equals 1/11"). -/
theorem bayesFactor_moreThan100_toward110 :
    bayesFactor ⟨moreThan 110, inferInstance, λ _ => 1/20⟩ (moreThan 100) = 11 := by
  decide +kernel

/-! ### Pragmatic argumentative strength (§5.2)

Assertability is stochastic: with probability 9/10 the listener enriches the utterance with
its scalar implicature (*more than 100* ⇝ *not more than 150*, *more than 110* ⇝ *not more
than 120*), so u is felicitously assertable only if the implicature is also true; with
probability 1/10 the utterance is interpreted literally. The mixture lives on the product of
bands and interpretations. -/

/-- How the listener resolves the utterance: enriched with its scalar implicature (9/10) or
literal (1/10). -/
inductive Interpretation where
  | enriched | literal
  deriving DecidableEq

instance : Fintype Interpretation where
  elems := {.enriched, .literal}
  complete := fun x => by cases x <;> simp

/-- The §5.2 mixture weights: 90% enriched, 10% literal. -/
def interpretationProb : Interpretation → ℚ
  | .enriched => 9/10
  | .literal => 1/10

/-- §5.2: the assertability space — bands × interpretations, goal still *more than 120*,
prior the product of the uniform band prior with the interpretation mixture. -/
def assertabilityContext : DTSContext (Band × Interpretation) :=
  ⟨{p | p.1 ∈ moreThan 120}, fun p => inferInstanceAs (Decidable (p.1 ∈ moreThan 120)),
    λ p => 1/20 * interpretationProb p.2⟩

example : ∑ p : Band × Interpretation, assertabilityContext.prior p = 1 := by decide +kernel

/-- Felicitous assertability of *more than n* with scalar implicature *not more than cap*:
true, and for an enriching listener the implicature holds as well. -/
def assertable (n cap : ℕ) : Set (Band × Interpretation) :=
  {p | p.1 ∈ moreThan n ∧ (p.2 = .enriched → p.1 ∉ moreThan cap)}

instance (n cap : ℕ) : DecidablePred (· ∈ assertable n cap) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

-- The paper's printed assertability probabilities: P(A(u)∣S) and P(A(u)∣¬S).
example : condProb assertabilityContext.prior (assertable 100 150)
    assertabilityContext.topic = 35/80 := by decide +kernel
example : condProb assertabilityContext.prior (assertable 110 120)
    assertabilityContext.topic = 1/10 := by decide +kernel
example : condProb assertabilityContext.prior (assertable 100 150)
    assertabilityContext.topicᶜ = 1/6 := by decide +kernel
example : condProb assertabilityContext.prior (assertable 110 120)
    assertabilityContext.topicᶜ = 1/12 := by decide +kernel

/-- §5.2: the assertability Bayes factor of *more than 100* is (35/80) / (1/6) = 21/8 (the
paper's log (21/8) = 0.419). -/
theorem assertable_bayesFactor_moreThan100 :
    bayesFactor assertabilityContext (assertable 100 150) = 21/8 := by decide +kernel

/-- §5.2: the assertability Bayes factor of *more than 110* is (1/10) / (1/12) = 6/5 (the
paper's log (6/5) = 0.079). -/
theorem assertable_bayesFactor_moreThan110 :
    bayesFactor assertabilityContext (assertable 110 120) = 6/5 := by decide +kernel

/-! ### The reversal -/

/-- Argumentative strength (eq. 17; eq. 25 on the assertability space): the log of the Bayes
factor, positive iff the utterance supports the goal. -/
noncomputable def strength {W : Type*} [Fintype W] (ctx : DTSContext W) (u : Set W)
    [DecidablePred (· ∈ u)] : ℝ :=
  Real.log (bayesFactor ctx u)

/-- The paper's central §5.2 demonstration: semantically *more than 110* is the stronger
argument for success, but under assertability the ordering reverses — precision that looks
argumentatively optimal is penalized once the listener's enrichment is priced in. -/
theorem strength_reversal :
    strength successContext (moreThan 100) < strength successContext (moreThan 110) ∧
    strength assertabilityContext (assertable 110 120) <
      strength assertabilityContext (assertable 100 150) := by
  unfold strength
  rw [bayesFactor_moreThan100, bayesFactor_moreThan110, assertable_bayesFactor_moreThan110,
    assertable_bayesFactor_moreThan100]
  exact ⟨Real.log_lt_log (by norm_num) (by norm_num),
    Real.log_lt_log (by norm_num) (by norm_num)⟩

end CumminsFranke2021
