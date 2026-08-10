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

- `bayesFactor_lt_of_goal_entails`: §5.1's alignment of semantic and argumentative strength,
  in general form — between utterances entailed by the goal, the semantically stronger one is
  the argumentatively stronger one, since its extra content can only shed ¬G-worlds.
- `condProb_byInterpretation` / `bayesFactor_byInterpretation`: §5.2's computation pattern in
  general form — over the enriched/literal interpretation mixture, an interpretation-dependent
  event's conditional probability is the ρ-weighted mixture of its branches.
- `strength_reversal`: the paper's central demonstration — semantically *more than 110* is the
  stronger argument for success (`semantic_ordering`, Bayes factors 6 < 12), but under
  assertability with a 90%-enriching listener the ordering *reverses* (21/8 vs 6/5).

The §5.1–5.2 Bayes-factor values are instantiation theorems computed from the general lemmas
over a `DTS.DTSContext`; `example`s certify the paper's printed conditional probabilities
(1/6, 1/12, 3/8, 35/80, 1/10). The measure `strength` is `Real.log` (nats) of
`DTS.bayesFactor`; the paper leaves the log base unspecified (its printed values are base 10)
and uses it only ordinally.

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

variable {W : Type*} [Fintype W]

/-! ### Semantic strength and goal entailment (§5.1) -/

/-- §5.1's alignment of semantic and argumentative strength: between two utterances entailed
by the goal, the semantically stronger (smaller) one is the argumentatively stronger one —
both are certain given the goal, and the weaker utterance's extra extension can only add
¬G-worlds to the denominator of the Bayes factor. -/
theorem bayesFactor_lt_of_goal_entails (ctx : DTSContext W) {u₁ u₂ : Set W}
    [DecidablePred (· ∈ u₁)] [DecidablePred (· ∈ u₂)]
    (hnn : ∀ w, ctx.prior w ≥ 0) (hG : probSum ctx.prior ctx.topic ≠ 0)
    (hsub : u₂ ⊆ u₁) (hent : ctx.topic ⊆ u₂)
    (hgap : 0 < probSum ctx.prior (u₁ ∩ ctx.topicᶜ ∩ u₂ᶜ))
    (hpos : 0 < probSum ctx.prior (u₂ ∩ ctx.topicᶜ)) :
    bayesFactor ctx u₁ < bayesFactor ctx u₂ := by
  have hNG : 0 < probSum ctx.prior ctx.topicᶜ :=
    lt_of_lt_of_le hpos (probSum_mono ctx.prior hnn _ _ fun w hw => hw.2)
  have hnum : probSum ctx.prior (u₂ ∩ ctx.topicᶜ) < probSum ctx.prior (u₁ ∩ ctx.topicᶜ) := by
    have hpart := probSum_partition ctx.prior (u₁ ∩ ctx.topicᶜ) u₂
    rw [probSum_congr ctx.prior
      (show (u₁ ∩ ctx.topicᶜ) ∩ u₂ = u₂ ∩ ctx.topicᶜ from
        Set.ext fun w => ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩)] at hpart
    linarith
  have hd₂ := condProb_unfold ctx.prior u₂ ctx.topicᶜ hNG.ne'
  have hd₁ := condProb_unfold ctx.prior u₁ ctx.topicᶜ hNG.ne'
  have hd₂pos : 0 < condProb ctx.prior u₂ ctx.topicᶜ := hd₂ ▸ div_pos hpos hNG
  have hdlt : condProb ctx.prior u₂ ctx.topicᶜ < condProb ctx.prior u₁ ctx.topicᶜ := by
    rw [hd₁, hd₂]; exact div_lt_div_of_pos_right hnum hNG
  rw [bayesFactor_unfold ctx u₁ (hd₂pos.trans hdlt).ne',
    bayesFactor_unfold ctx u₂ hd₂pos.ne',
    condProb_eq_one_of_subset ctx.prior (hent.trans hsub) hG,
    condProb_eq_one_of_subset ctx.prior hent hG]
  exact one_div_lt_one_div_of_lt hd₂pos hdlt

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

/-- §5.1 as an instance of `bayesFactor_lt_of_goal_entails`: both utterances are entailed by
the goal and *more than 110* is semantically stronger, so it is the stronger argument. -/
theorem semantic_ordering :
    bayesFactor successContext (moreThan 100) < bayesFactor successContext (moreThan 110) :=
  bayesFactor_lt_of_goal_entails successContext (fun _ => by norm_num [successContext])
    (by decide +kernel)
    (fun _ hk => le_trans (show (100 : ℕ) ≤ 110 by norm_num) hk)
    (fun _ hk => le_trans (show (110 : ℕ) ≤ 120 by norm_num) hk)
    (by decide +kernel) (by decide +kernel)

/-! ### The assertability mixture (§5.2)

Assertability is stochastic: with probability ρ = 9/10 the listener enriches the utterance
with its scalar implicature, so it is felicitously assertable only if the implicature is also
true; with probability 1/10 it is interpreted literally. The mixture lives on the product of
worlds and interpretations, and conditional probabilities decompose branchwise. -/

/-- How the listener resolves an utterance (§5.2): enriched with its scalar implicature, or
literal. -/
inductive Interpretation where
  | enriched | literal
  deriving DecidableEq

instance : Fintype Interpretation where
  elems := {.enriched, .literal}
  complete := fun x => by cases x <;> simp

/-- Extend a context with the listener-interpretation mixture: enriched with probability ρ,
literal otherwise. The issue lifts along the underlying world. -/
def withInterpretation (ctx : DTSContext W) (ρ : ℚ) : DTSContext (W × Interpretation) :=
  ⟨{p | p.1 ∈ ctx.topic}, fun p => ctx.topicDec p.1,
    λ p => ctx.prior p.1 * if p.2 = .enriched then ρ else 1 - ρ⟩

/-- An interpretation-dependent event: `enr` under enrichment, `lit` under literal
interpretation. -/
def byInterpretation (enr lit : Set W) : Set (W × Interpretation) :=
  {p | p.2 = .enriched ∧ p.1 ∈ enr ∨ p.2 = .literal ∧ p.1 ∈ lit}

instance (enr lit : Set W) [DecidablePred (· ∈ enr)] [DecidablePred (· ∈ lit)] :
    DecidablePred (· ∈ byInterpretation enr lit) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∨ _ ∧ _))

/-- The mixture decomposition of mass: an interpretation-dependent event weighs its enriched
branch by ρ and its literal branch by 1 − ρ. -/
theorem probSum_byInterpretation (ctx : DTSContext W) (ρ : ℚ) (enr lit : Set W)
    [DecidablePred (· ∈ enr)] [DecidablePred (· ∈ lit)] :
    probSum (withInterpretation ctx ρ).prior (byInterpretation enr lit) =
      ρ * probSum ctx.prior enr + (1 - ρ) * probSum ctx.prior lit := by
  unfold probSum
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (Finset.univ : Finset Interpretation) = {.enriched, .literal} from rfl,
    Finset.sum_pair (by decide)]
  by_cases h1 : w ∈ enr <;> by_cases h2 : w ∈ lit <;>
    simp [withInterpretation, byInterpretation, h1, h2] <;> ring

/-- §5.2's computation pattern: conditional on a lifted event, an interpretation-dependent
event's probability is the ρ-weighted mixture of its branches' conditional probabilities. -/
theorem condProb_byInterpretation (ctx : DTSContext W) (ρ : ℚ) (enr lit s : Set W)
    [DecidablePred (· ∈ enr)] [DecidablePred (· ∈ lit)] [DecidablePred (· ∈ s)] :
    condProb (withInterpretation ctx ρ).prior (byInterpretation enr lit) {p | p.1 ∈ s} =
      ρ * condProb ctx.prior enr s + (1 - ρ) * condProb ctx.prior lit s := by
  have hlift : ({p | p.1 ∈ s} : Set (W × Interpretation)) = byInterpretation s s :=
    Set.ext fun p => by cases hp : p.2 <;> simp [byInterpretation, hp]
  have hbase : probSum (withInterpretation ctx ρ).prior {p | p.1 ∈ s} =
      probSum ctx.prior s := by
    rw [probSum_congr _ hlift, probSum_byInterpretation]; ring
  by_cases hs : probSum ctx.prior s = 0
  · simp [condProb, hbase, hs]
  · have hs' : probSum (withInterpretation ctx ρ).prior {p | p.1 ∈ s} ≠ 0 := by
      rw [hbase]; exact hs
    have hinter : byInterpretation enr lit ∩ {p | p.1 ∈ s} =
        byInterpretation (enr ∩ s) (lit ∩ s) :=
      Set.ext fun p => by cases hp : p.2 <;> simp [byInterpretation, hp]
    rw [condProb_unfold _ _ _ hs', probSum_congr _ hinter, probSum_byInterpretation, hbase,
      condProb_unfold _ _ _ hs, condProb_unfold _ _ _ hs]
    ring

/-- The Bayes factor of an interpretation-dependent event, in mixture form (§5.2's
"(90% × ⋯ + 10% × ⋯)" computations). -/
theorem bayesFactor_byInterpretation (ctx : DTSContext W) (ρ : ℚ) (enr lit : Set W)
    [DecidablePred (· ∈ enr)] [DecidablePred (· ∈ lit)]
    (hden : ρ * condProb ctx.prior enr ctx.topicᶜ +
      (1 - ρ) * condProb ctx.prior lit ctx.topicᶜ ≠ 0) :
    bayesFactor (withInterpretation ctx ρ) (byInterpretation enr lit) =
      (ρ * condProb ctx.prior enr ctx.topic + (1 - ρ) * condProb ctx.prior lit ctx.topic) /
      (ρ * condProb ctx.prior enr ctx.topicᶜ +
        (1 - ρ) * condProb ctx.prior lit ctx.topicᶜ) := by
  have hcompl : condProb (withInterpretation ctx ρ).prior (byInterpretation enr lit)
      ((withInterpretation ctx ρ).topicᶜ) =
      ρ * condProb ctx.prior enr ctx.topicᶜ + (1 - ρ) * condProb ctx.prior lit ctx.topicᶜ :=
    condProb_byInterpretation ctx ρ enr lit ctx.topicᶜ
  have htopic : condProb (withInterpretation ctx ρ).prior (byInterpretation enr lit)
      ((withInterpretation ctx ρ).topic) =
      ρ * condProb ctx.prior enr ctx.topic + (1 - ρ) * condProb ctx.prior lit ctx.topic :=
    condProb_byInterpretation ctx ρ enr lit ctx.topic
  rw [bayesFactor_unfold _ _ (hcompl ▸ hden), hcompl, htopic]

/-! ### Assertability in the example (§5.2) -/

/-- §5.2: the assertability context — bands crossed with the listener's interpretation,
enriching with probability 9/10. -/
def assertabilityContext : DTSContext (Band × Interpretation) :=
  withInterpretation successContext (9/10)

example : ∑ p : Band × Interpretation, assertabilityContext.prior p = 1 := by decide +kernel

instance (n cap : ℕ) : DecidablePred (· ∈ (moreThan n \ moreThan cap : Set Band)) := fun k =>
  inferInstanceAs (Decidable (k ∈ moreThan n ∧ k ∉ moreThan cap))

/-- Felicitous assertability of *more than n* whose enrichment is *not more than cap*: under
enrichment both the content and the implicature must hold; under literal interpretation only
the content. -/
def assertable (n cap : ℕ) : Set (Band × Interpretation) :=
  byInterpretation (moreThan n \ moreThan cap) (moreThan n)

instance (n cap : ℕ) : DecidablePred (· ∈ assertable n cap) := fun p =>
  inferInstanceAs (Decidable (p ∈ byInterpretation (moreThan n \ moreThan cap) (moreThan n)))

/-- §5.2's value for *more than 100* (enriched to *not more than 150*). The shape is
`bayesFactor_byInterpretation`: P(A(u)∣S) = (9/10)·(3/8) + (1/10)·1 = 35/80 against
P(A(u)∣¬S) = 1/6, giving Bayes factor 21/8 (the paper's log (21/8) = 0.419). -/
theorem assertable_bayesFactor_moreThan100 :
    bayesFactor assertabilityContext (assertable 100 150) = 21/8 := by decide +kernel

/-- §5.2's value for *more than 110* (enriched to *not more than 120*): the enriched reading
is incompatible with success, so P(A(u)∣S) = (9/10)·0 + (1/10)·1 = 1/10 against
P(A(u)∣¬S) = 1/12, giving Bayes factor 6/5 (the paper's log (6/5) = 0.079). -/
theorem assertable_bayesFactor_moreThan110 :
    bayesFactor assertabilityContext (assertable 110 120) = 6/5 := by decide +kernel

/-! ### The reversal -/

/-- Argumentative strength (eq. 17; eq. 25 on the assertability space): the log of the Bayes
factor, positive iff the utterance supports the goal. -/
noncomputable def strength (ctx : DTSContext W) (u : Set W) [DecidablePred (· ∈ u)] : ℝ :=
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
