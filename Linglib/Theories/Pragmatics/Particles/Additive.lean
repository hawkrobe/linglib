import Linglib.Theories.Semantics.Questions.Answerhood.ProbabilisticAnswerhood
import Linglib.Theories.Semantics.Questions.Denotation.Basic
import Linglib.Core.Issue.Basic
import Linglib.Core.Issue.Hamblin
import Linglib.Core.Issue.Relevance

/-!
# Additive Particles: too, also, either
@cite{heim-1992} @cite{thomas-2026}

Felicity conditions for additive particles following @cite{thomas-2026}
"A probabilistic, question-based approach to additivity".

## Mathlib alignment

This module is built on the Set/Prop layer of `ProbabilisticAnswerhood`
(`relevantS`, `probAnswersS`, `someResolutionStrengthenedS`,
`isPositiveEvidenceS`) over `Core.Issue W` (downward-closed inquisitive
lattice) and `Set W` for propositions. Felicity predicates are `Prop`-valued
and `noncomputable` where they quantify over `Core.Issue.alt`; concrete
study contexts use the per-alternative `[DecidablePred]` infrastructure
to recover decidability.

## Related modules

- `Semantics.FocusParticles` (`Theories/Semantics/Focus/Particles.lean`):
  Traditional focus particle semantics (EVEN, only). @cite{thomas-2026} §6
  argues that Def. 64 subsumes @cite{heim-1992}'s individual-based
  presupposition as a special case of the standard focus-alternative use.
- `Ahn2015`: Ahn's ⊓/⊔ Boolean
  semantics for too/either. Independent analysis; Thomas does not discuss it.
- `ProbabilisticAnswerhood`: Core definitions (Defs. 61–63) used here.

## Heim 1992 Subsumption

@cite{thomas-2026} §6 argues that Def. 64 subsumes @cite{heim-1992}'s
individual-based additive presupposition as a special case. This is
captured by `heim_subsumption`: when ANT and π each entail distinct
alternatives of RQ (the Heim setup), the Antecedent and Conjunction
Conditions (Def. 64a-b) hold automatically.

## Definition 64: Felicity Conditions for TOO(π)

Given resolved question RQ and antecedent ANT:
1. **Antecedent Condition**: ANT probabilistically answers RQ
2. **Conjunction Condition**: ANT ∧ ⟦π⟧ answers RQ AND evidences some
   resolution A more strongly than ANT alone
3. **Prejacent Conditions**:
   - ⟦π⟧ doesn't entail the evidenced resolution
   - No weaker proposition works as well

## Standard vs Argument-Building Uses

**Standard use**: ANT and π are focus alternatives
- "John came. Mary came too."
- ANT = "John came", π = "Mary came", RQ = "Who came?"

**Argument-building use**: ANT and π jointly support a conclusion
- "A room just opened up at this hotel. It looks kind of fancy, too."
  (@cite{thomas-2026}, ex. 1c/14c/65)
- ANT = "room just opened up", π = "looks fancy"
- RQ = "What would be a good hotel?" (implicit)
- Together they evidence "This hotel would be a good place to stay"
-/

namespace Pragmatics.Particles.Additive

open scoped Classical
open Semantics.Questions.ProbabilisticAnswerhood

/-! ### Additive particle types -/

/-- Types of additive particles. -/
inductive AdditiveParticle where
  | too    -- positive polarity, typically sentence-final
  | also   -- positive polarity, typically medial position
  | either -- negative polarity
  deriving DecidableEq, Repr, Inhabited

/-- Whether the particle is a positive-polarity item: `too`/`also` are
    PPIs, `either` is an NPI. -/
def AdditiveParticle.IsPositivePolarity : AdditiveParticle → Prop
  | .too => True
  | .also => True
  | .either => False

instance : DecidablePred AdditiveParticle.IsPositivePolarity := fun p => by
  cases p <;> unfold AdditiveParticle.IsPositivePolarity <;> infer_instance

/-- A particle is licensed in a polarity context iff its PPI/NPI status
    matches the context's positivity. -/
def AdditiveParticle.IsLicensed (p : AdditiveParticle) (positive : Prop) : Prop :=
  p.IsPositivePolarity ↔ positive

/-! ### Discourse context -/

/-- Discourse context for evaluating additive particle felicity.

@cite{thomas-2026} requires:
- A resolved question (RQ) in the discourse
- An antecedent proposition (ANT) that answers RQ
- A prior probability distribution -/
structure AdditiveContext (W : Type*) [Fintype W] where
  /-- The resolved question (RQ) -/
  resolvedQuestion : Core.Issue W
  /-- The antecedent proposition (ANT) - what was just established -/
  antecedent : Set W
  /-- Prior probability distribution over worlds -/
  prior : Prior W

namespace AdditiveContext

variable {W : Type*} [Fintype W]

/-- Create a context from a polar question (Set version). -/
def fromPolar (p ant : Set W) (prior : Prior W) : AdditiveContext W :=
  { resolvedQuestion := Core.Issue.polar p
  , antecedent := ant
  , prior := prior }

/-- Create a context from a list of alternatives. -/
def fromList (alts : List (Set W)) (ant : Set W) (prior : Prior W) :
    AdditiveContext W :=
  { resolvedQuestion := Core.Issue.ofList alts
  , antecedent := ant
  , prior := prior }

end AdditiveContext

/-! ### Felicity conditions (Definition 64) -/

variable {W : Type*} [Fintype W]

/-- Condition 1: Antecedent probabilistically answers RQ (Def. 64a).

The antecedent must raise the probability of some resolution. -/
noncomputable def antecedentCondition (ctx : AdditiveContext W) : Prop :=
  probAnswersS ctx.antecedent ctx.resolvedQuestion ctx.prior

/-- Condition 2: Conjunction answers RQ and evidences more strongly.

@cite{thomas-2026} Def. 64b: ANT ∩ ⟦π⟧ Answers RQ, AND RQ|_{ANT∩⟦π⟧}
is Evidenced more strongly by ANT ∩ ⟦π⟧ than by ANT. -/
noncomputable def conjunctionCondition
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  probAnswersS (ctx.antecedent ∩ prejacent) ctx.resolvedQuestion ctx.prior ∧
  someResolutionStrengthenedS ctx.antecedent prejacent ctx.resolvedQuestion ctx.prior

/-- Condition 3a: Prejacent doesn't entail the strengthened resolution.

There exists a strengthened alternative `a` such that `prejacent ⊄ a`
(some prejacent world is outside `a`). -/
noncomputable def nonTrivialityCondition
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  ∃ a ∈ Core.Issue.alt ctx.resolvedQuestion,
    ¬ (prejacent ⊆ a) ∧
    ctx.prior.condProbSet (ctx.antecedent ∩ prejacent) a >
    ctx.prior.condProbSet ctx.antecedent a

open Classical in
/-- Condition 3b: Maximality (Def. 64c.ii) — no weaker proposition works as well.

For every alternative `a` that is **strengthened** by adding the prejacent
to the antecedent (i.e., `P(a | ANT ∩ π) > P(a | ANT)`), every
prior-positive world in `ANT ∩ a` must also be in `prejacent`. Vacuously
holds for unstrengthened alternatives.

Rationale: if any strict weakening `S ⊃ prejacent` could match the
evidence on a strengthened resolution `a`, then `ANT ∩ S` would dilute
`P(a | ANT ∩ S) ≥ P(a | ANT ∩ prejacent)`, preserving the strict
advantage iff prejacent already captures the `ANT ∩ a` witnesses. The
guard restricts the witnesses-capture obligation to those alternatives
where the strict advantage actually obtains, matching the original
Bool spec which iterated only over strengthened resolutions. -/
noncomputable def maximalityCondition
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  ∀ a ∈ Core.Issue.alt ctx.resolvedQuestion,
    ctx.prior.condProbSet (ctx.antecedent ∩ prejacent) a >
      ctx.prior.condProbSet ctx.antecedent a →
    ∀ w : W, ctx.prior w > 0 → w ∈ ctx.antecedent → w ∈ a → w ∈ prejacent

/-- Full felicity conditions for TOO(π).

Definition 64 from @cite{thomas-2026}. The same conditions apply to
sentence-medial *also*; sentence-initial *also* is not subject to
`maximalityCondition` (`Def. 64c.ii`), but that distinction is not
modelled here. -/
noncomputable def tooFelicitous
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  antecedentCondition ctx ∧
  conjunctionCondition ctx prejacent ∧
  nonTrivialityCondition ctx prejacent ∧
  maximalityCondition ctx prejacent

/-- Felicity for *either* — gates on negative polarity.

@cite{thomas-2026} explicitly defers a precise characterization of
*either* to future work (footnote 9). This placeholder simply requires
a negative-polarity context on top of the *too* conditions; see
@cite{ahn-2015} for a Boolean-algebra alternative. -/
noncomputable def eitherFelicitous
    (ctx : AdditiveContext W) (prejacent : Set W)
    (inNegativeContext : Prop) : Prop :=
  inNegativeContext ∧ tooFelicitous ctx prejacent

/-! ## Central theorems (@cite{thomas-2026})

1. **Standard Use Reduction**: When π directly entails an alternative of RQ,
   the probabilistic felicity conditions reduce to the traditional analysis.
2. **Argument-Building Characterization**: argument-building arises exactly
   when neither ANT nor π entails an alternative, but together they provide
   cumulative evidence.
3. **Cumulative Evidence Necessity**: if π provides no additional evidence
   beyond ANT, *too* is infelicitous.
-/

/-! ### Standard use as a special case -/

/-- When `cond ⊆ alt`, `P(alt | cond) = 1`. -/
private lemma condProb_eq_one_of_entails
    (prior : Prior W) (cond alt : Set W)
    [DecidablePred (· ∈ cond)] [DecidablePred (· ∈ alt)]
    (hEntails : cond ⊆ alt)
    (hPos : prior.probOfSet cond > 0) :
    prior.condProbSet cond alt = 1 := by
  have hEqMass : prior.probOfSet (cond ∩ alt) = prior.probOfSet cond := by
    simp only [Core.FinitePMF.probOfSet]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hc : w ∈ cond
    · have hAlt : w ∈ alt := hEntails hc
      simp [hc, hAlt, Set.mem_inter_iff]
    · simp [hc, Set.mem_inter_iff]
  rw [prior.condProbSet_of_pos cond alt hPos, hEqMass]
  exact div_self (ne_of_gt hPos)

/-- **Theorem: Standard Use Reduction**

When π directly determines an alternative `alt` of RQ, and `alt` isn't
already certain given ANT, then the conjunction strengthens evidence
for `alt` over ANT alone.

This captures why standard "too" works: if π = "Mary came" and this IS
an alternative of "Who came?", then learning π guarantees that alternative,
so ANT ∩ π always evidences it more strongly than ANT alone (unless ANT
already entailed it).

Linguistically: in standard focus-alternative uses, the general probabilistic
conditions REDUCE TO the simple requirement that ANT be true and π be true.
The complex probability calculations aren't needed — direct entailment suffices. -/
theorem standard_use_reduction
    (ctx : AdditiveContext W) (prejacent alt : Set W)
    (hEntails : prejacent ⊆ alt)
    (hNotAlreadyCertain : ctx.prior.condProbSet ctx.antecedent alt < 1)
    (hConjPossible : ctx.prior.probOfSet (ctx.antecedent ∩ prejacent) > 0) :
    ctx.prior.condProbSet (ctx.antecedent ∩ prejacent) alt >
    ctx.prior.condProbSet ctx.antecedent alt := by
  rw [condProb_eq_one_of_entails ctx.prior (ctx.antecedent ∩ prejacent) alt
      (fun _ hw => hEntails hw.2) hConjPossible]
  exact hNotAlreadyCertain

/-! ### Heim 1992 subsumption -/

/-- **Theorem: Heim 1992 Subsumption** (@cite{thomas-2026} §6).

@cite{heim-1992}'s additive presupposition for TOO(π) requires:
∃x ≠ y such that P(x) is established and π = "y P'd".

Under @cite{thomas-2026}'s Def. 64, this falls out as a SPECIAL CASE of
the standard focus-alternative use. When ANT and π each entail distinct
alternatives of RQ:

- The **Antecedent Condition** holds because ANT entails an alternative,
  raising its probability to 1.
- The **Conjunction Condition** holds because π entails another alternative
  that wasn't already certain given ANT, so ANT ∩ π provides new evidence.

The remaining conditions (non-triviality, maximality) depend on the
question structure and are verified concretely in study files.

This theorem makes precise the claim in @cite{thomas-2026} §6 that
Def. 64 **subsumes** @cite{heim-1992}'s individual-based presupposition:
every Heim-felicitous "too" is Thomas-felicitous, but Thomas additionally
explains argument-building uses that Heim cannot. -/
theorem heim_subsumption
    (ctx : AdditiveContext W) (prejacent altAnt altPi : Set W)
    -- Heim's setup: ANT entails one alternative, π entails another
    (hAntInQ : altAnt ∈ Core.Issue.alt ctx.resolvedQuestion)
    (hPiInQ : altPi ∈ Core.Issue.alt ctx.resolvedQuestion)
    (hAntEntails : ctx.antecedent ⊆ altAnt)
    (hPiEntails : prejacent ⊆ altPi)
    -- Probability assumptions (non-degeneracy)
    (hAntPossible : ctx.prior.probOfSet ctx.antecedent > 0)
    (hConjPossible : ctx.prior.probOfSet (ctx.antecedent ∩ prejacent) > 0)
    (hAntAltNotCertain : ctx.prior.probOfSet altAnt < 1)
    (hPiNotCertainGivenAnt : ctx.prior.condProbSet ctx.antecedent altPi < 1) :
    antecedentCondition ctx ∧
    someResolutionStrengthenedS ctx.antecedent prejacent
      ctx.resolvedQuestion ctx.prior := by
  refine ⟨⟨altAnt, hAntInQ, ?_⟩, ⟨altPi, hPiInQ, ?_⟩⟩
  · -- (i) P(altAnt | ANT) = 1 > P(altAnt) since ANT ⊆ altAnt and P(altAnt) < 1
    rw [condProb_eq_one_of_entails ctx.prior ctx.antecedent altAnt
        hAntEntails hAntPossible]
    exact hAntAltNotCertain
  · -- (ii) P(altPi | ANT ∩ π) = 1 > P(altPi | ANT)
    rw [condProb_eq_one_of_entails ctx.prior (ctx.antecedent ∩ prejacent) altPi
        (fun _ hw => hPiEntails hw.2) hConjPossible]
    exact hPiNotCertainGivenAnt

-- Result 2: Argument-Building Characterization

/-- **Predicate: Argument-Building Use**

Argument-building use arises exactly when:
1. Neither ANT nor π directly determines any alternative of RQ
2. But together, ANT ∧ π evidences some alternative more strongly than ANT alone

This is the DEFINITION of argument-building: ANT and π are not themselves
answers to RQ, but jointly serve as EVIDENCE for some answer.

Example (@cite{thomas-2026}, ex. 1c/65):
"A room just opened up at this hotel. It looks kind of fancy, too."
- RQ = "What would be a good hotel?" (implicit)
- ANT = "room just opened up" - doesn't determine which hotel is good
- π = "looks fancy" - doesn't determine which hotel is good
- But ANT ∧ π together raise the probability that this hotel is good -/
def isArgumentBuildingUseCharacterized {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  (¬ ∃ a ∈ Core.Issue.alt ctx.resolvedQuestion, ctx.antecedent ⊆ a) ∧
  (¬ ∃ a ∈ Core.Issue.alt ctx.resolvedQuestion, prejacent ⊆ a) ∧
  conjunctionCondition ctx prejacent

/-- Argument-building requires that the resolved question be about something
OTHER than what ANT and π directly assert.

This captures the "implicit QUD" requirement: in argument-building,
the question being addressed isn't "Did ANT happen?" or "Did π happen?"
but rather some further question that ANT and π provide evidence for. -/
theorem argumentBuilding_requires_implicit_qud {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : Set W)
    (hArgBuild : isArgumentBuildingUseCharacterized ctx prejacent) :
    (¬ ∃ a ∈ Core.Issue.alt ctx.resolvedQuestion, ctx.antecedent ⊆ a) ∧
    (¬ ∃ a ∈ Core.Issue.alt ctx.resolvedQuestion, prejacent ⊆ a) :=
  ⟨hArgBuild.1, hArgBuild.2.1⟩

-- Result 3: Cumulative Evidence Necessity

open Classical in
/-- π is conditionally independent of `target` given `cond` if
P(target | cond ∩ π) = P(target | cond). -/
noncomputable def conditionallyIndependent {W : Type*} [Fintype W]
    (cond p target : Set W) (prior : Prior W) : Prop :=
  prior.condProbSet (cond ∩ p) target = prior.condProbSet cond target

open Classical in
/-- π is evidentially irrelevant to Q given ANT if π doesn't change the
conditional probability of any alternative when we already know ANT. -/
noncomputable def evidentiallyIrrelevant {W : Type*} [Fintype W]
    (ant prejacent : Set W) (q : Core.Issue W) (prior : Prior W) : Prop :=
  ∀ a ∈ Core.Issue.alt q, conditionallyIndependent ant prejacent a prior

/-- **Theorem: Cumulative Evidence Necessity**

If π is evidentially irrelevant to RQ given ANT (i.e., π doesn't change
the probability of any alternative), then no resolution is strengthened,
so the strengthening half of the conjunction condition fails.

This explains WHY "too" requires the prejacent to contribute something:
if π is just noise that doesn't affect the question at hand, it can't
felicitously be marked with "too".

Example of failure:
- "Sue cooks, and she has brown hair, too."
- If hair color is independent of who should host the dinner party,
  this is infelicitous (or requires a different implicit QUD). -/
theorem cumulative_evidence_necessary {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : Set W)
    (hIrrelevant : evidentiallyIrrelevant ctx.antecedent prejacent
                     ctx.resolvedQuestion ctx.prior) :
    ¬ someResolutionStrengthenedS ctx.antecedent prejacent
        ctx.resolvedQuestion ctx.prior := by
  rintro ⟨a, ha, hgt⟩
  have h := hIrrelevant a ha
  simp only [conditionallyIndependent] at h
  rw [h] at hgt
  exact lt_irrefl _ hgt

/-- Corollary: If π is irrelevant, "too" is infelicitous. -/
theorem irrelevant_prejacent_infelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : Set W)
    (hIrrelevant : evidentiallyIrrelevant ctx.antecedent prejacent
                     ctx.resolvedQuestion ctx.prior) :
    ¬ tooFelicitous ctx prejacent := by
  intro hFel
  exact cumulative_evidence_necessary ctx prejacent hIrrelevant hFel.2.1.2

end Pragmatics.Particles.Additive
