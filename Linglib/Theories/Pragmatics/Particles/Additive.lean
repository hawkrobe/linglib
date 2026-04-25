import Linglib.Theories.Semantics.Questions.Answerhood.ProbabilisticAnswerhood
import Linglib.Theories.Semantics.Questions.Denotation.Basic
import Linglib.Core.Question.Basic

/-!
# Additive Particles: too, also, either
@cite{thomas-2026}

Felicity conditions for additive particles following @cite{thomas-2026}
"A probabilistic, question-based approach to additivity".

## Mathlib alignment

This module is built on the Set/Prop layer of `ProbabilisticAnswerhood`
(`probAnswersS`, `someResolutionStrengthenedS`) over `Core.Question W`
(downward-closed inquisitive lattice) and `Set W` for propositions.
Felicity predicates are `Prop`-valued and `noncomputable` where they
quantify over `Core.Question.alt`; concrete study contexts use the
per-alternative `[DecidablePred]` infrastructure to recover decidability.

## Related modules

- `Semantics.FocusParticles` (`Theories/Semantics/Focus/Particles.lean`):
  Traditional focus particle semantics (EVEN, only).
- `Phenomena.Focus.AdditiveParticles.Studies.Ahn2015`: Ahn's ⊓/⊔ Boolean
  semantics for too/either. Independent analysis; Thomas does not
  discuss it.
- `Phenomena.Focus.AdditiveParticles.Studies.Thomas2026`: end-to-end
  verification of Def. 64 on `Fin 4` scenarios, plus the abstract
  theorems characterising standard-use reduction, Heim-style setups,
  and the necessity of cumulative evidence.

## Definition 64: Felicity Conditions for TOO(π)

Given resolved question RQ and antecedent ANT (PDF lines 1554-1592):

1. **Antecedent Condition** (64a): ANT Answers RQ.
2. **Conjunction Condition** (64b): ANT ∩ ⟦π⟧ Answers RQ AND
   `RQ|_{ANT∩⟦π⟧}` is Evidenced more strongly by ANT ∩ ⟦π⟧ than by ANT.
3. **Prejacent Conditions** (64c):
   - (i) `⟦π⟧ ̸⊆ RQ|_{ANT∩⟦π⟧}` — prejacent does not entail the strengthened
     resolution.
   - (ii) For every `S ⊃ ⟦π⟧`, ANT ∩ ⟦π⟧ Evidences `RQ|_{ANT∩⟦π⟧}` more
     strongly than ANT ∩ S does (maximality / no weaker-prejacent works
     as well).

## Standard vs argument-building uses

**Standard use**: ANT and π are focus alternatives.
- "John came. Mary came too." — ANT = "John came", π = "Mary came",
  RQ = "Who came?".

**Argument-building use** (Thomas 2026 §1, §3): ANT and π jointly
support a conclusion they neither entail individually.
- "A room just opened up at this hotel. It looks kind of fancy, too."
  (Thomas 2026, ex. 1c/14c/65). ANT = "room just opened up",
  π = "looks fancy", RQ = "What would be a good hotel?".

The treatment of *also* and *either* is sketched in §6 as future work;
this file models *too* directly and provides placeholder predicates
for the other particles per Thomas's footnote 9.
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

/-! ### Discourse context -/

/-- Discourse context for evaluating additive particle felicity.

@cite{thomas-2026} requires:
- A resolved question (RQ) in the discourse
- An antecedent proposition (ANT) that answers RQ
- A prior probability distribution -/
structure AdditiveContext (W : Type*) [Fintype W] where
  /-- The resolved question (RQ) -/
  resolvedQuestion : Core.Question W
  /-- The antecedent proposition (ANT) - what was just established -/
  antecedent : Set W
  /-- Prior probability distribution over worlds -/
  prior : Prior W

/-! ### Felicity conditions (Definition 64) -/

variable {W : Type*} [Fintype W]

/-- Condition 1: Antecedent probabilistically answers RQ (Def. 64a).

The antecedent must raise the probability of some resolution. -/
noncomputable def antecedentCondition (ctx : AdditiveContext W) : Prop :=
  probAnswersS ctx.antecedent ctx.resolvedQuestion ctx.prior

/-- Condition 2: Conjunction answers RQ and evidences more strongly.

@cite{thomas-2026} Def. 64b: ANT ∩ ⟦π⟧ Answers RQ, AND `RQ|_{ANT∩⟦π⟧}`
is Evidenced more strongly by ANT ∩ ⟦π⟧ than by ANT. -/
noncomputable def conjunctionCondition
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  probAnswersS (ctx.antecedent ∩ prejacent) ctx.resolvedQuestion ctx.prior ∧
  someResolutionStrengthenedS ctx.antecedent prejacent ctx.resolvedQuestion ctx.prior

/-- Condition 3a: Prejacent doesn't entail the strengthened resolution
(Def. 64c.i, literal form): `⟦π⟧ ̸⊆ ⋂₀ T` for every conditional answer `T`
(Thomas's `RQ|_R` is `⋂₀ T`). Quantifies universally over conditional
answers since `IsConditionalAnswer.unique` is not derivable from Def. 62
alone. -/
noncomputable def nonTrivialityCondition
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  ∀ T : Set (Set W),
    IsConditionalAnswer (ctx.antecedent ∩ prejacent) ctx.resolvedQuestion
      ctx.prior T →
    ¬ prejacent ⊆ ⋂₀ T

/-- Condition 3b: Maximality (Def. 64c.ii, literal weakening-comparison
form): for every conditional answer `T` and every `S ⊋ ⟦π⟧`,
`condProbSet (ANT ∩ ⟦π⟧) (⋂₀ T) > condProbSet (ANT ∩ S) (⋂₀ T)`.

Includes the implicit non-trivial-weakening precondition
`P(ANT ∩ S) > P(ANT ∩ ⟦π⟧)`; without it the literal text has
measure-zero pathology on Thomas's own felicitous scenarios (e.g.
`S = ⟦π⟧ ∪ {w}` for `w ∉ ANT` gives equal conditional probabilities).
Thomas's worked example (68) at PDF lines 1871-1877 exhibits this
precondition implicitly. -/
noncomputable def maximalityCondition
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  ∀ T : Set (Set W),
    IsConditionalAnswer (ctx.antecedent ∩ prejacent) ctx.resolvedQuestion
      ctx.prior T →
    ∀ S : Set W, prejacent ⊂ S →
      ctx.prior.probOfSet (ctx.antecedent ∩ S) >
        ctx.prior.probOfSet (ctx.antecedent ∩ prejacent) →
      ctx.prior.condProbSet (ctx.antecedent ∩ prejacent) (⋂₀ T) >
        ctx.prior.condProbSet (ctx.antecedent ∩ S) (⋂₀ T)

/-- Full felicity conditions for TOO(π).

Definition 64 from @cite{thomas-2026}. The same conditions apply to
sentence-medial *also*; sentence-initial *also* is not subject to
`maximalityCondition` (Def. 64c.ii) per @cite{thomas-2026} §6, but
that distinction is not modelled here. -/
noncomputable def tooFelicitous
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  antecedentCondition ctx ∧
  conjunctionCondition ctx prejacent ∧
  nonTrivialityCondition ctx prejacent ∧
  maximalityCondition ctx prejacent

/-- Felicity for *either* — gates on negative polarity.

@cite{thomas-2026} explicitly defers a precise characterization of
*either* to future work (footnote 9): "A precise characterization of
the felicity conditions of either must be left to future work." This
placeholder simply requires a negative-polarity context on top of the
*too* conditions; see `Phenomena.Focus.AdditiveParticles.Studies.Ahn2015`
for a Boolean-algebra alternative. -/
noncomputable def eitherFelicitous
    (ctx : AdditiveContext W) (prejacent : Set W)
    (inNegativeContext : Prop) : Prop :=
  inNegativeContext ∧ tooFelicitous ctx prejacent

/-! ### Generic helper -/

/-- When `cond ⊆ alt`, `P(alt | cond) = 1`. Generic PMF lemma; promoted
out of `private` so paper-specific study files can reuse it. -/
lemma condProb_eq_one_of_entails
    (prior : Prior W) (cond alt : Set W)
    (hEntails : cond ⊆ alt)
    (hPos : prior.probOfSet cond > 0) :
    prior.condProbSet cond alt = 1 := by
  have hEqMass : prior.probOfSet (cond ∩ alt) = prior.probOfSet cond :=
    congrArg prior.probOfSet (Set.inter_eq_left.mpr hEntails)
  rw [PMF.condProbSet_eq_div, hEqMass]
  exact ENNReal.div_self hPos.ne' (PMF.probOfSet_ne_top prior cond)

end Pragmatics.Particles.Additive
