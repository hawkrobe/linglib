import Linglib.Theories.Semantics.Noun.Kind.Generics
import Linglib.Theories.Semantics.Quantification.CovertQuantifier

/-!
# @cite{cohen-1999a}: Probability-Based Generic Quantification

Ariel Cohen, *Think Generic! The Meaning and Use of Generic Sentences*, 1999.

## Core Proposal

Cohen proposes that the generic quantifier GEN is a probability operator:

    GEN(P, Q) is true iff P(Q | P) > 0.5

That is, a generic "Ps are Q" is true iff the conditional probability of
an object having property Q, given that it has property P, exceeds 0.5.

This contrasts with the frequency adverb *always*, which requires
P(Q | P) = 1.

## Connection to Threshold Semantics

Cohen's GEN is a special case of threshold semantics with θ = 1/2.
In linglib's infrastructure, `cohenGEN` is definitionally equal to
`thresholdGeneric situations restrictor scope (1/2)`.

## Homogeneity Constraint

Cohen introduces a **homogeneity** presupposition: the conditional
probability P(Q | P) must be uniform across all suitable partitions
of the domain. If the domain splits into subgroups with different
rates, the generic presupposition fails and the sentence is neither
true nor false.

This constraint is discussed in the introduction to *Genericity*
(Mari, Beyssade, Del Prete, OUP 2013):

> "A homogeneity requirement is introduced as a presupposition of
> generics and frequency statements, according to which the relative
> probability in every part of a suitable partition of any admissible
> history H must be the same as the probability in the whole H."

## Nickel's Critique (@cite{nickel-2009})

@cite{nickel-2009} shows that even with homogeneity, the majority-based
view cannot handle conjunctive generics like "Elephants live in Africa
and Asia." If this is equivalent to the conjunction "Elephants live in
Africa AND Elephants live in Asia," then both conjuncts would need to
hold with probability > 0.5, which is impossible if the populations
are disjoint. See `Phenomena/Generics/Studies/Nickel2009.lean`.
-/

namespace Cohen1999

open Core (Situation)

open Semantics.Noun.Kind.Generics
open Semantics.Quantification.CovertQuantifier
-- Cohen's Probability-Based GEN

/-- Cohen's GEN: a generic "Ps are Q" is true iff the conditional probability
    P(Q | P) exceeds 0.5.

    `prevalence situations restrictor scope` computes exactly this conditional
    probability: the proportion of restrictor-satisfying situations where scope
    holds. So Cohen's GEN is `prevalence > 1/2`. -/
def cohenGEN
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : Bool :=
  prevalence situations restrictor scope > 1/2

/-- Cohen's GEN is a special case of threshold semantics with θ = 1/2. -/
theorem cohen_is_threshold
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : cohenGEN situations restrictor scope =
      thresholdGeneric situations restrictor scope (1/2) := rfl

/-- Cohen's "always" requires conditional probability = 1 (no exceptions). -/
def cohenAlways
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : Bool :=
  prevalence situations restrictor scope == 1

-- Homogeneity Constraint

/-- Cohen's homogeneity constraint: the conditional probability P(scope | restrictor)
    must be the same in every non-empty sub-partition of the domain.

    Formally: for any sub-predicate `part`, if there are restrictor-satisfying
    elements in that partition, the proportion of scope-satisfying elements among
    `restrictor ∧ part` elements equals the overall proportion among `restrictor`
    elements.

    This is P(Q | P ∧ Pᵢ) = P(Q | P) for all partition cells Pᵢ.

    When homogeneity fails, the generic presupposition fails and the sentence
    is neither true nor false. -/
def homogeneous
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : Prop :=
  ∀ (part : Situation → Bool),
    (situations.filter (λ s => restrictor s && part s)).length > 0 →
    measure situations (λ s => restrictor s && part s) scope =
    measure situations restrictor scope

/-- A generic assertion according to Cohen: the prevalence exceeds 0.5
    AND the homogeneity presupposition is satisfied. -/
structure CohenGenericJudgment where
  situations : List Situation
  restrictor : Restrictor
  scope : Scope
  truth : Bool := cohenGEN situations restrictor scope
  presupposition : Prop := homogeneous situations restrictor scope

-- Examples

section DogsBark

/-- Ten situations: 8 with a barking dog, 2 with a sleeping dog. -/
def dogSituations : List Situation :=
  (List.range 10).map (λ n => ⟨n⟩)

def isDog : Restrictor := λ _ => true

def barks : Scope := λ s => s.id < 8

-- "Dogs bark" is true on Cohen's account: prevalence = 8/10 > 1/2
#guard cohenGEN dogSituations isDog barks

-- Prevalence is 4/5
#guard prevalence dogSituations isDog barks == 4/5

-- "Dogs always bark" is false: prevalence ≠ 1
#guard !cohenAlways dogSituations isDog barks

end DogsBark

section BirdsFly

/-- Birds: 80 flying, 20 non-flying (penguins, ostriches). -/
def birdSituations : List Situation :=
  (List.range 100).map (λ n => ⟨n⟩)

def isBird : Restrictor := λ _ => true

def flies : Scope := λ s => s.id < 80

-- "Birds fly" is true: prevalence = 80/100 = 4/5 > 1/2
#guard cohenGEN birdSituations isBird flies

end BirdsFly

-- Cohen GEN vs Traditional GEN

/-- When traditional GEN is true (all normal restrictor-cases satisfy scope),
    and the normal+restrictor cases are a majority, Cohen's GEN is also true.

    This shows agreement in the typical case: the traditional analysis with a
    well-chosen normalcy predicate yields the same truth value as the
    probability-based analysis. -/
theorem traditional_true_majority_implies_cohen
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    (_hTrad : traditionalGEN situations normal restrictor scope = true)
    (hMajority : prevalence situations restrictor scope > 1/2)
    : cohenGEN situations restrictor scope = true := by
  simp only [cohenGEN, decide_eq_true_iff]
  exact hMajority

-- The Key Advantage: No Hidden Parameters

/-!
## Cohen's Advantage over Traditional GEN

Traditional GEN has a hidden **normalcy** parameter that does all the
explanatory work. Cohen's probability-based GEN eliminates this parameter:
the threshold 0.5 is fixed, and the truth value is determined by observable
prevalence.

However, Cohen's approach faces its own challenges:

1. **Rare property generics**: "Mosquitoes carry malaria" is judged true
   despite prevalence well below 50%. Cohen must either deny these are
   true generics or invoke the homogeneity constraint.

2. **Conjunctive generics**: @cite{nickel-2009}'s "Elephants live in Africa
   and Asia" shows the majority-based view predicts the wrong truth conditions
   for conjoined habitat claims.

3. **Striking property generics**: "Sharks attack swimmers" — low prevalence
   but judged true. @cite{tessler-goodman-2019}'s RSA account handles this
   via pragmatic reasoning over priors, not a fixed threshold.
-/

-- Rare Property Problem

section RareProperty

/-- Mosquitoes: only ~1% carry malaria. -/
def mosquitoSituations : List Situation :=
  (List.range 100).map (λ n => ⟨n⟩)

def isMosquito : Restrictor := λ _ => true

def carriesMalaria : Scope := λ s => s.id == 0

-- "Mosquitoes carry malaria" is FALSE on Cohen's account (prevalence = 1/100),
-- even though speakers judge it true.
-- This is the key empirical challenge for fixed-threshold approaches.
#guard !cohenGEN mosquitoSituations isMosquito carriesMalaria

/-- Cohen's prediction conflicts with empirical judgments (@cite{leslie-2008}):
    "Mosquitos carry malaria" has prevalence ~1/100 but judgment ~85/100 (clearly
    true). Cohen predicts false (1/100 < 1/2). -/
theorem cohen_wrong_on_mosquitoes :
    (1 : ℚ) / 100 < 1/2 ∧ (85 : ℚ) / 100 > 1/2 := by
  constructor <;> norm_num

end RareProperty

-- Homogeneity Failure Example

section HomogeneityFailure

/-- A domain that VIOLATES homogeneity: urban vs rural dogs.
    Urban dogs bark more (all 5 bark), rural dogs bark less (1 of 5 barks).
    Overall prevalence = 6/10, but the partition into urban/rural shows
    different rates (5/5 vs 1/5). -/
def mixedDogSituations : List Situation :=
  (List.range 10).map (λ n => ⟨n⟩)

def allDogs : Restrictor := λ _ => true

def mixedBarks : Scope := λ s =>
  if s.id < 5 then true       -- urban dogs: all bark
  else s.id == 5              -- rural dogs: only one barks

def urbanPartition : Situation → Bool := λ s => s.id < 5

-- Overall prevalence = 6/10 = 3/5
#guard prevalence mixedDogSituations allDogs mixedBarks == 3/5

-- Urban prevalence = 5/5 = 1
#guard measure mixedDogSituations (λ s => allDogs s && urbanPartition s) mixedBarks == 1

-- Rural prevalence = 1/5
#guard measure mixedDogSituations (λ s => allDogs s && !urbanPartition s) mixedBarks == 1/5

-- The generic "Dogs bark" passes the > 0.5 test...
#guard cohenGEN mixedDogSituations allDogs mixedBarks

-- ...but FAILS homogeneity: urban (1) ≠ overall (3/5)
#guard measure mixedDogSituations (λ s => allDogs s && urbanPartition s) mixedBarks ≠
       measure mixedDogSituations allDogs mixedBarks

end HomogeneityFailure

-- Connection to GEN Eliminability

/-- Cohen's account is itself a special case of the general GEN eliminability
    result in `Comparisons/GenericSemantics.lean`. While that theorem shows
    ANY GEN configuration can be matched by SOME threshold, Cohen's contribution
    is fixing the threshold at 0.5 and adding the homogeneity presupposition. -/
theorem cohen_fixes_threshold :
    ∀ (situations : List Situation) (restrictor : Restrictor) (scope : Scope),
    cohenGEN situations restrictor scope =
    thresholdGeneric situations restrictor scope (1/2) :=
  λ _ _ _ => rfl

end Cohen1999
