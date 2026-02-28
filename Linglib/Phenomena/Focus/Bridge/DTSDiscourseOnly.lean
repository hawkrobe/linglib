import Linglib.Theories.Semantics.Lexical.Particle.DiscourseOnly
import Linglib.Theories.Pragmatics.DecisionTheoretic.But
import Linglib.Theories.Pragmatics.DecisionTheoretic.Core
import Linglib.Phenomena.Focus.DiscourseOnly

/-!
# Bridge: DTS ↔ Discourse *only*

Connects the CI of discourse *only* (Ippolito, Kiss & Williams 2025) to
Merin's (1999) Decision-Theoretic Semantics, specifically the notion of
unexpectedness from the analysis of *but*.

## Key Connection

Both *but* and discourse *only* express a form of evidential contrast:

- *but*: A is positively relevant and B is negatively relevant to H
  → B is unexpected given A (Theorem 8)
- discourse *only*: S supports α but S' does not support α
  → S' undermines the evidential direction

## The *but*/*only* Asymmetry (IKW 2025 §6)

*but* requires `negRelevant` (BF < 1): the second clause must actively
provide counter-evidence. Discourse *only* only requires `¬probSupports`:
the second clause merely fails to support the direction. Since
`negRelevant → ¬probSupports` (anti-support implies non-support), *but*'s
condition is strictly stronger. This means every *but* context could license
discourse *only*, but not vice versa.

## Architecture

```
Support.lean           → probSupports / probAntiSupports (probabilistic)
    ↕ (this bridge)
DecisionTheoretic/Core → posRelevant / negRelevant (Bayes factor)
DecisionTheoretic/But  → cip_contrariness_implies_unexpectedness
```

## References

- Ippolito, Kiss & Williams (2025). Discourse *only*. WCCFL 41.
- Merin (1999). Information, relevance, and social decisionmaking.
-/

namespace Phenomena.Focus.Bridge.DTSDiscourseOnly

open Core.Proposition
open Semantics.Questions.Inquisitive hiding supports
open Semantics.Questions.ProbabilisticAnswerhood
open Semantics.Questions.Support
open Semantics.Lexical.Particle.DiscourseOnly
open Theories.DTS
open Theories.DTS.But

-- Binary Issue Conversion

/-- Convert a DTS dichotomic issue {H, ¬H} to an inquisitive `Issue`.

A DTS `Issue W` is a single topic H (with ¬H implicit). The corresponding
inquisitive issue has two alternatives: H and ¬H. -/
def dtsToInquisitive {W : Type*} (topic : BProp W) : Semantics.Questions.Inquisitive.Issue W :=
  Semantics.Questions.Inquisitive.Issue.polar topic

/-- The DTS issue and inquisitive issue have matching alternatives. -/
theorem dtsToInquisitive_alternatives {W : Type*} (topic : BProp W) :
    (dtsToInquisitive topic).alternatives = [topic, λ w => !topic w] := rfl

-- Witness Structure

/-- A witness for the discourse *only* → DTS unexpectedness connection.

Bundles a DTS context, a discourse *only* configuration (as raw propositions
for the binary case), and evidence that S is positively relevant to the
topic H. Unlike the *but* witness, this does NOT require S' to be negatively
relevant — discourse *only* only requires S' to fail to support, which is
strictly weaker than negative relevance. -/
structure DTSDiscourseOnlyWitness (W : Type*) [Fintype W] where
  /-- The DTS context (dichotomic issue H + prior) -/
  dtsCtx : DTSContext W
  /-- Left clausal argument S (as a proposition for the binary case) -/
  s : W → Bool
  /-- Right clausal argument S' (as a proposition for the binary case) -/
  s' : W → Bool
  /-- S is positively relevant to H -/
  sPosRelevant : posRelevant dtsCtx s

-- Bridge Theorems

/-- For binary issues, probabilistic `probSupports` (P(H|S) > P(H)) is
equivalent to DTS `posRelevant` (BF_H(S) > 1).

Both capture the same intuition — S provides evidence for H — but via
different formalizations: `probSupports` uses the absolute probability boost,
while `posRelevant` uses the Bayes factor ratio.

Proof sketch: For binary issue {H, ¬H}, `probSupports prior S H` means
P(H|S) > P(H), i.e., `evidentialBoost S H prior > 0`. Meanwhile,
`posRelevant ctx S` means `bayesFactor ctx S > 1`, i.e.,
P(S|H)/P(S|¬H) > 1, i.e., P(S|H) > P(S|¬H). By Bayes' theorem,
P(H|S) > P(H) ↔ P(S|H) > P(S) ↔ P(S|H) > P(S|H)P(H) + P(S|¬H)P(¬H)
↔ P(S|H)(1−P(H)) > P(S|¬H)P(¬H) ↔ P(S|H)P(¬H) > P(S|¬H)P(¬H)
↔ P(S|H) > P(S|¬H) (when P(¬H) > 0) ↔ BF > 1. -/
theorem probSupports_iff_posRelevant_binary {W : Type*} [Fintype W]
    (prior : Prior W) (topic : BProp W) (evidence : W → Bool)
    (hH_pos : probOfProp prior topic > 0)
    (hNH_pos : probOfProp prior (λ w => !topic w) > 0)
    (hS_pos : probOfProp prior evidence > 0) :
    probSupports prior evidence topic = true →
    posRelevant ⟨⟨topic⟩, prior⟩ evidence := by
  sorry

/-- Negative relevance (DTS) implies non-support (probabilistic).

If S' is negatively relevant to H (BF < 1, i.e., P(S'|H) < P(S'|¬H)),
then S' does not probabilistically support H. This is the formal content
of IKW's observation that *but*'s condition on the second clause is strictly
stronger than discourse *only*'s.

Proof sketch: negRelevant means BF < 1, i.e., P(S'|H)/P(S'|¬H) < 1.
By the Bayes theorem argument (reverse of above), this gives P(H|S') < P(H),
i.e., evidentialBoost < 0, which means isNegativeEvidence = true. Since
evidentialBoost < 0 ↔ ¬(evidentialBoost > 0), we get ¬isPositiveEvidence
= ¬probSupports. -/
theorem negRelevant_implies_not_probSupports {W : Type*} [Fintype W]
    (prior : Prior W) (topic : BProp W) (evidence : W → Bool)
    (hH_pos : probOfProp prior topic > 0)
    (hNH_pos : probOfProp prior (λ w => !topic w) > 0)
    (hS_pos : probOfProp prior evidence > 0)
    (hNeg : negRelevant ⟨⟨topic⟩, prior⟩ evidence) :
    probSupports prior evidence topic = false := by
  sorry

/-- Every *but* context can license discourse *only*.

When S is posRelevant and S' is negRelevant (the *but* condition), S'
also fails to probabilistically support H (the *only* condition). This
formalizes IKW (2025) §6's claim that discourse *only* is strictly weaker
than *but*. -/
theorem but_sufficient_for_only {W : Type*} [Fintype W]
    (prior : Prior W) (topic : BProp W)
    (s s' : W → Bool)
    (hH_pos : probOfProp prior topic > 0)
    (hNH_pos : probOfProp prior (λ w => !topic w) > 0)
    (_hS_pos : probOfProp prior s > 0)
    (hS'_pos : probOfProp prior s' > 0)
    (_hSpos : posRelevant ⟨⟨topic⟩, prior⟩ s)
    (hS'neg : negRelevant ⟨⟨topic⟩, prior⟩ s') :
    probSupports prior s' topic = false :=
  negRelevant_implies_not_probSupports prior topic s' hH_pos hNH_pos hS'_pos hS'neg

/-- Discourse *only*'s CI implies unexpectedness when the QUD is binary,
S' is negatively relevant, and CIP holds.

When S is posRelevant and S' is negRelevant (the stronger *but* condition),
Merin's Theorem 8 gives P(S'|S) < P(S'): S' is unexpected given S.

Note: this theorem uses the stronger *but* condition (negRelevant) rather than
the weaker discourse *only* condition (¬probSupports). Unexpectedness in
Merin's sense requires active counter-relevance, not just failure to support.
This means unexpectedness is a consequence when discourse *only* sentences
happen to meet the stronger *but* threshold. -/
theorem discOnly_implies_unexpectedness_under_but {W : Type*} [Fintype W]
    (w : DTSDiscourseOnlyWitness W)
    (hS'neg : negRelevant w.dtsCtx w.s')
    (hPrior : ∀ x, w.dtsCtx.prior x ≥ 0)
    (hNorm : probSum w.dtsCtx.prior (Decidable.top W) = 1)
    (hS_pos : 0 < probSum w.dtsCtx.prior w.s)
    (hH_pos : 0 < probSum w.dtsCtx.prior w.dtsCtx.issue.topic)
    (hNH_pos : 0 < probSum w.dtsCtx.prior (Decidable.pnot W w.dtsCtx.issue.topic))
    (hCIP : CIP w.dtsCtx w.s w.s') :
    condProb w.dtsCtx.prior w.s' w.s <
    margProb w.dtsCtx.prior w.s' := by
  exact cip_contrariness_implies_unexpectedness w.dtsCtx w.s w.s'
    hPrior hNorm hCIP (.inl ⟨w.sPosRelevant, hS'neg⟩) hS_pos hH_pos hNH_pos

end Phenomena.Focus.Bridge.DTSDiscourseOnly
