import Linglib.Theories.Discourse.Coherence.Centering.Coherence
import Linglib.Theories.Discourse.Coherence.Centering.Rules
import Linglib.Theories.Discourse.Coherence.Centering.Instances.GrammaticalRole

/-!
# Centering ↔ Coherence Bridge — Combined Predictions
@cite{grosz-joshi-weinstein-1995} @cite{kehler-2002} @cite{poesio-stevenson-eugenio-hitzeman-2004}

The connection between Centering's transition typology and
@cite{kehler-2002}'s coherence-relation typology, lifted to the level
of Rule 2's pair-of-transitions preference.

The basic mapping `CoherenceRelation.preferredTransition` lives in
`Theories/Discourse/Centering/Coherence.lean`. This bridge is one level
up: it joins that mapping with the pair-of-transitions ranking from
`Rules.lean` to give a *coherence-pair preference* prediction. The
upshot: any pair of utterances connected by a continuation-licensing
relation is more coherent (in Rule 2's sense) than any pair connected
by a shifting-licensing relation, with retaining-licensing relations in
between.

This sits in the pragmatics-discourse interface because Centering is
typically classified as a pragmatic theory of local coherence whereas
@cite{kehler-2002}'s coherence relations are discourse-structural.
-/

set_option autoImplicit false

namespace Interfaces.PragmaticsDiscourse.CenteringCoherence

open Discourse.Coherence.Centering
open Core.Discourse.Coherence

/-- The Rule-2 score implied by a pair of consecutive coherence
    relations: convert each to its preferred transition and sum the
    transition ranks. -/
def coherencePairScore (r₁ r₂ : CoherenceRelation) : Nat :=
  pairRank (Discourse.Coherence.Centering.CoherenceRelation.preferredTransition r₁)
           (Discourse.Coherence.Centering.CoherenceRelation.preferredTransition r₂)

/-- A pair of explanation/result relations achieves the maximum
    Rule-2 score (both transitions are continuations). -/
theorem causal_pair_max_score :
    coherencePairScore .explanation .result =
    pairRank .continuation .continuation := rfl

/-- A pair of contrast/correction relations achieves the minimum
    nonzero Rule-2 score (both transitions are shifts). -/
theorem substitution_pair_min_score :
    coherencePairScore .contrast .correction =
    pairRank .shifting .shifting := rfl

/-- The combined prediction: causal/elaborative coherence pairs are
    Rule-2-preferred over substitution coherence pairs. -/
theorem causal_pair_preferred_over_substitution :
    coherencePairScore .explanation .result >
    coherencePairScore .contrast .correction := by decide

end Interfaces.PragmaticsDiscourse.CenteringCoherence
