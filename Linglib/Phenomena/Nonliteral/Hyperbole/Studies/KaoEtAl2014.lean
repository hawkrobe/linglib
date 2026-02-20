/-!
# Kao et al. (2014) — Empirical Data @cite{kao-etal-2014-hyperbole}

"Nonliteral understanding of number words"
PNAS 111(33): 12002-12007

## Experimental Design

Participants heard price utterances ("It cost $X") about items with known
typical prices (electric kettles, laptops, watches). Three experiments
measured: (3a) price priors, (3b) affect priors conditional on price,
(3c) listener interpretations of literal, hyperbolic, and round/sharp
utterances.

## Qualitative Findings

Any model of hyperbole should account for these 6 findings:

| # | Finding | Experiment |
|---|---------|------------|
| 1 | At the inferred price, the listener infers notable affect | 3c |
| 2 | Marginal notable affect > no affect for hyperbolic utterances | 3c |
| 3 | Listener infers speaker's QUD is valence, not price | 3c |
| 4 | Literal utterance → listener infers correct price | 3c |
| 5 | Literal utterance is not interpreted hyperbolically | 3c |
| 6 | Sharp numbers interpreted more precisely than round | 3c |
-/

namespace Phenomena.Nonliteral.Hyperbole.KaoEtAl2014

/-- The 6 qualitative findings from Kao et al. (2014) Experiments 3a–3c.
    Each model of hyperbole should formalize and prove all 6 findings. -/
inductive Finding where
  /-- Hearing "$10,000" for a kettle, the listener infers notable affect
      at the modal price (the most likely actual price under the posterior). -/
  | affect_at_modal
  /-- Marginalizing over all prices, notable affect dominates for "$10,000":
      Σ_s P(s, notable | "$10K") > Σ_s P(s, none | "$10K"). -/
  | affect_marginal
  /-- The listener infers the speaker's communicative goal (QUD) is to
      express valence/affect rather than to communicate exact price. -/
  | qud_valence
  /-- Hearing "$50" for a $50 kettle, the listener infers the correct price:
      P($50 | "$50") > P($500 | "$50"). -/
  | literal_correct
  /-- Literal utterances are not interpreted hyperbolically:
      P($50 | "$50") > P($10K | "$50"). -/
  | literal_not_hyperbolic
  /-- Sharp numbers are interpreted more precisely than round numbers:
      P(exact match | "$501") > P(exact match | "$500"). -/
  | halo_sharp_precise
  deriving DecidableEq, BEq, Repr

/-- All findings from the paper. -/
def findings : List Finding :=
  [.affect_at_modal, .affect_marginal, .qud_valence,
   .literal_correct, .literal_not_hyperbolic, .halo_sharp_precise]

end Phenomena.Nonliteral.Hyperbole.KaoEtAl2014
