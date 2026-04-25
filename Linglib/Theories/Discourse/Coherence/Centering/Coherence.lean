import Linglib.Theories.Discourse.Coherence.Centering.Transition
import Linglib.Core.Discourse.Coherence

/-!
# Centering — Coherence Relation Bridge
@cite{grosz-joshi-weinstein-1995} @cite{kehler-2002} @cite{poesio-stevenson-eugenio-hitzeman-2004}

A bridge between the discrete `CoherenceRelation` typology of
@cite{kehler-2002} and the discrete `Transition` typology of
@cite{grosz-joshi-weinstein-1995} Rule 2.

The motivation is that both classify how an utterance pair *coheres*,
but along different axes — one in terms of inferential connection
(causation, similarity, contiguity) and the other in terms of
center continuity. They overlap in their predictions about which
configurations are most coherent: elaboration and explanation, which
hold the topic constant, pattern with continuation; parallel and
occasion, which shift focus while preserving topic, pattern with
retaining; and contrast/correction, which substitute the topic,
pattern with shifting.

This bridge does not claim the two systems are equivalent — only that
they correlate predictably on the canonical cases that motivate Rule 2.
@cite{poesio-stevenson-eugenio-hitzeman-2004} formalizes the connection
in their PARAMETERIZED-CENTERING-MODEL by tying the choice of
ranking-and-instantiation to the discourse genre.
-/

set_option autoImplicit false

namespace Discourse.Coherence.Centering

open Core.Discourse.Coherence

/-- The transition pattern that the given coherence relation most
    naturally licenses, on the canonical mapping shared between
    @cite{kehler-2002} and @cite{grosz-joshi-weinstein-1995}:

    * **elaboration / explanation / result** — the same entity remains
      central across the segment boundary, so the prior Cb persists
      as Cb and typically as Cp ⇒ continuation.

    * **occasion / parallel** — the topic remains but a new entity may
      be highlighted in subject position ⇒ retaining.

    * **contrast / correction** — a new alternative is asserted in
      place of the prior one, often shifting the Cb itself ⇒ shifting.

    These are *predictions about preferred patterns*, not strict
    entailments; an actual discourse can violate them and remain
    interpretable (at a coherence cost). -/
def CoherenceRelation.preferredTransition : CoherenceRelation → Transition
  | .elaboration  => .continuation
  | .explanation  => .continuation
  | .result       => .continuation
  | .occasion     => .retaining
  | .parallel     => .retaining
  | .contrast     => .shifting
  | .correction   => .shifting

-- ════════════════════════════════════════════════════
-- § Rule-2-aligned predictions
-- ════════════════════════════════════════════════════

/-- Causal and elaborative relations license the most preferred
    transition (continuation). -/
theorem causeEffect_continuation :
    CoherenceRelation.preferredTransition .explanation = .continuation ∧
    CoherenceRelation.preferredTransition .result = .continuation := ⟨rfl, rfl⟩

/-- Resemblance relations of the substitution kind license the least
    preferred transition (shifting). -/
theorem substitution_shifts :
    CoherenceRelation.preferredTransition .contrast = .shifting ∧
    CoherenceRelation.preferredTransition .correction = .shifting := ⟨rfl, rfl⟩

/-- The bridge respects Rule 2's preference order: continuation-licensing
    relations outrank retaining-licensing relations, which outrank
    shifting-licensing relations. -/
theorem coherence_respects_rule2 :
    (CoherenceRelation.preferredTransition .explanation).rank >
      (CoherenceRelation.preferredTransition .occasion).rank ∧
    (CoherenceRelation.preferredTransition .occasion).rank >
      (CoherenceRelation.preferredTransition .contrast).rank := by
  refine ⟨?_, ?_⟩ <;> decide

end Discourse.Coherence.Centering
