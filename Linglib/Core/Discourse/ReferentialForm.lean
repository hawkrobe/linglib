import Linglib.Core.Prominence

/-!
# Referential Form in Production
@cite{ariel-2001} @cite{arnold-wasow-losongco-ginstrom-2000}

Speakers choose between reduced (pronoun) and full (name, description) forms
when referring to discourse entities. This choice is governed by the
**accessibility** of the referent: more accessible/predictable referents
license more reduced forms (@cite{ariel-2001}).

The same `DefinitenessLevel` scale that governs differential argument marking
(`Core.Prominence`) also describes the referential form options available to
a speaker. A pronoun is simultaneously:

1. The **most reduced** referential form (fewer words, less descriptive content)
2. The **lightest** NP (relevant to constituent ordering — @cite{arnold-wasow-losongco-ginstrom-2000})
3. The **highest-prominence** NP (tops the definiteness scale for DOM/DSM)

This module provides the link between accessibility/predictability and
referential form, connecting `Phenomena/Reference/` (form choice) to
`Phenomena/WordOrder/` (position choice) via the shared dimension of
NP weight/reduction.
-/

namespace Core.Discourse.ReferentialForm

open Core.Prominence

-- ════════════════════════════════════════════════════
-- § 1. Referential Form as Production Choice
-- ════════════════════════════════════════════════════

/-- Referential form options for referring to a discourse entity.
    Reuses `DefinitenessLevel` — the same scale governs both
    form selection (production) and differential marking (morphology). -/
abbrev ReferentialForm := DefinitenessLevel

/-- A pronoun is more reduced than a proper name. -/
theorem pronoun_more_reduced_than_name :
    DefinitenessLevel.personalPronoun.rank > DefinitenessLevel.properName.rank := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 2. Next-Mention Bias
-- ════════════════════════════════════════════════════

/-- Next-mention bias: how likely a discourse referent is to be
    mentioned again in the subsequent utterance. Driven by thematic
    roles, coherence relations, and discourse structure. -/
inductive NextMentionBias where
  | high     -- referent is expected to be mentioned next
  | low      -- referent is not expected to be mentioned next
  deriving DecidableEq, Repr, BEq

/-- Accessibility prediction: high next-mention bias licenses reduced
    referential form (pronoun); low bias requires full form (name).

    This is the monotone link at the heart of @cite{ariel-2001}'s
    Accessibility Marking Scale: more accessible referents → more
    reduced forms. The same relationship underlies the Probabilistic
    Reduction Hypothesis (more predictable → shorter/more reduced). -/
def NextMentionBias.predictedForm : NextMentionBias → ReferentialForm
  | .high => .personalPronoun
  | .low  => .properName

/-- The predicted form for high-bias referents is more reduced than
    for low-bias referents. -/
theorem high_bias_more_reduced :
    (NextMentionBias.high.predictedForm).rank >
    (NextMentionBias.low.predictedForm).rank := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 3. Weight Bridge
-- ════════════════════════════════════════════════════

/-- NP weight correlate: reduced referential forms are lighter.
    A pronoun weighs 1 word; a proper name weighs 1-2; a modified
    description weighs 3+. This connects form selection
    to constituent ordering (heavy NP shift, DLM).

    The same choice that makes a referent "more reduced" also makes
    it "lighter", linking @cite{ariel-2001}'s accessibility hierarchy
    to @cite{arnold-wasow-losongco-ginstrom-2000}'s heaviness effects. -/
def ReferentialForm.typicalWeight : ReferentialForm → Nat
  | .personalPronoun    => 1  -- "he", "she"
  | .properName         => 1  -- "Bob" (can be 2: "Sir Barnes")
  | .definite           => 2  -- "the chef"
  | .indefiniteSpecific => 3  -- "a certain chef"
  | .nonSpecific        => 2  -- "a chef"

/-- Pronouns are at most as heavy as any other referential form. -/
theorem pronoun_lightest :
    ReferentialForm.typicalWeight .personalPronoun ≤
    ReferentialForm.typicalWeight .definite := by
  native_decide

end Core.Discourse.ReferentialForm
