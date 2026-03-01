import Linglib.Theories.Pragmatics.RelevanceTheory.CognitiveEnvironment

/-!
# Ostensive Communication — Sperber & Wilson (1986/95)

Ostensive communication involves two layers of intention:

1. **Informative intention**: to make manifest (or more manifest) to the
   audience a set of assumptions
2. **Communicative intention**: to make mutually manifest to communicator
   and audience the communicator's informative intention

The communicative intention is what distinguishes ostensive communication
from mere information transmission. It creates a PRESUMPTION OF OPTIMAL
RELEVANCE (Postface p. 270), which triggers the comprehension procedure.

The presumption of optimal relevance does not have independent formal
content — it is REALIZED BY the comprehension procedure (see
`Comprehension.lean`). As S&W put it (Postface p. 271): "What makes it
possible to recognise the communicator's informative intention is [the
comprehension] procedure." The formal machinery that implements this
presumption is `RTScenario.comprehensionSelects`: the satisficing search
over interpretations ordered by accessibility IS what it means for the
hearer to treat the stimulus as optimally relevant.

## References

Sperber, D. & Wilson, D. (1986/95). Relevance. Ch. 1 §9, Ch. 4 §1;
Postface pp. 270-271.
-/

set_option autoImplicit false

namespace Theories.Pragmatics.RelevanceTheory

/-- An informative intention: the set of assumptions the communicator
    wants to make manifest (or more manifest) to the audience.

    S&W (p. 58): "Informative intention: to make manifest or more manifest
    to the audience a set of assumptions {I}." -/
structure InformativeIntention (A : Type*) where
  /-- Which assumptions the communicator intends to make manifest -/
  intended : List A

/-- An ostensive stimulus: a stimulus that makes manifest the
    communicator's intention to make certain assumptions manifest.

    Can be linguistic (an utterance), gestural (pointing), visual
    (showing), or any behavior that attracts attention and focuses it
    on the communicator's meaning.

    S&W (p. 63): "Communicative intention: to make it mutually manifest
    to audience and communicator that the communicator has this
    informative intention."

    The ostensive stimulus triggers the comprehension procedure by
    creating a presumption of optimal relevance. This presumption is not
    formalized as a separate Prop — it is operationalized by the
    `RTScenario.comprehensionSelects` predicate in `Comprehension.lean`. -/
structure OstensiveStimulus (W : Type*) (A : Type*) where
  /-- The communicator's informative intention -/
  informativeIntention : InformativeIntention A
  /-- The communicator's cognitive environment -/
  communicatorEnv : CogEnv W A

end Theories.Pragmatics.RelevanceTheory
