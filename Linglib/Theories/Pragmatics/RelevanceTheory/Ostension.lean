import Linglib.Theories.Pragmatics.RelevanceTheory.CognitiveEnvironment

/-!
# Ostensive Communication — Sperber & Wilson (1986/95)

Ostensive communication involves two layers of intention:

1. **Informative intention**: to make manifest (or more manifest) to the
   audience a set of assumptions
2. **Communicative intention**: to make mutually manifest to communicator
   and audience the communicator's informative intention

The communicative intention is what distinguishes ostensive communication
from mere information transmission. It triggers the comprehension procedure
by creating an expectation of optimal relevance.

## References

Sperber, D. & Wilson, D. (1986/95). Relevance. Ch. 1 §9, Ch. 4 §1.
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
    informative intention." -/
structure OstensiveStimulus (W : Type*) (A : Type*) where
  /-- The communicator's informative intention -/
  informativeIntention : InformativeIntention A
  /-- The communicator's cognitive environment -/
  communicatorEnv : CogEnv W A

/-- An ostensive stimulus creates a presumption of optimal relevance.
    This is the Second (Communicative) Principle of Relevance.

    The hearer assumes:
    (a) The stimulus is relevant enough to be worth processing
    (b) It is the most relevant one compatible with the communicator's
        abilities and preferences

    This presumption triggers and guides the comprehension procedure. -/
def OstensiveStimulus.presumesRelevance {W : Type*} {A : Type*}
    (_ : OstensiveStimulus W A) : Prop := True

end Theories.Pragmatics.RelevanceTheory
