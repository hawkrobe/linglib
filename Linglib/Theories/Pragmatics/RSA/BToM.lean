import Linglib.Core.Agent.BToM
import Linglib.Theories.Pragmatics.RSA.Basic

/-!
# RSA-BToM Grounding: Latent Classification
@cite{baker-jara-ettinger-saxe-tenenbaum-2017} @cite{clark-1996} @cite{goodman-frank-2016}

The structural mapping `toBToM` and the bridge theorem `L1_eq_btom_worldMarginal`
now live in `Config.lean` (§5), where they are methods on `RSAConfig`. This file
retains the **latent classification** infrastructure: the cognitive-level
interpretation of what kind of thing each latent variable represents.

## Latent Classification

RSAConfig bundles all non-world latent variables into a single `Latent` type.
A `LatentClassification` assigns each component to a BToM ontological category,
making the cognitive interpretation explicit. Different theoretical positions
correspond to different classifications:

- **Strong Gricean**: Everything is mental state attribution. Interp → desire
  (speaker's intended meaning), Lexicon → belief (speaker's word knowledge),
  BeliefState → belief, Goal → desire.
- **Channel-theoretic**: Some variables are medium properties. Interp → medium
  (structural ambiguity), Lexicon → medium (language convention),
  BeliefState → belief, Goal → desire.
- **Clarkian**: Some variables are shared state. QUD → shared (jointly maintained
  question stack), common ground → shared, Lexicon → shared (conventions).

## Behavioral Equivalence

Different classifications of the same RSAConfig yield identical behavioral
predictions. This follows because marginalization doesn't care about labels:
`Σ_l f(l)` is the same whether `l` is called a belief or a medium property.
The classifications diverge only on cognitive-level claims about what kind
of inference the listener is performing.

-/

open Core.BToM BigOperators

-- ============================================================================
-- §1. Latent Classification
-- ============================================================================

namespace RSA.BToMGrounding

/-- A classification of RSA latent variables into BToM ontological categories.

This is a cognitive-level commitment: it says what *kind* of thing each
latent variable represents. The classification does not affect behavioral
predictions: the classify function is never called by `toBToM` or the
inference machinery, so different classifications yield identical BToM
world marginals. -/
structure LatentClassification (Latent : Type*) where
  /-- Assign each latent variable value to a BToM category. -/
  classify : Latent → LatentCategory
  /-- Assign each latent variable a temporal dynamics.
      Default: episodic (each observation is independent). -/
  dynamics : Latent → FactorDynamics := fun _ => .episodic

/-- The strong Gricean classification: all latent variables are mental states.
    L1's inference is entirely Theory of Mind. -/
def griceanClassification (Latent : Type*) : LatentClassification Latent where
  classify _ := .mental

/-- The channel-theoretic classification: all latent variables are medium
    properties (structural ambiguity, conventions, channel noise).
    L1's inference is entirely signal disambiguation. -/
def channelClassification (Latent : Type*) : LatentClassification Latent where
  classify _ := .medium

/-! ## Open conjectures

`TODO`: Three open questions about the BToM ↔ Hintikka intensional-logic
correspondence (previously stubbed in the deleted `Core/Conjectures.lean`):

1. **Accessibility ↔ positive credence**: the categorical accessibility
   relation `R` from `Core.IntensionalLogic` should be the support of the
   probabilistic credence: `R x w w' ↔ credence x w w' > 0`.
2. **Doxastic necessity ↔ credence one**: `□_x p ↔ P_x(p) = 1`. The two
   doxastic operators agree at the probability-1 limit.
3. **Rigidity ↔ common-ground constancy**: a `Core.Intension` is rigid
   iff every agent assigns it the same value across all positively-
   credenced worlds.

Formalizing requires choosing canonical types for `R` and a PMF-based
`credence` map and stating the biconditionals. -/

end RSA.BToMGrounding
