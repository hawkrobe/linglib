import Linglib.Core.InformationTheory
import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Theories.Pragmatics.RSA.Core.BToMGrounding
import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic

/-!
# Grammar as Distribution

@cite{dunn-2026} @cite{hawkins-franke-frank-goldberg-smith-griffiths-goodman-2023}

A grammar is a frequency profile over constructions (Dunn 2025). This
generalizes lexical uncertainty (Bergen et al. 2016): where LU varies meaning
assignments, grammar uncertainty varies both meaning AND production frequency.

## Architecture

Two types capture the individual–population hierarchy from CHAI (Hawkins et al.
2023) and Dunn's (2025) variationist CxG:

- `GrammarDist C` — frequency profile over constructions (individual grammar)
- `Grammar C W` — frequency + interpretation (connects to RSA `Lexicon`)

These embed into existing RSA infrastructure without new machinery:

| Concept | RSAConfig slot | Type |
|---------|---------------|------|
| Individual grammar | `Latent` | `Grammar C W` |
| Population grammar | `latentPrior` | `W → Grammar C W → ℝ` |
| Community convention | `Latent` (2nd level) | `Grammar C W × Convention` |

CHAI's two-level hierarchy (Θ, φ_k) maps directly:
- φ_k (partner-specific lexicon) = a `Grammar` value
- Θ (community convention) = the `latentPrior` shape parameter
- P(φ_k | Θ) · P(Θ) = `latentPrior` over `Latent := Grammar × Convention`

The same grammar object classifies differently in BToM depending on the
phenomenon (§5): variability → medium, generalization → shared,
online learning → mental.

## References

- Dunn, J. (2025). Syntactic Variation from Individuals to Populations.
  Cambridge University Press.
- Hawkins, Franke, Frank, Goldberg, Smith, Griffiths & Goodman (2023). From
  Partners to Populations. Psychological Review 130(4), 977.
- Bergen, Levy & Goodman (2016). Pragmatic Reasoning through Semantic Inference.
-/

namespace ConstructionGrammar

open Core.InformationTheory Core.BToM RSA.BToMGrounding

-- ============================================================================
-- §1. Core Types
-- ============================================================================

/-- A non-negative frequency profile over constructions (Dunn 2025).

An individual's grammar is a frequency-weighted profile over constructions —
not a binary set (in/out) but a weighting reflecting how often each
construction is used. Note: this does not enforce normalization (Σ freq = 1);
the weights are relative frequencies, not probabilities.

In CHAI (Hawkins et al. 2023), this is φ_k — the partner-specific
production model that determines both what to say and how to interpret. -/
structure GrammarDist (C : Type) where
  freq : C → ℚ
  freq_nonneg : ∀ c, 0 ≤ freq c

/-- A full grammar: frequency profile + interpretation function.

Extends `GrammarDist` with a meaning function mapping each construction
to a graded truth function over worlds. This connects grammar distributions
to RSA's literal semantics and to Bergen et al.'s (2016) `Lexicon` type.

The meaning function corresponds to CHAI's L_φ(u, o) — the truth-conditional
function parameterized by the grammar. -/
structure Grammar (C W : Type) extends GrammarDist C where
  meaning : C → W → ℚ

-- ============================================================================
-- §2. Entropy and Similarity
-- ============================================================================

section EntropyAndSimilarity
variable {C : Type} [BEq C]

/-- Constructional diversity: Shannon entropy of the frequency profile.

Higher entropy = more diverse construction usage. Dunn (2025) uses
grammar entropy to compare registers, dialects, and individual variation
within L1 populations. -/
def GrammarDist.entropyOver (g : GrammarDist C) (inventory : List C) : ℚ :=
  entropy (inventory.map fun c => (c, g.freq c))

/-- Jensen-Shannon divergence between two grammars over a shared inventory.

Symmetric, bounded, and a metric (after sqrt). Used by Dunn (2025) to
measure register distance, dialect boundaries, and L1-L2 differences. -/
def GrammarDist.jsd (p q : GrammarDist C) (inventory : List C) : ℚ :=
  jsdOf inventory p.freq q.freq

end EntropyAndSimilarity

-- ============================================================================
-- §3. Connection to Lexicon (Bergen et al. 2016)
-- ============================================================================

section LexiconConnection
variable {C W U : Type}

/-- Project a grammar to a lexicon by forgetting frequency.

A `Lexicon` (Bergen et al. 2016) is a meaning assignment `C → W → ℚ`.
A `Grammar` is a meaning assignment PLUS a frequency profile. The
projection forgets frequency, retaining only interpretation. -/
def Grammar.toLexicon (g : Grammar C W) : Lexicon C W where
  meaning := g.meaning

/-- Embed a lexicon as a grammar with uniform frequency.

This is the key structural claim: lexical uncertainty (Bergen et al. 2016)
is the special case of grammar uncertainty where only meaning varies and
production frequency is uniform across constructions.

In CHAI terms: standard LU uses a flat prior P(φ) over lexicons; grammar
uncertainty extends this to structured priors P(φ | Θ) where Θ encodes
population-level frequency norms. -/
def grammarOfLexicon (L : Lexicon U W) : Grammar U W where
  freq := fun _ => 1
  freq_nonneg := fun _ => by norm_num
  meaning := L.meaning

/-- Round-trip: Lexicon → Grammar → Lexicon preserves meaning.

The meaning function is unchanged by embedding into Grammar and projecting
back. This makes `toLexicon ∘ grammarOfLexicon` the identity on meaning. -/
theorem toLexicon_grammarOfLexicon_meaning (L : Lexicon U W) (u : U) (w : W) :
    (grammarOfLexicon L).toLexicon.meaning u w = L.meaning u w := rfl

/-- Lexical uncertainty embeds into grammar uncertainty (meaning preserved).

Every `Lexicon` embeds as a `Grammar` with uniform frequency, preserving
the meaning function. The embedding is meaning-preserving: `toLexicon`
after `grammarOfLexicon` recovers the original meaning. Grammar uncertainty
extends LU by additionally varying production frequency. -/
theorem grammar_subsumes_lexical_uncertainty (L : Lexicon U W) :
    (grammarOfLexicon L).toLexicon.meaning = L.meaning := rfl

end LexiconConnection

-- ============================================================================
-- §4. Grammar as RSA Cost
-- ============================================================================

section RSACost
variable {C : Type}

/-- Production cost derived from frequency: -log₂(freq).

Frequent constructions are cheap; rare ones are expensive. This connects
Dunn's frequency-based grammar to RSA's utterance cost: setting
`cost(u) = -log₂(freq(u))` in S1's action-based scoring rule grounds
utterance cost in production frequency rather than stipulating it.

In CHAI, this corresponds to the speaker's production model: S1 prefers
utterances that are frequent in the speaker's grammar φ_k AND
informative about the intended referent. -/
def GrammarDist.cost (g : GrammarDist C) (c : C) : ℚ :=
  if g.freq c ≤ 0 then 10
  else -log2Approx (g.freq c)

end RSACost

-- ============================================================================
-- §5. BToM Classification
-- ============================================================================

/-- Three BToM roles for grammars, corresponding to CHAI's three capacities.

The same `Grammar C W` object classifies differently in BToM depending on
the theoretical question. These correspond to the three core capacities
identified in CHAI (Hawkins et al. 2023, §2.2):

| Role | BToM Category | Dynamics | CHAI capacity | Phenomenon |
|------|---------------|----------|---------------|------------|
| Competence | Medium | Dispositional | C1 (variability) | Dialect ID |
| Convention | Shared | Dynamic | C3 (generalization) | Convention |
| Accommodation | Mental | Episodic | C2 (online learning) | Accommodation |

These classifications yield identical behavioral predictions (BToM marginals
are insensitive to labels). They differ in cognitive-level claims about what
inference the listener performs. -/
inductive GrammarRole where
  | competence    -- C1: fixed property of the speaker (their dialect/register)
  | convention    -- C3: shared equilibrium abstracted across partners
  | accommodation -- C2: speaker's online model of partner's grammar
  deriving DecidableEq, Repr

/-- Map grammar roles to BToM ontological categories. -/
def GrammarRole.toBToMCategory : GrammarRole → LatentCategory
  | .competence => .medium
  | .convention => .shared
  | .accommodation => .mental

/-- Map grammar roles to temporal dynamics. -/
def GrammarRole.toDynamics : GrammarRole → FactorDynamics
  | .competence => .dispositional
  | .convention => .dynamic
  | .accommodation => .episodic

/-- Construct a BToM latent classification from a grammar role.

This makes explicit the cognitive commitment: treating grammar as
medium (stable language structure), shared (evolving convention), or
mental (belief about interlocutor). -/
def grammarClassification (role : GrammarRole) :
    LatentClassification Unit where
  classify _ := role.toBToMCategory
  dynamics _ := role.toDynamics

-- ============================================================================
-- §6. CHAI Hierarchy: From Partners to Populations
-- ============================================================================

/-- CHAI's two-level hierarchy expressed via RSAConfig.

In CHAI (Hawkins et al. 2023), convention formation is modeled as
hierarchical Bayesian inference over two levels of grammar:

- φ_k : partner-specific grammars (updated online through interaction)
- Θ : community-level convention (abstracted across partners)

These correspond to the two components of the latent variable in RSAConfig:
set `Latent := Grammar C W × Convention` and define
`latentPrior _ (φ, θ) := P(φ | θ) · P(θ)`.

L1's marginalization then automatically computes CHAI's Eq 4:
  L1(w|u) ∝ prior(w) · Σ_{φ,θ} P(φ|θ) · P(θ) · S1(u|w, φ)

This derives three phenomena:
- P1 (efficiency): S1 incorporates φ.cost, so frequent constructions win
- P2 (partner → community): Θ pools across partners via P(θ | D₁, D₂, ...)
- P3 (context-sensitivity): different L0 meanings for different Θ values

The `partnerGrammars` list contains one φ_k per interaction partner.
CHAI's key claim is that Θ is abstracted by pooling across partners:
P(Θ | D₁, ..., D_K) ∝ P(Θ) · Π_k P(D_k | Θ). Each partner grammar
φ_k is drawn from P(φ | Θ) and updated independently through interaction.

TODO: Formalize the dynamic aspect (sequential Bayesian updating of φ_k and
Θ across discourse turns). The current RSAConfig is static (single-utterance);
extending to sequential observation requires `BToMModel.sharedUpdate`. -/
structure CHAIHierarchy (C W : Type) where
  /-- Partner-specific grammars (CHAI's φ_k for each partner k). -/
  partnerGrammars : List (Grammar C W)
  /-- Community-level convention parameter (CHAI's Θ).
      Abstractly: a shape parameter for the distribution over partner grammars.
      Concretely: a "default" grammar that partner grammars are drawn from. -/
  communityConvention : Grammar C W

section CHAIConventionality
variable {C W : Type}

/-- A grammar is conventional if it is a fixed point of CHAI's hierarchical
learning: the community convention Θ concentrates on g, and new partners'
grammars φ_k converge to g through interaction.

Formally: g is conventional when, for any partner k starting from the
community prior P(φ | Θ=g), Bayesian updating on observations from a
g-speaker yields a posterior that also concentrates on g.

In signaling game terms: g is a Lewis convention — a regularity in behavior
that is common knowledge, preferred over alternatives, and self-reinforcing.

TODO: State as a fixed-point condition on the Bayesian update:
  P(φ_k | D_k, Θ=g) concentrates on g when D_k is generated by g. -/
def Grammar.isConventional (_g : Grammar C W) : Prop :=
  sorry

end CHAIConventionality

end ConstructionGrammar
