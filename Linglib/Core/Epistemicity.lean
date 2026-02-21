import Linglib.Core.Evidence
import Linglib.Core.Context

/-!
# Epistemic Profile Layer

Connective layer bundling evidential source, epistemic authority (egophoricity),
and mirativity into a unified `EpistemicProfile`. Bridges these feature-geometric
dimensions to the model-theoretic level (`KContext`).

## Motivation

Gawne & Spronck (2024) identify 10 concept areas forming a coherent epistemic
domain. Linglib already covers evidential source (`Core/Evidence.lean`), epistemic
modality (`Modality/Kernel.lean`), and mirativity (`Core/Evidence.lean`), but these
are scattered with no connective tissue. The main gap is **egophoricity** — the
dimension of WHO has privileged epistemic access (speaker vs addressee vs third
party), which the glossary argues is independent of evidential source.

## Design

`EpistemicAuthority` fills the egophoricity gap. `EpistemicProfile` bundles it
with `EvidentialSource` and `MirativityValue` for unified epistemic specification.
`epistemicAuthority` bridges epistemic authority to `KContext` (which already has
agent/addressee fields).

## Not Yet Formalized

Engagement, logophoricity, and epistemic vigilance would require substantial new
infrastructure (discourse model, binding theory extension, RSA listener model
extension respectively) and are left for future work.

## References

- Gawne, L. & Spronck, S. (2024). Evidentiality, egophoricity, and engagement:
  the epistemicity glossary. *Linguistic Typology*.
- Tournadre, N. (2008). Arguments against the concept of "conjunct"/"disjunct".
  *Linguistics of the Tibeto-Burman Area* 31(2):121–146.
- Floyd, S. (2018). Egophoricity and argument structure in Cha'palaa.
  In Simeon Floyd, Elisabeth Norcliffe & Lila San Roque (eds.),
  *Egophoricity*, 269–304. John Benjamins.
-/

namespace Core.Epistemicity

open Core.Evidence
open Core.Context

/-- Epistemic authority: WHO has privileged access to the propositional content.
    Egophoric systems (Tournadre 2008, Floyd 2018, Gawne & Spronck glossary §2)
    grammaticalize the distinction between:
    - ego: speaker has privileged access (1st person knowledge, volition, intention)
    - allocutive: addressee has privileged access (2nd person questions)
    - nonparticipant: neither speech-act participant has special access -/
inductive EpistemicAuthority where
  | ego            -- speaker has privileged epistemic access
  | allocutive     -- addressee has privileged epistemic access
  | nonparticipant -- no speech-act participant has special access
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Epistemic profile: bundles the three orthogonal epistemic dimensions
    that the glossary identifies as cross-linguistically relevant.
    - source: WHAT kind of evidence (Aikhenvald's 3-way)
    - authority: WHO has privileged access (egophoric dimension)
    - mirativity: WHETHER the content is expected (DeLancey's dimension) -/
structure EpistemicProfile where
  source     : EvidentialSource
  authority  : EpistemicAuthority
  mirativity : MirativityValue := .neutral
  deriving Repr, BEq

/-- Determine epistemic authority from a KContext: ego if the knower is the
    agent, allocutive if the knower is the addressee, nonparticipant otherwise. -/
def epistemicAuthority {W E P T : Type*} [DecidableEq E]
    (ctx : KContext W E P T) (knower : E) : EpistemicAuthority :=
  if knower == ctx.agent then .ego
  else if knower == ctx.addressee then .allocutive
  else .nonparticipant

/-- Ego authority with direct evidence: the canonical "strong assertion" profile.
    The speaker saw it themselves — maximally authoritative. -/
def strongAssertion : EpistemicProfile :=
  { source := .direct, authority := .ego }

/-- Non-ego authority with inferential evidence: the canonical profile
    for epistemic 'must' (VF&G 2010). Speaker infers, no privileged access. -/
def inferentialClaim : EpistemicProfile :=
  { source := .inference, authority := .nonparticipant }

/-- In ego-authority contexts, direct evidence is the default source.
    This captures the generalization that 1st-person volitional claims
    ("I'm going to leave") use ego marking, not evidential marking. -/
theorem ego_default_direct : strongAssertion.source = .direct := rfl

/-- In allocutive contexts, evidential source is typically irrelevant —
    the addressee's authority overrides source distinctions.
    (Tibetan -payin ego vs -pa'dug non-ego; Akhvakh -eri ego vs -ari non-ego) -/
def allocutiveProfile (s : EvidentialSource) : EpistemicProfile :=
  { source := s, authority := .allocutive }

end Core.Epistemicity
