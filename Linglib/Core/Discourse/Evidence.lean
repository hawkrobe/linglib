/-!
# Evidential Source Classification
@cite{aikhenvald-2004} @cite{cumming-2026} @cite{von-fintel-gillies-2010}

Canonical three-way classification of evidential source and its causal-temporal correlates.

All evidential sources — direct observation, hearsay, and inference — share
the property that the speaker's evidence is **causally downstream** of the
described event: the event causes the perceptual state, the report, or the
observable effects from which the inference is drawn.

This module provides the shared vocabulary that bridges:
- @cite{cumming-2026}'s tense evidentiality (T ≤ A = downstream evidence)
- @cite{von-fintel-gillies-2010} epistemic evidentiality (direct vs indirect)

-/

namespace Core.Evidence

/-- Canonical three-way evidential source classification. -/
inductive EvidentialSource where
  /-- Direct sensory observation (seeing, hearing the event). -/
  | direct
  /-- Hearsay / reported evidence (told about the event). -/
  | hearsay
  /-- Inference from observable effects (reasoning about the event). -/
  | inference
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Evidential perspective: the temporal relation of T to A.
    @cite{cumming-2026}'s three evidential orientations. Framework-agnostic:
    just names the three temporal relations between event and evidence
    acquisition. -/
inductive EvidentialPerspective where
  /-- T ≤ A: evidence acquired after (or at) the event. Speaker observed
      consequences or received reports. -/
  | retrospective
  /-- T = A: evidence acquired contemporaneously with the event. -/
  | contemporaneous
  /-- A < T: evidence acquired before the event. Speaker has predictive
      grounds (plans, schedules, dispositions). -/
  | prospective
  deriving DecidableEq, Repr, BEq

/-- Is this evidential perspective nonfuture? Retrospective and
    contemporaneous perspectives involve evidence that is downstream
    of the event (T ≤ A); prospective does not. -/
def EvidentialPerspective.isNonfuture : EvidentialPerspective → Bool
  | .retrospective => true
  | .contemporaneous => true
  | .prospective => false

/-- Every evidential source maps to an evidential perspective.
    Direct observation is contemporaneous (A = T), hearsay and inference
    are retrospective (A ≥ T) — in all cases, the event causally precedes
    or coincides with evidence acquisition. -/
def EvidentialSource.toEvidentialPerspective : EvidentialSource → EvidentialPerspective
  | .direct => .contemporaneous
  | .hearsay => .retrospective
  | .inference => .retrospective

/-- Mirativity: whether the propositional content is expected or
    surprising to the speaker (DeLancey 1997, @cite{aikhenvald-2004} Ch 6). -/
inductive MirativityValue where
  | expected
  | unexpected
  | neutral
  deriving DecidableEq, Repr, BEq

/-- Does this mirativity value mark surprise/new information? -/
def MirativityValue.isMirative : MirativityValue → Bool
  | .unexpected => true
  | _ => false

/-- Is this evidence source indirect? Hearsay and inference are indirect;
    direct observation is not. This is @cite{izvorski-1997}'s binary partition
    of Aikhenvald's three-way classification. -/
def EvidentialSource.isIndirect : EvidentialSource → Bool
  | .direct => false
  | .hearsay => true
  | .inference => true

end Core.Evidence
