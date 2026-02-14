/-!
# Evidential Source Classification

Canonical three-way classification of evidential source (Aikhenvald 2004,
Cumming 2026) and its causal-temporal correlates.

All evidential sources — direct observation, hearsay, and inference — share
the property that the speaker's evidence is **causally downstream** of the
described event: the event causes the perceptual state, the report, or the
observable effects from which the inference is drawn.

This module provides the shared vocabulary that bridges:
- Cumming's (2026) tense evidentiality (T ≤ A = downstream evidence)
- von Fintel & Gillies's (2010) epistemic evidentiality (direct vs indirect)

## References

- Aikhenvald, A. Y. (2004). Evidentiality. OUP.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
- von Fintel, K. & Gillies, A. (2010). Must...stay...strong! *NLS* 18:351–383.
-/

namespace Core.Evidence

/-- Canonical three-way evidential source classification (Aikhenvald 2004). -/
inductive EvidentialSource where
  /-- Direct sensory observation (seeing, hearing the event). -/
  | direct
  /-- Hearsay / reported evidence (told about the event). -/
  | hearsay
  /-- Inference from observable effects (reasoning about the event). -/
  | inference
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Evidential perspective: the temporal relation of T to A.
    Cumming's (2026, §3) three evidential orientations. Framework-agnostic:
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

end Core.Evidence
