/-!
# Modal-Temporal Axes

@cite{condoravdi-2002}

The two temporal axes that any modal interpretation theory must
distinguish (cf. @cite{condoravdi-2002}, §2):

- **Temporal perspective**: the time at which the modal base / ordering
  source is evaluated. Either present (utterance time) or past (an
  earlier evaluation point, accessed via a past-shifting operator
  scoping over the modal).

- **Temporal orientation**: the relation between the perspective time
  and the time of the modal's prejacent. Past, present (coincident),
  or future.

These axes are framework-neutral: they are used by Condoravdi 2002
(English `might`/`would`), Hacquard 2006 (event-relative modals),
Klecha 2016 (CIR-based future orientation), Matthewson 2013 (Gitksan
`dim`-based future orientation), and any other modal-temporal theory.

This file is the canonical home; downstream modules import from here
rather than redeclaring local copies.

## Note on @cite{condoravdi-2002}'s narrower local enums

`Phenomena/Modality/Studies/Condoravdi2002.lean` carries its own
2-element `Perspective` (matching `TemporalPerspective` here) and a
2-element `Orientation` (`future | past` only — Condoravdi's 4-reading
typology has no present-orientation cell). Those local enums are
tightly coupled with `ModalReading`, `projectedRegion`, and
`FrameAdverb.compatible` machinery and are not migrated here. The
canonical `TemporalOrientation` below is the strict superset; a
Condoravdi-style 2-way `Orientation` would inject into it.
-/

namespace Core.Modality

/-- Temporal perspective: the time at which a modal base / ordering
    source is evaluated. -/
inductive TemporalPerspective where
  /-- Modal base evaluated at the utterance time. -/
  | present
  /-- Modal base evaluated at a prior time (e.g., via PERF > MODAL). -/
  | past
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Temporal orientation: the temporal relation between the perspective
    time and the prejacent's instantiation time. -/
inductive TemporalOrientation where
  /-- Prejacent instantiated before the perspective time. -/
  | past
  /-- Prejacent coincides with the perspective time. -/
  | present
  /-- Prejacent instantiated at or after the perspective time. -/
  | future
  deriving DecidableEq, Repr, BEq, Inhabited

end Core.Modality
