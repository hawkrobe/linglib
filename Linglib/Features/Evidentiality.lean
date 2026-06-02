/-!
# Evidentiality
@cite{aikhenvald-2004} @cite{cumming-2026} @cite{von-fintel-gillies-2010}

Framework-agnostic evidentiality vocabulary: the canonical Aikhenvald
three-way source taxonomy, the temporal-orientation classification of
evidence acquisition, and a typeclass `HasEvidentialPerspective` that lets
downstream types (semantic constraint enums, paradigm rows, modal evidence
types) project into the perspective taxonomy uniformly.

All evidential sources — direct observation, hearsay, and inference — share
the property that the speaker's evidence is **causally downstream** of the
described event: the event causes the perceptual state, the report, or the
observable effects from which the inference is drawn.

This module supplies the shared vocabulary that bridges
@cite{cumming-2026}'s tense evidentiality (T ≤ A = downstream evidence) and
@cite{von-fintel-gillies-2010} epistemic evidentiality (direct vs indirect).

-/

namespace Features.Evidentiality

/-- Canonical three-way evidential source classification (@cite{aikhenvald-2004}). -/
inductive CoarseSource where
  /-- Direct sensory observation (seeing, hearing the event). -/
  | direct
  /-- Hearsay / reported evidence (told about the event). -/
  | hearsay
  /-- Inference from observable effects (reasoning about the event). -/
  | inference
  deriving DecidableEq, Repr, Inhabited

/-- Evidential perspective: the temporal relation of evidence acquisition
    to the described event. @cite{cumming-2026}'s three evidential
    orientations, named in framework-agnostic terms. -/
inductive EvidentialPerspective where
  /-- T ≤ A: evidence acquired after (or at) the event. Speaker observed
      consequences or received reports. -/
  | retrospective
  /-- T = A: evidence acquired contemporaneously with the event. -/
  | contemporaneous
  /-- A < T: evidence acquired before the event. Speaker has predictive
      grounds (plans, schedules, dispositions). -/
  | prospective
  deriving DecidableEq, Repr, Inhabited

/-- Types that project to an evidential perspective.

    The `Option` codomain accommodates types like tense-paradigm constraints
    where some values (e.g. an `unconstrained` future) have no canonical
    perspective. Types with a total projection (the source taxonomy itself,
    or the perspective type) wrap the result in `some`. -/
class HasEvidentialPerspective (α : Type) where
  /-- The evidential perspective of `a`, when defined. -/
  toEvidentialPerspective : α → Option EvidentialPerspective

export HasEvidentialPerspective (toEvidentialPerspective)

/-- A value is *nonfuture* iff it projects to a retrospective or
    contemporaneous perspective — i.e., evidence is downstream of the
    event (T ≤ A). Prospective and "no perspective" both fail.

    Defined uniformly over `HasEvidentialPerspective` so that downstream
    types (constraint enums, paradigm rows, modal evidence types) inherit
    one decidable predicate instead of hand-rolling parallel definitions. -/
def IsNonfuture {α : Type} [HasEvidentialPerspective α] (a : α) : Prop :=
  toEvidentialPerspective a = some .retrospective ∨
  toEvidentialPerspective a = some .contemporaneous

instance {α : Type} [HasEvidentialPerspective α] :
    DecidablePred (@IsNonfuture α _) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

-- ════════════════════════════════════════════════════════════════
-- § Canonical instances
-- ════════════════════════════════════════════════════════════════

/-- The Aikhenvald source taxonomy projects to perspective by the canonical
    typological mapping: direct observation is contemporaneous (A = T), while
    hearsay and inference are retrospective (A ≥ T). The event causally
    precedes or coincides with evidence acquisition in all three cases.

    Note: this encodes a typological generalization, not a definitional
    truth. Live quotatives and predictive inference can violate the
    canonical mapping; per-construction classifications should override. -/
def CoarseSource.toEvidentialPerspective :
    CoarseSource → Option EvidentialPerspective
  | .direct    => some .contemporaneous
  | .hearsay   => some .retrospective
  | .inference => some .retrospective

instance : HasEvidentialPerspective CoarseSource where
  toEvidentialPerspective := CoarseSource.toEvidentialPerspective

/-- The perspective type projects to itself. -/
instance : HasEvidentialPerspective EvidentialPerspective where
  toEvidentialPerspective := some

/-- Dot-notation alias for `Features.Evidentiality.IsNonfuture` on perspectives. -/
def EvidentialPerspective.IsNonfuture (p : EvidentialPerspective) : Prop :=
  Features.Evidentiality.IsNonfuture p

instance : DecidablePred EvidentialPerspective.IsNonfuture :=
  fun _ => inferInstanceAs (Decidable (Features.Evidentiality.IsNonfuture _))

-- ════════════════════════════════════════════════════════════════
-- § Simp lemmas
-- ════════════════════════════════════════════════════════════════

@[simp] theorem CoarseSource.toEvidentialPerspective_direct :
    CoarseSource.toEvidentialPerspective .direct = some .contemporaneous := rfl

@[simp] theorem CoarseSource.toEvidentialPerspective_hearsay :
    CoarseSource.toEvidentialPerspective .hearsay = some .retrospective := rfl

@[simp] theorem CoarseSource.toEvidentialPerspective_inference :
    CoarseSource.toEvidentialPerspective .inference = some .retrospective := rfl

-- ════════════════════════════════════════════════════════════════
-- § Fine-grained source taxonomies (Aikhenvald 2004)
-- ════════════════════════════════════════════════════════════════

/-- Sensory channel of a direct (firsthand) evidential. The visual vs
    non-visual contrast is grammaticalized in many languages
    (Tuyuca, Tariana, Kashaya); finer distinctions (auditory vs other
    non-visual sensory) are grammaticalized in some (Kashaya). Languages
    that don't grammaticalize the contrast use `.unspecified`. -/
inductive DirectSource where
  | unspecified
  | visual
  | auditory
  | nonvisualSensory
  | olfactory
  deriving DecidableEq, Repr, Inhabited

/-- Source-identity of a reportative evidential. Aikhenvald 2004 distinguishes
    `hearsay` (original speaker not identified) from `quotative` (specifically
    named source). -/
inductive ReportativeSource where
  | unspecified
  | unidentified
  | identified
  deriving DecidableEq, Repr, Inhabited

/-- Basis of an inferential evidential. Aikhenvald 2004 distinguishes
    inference `fromResult` (observable consequences) from `fromAssumption`
    (general knowledge / reasoning). -/
inductive InferentialBasis where
  | unspecified
  | fromResult
  | fromAssumption
  deriving DecidableEq, Repr, Inhabited

end Features.Evidentiality
