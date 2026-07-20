import Mathlib.Tactic.TypeStar

/-!
# Evidential — coarse source and perspective
[willett-1988] [aikhenvald-2004] [cumming-2026] [von-fintel-gillies-2010]

Framework-agnostic evidentiality vocabulary: [willett-1988]'s coarse
three-way source taxonomy, the temporal-orientation classification of
evidence acquisition, and the typeclasses `HasCoarseSource` and
`HasEvidentialPerspective` that let downstream types (semantic constraint
enums, paradigm rows, modal evidence types) project into the taxonomies
uniformly.

In the typologically canonical case, an evidential source — direct
observation, report, or inference from results — is **causally downstream**
of the described event: the event causes the perceptual state, the report,
or the observable effects. Assumption-based inferentials and predictive
evidentials fall outside this pattern; the `prospective` perspective and the
`Option` codomain of the projection accommodate them.

This module supplies the shared vocabulary consumed by both
[cumming-2026]'s tense evidentiality (T ≤ A = downstream evidence) and
[von-fintel-gillies-2010]'s epistemic evidentiality (direct vs indirect).
[aikhenvald-2004]'s finer six-way parameter carving lives with the
evidential lexical API in the sibling `Defs`/`Basic` files.
-/

namespace Semantics.Evidential

/-- Coarse three-way evidential source classification: [willett-1988]'s
    attested / reported / inferring tripartition. `hearsay` is the umbrella
    for Willett's reported category (subsuming hearsay proper and quotative);
    finer carvings ([aikhenvald-2004]) live at `Semantics/Evidential/`. -/
inductive CoarseSource where
  /-- Direct sensory observation (seeing, hearing the event). -/
  | direct
  /-- Hearsay / reported evidence (told about the event). -/
  | hearsay
  /-- Inference from observable effects (reasoning about the event). -/
  | inference
  deriving DecidableEq, Repr, Inhabited

/-- A coarse source is *indirect* iff it is not direct observation. The
    shared contrast variable of indirect-evidential operators:
    [izvorski-1997]'s EV and [von-fintel-gillies-2010]'s *must* both
    presuppose an indirect evidence basis. -/
def CoarseSource.IsIndirect (s : CoarseSource) : Prop := s ≠ .direct

instance : DecidablePred CoarseSource.IsIndirect := fun s =>
  inferInstanceAs (Decidable (s ≠ .direct))

/-- Evidential perspective: the temporal relation of evidence acquisition
    to the described event. [cumming-2026]'s three evidential
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
class HasEvidentialPerspective (α : Type*) where
  /-- The evidential perspective of `a`, when defined. -/
  toEvidentialPerspective : α → Option EvidentialPerspective

export HasEvidentialPerspective (toEvidentialPerspective)

/-- A value is *nonfuture* iff it projects to a retrospective or
    contemporaneous perspective — i.e., evidence is downstream of the
    event (T ≤ A). Prospective and "no perspective" both fail.

    Defined uniformly over `HasEvidentialPerspective` so that downstream
    types (constraint enums, paradigm rows, modal evidence types) inherit
    one decidable predicate instead of hand-rolling parallel definitions. -/
def IsNonfuture {α : Type*} [HasEvidentialPerspective α] (a : α) : Prop :=
  toEvidentialPerspective a = some .retrospective ∨
  toEvidentialPerspective a = some .contemporaneous

instance {α : Type*} [HasEvidentialPerspective α] :
    DecidablePred (@IsNonfuture α _) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Types that project to a coarse evidential source. The stronger entry
    point into the vocabulary: declaring a source also yields a
    perspective, via the canonical source mapping (the low-priority
    instance below). Types whose evidence classification cross-cuts the
    source taxonomy project partially (`none` off the shared part). -/
class HasCoarseSource (α : Type*) where
  /-- The coarse evidential source of `a`, when defined. -/
  toCoarseSource : α → Option CoarseSource

export HasCoarseSource (toCoarseSource)

/-! ### Canonical instances -/

/-- The coarse source taxonomy projects to perspective by the canonical
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

instance : HasCoarseSource CoarseSource where
  toCoarseSource := some

/-- Source-declaring types inherit their perspective through the canonical
    mapping. Low priority: a type with its own perspective classification
    keeps it. -/
instance (priority := 100) {α : Type*} [HasCoarseSource α] :
    HasEvidentialPerspective α where
  toEvidentialPerspective a :=
    (toCoarseSource a).bind CoarseSource.toEvidentialPerspective

/-- The perspective type projects to itself. -/
instance : HasEvidentialPerspective EvidentialPerspective where
  toEvidentialPerspective := some

end Semantics.Evidential
