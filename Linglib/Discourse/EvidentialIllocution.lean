import Mathlib.Data.Set.Insert
import Linglib.Semantics.Composition.Layered
import Linglib.Features.Evidentiality
import Linglib.Discourse.Roles

/-!
# Evidential Illocutionary Operators
@cite{faller-2002} @cite{faller-2019a} @cite{murray-2014} @cite{murray-2017}
@cite{krifka-2014} @cite{anderbois-brasoveanu-henderson-2015}
@cite{martinez-vera-2024} @cite{martinez-vera-2026}

Two illocutionary operators consistently distinguish direct from indirect
evidentials in the Faller / Murray tradition:

- `assert` (paired with direct evidentials, e.g. Cuzco Quechua *-mi*,
  Saraguro Kichwa *-rka*, Aymara direct *-cha*): the speaker commits to
  the scope proposition AND to the not-at-issue evidential proposition.
- `present` (paired with reportative/inferential evidentials, e.g. Cuzco
  Quechua *-si*, Saraguro Kichwa *-shka*): the speaker brings the scope to
  the addressee's attention WITHOUT committing to it; commits only to the
  not-at-issue evidential proposition.

Both operators are *illocutionary* in the sense of
@cite{martinez-vera-2026} Composition Rule III: they consume the full
⟨at-issue, not-at-issue⟩ pair from `Semantics/Composition/Layered`
and produce a discourse update.

## What this module exposes

* `EvidentialAct W` — the act type produced by `assert`/`present`. The
  name disambiguates from `Dialogue.Krifka.SpeechAct W` (commitment-space
  framework, different shape) and `Semantics.Modality.Assert.SpeechActEvent W`
  (event-style speech-act primitive). All three are different
  formalisations of overlapping concepts; future bridge work would
  unify them through projection lemmas.
* `EvidentialAct.raisedPropositions` — the propositions the act puts
  forward to the addressee. **This is the substrate-level projection
  that downstream highlighting consumers cite, rather than re-deriving
  from `commitsToScope`.** `assert` raises just the scope; `present`
  raises both the scope and its complement (the polar issue), since
  the speaker is non-committal and both options are on the table.
* Substrate theorems `present_raises_polar_negation`,
  `assert_raises_only_scope` connect `commitsToScope` to the
  highlighting-relevant projection. Verum studies, biased polar question
  studies, and reportative-evidential studies all consume these instead
  of re-stipulating discourse-update behaviour.

Existing substrate:
* `Discourse.Commitment` provides commitment slates and
  `IndexedCommitment` (Krifka 2015's S⊢φ); `EvidentialAct` here is a
  thinner illocutionary-output type that any of the larger
  discourse-state trackers can ingest.
* `Features.Evidentiality.EvidentialSource` provides the canonical
  Aikhenvald 3-way; this module supplies the typological default
  evidence-source-to-illocutionary-operator mapping.
-/

namespace Discourse.EvidentialIllocution

open Semantics.Composition.Layered (BiLayered)
open Discourse (DiscourseRole)
open Features.Evidentiality (EvidentialSource)

/-- The result of applying an illocutionary operator to a layered argument.

    Records: speaker, addressee, the scope proposition (regardless of
    commitment), the not-at-issue evidential proposition, and the binary
    flag distinguishing `assert`-flavour (commits to scope) from
    `present`-flavour (does not). All four discourse-update tracker
    families (Krifka commitment-space, Farkas-Bruce table, Murray-style
    cards, Anderbois-Brasoveanu-Henderson AI-stack) can ingest this
    record by reading the relevant fields.

    Named `EvidentialAct` to disambiguate from the existing
    `Dialogue.Krifka.SpeechAct` (CommitmentSpace.lean) and
    `Semantics.Modality.Assert.SpeechActEvent` — three different
    formalisations of overlapping concepts that should eventually be
    bridged. -/
structure EvidentialAct (W : Type*) where
  /-- Speaker of the act. -/
  speaker : DiscourseRole
  /-- Addressee. -/
  addressee : DiscourseRole
  /-- The proposition under consideration (regardless of speaker commitment). -/
  scope : Set W
  /-- The not-at-issue (evidential) proposition the speaker commits to. -/
  evidentialContent : Set W
  /-- Whether the speaker publicly commits to `scope` (assert-flavour) or
      merely brings it to attention (present-flavour). -/
  commitsToScope : Bool

variable {W : Type*}

/-- @cite{faller-2002}/@cite{faller-2019a}: `assert(⟨A, N⟩)` commits the
    speaker both to A (the scope proposition) and to N (the evidential
    proposition). Used with direct evidentials. -/
def assert (s a : DiscourseRole) (β : BiLayered W) : EvidentialAct W :=
  { speaker := s
  , addressee := a
  , scope := { w | β.atIssue w }
  , evidentialContent := { w | β.notAtIssue w }
  , commitsToScope := true }

/-- @cite{murray-2014}/@cite{faller-2019a}: `present(⟨A, N⟩)` brings A to
    the addressee's attention but does NOT commit the speaker to A; it
    commits only to N (the evidential proposition). Used with
    reportative/inferential evidentials. -/
def present (s a : DiscourseRole) (β : BiLayered W) : EvidentialAct W :=
  { speaker := s
  , addressee := a
  , scope := { w | β.atIssue w }
  , evidentialContent := { w | β.notAtIssue w }
  , commitsToScope := false }

@[simp] theorem assert_commitsToScope (s a : DiscourseRole) (β : BiLayered W) :
    (assert s a β).commitsToScope = true := rfl

@[simp] theorem present_commitsToScope (s a : DiscourseRole) (β : BiLayered W) :
    (present s a β).commitsToScope = false := rfl

/-- The defining contrast between `assert` and `present`: they agree on
    speaker, addressee, scope, and evidential content, but disagree on
    whether the speaker commits to scope. -/
theorem assert_present_differ_only_in_scope_commitment
    (s a : DiscourseRole) (β : BiLayered W) :
    (assert s a β).scope = (present s a β).scope ∧
    (assert s a β).evidentialContent = (present s a β).evidentialContent ∧
    (assert s a β).commitsToScope ≠ (present s a β).commitsToScope := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [assert_commitsToScope, present_commitsToScope]
  decide

/-! ### § Raised propositions: the substrate-level highlighting projection

`raisedPropositions` is the propositions an act puts forward for the
addressee to consider. The `commitsToScope` flag determines what's
raised:

* `commitsToScope = true` (assert): the speaker has settled the issue;
  only the scope proposition is raised.
* `commitsToScope = false` (present): the speaker has NOT settled the
  issue; both the scope and its negation are raised — the polar issue
  is open.

This is the substrate-level claim about Faller/Murray's analysis.
Verum studies (e.g. `Studies/MartinezVera2026.lean`)
build their discourse-update maps by adding `raisedPropositions` to
whatever salience tracker they use, rather than re-stipulating the
match-on-`commitsToScope`.
-/

/-- The propositions an act puts forward to the addressee.

    `assert` raises just the scope (the speaker has committed; ¬scope is
    not on the table). `present` raises both scope and ¬scope (the speaker
    is non-committal, so both polar options are open).

    This is the substrate-level projection that downstream highlighting
    consumers cite. The `if` is local here so future studies don't
    re-derive it. -/
def EvidentialAct.raisedPropositions (a : EvidentialAct W) : Set (Set W) :=
  if a.commitsToScope then {a.scope} else {a.scope, a.scopeᶜ}

/-- `assert` raises only the scope. -/
@[simp] theorem assert_raisedPropositions (s a : DiscourseRole) (β : BiLayered W) :
    (assert s a β).raisedPropositions = {{ w | β.atIssue w }} := by
  simp [EvidentialAct.raisedPropositions, assert]

/-- `present` raises both the scope and its complement (the polar issue). -/
@[simp] theorem present_raisedPropositions (s a : DiscourseRole) (β : BiLayered W) :
    (present s a β).raisedPropositions =
      ({ { w | β.atIssue w }, { w | β.atIssue w }ᶜ } : Set (Set W)) := by
  simp [EvidentialAct.raisedPropositions, present]

/-- `present` raises the negation of its scope as a salient alternative.
    This is the substrate fact verum studies cite to license a verum-marker
    follow-up after a reportative evidential. -/
theorem present_raises_polar_negation (s a : DiscourseRole) (β : BiLayered W) :
    { w | β.atIssue w }ᶜ ∈ (present s a β).raisedPropositions := by
  simp

/-- `assert` does NOT raise the negation of its scope, **provided** the
    scope is satisfiable (some world satisfies it). This rules out the
    degenerate empty-`W` case where every set equals its complement. The
    substrate fact verum studies cite to predict that a verum-marker
    follow-up is INFELICITOUS after a direct evidential. -/
theorem assert_does_not_raise_polar_negation
    (s a : DiscourseRole) (β : BiLayered W)
    (hne : ∃ w, β.atIssue w) :
    { w | β.atIssue w }ᶜ ∉ (assert s a β).raisedPropositions := by
  simp only [assert_raisedPropositions, Set.mem_singleton_iff]
  intro h
  obtain ⟨w, hw⟩ := hne
  have : w ∉ ({ w | β.atIssue w }ᶜ : Set W) := by simp [hw]
  rw [h] at this
  exact this hw

/-! ### § Typological mapping from evidence source to illocutionary flavour -/

/-- Typological mapping from evidential source to illocutionary operator
    flavour. Direct evidence licenses `assert`; hearsay and inference
    license `present` (@cite{faller-2002}, @cite{faller-2019a},
    @cite{murray-2014}, @cite{murray-2017}).

    This is a typological generalisation, not a definitional truth.
    Footnote 7 of @cite{martinez-vera-2026} documents an Andean exception
    (a speaker authoritative about Inca history uses the direct *-rka* in
    the absence of direct perceptual evidence); per-construction analyses
    can override the default. -/
inductive IllocutionaryFlavour where
  | assertFlavour
  | presentFlavour
  deriving DecidableEq, Repr, Inhabited

/-- Default mapping from evidential source to illocutionary flavour. -/
def IllocutionaryFlavour.ofEvidentialSource :
    EvidentialSource → IllocutionaryFlavour
  | .direct => .assertFlavour
  | .hearsay => .presentFlavour
  | .inference => .presentFlavour

@[simp] theorem flavour_direct :
    IllocutionaryFlavour.ofEvidentialSource .direct = .assertFlavour := rfl

@[simp] theorem flavour_hearsay :
    IllocutionaryFlavour.ofEvidentialSource .hearsay = .presentFlavour := rfl

@[simp] theorem flavour_inference :
    IllocutionaryFlavour.ofEvidentialSource .inference = .presentFlavour := rfl

/-- Apply the typologically-default operator for a given evidential source. -/
def applyDefault (src : EvidentialSource) (s a : DiscourseRole) (β : BiLayered W) :
    EvidentialAct W :=
  match IllocutionaryFlavour.ofEvidentialSource src with
  | .assertFlavour => assert s a β
  | .presentFlavour => present s a β

@[simp] theorem applyDefault_direct (s a : DiscourseRole) (β : BiLayered W) :
    applyDefault .direct s a β = assert s a β := rfl

@[simp] theorem applyDefault_hearsay (s a : DiscourseRole) (β : BiLayered W) :
    applyDefault .hearsay s a β = present s a β := rfl

@[simp] theorem applyDefault_inference (s a : DiscourseRole) (β : BiLayered W) :
    applyDefault .inference s a β = present s a β := rfl

/-- Direct evidentials commit the speaker to the scope proposition;
    indirect (hearsay/inference) evidentials do not. The headline
    typological generalisation. -/
theorem direct_commits_indirect_does_not (s a : DiscourseRole) (β : BiLayered W) :
    (applyDefault .direct s a β).commitsToScope = true ∧
    (applyDefault .hearsay s a β).commitsToScope = false ∧
    (applyDefault .inference s a β).commitsToScope = false :=
  ⟨rfl, rfl, rfl⟩

end Discourse.EvidentialIllocution
