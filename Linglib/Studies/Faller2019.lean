import Mathlib.Data.Set.Basic
import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.Commitment.Table

/-!
# Faller (2019): The discourse commitments of illocutionary reportatives

@cite{faller-2019a} @cite{farkas-bruce-2010} @cite{stalnaker-1978}
@cite{walker-1996} @cite{krifka-2014} @cite{anderbois-2014}
@cite{gunlogson-2008} @cite{murray-2014} @cite{goffman-1979}

Faller's discourse-update account of the Cuzco Quechua reportative `=si`.
The puzzle (her display (1)): a speaker of a reportative declarative need
not be committed to the reported proposition `φ` — they may even deny it
(1a) — yet often intends `φ` to resolve the QUD (1b). Faller's solution
splits Goffman's *animator* from *principal*: the reportative commits the
animator only to having reportative evidence, while the distinct principal
carries the truth commitment. The Collaborative Principle (@cite{walker-1996})
then derives the animator's *dependent* truth commitment when they do not
disagree.

## Main declarations

* `GoffmanRole`, `RoleAssignment` — animator / author / principal (her (30)).
* `EvidenceType` — adequate / reportative / bpg (her (24)–(25)), with an
  `inferential` extension.
* `DiscourseState` — the Farkas-Bruce table state extended with
  per-evidence-type commitment sets.
* `PRESENT`, `reportativePRESENT` — the speech-act operators (her (34), (35)).

## Implementation notes

* Built over `Discourse.Commitment.Table.DiscourseState A W (Set W)`: truth
  commitments live in the inherited per-agent slate `dc`, the Table is the
  proposition stack (`I := Set W`), and the common ground is `cg`. Only the
  evidence-type family `evidCommit` is Faller-specific.
* Faller numbers her framework as displays `(24)`, `(34)`, `(35)` — not
  equations.

## Todo

* Model the (1b) half of the puzzle: the Collaborative Principle
  (@cite{walker-1996}, her (29)) deriving the animator's *dependent* truth
  commitment when they do not disagree (her Figure 6). Only the (1a)
  Absence-of-Commitment half is formalized here.
* Promote `GoffmanRole` / `EvidenceType` to `Discourse/` once a second
  consumer (e.g. @cite{anderbois-2014}, @cite{murray-2014}) imports them.
-/

namespace Faller2019

open Discourse.Commitment (CommitmentSlate TaggedSlate CommitmentSource)

/-! ### Goffman 1979 speaker roles -/

/-- @cite{goffman-1979} "Footing" distinguishes three roles within
    "speaker": the **animator** physically utters; the **author** chose the
    words; the **principal** is committed by the words. In standard cases all
    three coincide; reportatives, quotations, and messengers separate them. -/
inductive GoffmanRole where
  /-- The individual physically producing the utterance (sound waves). -/
  | animator
  /-- The individual who selected the words and sentiments expressed. -/
  | author
  /-- The individual whose position is established by the words. -/
  | principal
  deriving DecidableEq, Repr, Inhabited

/-- A Goffman-role assignment: who fills each role in an utterance. In default
    cases (`animator = author = principal`) it collapses to the standard
    speaker; reportatives require `animator ≠ principal`. -/
structure RoleAssignment (E : Type*) where
  animator : E
  author : E
  principal : E

namespace RoleAssignment

variable {E : Type*}

/-- The canonical-speaker assignment: animator = author = principal. -/
def canonical (e : E) : RoleAssignment E := ⟨e, e, e⟩

/-- A messenger-style assignment: animator and principal distinct. This is
    the configuration the CQ reportative `=si` requires (her (35ii)). -/
def messenger (anim prin : E) : RoleAssignment E := ⟨anim, anim, prin⟩

@[simp] theorem canonical_animator (e : E) : (canonical e).animator = e := rfl
@[simp] theorem canonical_author (e : E) : (canonical e).author = e := rfl
@[simp] theorem canonical_principal (e : E) : (canonical e).principal = e := rfl

@[simp] theorem messenger_animator (anim prin : E) :
    (messenger anim prin).animator = anim := rfl
@[simp] theorem messenger_principal (anim prin : E) :
    (messenger anim prin).principal = prin := rfl

end RoleAssignment

/-! ### Commitment-typed discourse state -/

/-- The evidence types Faller tracks in distinct commitment sets. Her (24)–(25)
    define exactly the first three (AeC, RepC, BpgC); `inferential` is an
    extension — Faller mentions inferential commitment in prose but defines no
    `InfC` set. -/
inductive EvidenceType where
  /-- Adequate evidence (@cite{faller-2019a}, after Grice): the default for
      unmarked assertions. -/
  | adequate
  /-- Reportative evidence (hearsay). The CQ `=si` adds to this. -/
  | reportative
  /-- Best possible grounds (strongest first-hand evidence). The CQ `=mi`
      adds to this. -/
  | bpg
  /-- Inferential evidence (the CQ `-chá` conjectural). Extension; not one of
      Faller's defined commitment sets. -/
  | inferential
  deriving DecidableEq, Repr, Inhabited

/-- Faller's discourse structure: the Farkas-Bruce table state — truth
    commitments in the inherited slate `dc`, a proposition-stack Table, and a
    common ground — extended with per-evidence-type commitment sets. -/
structure DiscourseState (A W : Type*)
    extends Discourse.Commitment.Table.DiscourseState A W (Set W) where
  /-- Per-evidence-type commitment sets per agent (AeC, RepC, BpgC, ...). -/
  evidCommit : EvidenceType → A → CommitmentSlate W

namespace DiscourseState

variable {A W : Type*}

/-- The empty discourse state: no commitments, empty Table, trivial CommonGround. -/
def empty : DiscourseState A W :=
  { Discourse.Commitment.Table.DiscourseState.empty with
    evidCommit := fun _ _ => CommitmentSlate.empty }

/-- Agent `a` is truth-committed to `φ` (φ ∈ TC_a). -/
def CommittedTrue (s : DiscourseState A W) (a : A) (φ : Set W) : Prop :=
  φ ∈ (s.dc a).toSlate.commitments

/-- Agent `a` holds `φ` as evidence of type `et` (φ ∈ et-C_a). -/
def CommittedEvid (s : DiscourseState A W) (et : EvidenceType) (a : A) (φ : Set W) :
    Prop :=
  φ ∈ (s.evidCommit et a).commitments

/-- Push a proposition onto the Table. -/
def pushTable (s : DiscourseState A W) (φ : Set W) : DiscourseState A W :=
  { s with toDiscourseState := s.toDiscourseState.pushItem φ }

/-- Add `φ` to agent `a`'s truth commitments (the inherited slate `dc`), with
    provenance `src` (default self-generated — the plain-assertion case;
    `reportativePRESENT` marks the principal's animator-introduced commitment
    other-generated, per @cite{faller-2019a} fn. 30 / §6.1). -/
def addTruthCommit [DecidableEq A] (s : DiscourseState A W) (a : A) (φ : Set W)
    (src : CommitmentSource := .selfGenerated) : DiscourseState A W :=
  { s with toDiscourseState := s.toDiscourseState.addCommit a φ src }

/-- Add `φ` to agent `a`'s type-`et` evidential commitments. -/
def addEvidCommit [DecidableEq A] (s : DiscourseState A W)
    (et : EvidenceType) (a : A) (φ : Set W) : DiscourseState A W where
  toDiscourseState := s.toDiscourseState
  evidCommit :=
    Function.update s.evidCommit et
      (Function.update (s.evidCommit et) a ((s.evidCommit et a).add φ))

/-! #### Update API

Per-operator `@[simp]` lemmas, so the headline proofs reduce through this API
rather than reaching into substrate slate internals.
-/

@[simp] theorem pushTable_toDiscourseState (s : DiscourseState A W) (φ : Set W) :
    (s.pushTable φ).toDiscourseState = s.toDiscourseState.pushItem φ := rfl

@[simp] theorem addTruthCommit_toDiscourseState [DecidableEq A]
    (s : DiscourseState A W) (a : A) (φ : Set W) (src : CommitmentSource) :
    (s.addTruthCommit a φ src).toDiscourseState =
      s.toDiscourseState.addCommit a φ src := rfl

@[simp] theorem addEvidCommit_toDiscourseState [DecidableEq A]
    (s : DiscourseState A W) (et : EvidenceType) (a : A) (φ : Set W) :
    (s.addEvidCommit et a φ).toDiscourseState = s.toDiscourseState := rfl

@[simp] theorem addTruthCommit_evidCommit [DecidableEq A]
    (s : DiscourseState A W) (a : A) (φ : Set W) (src : CommitmentSource) :
    (s.addTruthCommit a φ src).evidCommit = s.evidCommit := rfl

@[simp] theorem pushTable_evidCommit (s : DiscourseState A W) (φ : Set W) :
    (s.pushTable φ).evidCommit = s.evidCommit := rfl

@[simp] theorem addEvidCommit_evidCommit_self [DecidableEq A]
    (s : DiscourseState A W) (et : EvidenceType) (a : A) (φ : Set W) :
    (s.addEvidCommit et a φ).evidCommit et a = (s.evidCommit et a).add φ := by
  simp [addEvidCommit]

@[simp] theorem addEvidCommit_evidCommit_of_ne_agent [DecidableEq A]
    (s : DiscourseState A W) (et : EvidenceType) {a b : A} (h : b ≠ a) (φ : Set W) :
    (s.addEvidCommit et a φ).evidCommit et b = s.evidCommit et b := by
  simp [addEvidCommit, Function.update_of_ne h]

@[simp] theorem addEvidCommit_evidCommit_of_ne_type [DecidableEq A]
    (s : DiscourseState A W) {et et' : EvidenceType} (h : et' ≠ et) (a : A)
    (φ : Set W) :
    (s.addEvidCommit et a φ).evidCommit et' = s.evidCommit et' := by
  simp [addEvidCommit, Function.update_of_ne h]

/-! #### Commitment-membership API -/

@[simp] theorem committedTrue_addTruthCommit_self [DecidableEq A]
    (s : DiscourseState A W) (a : A) (φ : Set W) (src : CommitmentSource) :
    (s.addTruthCommit a φ src).CommittedTrue a φ := by
  simp [CommittedTrue, TaggedSlate.toSlate, TaggedSlate.add]
  exact List.mem_cons_self

@[simp] theorem committedTrue_addTruthCommit_of_ne [DecidableEq A]
    (s : DiscourseState A W) {a b : A} (h : b ≠ a) (φ ψ : Set W)
    (src : CommitmentSource) :
    (s.addTruthCommit a φ src).CommittedTrue b ψ ↔ s.CommittedTrue b ψ := by
  simp [CommittedTrue, h]

@[simp] theorem committedTrue_pushTable (s : DiscourseState A W) (φ ψ : Set W)
    (a : A) : (s.pushTable φ).CommittedTrue a ψ ↔ s.CommittedTrue a ψ := by
  simp [CommittedTrue]

@[simp] theorem committedTrue_addEvidCommit [DecidableEq A]
    (s : DiscourseState A W) (et : EvidenceType) (a b : A) (φ ψ : Set W) :
    (s.addEvidCommit et a φ).CommittedTrue b ψ ↔ s.CommittedTrue b ψ := by
  simp [CommittedTrue]

@[simp] theorem committedEvid_addEvidCommit_self [DecidableEq A]
    (s : DiscourseState A W) (et : EvidenceType) (a : A) (φ : Set W) :
    (s.addEvidCommit et a φ).CommittedEvid et a φ := by
  simp [CommittedEvid, CommitmentSlate.add]
  exact List.mem_cons_self

@[simp] theorem committedEvid_addTruthCommit [DecidableEq A]
    (s : DiscourseState A W) (et : EvidenceType) (a b : A) (φ ψ : Set W)
    (src : CommitmentSource) :
    (s.addTruthCommit b φ src).CommittedEvid et a ψ ↔ s.CommittedEvid et a ψ := by
  simp [CommittedEvid]

@[simp] theorem committedEvid_pushTable (s : DiscourseState A W) (et : EvidenceType)
    (a : A) (φ ψ : Set W) :
    (s.pushTable φ).CommittedEvid et a ψ ↔ s.CommittedEvid et a ψ := by
  simp [CommittedEvid]

@[simp] theorem not_committedTrue_empty (a : A) (φ : Set W) :
    ¬ (empty : DiscourseState A W).CommittedTrue a φ := by
  simp [CommittedTrue, empty, TaggedSlate.toSlate, TaggedSlate.empty]
  exact List.not_mem_nil

end DiscourseState

/-! ### PRESENT and =si

Faller's final PRESENT, her display (34) (revising the initial three-clause
(27), which committed the speaker's own `TC` and `AeC`):

```
PRESENT(φ, a, K_i) = K_{i+1} such that
  (i)   T_{i+1}   = push(φ, T_i)            -- always: scope on Table
  (ii)  TC_{p,i+1} = TC_{p,i} ∪ {φ}         -- principal commits to truth
  (iii) AeC_{a,i+1} = AeC_{a,i} ∪ {φ}       -- animator commits to evidence
  (iv)  a_{i+1}    = p_{i+1}                -- default: animator = principal
```

The reportative `=si` (her (35)) is a modifier on PRESENT:

```
=si(PRESENT)(φ, a, K_i) = PRESENT(φ, a, K_i) such that
  (i)  RepC_{a,i+1} = RepC_{a,i} ∪ {φ}      -- override (34iii): RepC, not AeC
  (ii) a_{i+1} ≠ p_{i+1}                    -- override (34iv): animator ≠ principal
```
-/

namespace DiscourseState

variable {A W : Type*}

/-- @cite{faller-2019a} (34): with defaults active, PRESENT pushes `φ` to the
    Table, commits the principal to truth, and the animator to adequate
    evidence. The `roles` argument carries (34iv) flexibility: the canonical
    speaker uses `RoleAssignment.canonical`; a messenger uses the explicit
    assignment. -/
def PRESENT [DecidableEq A] (φ : Set W) (roles : RoleAssignment A)
    (s : DiscourseState A W) : DiscourseState A W :=
  s.pushTable φ
    |>.addTruthCommit roles.principal φ
    |>.addEvidCommit .adequate roles.animator φ

/-- @cite{faller-2019a} (35): the CQ `=si` modifier on PRESENT overrides
    (34iii) (commit to RepC, not AeC) and requires (35ii) (animator ≠
    principal). The distinctness requirement is a precondition: the operator
    updates only when `roles.animator ≠ roles.principal`, else returns the
    input unchanged (a defective speech act). -/
def reportativePRESENT [DecidableEq A] (φ : Set W) (roles : RoleAssignment A)
    (s : DiscourseState A W) : DiscourseState A W :=
  if roles.animator = roles.principal then s
  else
    s.pushTable φ
      |>.addTruthCommit roles.principal φ .otherGenerated
      |>.addEvidCommit .reportative roles.animator φ

/-! ### Headline theorems

These lift Faller's verbal claims to provable statements over the substrate
discourse state.
-/

/-- @cite{faller-2019a} (34ii): default PRESENT puts `φ` in the principal's
    truth commitments. -/
theorem present_commits_principal_to_truth [DecidableEq A]
    (φ : Set W) (e : A) (s : DiscourseState A W) :
    (PRESENT φ (RoleAssignment.canonical e) s).CommittedTrue e φ := by
  simp [PRESENT]

/-- @cite{faller-2019a} (34iii): default PRESENT puts `φ` in the animator's
    adequate-evidence commitments. -/
theorem present_commits_animator_to_adequate_evidence [DecidableEq A]
    (φ : Set W) (e : A) (s : DiscourseState A W) :
    (PRESENT φ (RoleAssignment.canonical e) s).CommittedEvid .adequate e φ := by
  simp [PRESENT]

/-- @cite{faller-2019a} (35i): `=si` adds `φ` to the animator's reportative
    commitments — the headline that reportatives flag the evidence type. -/
theorem reportative_commits_animator_to_reportative_evidence [DecidableEq A]
    (φ : Set W) (anim prin : A) (h : anim ≠ prin) (s : DiscourseState A W) :
    (reportativePRESENT φ (RoleAssignment.messenger anim prin) s).CommittedEvid
        .reportative anim φ := by
  simp [reportativePRESENT, if_neg h]

/-- @cite{faller-2019a} (35): `=si` commits the *principal* (not the animator)
    to truth — the reportative shifts truth-commitment to the third party. -/
theorem reportative_commits_principal_to_truth [DecidableEq A]
    (φ : Set W) (anim prin : A) (h : anim ≠ prin) (s : DiscourseState A W) :
    (reportativePRESENT φ (RoleAssignment.messenger anim prin) s).CommittedTrue
        prin φ := by
  simp [reportativePRESENT, if_neg h]

/-- @cite{faller-2019a} *Absence of Commitment* (1a): after `=si(PRESENT(φ))`
    with distinct animator and principal, the animator is *not* truth-committed
    to `φ`. Starting from `empty`, the animator's truth commitments stay empty
    because `=si`'s truth update fires only on the principal. -/
theorem reportative_does_not_commit_animator_to_truth [DecidableEq A]
    (φ : Set W) (anim prin : A) (h : anim ≠ prin) :
    ¬ (reportativePRESENT φ (RoleAssignment.messenger anim prin)
          DiscourseState.empty).CommittedTrue anim φ := by
  simp [reportativePRESENT, h]

/-- @cite{faller-2019a} (25): truth and evidential commitments are formally
    independent — witnessed by the reportative configuration, where the animator
    holds `φ` as reportative evidence yet is *not* truth-committed to it. -/
theorem reportative_evidence_without_truth [DecidableEq A]
    (φ : Set W) (anim prin : A) (h : anim ≠ prin) :
    (reportativePRESENT φ (RoleAssignment.messenger anim prin)
        DiscourseState.empty).CommittedEvid .reportative anim φ ∧
      ¬ (reportativePRESENT φ (RoleAssignment.messenger anim prin)
          DiscourseState.empty).CommittedTrue anim φ :=
  ⟨reportative_commits_animator_to_reportative_evidence φ anim prin h _,
   reportative_does_not_commit_animator_to_truth φ anim prin h⟩

end DiscourseState

end Faller2019
