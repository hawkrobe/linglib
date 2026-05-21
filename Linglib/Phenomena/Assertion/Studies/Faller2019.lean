import Mathlib.Data.Set.Basic
import Linglib.Core.Discourse.Roles
import Linglib.Theories.Semantics.Questions.Basic

/-!
# Faller (2019): The discourse commitments of illocutionary reportatives
@cite{faller-2019a} @cite{farkas-bruce-2010} @cite{stalnaker-1978}
@cite{walker-1996} @cite{krifka-2014} @cite{anderbois-2014}
@cite{gunlogson-2008} @cite{murray-2014} @cite{goffman-1979}

Faller's discourse-update framework for the Cuzco Quechua reportative
`=si`. The empirical puzzle (her eq. 1):

* (a) Speakers of CQ uttering a declarative with `=si` need NOT be
  committed to the reported proposition φ — they may even deny it.
* (b) Despite (a), they often INTEND φ to resolve the QUD.

Faller's solution: separate **animator** from **principal** (Goffman
1979). The reportative encodes that the animator's commitment is to
HAVING REPORTATIVE EVIDENCE, while the principal — distinct from the
animator — is the one committed to truth. The Collaborative Principle
(Walker 1996) then derives the animator's *dependent* truth commitment
when they don't immediately disagree.

## Substrate consumed

* `Core/Discourse/Roles.DiscourseRole` for binary speaker/addressee
  (Faller adds Goffman's animator/author/principal — see § Goffman roles
  below; if a second study consumes these they graduate to substrate).
* `Theories/Semantics/Questions/Basic.Core.Question` is *not* directly used — Faller's
  Table is a stack of pushed propositions (her T_i), simpler than
  the inquisitive substrate.

## What this file does NOT consume

* `Theories/Dialogue/SAL/*` (van der Leer 2026): SAL refines Faller
  by adding a Kripke layer inside each commitment-set. Faller's
  framework is the coarser set-of-propositions level. Faller and
  SAL relate by forgetful projection (SAL → Faller drops the Kripke
  structure inside states).
* `Theories/Dialogue/CommitmentSpace.lean` (Krifka 2015): a different
  framework (commitment-space tree of propositional states); Faller
  builds on Farkas-Bruce 2010 instead.

## Notes for future substrate promotion

Three patterns arise in this file that may eventually graduate to
substrate when a second consumer needs them:

1. **Goffman roles** (Animator/Author/Principal). Cited by AnderBois
   2014, Murray 2014, Bary 2025, MV 2026. If/when a second study file
   imports them, promote to `Core/Discourse/GoffmanRoles.lean`.
2. **Multi-typed commitment sets** (TC, AeC, RepC, BpgC). The "open
   list of evidence-typed commitment sets per agent" pattern. Faller
   has 4 types; future papers may add more. If a second consumer wants
   the same shape, promote a generic `EvidenceTypedCommitments` to
   `Theories/Discourse/`.
3. **Collaborative Principle** as a defeasible discourse rule.
   Referenced by Walker 1996, Asher-Lascarides 2008, Geurts 2019,
   Bary 2025. Substrate candidate.

Each is currently inline in this study file.
-/

namespace Phenomena.Assertion.Studies.Faller2019

open Core.Discourse (DiscourseRole)

variable {W : Type*}

/-! ### § Goffman 1979 speaker roles (inline; promote to substrate when 2nd consumer arrives) -/

/-- @cite{goffman-1979} Frame Analysis distinguishes three roles within
    "speaker": the **animator** physically utters; the **author** chose
    the words; the **principal** is committed by the words.

    In standard cases all three coincide; reportatives (Faller 2019),
    quotations, messengers, and spokespersons separate them. -/
inductive GoffmanRole where
  /-- The individual physically producing the utterance (sound waves). -/
  | animator
  /-- The individual who selected the words and sentiments expressed. -/
  | author
  /-- The individual whose position is established by the words —
      whose commitment is conveyed. -/
  | principal
  deriving DecidableEq, Repr, Inhabited

/-- A Goffman-role assignment: who fills each of the three roles in a
    given utterance. In default cases (`a = author = principal`), this
    collapses to the standard speaker. Reportatives require
    `animator ≠ principal`. -/
structure RoleAssignment (E : Type*) where
  animator : E
  author : E
  principal : E

/-- The canonical-speaker assignment: animator = author = principal. -/
def RoleAssignment.canonical {E : Type*} (e : E) : RoleAssignment E :=
  { animator := e, author := e, principal := e }

@[simp] theorem canonical_animator {E : Type*} (e : E) :
    (RoleAssignment.canonical e).animator = e := rfl

@[simp] theorem canonical_principal {E : Type*} (e : E) :
    (RoleAssignment.canonical e).principal = e := rfl

@[simp] theorem canonical_author {E : Type*} (e : E) :
    (RoleAssignment.canonical e).author = e := rfl

/-- A messenger-style role assignment: animator and principal are distinct.
    This is the configuration the CQ reportative `=si` requires
    (Faller 2019 eq. 35.ii). -/
def RoleAssignment.messenger {E : Type*} (anim prin : E) : RoleAssignment E :=
  { animator := anim, author := anim, principal := prin }

/-! ### § Faller's commitment-typed discourse state -/

/-- @cite{faller-2019a} eqs. 24-25: the per-agent commitment sets.
    Open-ended; Faller introduces TC, AeC, RepC, BpgC explicitly and
    notes "other types of evidential commitment sets" can be added.

    A `Set (Set W)` per evidence type per agent: the set of propositions
    (modelled as `Set W`) the agent has committed to *of that type*.

    `truthCommit a` = TC_a : "x is committed to the truth of φ"
    `evidCommit .adequate a` = AeC_a : "x has adequate evidence for φ"
    `evidCommit .reportative a` = RepC_a : "x has reportative evidence"
    `evidCommit .bpg a` = BpgC_a : "x has best possible grounds"
    Future cases extend `EvidenceType`. -/
inductive EvidenceType where
  /-- Adequate evidence (Grice 1989: p. 29). The default for unmarked
      assertions per Faller 2019 §4.2. -/
  | adequate
  /-- Reportative evidence (hearsay). The CQ `=si` adds to this. -/
  | reportative
  /-- Best possible grounds (the strongest perceptual / first-hand
      evidence type). The CQ `=mi` adds to this. -/
  | bpg
  /-- Inferential evidence (the CQ `-chá` conjectural). -/
  | inferential
  deriving DecidableEq, Repr, Inhabited

/-- Faller 2019's discourse state: per-agent typed commitment sets
    plus a Table (stack of issues) and Common Ground.

    Genericised over agent type `E` and world type `W`. -/
structure DiscourseState (W : Type*) (E : Type*) where
  /-- TC_x : truth commitments per agent. -/
  truthCommit : E → Set (Set W)
  /-- Per-evidence-type commitment sets per agent. -/
  evidCommit : EvidenceType → E → Set (Set W)
  /-- Faller's Table T: a stack of propositions pushed by speech acts. -/
  table : List (Set W)
  /-- Common Ground: jointly accepted propositions. -/
  commonGround : Set (Set W)

namespace DiscourseState

variable {E : Type*}

/-- The empty discourse state: no commitments, no table, no CG. -/
def empty : DiscourseState W E where
  truthCommit := fun _ => ∅
  evidCommit := fun _ _ => ∅
  table := []
  commonGround := ∅

/-- Add a proposition to an agent's truth commitments.

    Encoded propositionally (no `if`) to avoid requiring `DecidableEq E`:
    every other agent's commitments stay the same because the
    "added when `a' = a`" disjunct is only satisfied at the target
    agent. -/
def addTruthCommit (s : DiscourseState W E) (a : E) (φ : Set W) :
    DiscourseState W E :=
  { s with truthCommit := fun a' =>
      { ψ | ψ ∈ s.truthCommit a' ∨ (a' = a ∧ ψ = φ) } }

/-- Add a proposition to an agent's typed evidential commitments.
    Same propositional encoding as `addTruthCommit`. -/
def addEvidCommit (s : DiscourseState W E) (et : EvidenceType) (a : E) (φ : Set W) :
    DiscourseState W E :=
  { s with evidCommit := fun et' a' =>
      { ψ | ψ ∈ s.evidCommit et' a' ∨ (et' = et ∧ a' = a ∧ ψ = φ) } }

/-- Push a proposition on top of the Table. -/
def pushTable (s : DiscourseState W E) (φ : Set W) : DiscourseState W E :=
  { s with table := φ :: s.table }

@[simp] theorem empty_truthCommit (a : E) :
    (empty : DiscourseState W E).truthCommit a = ∅ := rfl

@[simp] theorem empty_evidCommit (et : EvidenceType) (a : E) :
    (empty : DiscourseState W E).evidCommit et a = ∅ := rfl

@[simp] theorem empty_table : (empty : DiscourseState W E).table = [] := rfl

end DiscourseState

/-! ### § PRESENT and =si

Faller 2019 eq. 27 (initial), revised at eq. 34 with role assignments:

```
PRESENT(φ, a, K_i) = K_{i+1} such that
  (i)   T_{i+1} = push(φ, T_i)               -- always: scope on Table
  (ii)  TC_{p, i+1} = TC_{p, i} ∪ {φ}        -- DEFAULT: principal commits to truth
  (iii) AeC_{a, i+1} = AeC_{a, i} ∪ {φ}      -- DEFAULT: animator commits to evidence
  (iv)  a_{i+1} = p_{i+1}                    -- DEFAULT: animator = principal
```

The reportative `=si` (Faller 2019 eq. 35) is a modifier on PRESENT:

```
=si(PRESENT)(φ, a, K_i) = PRESENT(φ, a, K_i) such that
  (i)  RepC_{a, i+1} = RepC_{a, i} ∪ {φ}    -- override (iii): RepC, not AeC
  (ii) a_{i+1} ≠ p_{i+1}                    -- override (iv): animator ≠ principal
```
-/

variable {E : Type*}

/-- @cite{faller-2019a} eq. 34 (final PRESENT): with all defaults active,
    PRESENT updates Table + TC_principal + AeC_animator + sets
    animator = principal.

    The `roles : RoleAssignment E` argument carries Faller's eq. 34.iv
    flexibility: the canonical speaker uses `RoleAssignment.canonical`;
    a messenger or reportative use the explicit assignment. -/
def PRESENT (φ : Set W) (roles : RoleAssignment E) (s : DiscourseState W E) :
    DiscourseState W E :=
  s.pushTable φ
    |>.addTruthCommit roles.principal φ
    |>.addEvidCommit .adequate roles.animator φ

/-- @cite{faller-2019a} eq. 35 (CQ `=si` modifier on PRESENT): override
    eq. 34.iii (commit to RepC instead of AeC) and require eq. 35.ii
    (animator ≠ principal).

    The role-distinctness requirement is encoded as a precondition: the
    operator only updates the state when `roles.animator ≠ roles.principal`.
    Otherwise it returns the input state unchanged (a defective speech
    act, per Faller's analysis). Requires `DecidableEq E` to test the
    role-distinctness premise — agents in any concrete discourse model
    are decidable-equal. -/
def reportativePRESENT [DecidableEq E] (φ : Set W) (roles : RoleAssignment E)
    (s : DiscourseState W E) : DiscourseState W E :=
  if roles.animator = roles.principal then s
  else
    s.pushTable φ
      |>.addTruthCommit roles.principal φ
      |>.addEvidCommit .reportative roles.animator φ

/-! ### § Headline theorems

These lift Faller's verbal claims to provable statements.
-/

/-- @cite{faller-2019a} default-PRESENT puts φ in the principal's TC.
    The headline (i) consequence of PRESENT — the speaker (=principal,
    canonically) commits to truth. -/
theorem present_commits_principal_to_truth
    (φ : Set W) (e : E) (s : DiscourseState W E) :
    φ ∈ (PRESENT φ (RoleAssignment.canonical e) s).truthCommit e := by
  -- After PRESENT, the principal's TC is `s.truthCommit e ∪ {φ}` modulo
  -- the propositional encoding. Witness via the `(a' = a ∧ ψ = φ)` disjunct.
  show φ ∈ { ψ | ψ ∈ _ ∨ (e = e ∧ ψ = φ) }
  exact Or.inr ⟨rfl, rfl⟩

/-- @cite{faller-2019a} default-PRESENT puts φ in the animator's AeC. -/
theorem present_commits_animator_to_adequate_evidence
    (φ : Set W) (e : E) (s : DiscourseState W E) :
    φ ∈ (PRESENT φ (RoleAssignment.canonical e) s).evidCommit .adequate e := by
  show φ ∈ { ψ | ψ ∈ _ ∨ (EvidenceType.adequate = .adequate ∧ e = e ∧ ψ = φ) }
  exact Or.inr ⟨rfl, rfl, rfl⟩

/-- @cite{faller-2019a} eq. 35.i: `=si` adds to RepC. The animator's
    RepC for φ DOES include φ after `=si(PRESENT(φ))` — the headline
    finding that reportatives flag the evidence type. -/
theorem reportative_commits_animator_to_reportative_evidence
    [DecidableEq E] (φ : Set W) (anim prin : E) (h : anim ≠ prin)
    (s : DiscourseState W E) :
    φ ∈ (reportativePRESENT φ (RoleAssignment.messenger anim prin) s).evidCommit
        .reportative anim := by
  simp only [reportativePRESENT, RoleAssignment.messenger, if_neg h]
  show φ ∈ { ψ | ψ ∈ _ ∨ (EvidenceType.reportative = .reportative ∧ anim = anim ∧ ψ = φ) }
  exact Or.inr ⟨rfl, rfl, rfl⟩

/-- @cite{faller-2019a} eq. 35: `=si` commits the *principal* (not the
    animator) to truth. The headline finding: the reportative shifts
    truth-commitment to the third-party principal. -/
theorem reportative_commits_principal_to_truth
    [DecidableEq E] (φ : Set W) (anim prin : E) (h : anim ≠ prin)
    (s : DiscourseState W E) :
    φ ∈ (reportativePRESENT φ (RoleAssignment.messenger anim prin) s).truthCommit
        prin := by
  simp only [reportativePRESENT, RoleAssignment.messenger, if_neg h]
  show φ ∈ { ψ | ψ ∈ _ ∨ (prin = prin ∧ ψ = φ) }
  exact Or.inr ⟨rfl, rfl⟩

/-- @cite{faller-2019a} *Absence of Commitment* (eq. 1.a, headline):
    after `=si(PRESENT(φ))` with distinct animator and principal, the
    ANIMATOR is NOT committed to truth of φ.

    Formal version: starting from the empty state, `=si(PRESENT(φ))`
    does not put φ in the animator's TC. -/
theorem reportative_does_not_commit_animator_to_truth
    [DecidableEq E] (φ : Set W) (anim prin : E) (h : anim ≠ prin) :
    φ ∉ (reportativePRESENT φ (RoleAssignment.messenger anim prin)
          DiscourseState.empty).truthCommit anim := by
  simp only [reportativePRESENT, RoleAssignment.messenger, if_neg h]
  -- The animator's TC update only fires on the principal's TC (per eq. 35),
  -- so the only φ-witness branch requires `anim = prin`, contradicting `h`.
  show ¬ φ ∈ { ψ | ψ ∈ _ ∨ (anim = prin ∧ ψ = φ) }
  rintro (hempty | ⟨heq, _⟩)
  · exact (hempty : φ ∈ (∅ : Set (Set W))).elim
  · exact h heq

end Phenomena.Assertion.Studies.Faller2019
