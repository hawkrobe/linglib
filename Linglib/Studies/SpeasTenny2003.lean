/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Selection
import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Semantics.Context.Tower
import Linglib.Discourse.Roles
import Linglib.Semantics.Mood.Defs
import Linglib.Semantics.Epistemicity
import Linglib.Features.Evidentiality
import Linglib.Fragments.English.Pronouns
import Linglib.Features.Person.Basic

/-!
# Configurational Point-of-View Roles

Formalizes [speas-tenny-2003]. Pragmatic roles (SPEAKER, HEARER, SEAT OF
KNOWLEDGE) are configurationally determined by structural position in the
Speech Act Phrase (SAP), not primitive. Four moods are derived from two binary
features: [±finite] on the utterance content × whether the HEARER c-commands
the content.

## Key Claims

1. P-roles (SPEAKER, HEARER) are structural positions in SAP, not primitives.
2. 4 moods = 2×2 feature matrix: [±finite] × [±hearer-c-commands-content].
3. SEAT OF KNOWLEDGE is the *highest argument* of the Point-of-View domain
   (p.335): the HEARER exactly when the hearer c-commands the content. It is
   therefore *derived* from the same feature that drives `deriveMood`, not
   stipulated independently — so the matrix and the seat cannot disagree.
4. SAP is the highest phase → P-role resolution is root-only (invariant under
   context shift). Proved as `resolvePRole_shift_invariant`.

## Connections

- **Semantics/Context/Tower.lean**: `KContext.agent` = SPEAKER,
  `KContext.addressee` = HEARER; P-roles resolve through the canonical
  `Discourse.resolveRole` over a `ContextTower`.
- **Phase.lean**: `isPhaseHeadOf .SA` — SAP is the highest phase.
- **ExtendedProjection/Basic.lean**: `fValue .SA = 7 > fValue .C = 6`.
- **Semantics/Mood/Defs.lean**: the configurational seat-of-knowledge
  *diverges* from Lakoff's deontic `Illocutionary.authority` on imperatives
  (`seatOfKnowledge_diverges_from_authority_on_imperative`).
- **Semantics/Epistemicity.lean**: EvalP-spec → `EpistemicProfile.authority`,
  EvidP-spec → `EpistemicProfile.source`; S&T's seat is the speech-act-
  participant restriction of `EpistemicAuthority` (`seat_never_nonparticipant`).

S&T call SAP "the maximal structure"; the "highest phase" framing here is the
formaliser's modernization.

-/


namespace SpeasTenny2003

open Minimalist
open Semantics.Context (KContext ContextTower ContextShift)
open Semantics.Mood (Illocutionary ClauseType)
open Semantics.Epistemicity (EpistemicAuthority EpistemicProfile)

/-! ### Pragmatic roles -/

/-- Pragmatic roles determined by structural position in SAP.

    [speas-tenny-2003]: these are NOT primitives — they are configurationally
    assigned by position in the Speech Act Phrase:
    - SPEAKER = Spec-SAP (external argument of SA)
    - HEARER = complement of SA (internal argument)
    - SEAT OF KNOWLEDGE = varies by mood -/
inductive PRole where
  | speaker          -- Spec-SAP (external argument)
  | hearer           -- Complement of SA (internal argument)
  | seatOfKnowledge  -- Highest argument of the POV domain; varies by mood
  deriving Repr, DecidableEq

/-! ### SAP mood — the 2×2 feature matrix -/

/-- Speas & Tenny's central result: 4 sentence moods from 2 binary features.

    | contentFinite | hearerCCommands | Mood          |
    |---------------|-----------------|---------------|
    | true          | false           | declarative   |
    | true          | true            | interrogative |
    | false         | true            | imperative    |
    | false         | false           | subjunctive   | -/
inductive SAPMood where
  | declarative     -- [+finite, hearer does NOT c-command content]
  | interrogative   -- [+finite, hearer c-commands content]
  | imperative      -- [-finite, hearer c-commands content]
  | subjunctive     -- [-finite, hearer does NOT c-command content]
  deriving Repr, DecidableEq

/-- Derive mood from the two binary features. -/
def deriveMood (contentFinite hearerCCommandsContent : Bool) : SAPMood :=
  match contentFinite, hearerCCommandsContent with
  | true,  false => .declarative
  | true,  true  => .interrogative
  | false, true  => .imperative
  | false, false => .subjunctive

/-- Feature 1 (subcategorization-like): is the utterance content finite?
    (A genuine two-valued morphosyntactic feature value, not a predicate.) -/
def SAPMood.contentFinite : SAPMood → Bool
  | .declarative | .interrogative => true
  | .imperative  | .subjunctive   => false

/-- Feature 2 (spec-head / promotion): does the HEARER c-command the content?
    True for interrogatives/imperatives (hearer promoted), false otherwise. -/
def SAPMood.hearerCCommandsContent : SAPMood → Bool
  | .interrogative | .imperative => true
  | .declarative   | .subjunctive => false

/-- The 2×2 matrix is a genuine bijection (left inverse): recovering the two
    features of a mood and re-deriving returns the same mood. -/
theorem deriveMood_features (m : SAPMood) :
    deriveMood m.contentFinite m.hearerCCommandsContent = m := by
  cases m <;> rfl

/-- The 2×2 matrix is a genuine bijection (right inverse): every feature pair
    is recovered from its derived mood. Together with `deriveMood_features`
    this shows the four moods exhaust `Bool × Bool` bijectively (replacing the
    vacuous "exhaustiveness" claim — every total map into a 4-constructor type
    is "exhaustive"). -/
theorem features_deriveMood (f h : Bool) :
    (deriveMood f h).contentFinite = f ∧ (deriveMood f h).hearerCCommandsContent = h := by
  cases f <;> cases h <;> exact ⟨rfl, rfl⟩

/-! ### Bridge to ClauseType -/

/-- Map configurational mood to a framework-agnostic `ClauseType`
    (illocutionary force × grammatical mood).

    The four mappings:
    - `.declarative`   → ⟨declarative, indicative⟩
    - `.interrogative` → ⟨interrogative, indicative⟩
    - `.imperative`    → ⟨imperative, indicative⟩  (mood often neutralized)
    - `.subjunctive`   → ⟨declarative, subjunctive⟩

    The subjunctive mapping is a *lossy placeholder*: `Illocutionary` has
    no token for S&T's configurational subjunctive (Latin promise/wish/jussive;
    the speaker is "responsible for choosing the preferred world", p.335), so
    the force component falls back to `.declarative`. (The earlier `.promissive`
    mapping was wrong in the other direction — it conflated S&T's terminology
    with Searle's commissive class.) `.exclamative` has no `SAPMood`
    counterpart (exclamatives are not derived in the 2×2 matrix). -/
def SAPMood.toClauseType : SAPMood → ClauseType
  | .declarative    => { force := .declarative,   mood := .indicative }
  | .interrogative  => { force := .interrogative, mood := .indicative }
  | .imperative     => { force := .imperative,    mood := .indicative }
  | .subjunctive    => { force := .declarative,   mood := .subjunctive }

/-- Convenience projection: SAPMood's illocutionary force component. -/
def SAPMood.toForce (m : SAPMood) : Illocutionary :=
  m.toClauseType.force

/-! ### Seat of knowledge (derived) -/

/-- The SEAT OF KNOWLEDGE is the *highest argument* of the Point-of-View
    domain ([speas-tenny-2003] p.335: "the seat of knowledge is controlled by
    the highest argument"), which is the HEARER exactly when the hearer
    c-commands the utterance content. Derived from `hearerCCommandsContent` —
    the *same* feature that drives `deriveMood` — so the seat cannot disagree
    with the matrix:
    - declarative   → speaker  (content c-commands hearer)
    - interrogative → hearer   (hearer promoted, c-commands content)
    - imperative    → hearer   (passive-like promotion; the hearer is
                                responsible for realizing the unrealized
                                proposition, p.335)
    - subjunctive   → speaker  (speaker is highest; responsible for the
                                preferred world) -/
def seatOfKnowledge (m : SAPMood) : PRole :=
  if m.hearerCCommandsContent then .hearer else .speaker

/-- Map P-roles to framework-agnostic discourse roles.
    SPEAKER → speaker, HEARER → addressee, SEAT OF KNOWLEDGE → speaker
    (default; use `seatOfKnowledge` for mood-sensitive resolution). -/
def PRole.toDiscourseRole : PRole → Discourse.DiscourseRole
  | .speaker         => .speaker
  | .hearer          => .addressee
  | .seatOfKnowledge => .speaker  -- default; varies by mood

/-- Map P-roles to egophoric `EpistemicAuthority` ([tournadre-2008],
    [floyd-2018]): SPEAKER → ego, HEARER → allocutive, SEAT OF KNOWLEDGE → ego
    (default). The image never includes `.nonparticipant`. -/
def PRole.toEpistemicAuthority : PRole → EpistemicAuthority
  | .speaker         => .ego
  | .hearer          => .allocutive
  | .seatOfKnowledge => .ego

/-- **Divergence (the empirical content).** S&T's configurational
    seat-of-knowledge and Lakoff's deontic `Illocutionary.authority`
    ([lakoff-1970], via `ClauseType.authority`) DISAGREE on imperatives:
    S&T locate the seat with the HEARER (who must realize the unrealized
    proposition, p.335), Lakoff with the SPEAKER (who has authority to
    command). -/
theorem seatOfKnowledge_diverges_from_authority_on_imperative :
    (seatOfKnowledge .imperative).toDiscourseRole ≠
      (SAPMood.imperative.toClauseType).authority := by
  decide

/-- Off imperatives the two notions agree: declarative/subjunctive → speaker,
    interrogative → addressee. The disagreement is isolated to imperatives. -/
theorem seatOfKnowledge_agrees_with_authority_off_imperative
    (m : SAPMood) (h : m ≠ .imperative) :
    (seatOfKnowledge m).toDiscourseRole = m.toClauseType.authority := by
  cases m <;> first | exact absurd rfl h | rfl

/-! ### Context grounding -/

/-- Resolve a P-role to a discourse participant through a `ContextTower`,
    reusing the canonical `Discourse.resolveRole` (which reads from the
    speech-act origin). SEAT OF KNOWLEDGE resolves through its default
    discourse role; use `resolvePRoleInMood` for mood-sensitive resolution. -/
def resolvePRole {W E P T : Type*} (tower : ContextTower (KContext W E P T)) (r : PRole) : E :=
  Discourse.resolveRole tower r.toDiscourseRole

/-- Mood-sensitive role resolution: SEAT OF KNOWLEDGE is resolved through
    `seatOfKnowledge` before mapping to a participant. -/
def resolvePRoleInMood {W E P T : Type*} (tower : ContextTower (KContext W E P T))
    (m : SAPMood) : PRole → E
  | .seatOfKnowledge => resolvePRole tower (seatOfKnowledge m)
  | r => resolvePRole tower r

/-- SPEAKER resolves to the speech-act origin's agent. -/
theorem resolvePRole_speaker {W E P T : Type*} (tower : ContextTower (KContext W E P T)) :
    resolvePRole tower .speaker = tower.origin.agent := rfl

/-- HEARER resolves to the speech-act origin's addressee. -/
theorem resolvePRole_hearer {W E P T : Type*} (tower : ContextTower (KContext W E P T)) :
    resolvePRole tower .hearer = tower.origin.addressee := rfl

/-- **Key Claim 4 as a theorem.** P-roles are resolved from the SPEECH-ACT
    context (SAP is the highest phase), so resolution is invariant under
    context shift / embedding — inherited from
    `Discourse.resolveRole_shift_invariant`. -/
theorem resolvePRole_shift_invariant {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) (σ : ContextShift (KContext W E P T))
    (r : PRole) :
    resolvePRole (tower.push σ) r = resolvePRole tower r := by
  simp only [resolvePRole, Discourse.resolveRole_shift_invariant]

/-- In declaratives the seat of knowledge resolves to the speaker (agent). -/
theorem seatOfKnowledge_declarative_resolves {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    resolvePRoleInMood tower .declarative .seatOfKnowledge = tower.origin.agent := rfl

/-- In interrogatives the seat of knowledge resolves to the hearer (addressee). -/
theorem seatOfKnowledge_interrogative_resolves {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    resolvePRoleInMood tower .interrogative .seatOfKnowledge = tower.origin.addressee := rfl

/-- In imperatives the seat of knowledge resolves to the hearer (addressee) —
    the corrected value (p.335), where the hearer realizes the proposition. -/
theorem seatOfKnowledge_imperative_resolves {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    resolvePRoleInMood tower .imperative .seatOfKnowledge = tower.origin.addressee := rfl

/-! ### SAP as a phase, and the F-hierarchy -/

/-- SA is a phase head: if the syntactic object's head category is SA,
    then `isPhaseHeadOf .SA` holds. -/
theorem sa_is_phase_head (so : SyntacticObject)
    (h : so.outerCatC = some .SA) :
    isPhaseHeadOf .SA so = true := by
  simp only [isPhaseHeadOf, SyntacticObject.isPhaseHeadOf, h, beq_self_eq_true]

/-- SAP is derivation-final (the highest phase). -/
theorem sa_phase_derivation_final :
    isPhaseHeadOf .SA (SyntacticObject.mkLeaf .SA [] 0) = true := by
  decide

/-- SAP outranks CP on the extended-projection F-hierarchy
    (`fValue .SA = 7 > fValue .C = 6`): the speech-act layer sits above the
    complementizer layer. (`fValue` is globally non-injective — T/Neg/Pol all
    share F2 — so the only S&T-relevant fact is this pairwise inequality.) -/
theorem sa_outranks_c : fValue Cat.SA > fValue Cat.C := by decide

/-! ### Person → P-role mapping -/

/-- Map grammatical person to SAP P-role.

    1st person → SPEAKER (Spec-SAP)
    2nd person → HEARER (complement of SA)
    3rd person / zero → neither (referential, not a discourse role) -/
def personToRole : Person → Option PRole
  | .first | .firstInclusive | .firstExclusive => some .speaker
  | .second => some .hearer
  | .third  => none
  | .zero   => none

/-- Discourse role of a pronoun entry (theory-side, not baked into fragment).
    Determined entirely by the person feature. -/
def pronounDiscourseRole (p : PersonalPronoun) : Option PRole :=
  p.person.bind personToRole

section Pronouns
open English.Pronouns

theorem first_person_are_speakers :
    (pronounDiscourseRole i = some .speaker) ∧
    (pronounDiscourseRole me = some .speaker) ∧
    (pronounDiscourseRole we = some .speaker) ∧
    (pronounDiscourseRole us = some .speaker) := ⟨rfl, rfl, rfl, rfl⟩

theorem second_person_are_hearers :
    (pronounDiscourseRole you = some .hearer) ∧
    (pronounDiscourseRole you_pl = some .hearer) := ⟨rfl, rfl⟩

theorem third_person_no_role :
    (pronounDiscourseRole he = none) ∧
    (pronounDiscourseRole she = none) ∧
    (pronounDiscourseRole it = none) := ⟨rfl, rfl, rfl⟩

end Pronouns

/-- Discourse role is determined entirely by the person feature. -/
theorem discourse_role_from_person (p : PersonalPronoun)
    (per : Person) (hp : p.person = some per) :
    pronounDiscourseRole p = personToRole per := by
  simp [pronounDiscourseRole, hp]

/-! ### Sentience domain ([speas-tenny-2003] §2) -/

/-- Functional projections in the Sentience Domain.

    Below SAP, the Sentience Domain mediates between the speech-act layer and
    propositional content. It hosts two projections:

    - **EvalP** (Evaluation Phrase): specifier = SEAT OF KNOWLEDGE, the
      sentient mind that evaluates the proposition's truth.
    - **EvidP** (Evidential Phrase): specifier = EVIDENCE, the type of
      evidence supporting the evaluation.

    Sentience Phrase (structure 34): `EvalP > EvidP > S(episP)`; the SAP scopes
    above it (p.333), so overall `SAP > EvalP > EvidP > S`. (S&T label the base
    `S(episP)`; equating it with TP is the formaliser's gloss.)

    The Sentience Domain captures "judgements and evaluations by a sentient
    mind on the truth-value of the proposition" (p.333).

    Cross-framework note: the canonical `Cat.Evid` of the extended projection
    is Cinque's evaluative/evidential head at F-level 2 (above T, below Fin) —
    structurally *lower* than S&T's EvidP, which sits in the Sentience Domain
    just above TP. Two cited evidential projections at different heights. -/
inductive SentienceProjection where
  | EvidP   -- Evidential Phrase: hosts EVIDENCE
  | EvalP   -- Evaluation Phrase: hosts SEAT OF KNOWLEDGE
  deriving DecidableEq, Repr, Fintype

/-- Rank ordering of Sentience Domain projections: EvidP < EvalP < SAP. -/
def SentienceProjection.rank : SentienceProjection → Nat
  | .EvidP => 0
  | .EvalP => 1

/-- The rank function is injective: distinct projections have distinct ranks. -/
theorem rank_injective : Function.Injective SentienceProjection.rank := by
  decide

/-- The specifier of EvalP hosts a P-role: SEAT OF KNOWLEDGE (the sentient
    mind performing the evaluation), same as `seatOfKnowledge`. -/
abbrev evalPSpecifier : SAPMood → PRole := seatOfKnowledge

/-- The specifier of EvidP hosts the evidence type, mapped to the
    framework-agnostic `CoarseSource` of `Features/Evidentiality.lean`
    (direct / inference / hearsay). NB this three-way coarsening merges S&T's
    top tier (personal experience) into "direct"; the paper's full evidence
    hierarchy is personal experience ≫ direct ≫ indirect ≫ hearsay (p.327). -/
abbrev EvidPSpecifier := Features.Evidentiality.CoarseSource

/-- **Real bridge to `Semantics/Epistemicity.lean`.** The Sentience Domain's
    two specifiers ARE the two main fields of an `EpistemicProfile`:
    EvalP-spec (SEAT OF KNOWLEDGE) → `authority`, EvidP-spec (EVIDENCE) →
    `source`. The structural hierarchy EvalP > EvidP corresponds to authority
    scoping over source. -/
def sentienceProfile (m : SAPMood) (ev : EvidPSpecifier) : EpistemicProfile :=
  { source := ev, authority := (evalPSpecifier m).toEpistemicAuthority }

/-- The EvidP specifier IS the profile's evidential source (shared `CoarseSource`). -/
@[simp] theorem sentienceProfile_source (m : SAPMood) (ev : EvidPSpecifier) :
    (sentienceProfile m ev).source = ev := rfl

/-- The EvalP specifier's epistemic authority IS the profile's authority. -/
@[simp] theorem sentienceProfile_authority (m : SAPMood) (ev : EvidPSpecifier) :
    (sentienceProfile m ev).authority = (evalPSpecifier m).toEpistemicAuthority := rfl

/-- **Asymmetry made visible.** S&T's two-participant seat-of-knowledge never
    projects `.nonparticipant` authority, which the egophoric inventory
    ([tournadre-2008], [floyd-2018]) carries for third-party access. S&T's role
    space is the speech-act-participant restriction of `EpistemicAuthority`. -/
theorem seat_never_nonparticipant (m : SAPMood) :
    (evalPSpecifier m).toEpistemicAuthority ≠ .nonparticipant := by
  cases m <;> decide

end SpeasTenny2003
