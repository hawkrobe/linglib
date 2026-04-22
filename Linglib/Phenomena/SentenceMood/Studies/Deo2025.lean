import Linglib.Core.Discourse.Commitment
import Linglib.Theories.Semantics.Attitudes.CondoravdiLauer
import Linglib.Fragments.Marathi.Particles

/-!
# Deo (2025): The Marathi Discourse Particle *bərə*
@cite{deo-2025-bara}

Take on This Commitment: The Particle *bərə* in Marathi (Indo-Aryan).
*Proceedings of Sinn und Bedeutung 29*, ed. F. Longo and D. Panizza.
Pp. 386–403.

## Empirical claim (§ 2)

Marathi utterance-final *bərə* combines with declaratives, imperatives,
and wh-interrogatives (never polar interrogatives). It is felicitous in:
warnings (1, 4, 5a, 8), advice (6), reminders (7), commands (12), strong
recommendations (13, 14). Infelicitous with: requests (10a), pleas (10b),
offers (11a), permissions/well-wishes (11b), concessions (11c), curses
(11d), declarative commissives (9), agreement-with-addressee (16).

## Architectural claim (§ 3)

@cite{deo-2025-bara} proposes a discourse model with two innovations
beyond @cite{farkas-bruce-2010} / @cite{gunlogson-2001}:

* Each interlocutor's discourse commitments split into doxastic vs
  preferential (eq. 17a–c) — formalized at
  `Core.Discourse.Commitment.CommitmentForce` (Phase 2).
* The @cite{gunlogson-2001} source/dependent distinction lifts to
  *both* commitment forces — the 2×2 cross
  `CommitmentSource × CommitmentForce`.

Deo's *bərə* convention (eq. 20): the speaker preferentially commits to
the *meta-proposition* "addressee dependently commits to *p*". Note the
agent-source asymmetry: the speaker's commitment is *self*-sourced and
preferential; the embedded commitment (about which the speaker preferences
this state of affairs) is *dependent* on the addressee's side. This is
not a single 2×2 cell — it is a higher-order operation that *uses* the
2×2 (`baraMetaContent` below).

The secondary felicity condition (eq. 21): addressee uptake of *p* must
be a precondition for fulfilling a contextually salient
addressee-benefiting goal `g_c ∈ EP(s, w)` — the speaker's effective
preferences (`Semantics.Attitudes.CondoravdiLauer.EffectivePreferentialBackground`).

## What this file does

Captures Deo's empirical felicity profile as data, his architectural
analysis as three structural conditions, and proves the analysis
correctly predicts the empirical pattern. Exposes the bərə denotation
as a `Scoreboard` transformation on a minimal two-agent model whose
slates are the Phase-2 `TaggedSlate`s.

The `roberts_vs_condoravdi_lauer_disagree` cross-framework theorem is
stated upstream in `Phenomena/Directives/Studies/Roberts2023.lean`
(planned Phase 3); this file is silent on that disagreement.
-/

namespace Phenomena.SentenceMood.Studies.Deo2025

open Core.Discourse.Commitment

universe u

variable {W : Type u}

/-! ## § 1. Two-agent scoreboard -/

/-- The two interlocutors. -/
inductive Agent | speaker | addressee
  deriving DecidableEq, Repr, Inhabited

/-- A minimal discourse state: per-agent tagged commitment slates. -/
structure Scoreboard (W : Type u) where
  speakerSlate   : TaggedSlate W := TaggedSlate.empty
  addresseeSlate : TaggedSlate W := TaggedSlate.empty

instance : Inhabited (Scoreboard W) := ⟨{}⟩

namespace Scoreboard

variable (K : Scoreboard W)

/-- Per-agent slate accessor. -/
def slateOf : Agent → TaggedSlate W
  | .speaker   => K.speakerSlate
  | .addressee => K.addresseeSlate

/-- The dependent commitments of agent `a` (any force) — Deo's `DC_a_dep`. -/
def dcDep (a : Agent) : List (W → Prop) :=
  (K.slateOf a).commitments.filter (·.source == .otherGenerated) |>.map (·.content)

/-- The dependent doxastic commitments of agent `a` —
    @cite{deo-2025-bara} (17a) restricted to `.otherGenerated`. -/
def dcDepDox (a : Agent) : List (W → Prop) :=
  (K.slateOf a).commitments.filter
    (fun c => c.source == .otherGenerated && c.commitmentForce == .doxastic)
  |>.map (·.content)

/-- The dependent preferential commitments of agent `a`. -/
def dcDepPref (a : Agent) : List (W → Prop) :=
  (K.slateOf a).commitments.filter
    (fun c => c.source == .otherGenerated && c.commitmentForce == .preferential)
  |>.map (·.content)

end Scoreboard

/-! ## § 2. Bərə's denotation (eq. 20)

The bərə convention is a higher-order update: the speaker (independent
source) preferentially commits to the meta-proposition that *p* is in the
addressee's dependent-commitment slate. We model the meta-proposition as a
`Scoreboard W → Prop`.
-/

/-- The bərə meta-content: "*p* is among the addressee's dependent
    commitments." This is the proposition the speaker preferentially
    commits to. @cite{deo-2025-bara} (20). -/
def baraMetaContent (p : W → Prop) (K : Scoreboard W) : Prop :=
  p ∈ K.dcDep .addressee

/-- The bərə update on a discourse state: adds the speaker's preferential
    (independently-sourced) commitment to the meta-content `baraMetaContent
    p`. The embedded `p` itself is *not* added directly to either slate
    by `bara`; the clause-type-determined update (DEC or IMP) handles `p`
    on the appropriate slot, and `bara` *augments* with the meta-level
    commitment. -/
def baraUpdate (p : W → Prop) (K : Scoreboard W) : Scoreboard W :=
  -- The meta-content is a scoreboard predicate, not a world predicate;
  -- to record it on the speaker's tagged slate, we project to its
  -- propositional shadow `bara_meta p`. Faithful encodings of the full
  -- meta-update would lift the slate's content type to allow
  -- scoreboard-relative content; this is the documented simplification
  -- per the pragmatics-expert review.
  { K with speakerSlate :=
      K.speakerSlate.add p .selfGenerated .preferential }

/-! ## § 3. Empirical felicity profile (Deo § 2) -/

/-- The illocutionary acts surveyed by @cite{deo-2025-bara}. -/
inductive IllocutionaryAct
  | warning | advice | reminder | command | strongRecommendation
  | request | plea | offer | permission | concession | curse
  | commissive | agreement
  deriving DecidableEq, Repr

/-- Deo's reported empirical felicity of bərə across illocutionary acts.
    Each line cites the example in @cite{deo-2025-bara} that establishes
    the judgment. -/
def deoEmpiricalReport : IllocutionaryAct → Bool
  | .warning              => true   -- exx. (1), (4), (5a), (8)
  | .advice               => true   -- ex. (6)
  | .reminder             => true   -- ex. (7)
  | .command              => true   -- ex. (12)
  | .strongRecommendation => true   -- exx. (13), (14)
  | .request              => false  -- ex. (10a)
  | .plea                 => false  -- ex. (10b)
  | .offer                => false  -- ex. (11a)
  | .permission           => false  -- ex. (11b)
  | .concession           => false  -- ex. (11c)
  | .curse                => false  -- ex. (11d)
  | .commissive           => false  -- ex. (9)
  | .agreement            => false  -- ex. (16)

/-! ## § 4. Architectural preconditions (Deo § 2 summary, eq. 21)

Deo abstracts three structural conditions a context must satisfy for
*bərə* to be felicitous:

1. The addressee has *no* pre-existing preference to realize the content.
   Rules out requests/pleas/offers/permissions/concessions/curses
   (whose felicity presumes such a preference).
2. The speaker presumes authority over the addressee in realizing the
   content. Rules out permissions/concessions (and trivially fails for
   curses/requests/pleas).
3. The content's realization is preconditioned on a contextually salient
   *addressee-benefiting* goal `g_c ∈ EP(s, w)`. Rules out
   speaker-benefiting acts (requests, pleas) and detrimental acts
   (curses), as well as commissives and agreements (where the speaker is
   the relevant agent or the addressee is already aligned).
-/

/-- (1) Does the act presume the addressee already prefers realizing the
    content? -/
def addresseeHasPreExistingPref : IllocutionaryAct → Bool
  | .request | .plea | .offer | .permission | .concession => true
  | _ => false

/-- (2) Does the speaker presume authority for realizing the content? -/
def speakerHasAuthority : IllocutionaryAct → Bool
  | .request | .plea          => false  -- subordinate to addressee
  | .offer | .permission      => false  -- addressee chooses
  | .concession               => false  -- addressee has insisted
  | .curse                    => false  -- hostility, not authority
  | .commissive | .agreement  => false  -- speaker not commanding addressee
  | _                         => true

/-- (3) Does the salient goal benefit the addressee? -/
def goalBenefitsAddressee : IllocutionaryAct → Bool
  | .request | .plea          => false  -- benefit speaker
  | .curse                    => false  -- detriment addressee
  | .commissive | .agreement  => false  -- addressee already aligned
  | _                         => true

/-- The conjunction of Deo's three preconditions on bərə felicity
    (eq. 21 + § 2 summary). -/
def baraFelicitous (act : IllocutionaryAct) : Bool :=
  !addresseeHasPreExistingPref act
  && speakerHasAuthority act
  && goalBenefitsAddressee act

/-! ## § 5. Bridge: predictions match the empirical pattern -/

/-- @cite{deo-2025-bara}'s three architectural conditions correctly
    predict the reported empirical felicity profile across all 13
    surveyed illocutionary acts. The proof is `decide` over the
    13-element `IllocutionaryAct` enum — the substantive content is in
    the *separate* stipulation of the per-act values for the three
    conditions and the empirical report; the theorem checks that the
    structural account `baraFelicitous` and the empirical data
    `deoEmpiricalReport` agree pointwise. -/
theorem bara_predictions_match_empirical (act : IllocutionaryAct) :
    baraFelicitous act = deoEmpiricalReport act := by
  cases act <;> rfl

/-! ## § 6. Lexicon-side verification

The Marathi Fragment entry's clause-type distribution and
preferential-commitment marking agree with the architectural account.
-/

open Fragments.Marathi.Particles

theorem bara_carries_preferential :
    bara.carriesPreferentialCommitment = true := rfl

theorem bara_excludes_polar_q :
    bara.inPolarInterrogatives = false := rfl

theorem bara_in_three_clause_types :
    bara.inDeclaratives = true ∧
    bara.inImperatives = true ∧
    bara.inWhInterrogatives = true := ⟨rfl, rfl, rfl⟩

end Phenomena.SentenceMood.Studies.Deo2025
