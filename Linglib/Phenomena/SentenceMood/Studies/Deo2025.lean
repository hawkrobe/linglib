import Linglib.Core.Discourse.Commitment
import Linglib.Core.Discourse.Roles
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Theories.Pragmatics.Assertion.Gunlogson
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
warnings (1, 4, 5a, 8, 13), advice (6), reminders (7), commands (12),
strong recommendations (14). Infelicitous with: requests (10a), pleas
(10b), offers (11a), permissions/well-wishes (11b), concessions (11c),
curses (11d), declarative commissives (9), agreement-with-addressee (16).

## Architectural claim (§ 3)

@cite{deo-2025-bara} proposes a discourse model with two innovations
beyond @cite{farkas-bruce-2010} / @cite{gunlogson-2001}:

* Each interlocutor's discourse commitments split into doxastic vs
  preferential (eq. 17a–c) — formalized at
  `Core.Discourse.Commitment.CommitmentForce`.
* The @cite{gunlogson-2001} source/dependent distinction lifts to
  *both* commitment forces — the 2×2 cross
  `CommitmentSource × CommitmentForce`. The four cells are exposed as
  `Core.Discourse.Commitment.TaggedSlate.{dependent, independent,
  dependentDoxastic, dependentPreferential, independentDoxastic,
  independentPreferential}`.

Deo's *bərə* convention (eq. 20): the speaker preferentially commits to
the *meta-proposition* "addressee dependently commits to *p*". The
agent-source asymmetry — speaker's commitment is self-sourced and
preferential, embedded commitment is dependent on the addressee's side —
makes this a higher-order operation that *uses* the 2×2, not a single
2×2 cell.

The secondary felicity condition (eq. 21): addressee uptake of *p* must
be a precondition for fulfilling a contextually salient
addressee-benefiting goal `g_c ∈ EP(s, w)`
(`Semantics.Attitudes.CondoravdiLauer.EffectivePreferentialBackground`).

## Out of scope

(i) bərə + ka compound (§ 4, p. 401); (ii) wh-interrogative uses (per
p. 387); (iii) threat-commissives (footnote 14, p. 400), which *are*
felicitous — the `commissive` case below covers the cooperative
commissive only.
-/

namespace Phenomena.SentenceMood.Studies.Deo2025

open Core.Discourse
open Core.Discourse.Commitment
open Pragmatics.Assertion.Gunlogson (GunlogsonState)

universe u

variable {W : Type u}

/-! ## § 1. Bərə's denotation (eq. 20)

The bərə convention is a higher-order update: the speaker (independent
source) preferentially commits to the meta-proposition that *p* is in
the addressee's dependent-commitment slate. The meta-proposition is a
`GunlogsonState W → Prop`. The corresponding state-update is *not*
formalized here — it would require lifting `TaggedSlate`'s content type
to admit scoreboard-relative propositions, a Core refactor outside the
scope of this study file.
-/

/-- The bərə meta-content: "*p* is among the addressee's dependent
    commitments." This is the proposition the speaker preferentially
    commits to. @cite{deo-2025-bara} (20). -/
def baraMetaContent (p : W → Prop) (K : GunlogsonState W) : Prop :=
  p ∈ (K.slateOf .addressee).dependent

/-! ## § 3. Empirical felicity profile (Deo § 2) -/

/-- The illocutionary acts surveyed by @cite{deo-2025-bara}.

    Refines `Core.Discourse.IllocutionaryForce.SearleClass` for the
    directive subset (warning/advice/reminder/command/strongRec/
    request/plea/offer/permission/concession/curse all `.directive`),
    plus `commissive` (`.commissive`) and `agreement` (`.assertive`).
    The `toSearleClass` projection makes this refinement structural. -/
inductive IllocutionaryAct
  | warning | advice | reminder | command | strongRecommendation
  | request | plea | offer | permission | concession | curse
  | commissive | agreement
  deriving DecidableEq, Repr

/-- The Searle class of each illocutionary act in Deo's enum. -/
def IllocutionaryAct.toSearleClass : IllocutionaryAct → SearleClass
  | .warning | .advice | .reminder | .command | .strongRecommendation
  | .request | .plea | .offer | .permission | .concession | .curse => .directive
  | .commissive => .commissive
  | .agreement  => .assertive

/-- Deo's reported empirical felicity of bərə across illocutionary acts.
    Acts where bərə is felicitous (per @cite{deo-2025-bara} § 2):
    `warning` (exx. 1, 4, 5a, 8, 13), `advice` (ex. 6), `reminder`
    (ex. 7), `command` (ex. 12), `strongRecommendation` (ex. 14). All
    other acts in the enum are infelicitous: `request` (ex. 10a),
    `plea` (ex. 10b), `offer` (ex. 11a), `permission` (ex. 11b),
    `concession` (ex. 11c), `curse` (ex. 11d), `commissive` (ex. 9),
    `agreement` (ex. 16).

    The fine-grained warning/advice/reminder/command/strongRecommendation
    partition is study-introduced for predicate clarity; Deo's text
    (p. 392) clusters them as "strong directives" without sharp
    boundaries. The `agreement` act is short for "expressing agreement
    with or approval of an actional commitment undertaken by the
    addressee" (p. 393, p. 400).

    Caveat: the `commissive` case reflects the *cooperative* commissive
    (ex. 9). Deo's footnote 14 (p. 400) flags that *threat-commissives*
    (e.g., "If you don't go to bed, I will take your video game bərə!")
    *are* felicitous; this enum coarsens over that distinction. -/
def empiricalFelicityClass : Set IllocutionaryAct :=
  {.warning, .advice, .reminder, .command, .strongRecommendation}

instance : DecidablePred (· ∈ empiricalFelicityClass) := fun act =>
  inferInstanceAs (Decidable (act = .warning ∨ act = .advice ∨ act = .reminder ∨
    act = .command ∨ act = .strongRecommendation))

/-! ## § 4. Architectural preconditions

Deo (p. 392) identifies *two* preconditions on imperative–bərə felicity:

* **(a)** The addressee has no pre-existing preference to realize the
  imperative content. Permissions and concessions fail this.
* **(b)** It is appropriate for the speaker to presume authority over the
  addressee in realizing the content (or to expect unquestioning
  compliance). Requests, pleas, offers, invitations, and curses fail
  this.

A *separate* semantic-component felicity condition (eq. 21) requires
the speaker to have a contextually salient addressee-benefiting goal
`g_c ∈ EP(s, w)` whose fulfilment is preconditioned on addressee uptake
of the prejacent. This applies across both clause types and rules out
acts where the goal benefits the speaker (requests, pleas) or
detriments the addressee (curses).

For declaratives (commissives ex. 9, agreement ex. 16), Deo applies the
analog of (a) — the addressee has a *manifest* preference from a prior
discourse move (p. 393, p. 400). The speaker-authority condition (b) is
not directly applicable to declaratives but is treated as trivially
satisfied for predicate-conjunction purposes. -/

/-- **(a)** Does the addressee have a pre-existing preference to realize
    the content? -/
def AddresseeHasPreExistingPref (act : IllocutionaryAct) : Prop :=
  act = .permission ∨ act = .concession ∨ act = .commissive ∨ act = .agreement

instance : DecidablePred AddresseeHasPreExistingPref := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- **(b)** Does the speaker presume authority for realizing the content? -/
def SpeakerHasAuthority (act : IllocutionaryAct) : Prop :=
  ¬ (act = .request ∨ act = .plea ∨ act = .offer ∨ act = .curse)

instance : DecidablePred SpeakerHasAuthority := fun _ =>
  inferInstanceAs (Decidable (¬ _))

/-- **(eq. 21)** Does the contextually salient goal benefit the addressee? -/
def GoalBenefitsAddressee (act : IllocutionaryAct) : Prop :=
  ¬ (act = .request ∨ act = .plea ∨ act = .curse)

instance : DecidablePred GoalBenefitsAddressee := fun _ =>
  inferInstanceAs (Decidable (¬ _))

/-- The conjunction of Deo's two imperative preconditions ((a) negated +
    (b)) and the secondary felicity condition (eq. 21). -/
def BaraFelicitous (act : IllocutionaryAct) : Prop :=
  ¬ AddresseeHasPreExistingPref act
  ∧ SpeakerHasAuthority act
  ∧ GoalBenefitsAddressee act

instance : DecidablePred BaraFelicitous := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## § 5. Deo's central characterization theorem -/

/-- **Deo's central claim**: the three architectural conditions
    (`¬ AddresseeHasPreExistingPref ∧ SpeakerHasAuthority ∧
    GoalBenefitsAddressee`) characterize the empirically attested
    felicity class — the strong-directive subset
    `{warning, advice, reminder, command, strongRecommendation}`.

    The substantive content is in the structural decomposition: that
    Deo's three independently motivated conditions exactly carve out
    the cluster of acts where bərə is reported felicitous, with no
    over- or under-prediction across the 13-act survey. -/
theorem deo_characterization (act : IllocutionaryAct) :
    BaraFelicitous act ↔ act ∈ empiricalFelicityClass := by
  cases act <;> decide

/-! ## § 6. Bərə vs the Searle taxonomy

Bərə-felicitous acts are all `.directive` in the Searle classification,
but the converse fails: many directive acts (`request`, `plea`, `offer`,
`permission`, `concession`, `curse`) are bərə-infelicitous. Bərə picks
out a strict subset of the directive class.
-/

theorem felicitous_implies_directive (act : IllocutionaryAct) :
    BaraFelicitous act → act.toSearleClass = .directive := by
  cases act <;> decide

theorem directive_class_strictly_larger :
    ∃ act, act.toSearleClass = .directive ∧ ¬ BaraFelicitous act :=
  ⟨.request, by decide, by decide⟩

end Phenomena.SentenceMood.Studies.Deo2025
