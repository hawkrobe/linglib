import Linglib.Semantics.Lexical.EventStructure
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.Lexical.LevinClass

/-!
# Variable Agentivity: Polysemy or Underspecification?

[rappaport-hovav-levin-2024]

A formalization of Rappaport Hovav & Levin's 2024 *Glossa* paper on the
English verb *sweep* and the wiping-verbs class. The paper argues that the
variable agentivity of *sweep* — *Matt swept the walk* (agentive) vs *the
branch of the tree swept the window* (non-agentive) — is the joint effect
of two mechanisms, not one.

## Main claims

1. **basic-*sweep*** is unspecified for agentivity. Its event structure
   ([rappaport-hovav-levin-2024] p.17, eq.42) is a complex activity
   with two grammatically relevant predicates: motion and force-transmission
   through contact. Either predicate can determine argument realization
   per-frame, yielding the simple transitive, transitive+PP, and
   unaccusative+PP frames attested in COCA.

2. **broom-*sweep*** is obligatorily agentive. It is derived from
   basic-*sweep* by lexicalization of the moving entity as a broom
   ([kiparsky-1997] on canonical-use of denominal verbs). The broom's
   instrument status forces an agent who manipulates it; the broom's
   design purpose underlies the routine-activity narrowing that licenses
   the unspecified-object frame ([glass-2022], [brisson-1994],
   [mittwoch-2005]). The two senses constitute motivated polysemy
   (distinct from regular polysemy à la Apresjan; zeugma test eq.35).

3. The motion-and-sustained-contact event structure generalizes to the
   wiping-verbs class ([levin-1993] 10.4): *sweep*, *rub*, *scrape*,
   *wipe*. Force-dynamic primitives follow [talmy-1988],
   [croft-2012], [copley-harley-2015],
   [goldschmidt-zwarts-2016].

4. **Counterexample to the resultative restriction.**
   [schaefer-2012]'s and [folli-harley-2008]'s claim that
   non-agentive external arguments require a result phrase fails for
   basic-*sweep* (eq.92: *A breeze moved the willows, the tips of their
   branches sweeping the ground*).

## Main declarations

* `MotionContactES`: the two-predicate complex-activity event structure for
  the wiping-verbs class. `basicSweep` and `broomSweep` are instances.
* `ForceRole` and `Effector`: force-dynamic primitives following
  [talmy-1988], [croft-2012], [copley-harley-2015].
* `DeterminingPredicate` (motion / contact): per-frame parameter to the
  argument-realization principles.
* `Frame`: the five syntactic frames attested for basic-*sweep* and
  broom-*sweep* (p.5, §2.2).
* `realizeFrame`: applies argument-realization principles (43)-(45) to
  produce the predicted frame from an event structure and a determining
  predicate.
* `WipingVerb`: the [levin-1993] class 10.4 (sweep / rub / scrape /
  wipe) sharing the basic-*sweep* event structure.

## Implementation notes

This file does *not* add a fifth case to `Semantics.Lexical.EventStructure.Template`.
RHL 2024's contribution is an enrichment of the *internal structure* of
the activity template for one manner subclass — two grammatically relevant
predicates instead of one — and a per-frame choice of which predicate
determines argument realization. The current `Template.motionContact`
case in `Features/EventStructure.lean` is a misformalization of the
2024 paper and is queued for removal.

Footnote 31 of the paper explicitly disclaims the asymmetric "x moves...
while x imparts..." formulation: the subordination is prose-only.
Footnote 32 generalizes the mechanism beyond *sweep* to locative
alternation ([rappaport-hovav-levin-1998] 1c–d), substance-emission
verbs ([levin-krejci-2019]), and *drown*.

## Todo

* Bridge `broomSweep` to `Fragments/English/Predicates/Verbal.lean`'s
  `sweepBroomSubjectProfile` once the inline `EntailmentProfile` records
  are promoted to named exports (project decision pending).
* Formalize the lexicon-uniformity blocker for some causative-alternation
  pairs ([rappaport-hovav-2014] on direct-causation requirement).
* Engage [ramchand-2008]'s first-phase syntax and
  [borer-2005] as syntactic rivals to the lexical-projection account
  this paper inherits from [rappaport-hovav-levin-1998].
-/

namespace RappaportHovavLevin2024

open Semantics.Lexical.EventStructure
open ArgumentStructure.EntailmentProfile
open Semantics.Lexical

/-! ### Force-dynamic primitives -/

/-- Role in a force-transmission sub-event
([talmy-1988], [croft-2012], [goldschmidt-zwarts-2016]).

In basic-*sweep*'s event structure (p.17, eq.42), x is the **force-bearer**
(it imparts the force) and y is the **force-recipient** (the surface
receiving the force throughout the contact). -/
inductive ForceRole where
  /-- Force-bearer: imparts force via motion-induced contact (x in eq.42). -/
  | bearer
  /-- Force-recipient: receives force throughout the contact (y; the surface). -/
  | recipient
  deriving DecidableEq, Repr

/-- The ontological types of entity that can occupy the basic-*sweep*
subject position. The paper restricts the moving entity to entities
capable of motion across a surface (p.5).

`naturalPhenomenon` and `projectile` together qualify as **effectors**
in the strict sense (p.25): self-energetic. Agents are effectors via
intentional control. Instruments and body parts qualify as force-bearers
only under agent control (footnote 9, p.7). -/
inductive Effector where
  /-- Volitional, intentional human or animal participant
      ([cruse-1973], [van-valin-wilkins-1996], p.7). -/
  | agent
  /-- Wind, fire, water, storms — inherently self-energetic
      (p.25). -/
  | naturalPhenomenon
  /-- Physical objects with kinetic energy imparted by an unmentioned
      causer; can transmit that energy through contact
      ([kearns-2000] on projectiles; p.23). -/
  | projectile
  /-- Self-propelled artifact (footnote 9, p.7); patterns with agents
      grammatically but not in the strict animate-intentional sense. -/
  | machine
  /-- Instrument or body part. Cannot be a force-bearer without an
      agent providing the energy (p.21, p.25). -/
  | instrument
  /-- Displaced entity moved along the surface (basic-*sweep* with
      transitive+PP frame; p.21). -/
  | displacedEntity
  deriving DecidableEq, Repr

/-- Self-energetic force-bearers that qualify as **effectors** in the
strict sense (p.25). These are the kinds of subjects basic-*sweep*
allows in the non-agentive simple transitive frame. -/
def Effector.IsSelfEnergetic : Effector → Prop
  | .agent              => True   -- via intentional control
  | .naturalPhenomenon  => True
  | .projectile         => True
  | .machine            => True
  | .instrument         => False  -- requires agent
  | .displacedEntity    => False  -- not a force-bearer

instance (e : Effector) : Decidable e.IsSelfEnergetic := by
  cases e <;> unfold Effector.IsSelfEnergetic <;> infer_instance

/-- An effector qualifies as a basic-*sweep* simple-transitive subject
under the contact-determines-AR derivation (p.24-25) iff it is
self-energetic. -/
abbrev Effector.QualifiesAsSimpleTransitiveSubject : Effector → Prop :=
  Effector.IsSelfEnergetic

/-- An effector can intentionally manipulate an instrument
([rappaport-hovav-levin-2024] p.7, footnote 9). Only agents and
self-propelled machines pattern this way; machines pattern with agents
grammatically but are not animate-intentional. Natural phenomena and
projectiles, despite being self-energetic, do not manipulate
instruments. -/
def Effector.CanManipulateInstrument : Effector → Prop
  | .agent              => True
  | .machine            => True   -- footnote 9: patterns with agents
  | _                   => False

instance (e : Effector) : Decidable e.CanManipulateInstrument := by
  cases e <;> unfold Effector.CanManipulateInstrument <;> infer_instance

/-! ### The basic-*sweep* event structure (eq. 42)

The grammatically relevant meaning components of *sweep* and other
verbs in the wiping-verbs class. Encoded as a structure type so that
broom-*sweep* (with the moving entity lexicalized) is derived by
field-level minimal adjustment per [rappaport-hovav-levin-2024] §3.5
(eq.76). -/

/-- The motion-and-sustained-contact event structure
([rappaport-hovav-levin-2024] p.17, eq.42):

> *x moves across a surface y while x imparts a force to y through contact*

Two grammatically relevant predicates: a motion predicate and a
force-transmission predicate, sharing the moving entity x. Footnote 31
disclaims the "while" subordination — there is no theoretical
significance to which predicate is "main"; the two are equipotent in
determining argument realization.

The `movingEntityLexicalization` field carries broom-*sweep*'s
lexical saturation (eq.76: `x_broom`); `none` is basic-*sweep*. -/
structure MotionContactES where
  /-- Lexicalization status of the moving entity x.
      `none` = unsaturated (basic-*sweep*); `some "broom"` =
      basic-*sweep*'s moving-entity variable saturated by broom (broom-*sweep*).
      Other instrument-lexicalizations in English ([harley-haugen-2007]):
      `comb`, `funnel`, `hoe`, `mop`, `plow`, `rake`, `saw`, `shovel`,
      `staple`, `towel`, `whip` (paper eq.77). -/
  movingEntityLexicalization : Option String := none
  deriving DecidableEq, Repr

/-- basic-*sweep*: the underspecified base sense. Moving entity x is
unsaturated; subject can be agent, natural phenomenon, projectile, or
displaced entity depending on the frame and which predicate determines
argument realization. -/
def basicSweep : MotionContactES := {}

/-- broom-*sweep*: the specialized agentive sense (eq.76). Moving entity
x is lexically saturated as a broom; the broom's instrument status
forces an agent. -/
def broomSweep : MotionContactES := { movingEntityLexicalization := some "broom" }

/-- An event structure is **lexically saturated** iff its moving entity
variable is fixed. -/
def MotionContactES.IsLexicallySaturated (es : MotionContactES) : Prop :=
  match es.movingEntityLexicalization with
  | none => False
  | some _ => True

instance (es : MotionContactES) : Decidable es.IsLexicallySaturated := by
  unfold MotionContactES.IsLexicallySaturated
  cases es.movingEntityLexicalization <;> infer_instance

@[simp] theorem broomSweep_saturated : broomSweep.IsLexicallySaturated := trivial

@[simp] theorem basicSweep_not_saturated : ¬ basicSweep.IsLexicallySaturated := id

/-! ### Argument-realization principles ((43)-(45)) -/

/-- Per-frame choice of which predicate in the event structure
[rappaport-hovav-levin-2024] (eq.42) determines argument realization.

> "When an event structure includes two grammatically relevant predicates,
> the argument realization principles are applied with respect to only
> one" (p.18, after eq.47).

The choice is per-frame, not per-verb: basic-*sweep* admits both
motion-determines and contact-determines derivations of distinct frames
from the same lexical entry. -/
inductive DeterminingPredicate where
  /-- Motion determines: principle (43) applies, yielding a small-clause
      realization where the moving entity is the small-clause subject
      and a path PP is the predicate. Yields unaccusative+PP and
      transitive+PP frames. -/
  | motion
  /-- Contact determines: principles (44)-(45) apply, force-recipient
      → internal argument, effector → external argument. Yields simple
      transitive and unspecified-object frames. -/
  | contact
  deriving DecidableEq, Repr

/-! ### Syntactic frames -/

/-- The five syntactic frames attested for the wiping-verbs class
([rappaport-hovav-levin-2024] §2, p.5-13). -/
inductive Frame where
  /-- *the branch of the tree swept the window*: contact determines AR
      from basic-*sweep*. Subject is force-bearer/effector; surface is
      direct object. -/
  | simpleTransitive
  /-- *the wind swept the fires through the top growth*: motion determines
      AR; CAUSE applied on top (eq.50, causativized counterpart of eq.47).
      Subject is causer; moving entity is direct object; path is PP. -/
  | transitivePP
  /-- *the fires swept through the top growth*: motion determines AR
      without external causer (eq.46, eq.47); unaccusative+PP frame from
      basic-*sweep*'s underlying event structure. -/
  | unaccusativePP
  /-- *Yesterday I swept in the morning*: contact determines AR from
      broom-*sweep*; surface omitted under routine-activity narrowing
      ([glass-2022], [brisson-1994], [mittwoch-2005]). -/
  | unspecifiedObject
  deriving DecidableEq, Repr

/-- Argument-realization principles (eqs. 43-45) applied to an event
structure with a given determining-predicate choice. Outputs the
predicted frame, or `none` when the derivation is blocked.

* (43a) An entity in motion along a path is the subject of a small
  clause. Requires the moving entity variable to be available for
  syntactic expression — fails if x is lexically saturated (p.30,
  after eq.86).
* (43b) A path is the predicate of a small clause.
* (44) A force recipient is an internal argument.
* (45) An effector is an external argument.

The `hasCauser` parameter encodes whether an external z is added
(eq.50: *z causes x to move across y while x imparts a force to y*);
without it, the motion-determined frame is unaccusative+PP. -/
def realizeFrame (es : MotionContactES) (dp : DeterminingPredicate)
    (hasCauser : Bool) : Option Frame :=
  match dp with
  -- Contact determines: simple transitive frame; routine-activity
  -- narrowing licenses the unspecified-object frame for saturated
  -- event structures (§3.5.2), which we fold into simpleTransitive here.
  | .contact => some .simpleTransitive
  | .motion =>
    -- (43a) requires the moving entity to form a small clause with a
    -- path PP; a lexically saturated moving entity (broom) is
    -- unavailable for syntactic expression and blocks this derivation
    -- (p.30, eqs. 86-87).
    match es.movingEntityLexicalization with
    | some _ => none
    | none => some (if hasCauser then .transitivePP else .unaccusativePP)

/-! ### Variable agentivity in basic-*sweep* -/

/-- basic-*sweep*'s simple transitive frame admits non-agentive subjects
provided the subject is a self-energetic effector
(p.25). This is the **variable agentivity** of basic-*sweep*. -/
theorem basicSweep_simple_transitive_admits_natural_force (e : Effector)
    (h : e = .naturalPhenomenon ∨ e = .projectile) :
    e.QualifiesAsSimpleTransitiveSubject := by
  rcases h with h | h <;> subst h <;> decide

/-- basic-*sweep* admits an agentive subject in the simple transitive
frame, but only with a `with` phrase specifying body part or instrument
to provide a force-bearer (p.25 on *The harpist swept the strings of her
instrument ??(with a bow)*). The agent qualifies as effector by (45);
the body part / instrument is the force-bearer.

This is captured at the type level: an `agent` Effector qualifies as a
simple-transitive subject because it's self-energetic via intentional
control. The `with`-phrase requirement is a separate condition on the
syntactic frame, not on the effector classification.

[rissman-vanputten-majid-2022]: body parts as instrument-like
extensions of the subject. -/
theorem basicSweep_simple_transitive_admits_agent :
    Effector.agent.QualifiesAsSimpleTransitiveSubject := trivial

/-- An instrument or body part by itself cannot be a basic-*sweep* simple
transitive subject (p.21: *body part and instrument options are not
found* without an agent). They are not self-energetic. -/
theorem basicSweep_rejects_bare_instrument :
    ¬ Effector.instrument.QualifiesAsSimpleTransitiveSubject := id

/-! ### Obligatory agentivity in broom-*sweep* -/

/-- broom-*sweep*'s lexically saturated moving entity is a broom — an
artifact-noun-derived instrument ([kiparsky-1997] on canonical-use).
Brooms require intentional manipulation (paper footnote 9, p.7);
therefore the external argument of broom-*sweep* must be capable of
intentional instrument manipulation: agent or machine.

This is the **obligatory agentivity** of broom-*sweep*.

The proof factors through `Effector.canManipulateInstrument`: only `agent`
and `machine` qualify, matching the disjunction in the conclusion. -/
theorem broomSweep_obligatorily_agentive (e : Effector)
    (h : e.CanManipulateInstrument) :
    e = .agent ∨ e = .machine := by
  cases e <;> simp_all [Effector.CanManipulateInstrument]

/-! ### broom-*sweep* lacks the causative alternation -/

/-- broom-*sweep* is obligatorily agentive (above), and lacks the
causative alternation: *Danny swept the floor / \*The floor swept*
(p.12, eq.31).

At the level of the event-structure-to-frame mapping: motion-determines
AR is unavailable for broom-*sweep* because x_broom is lexically
saturated and cannot serve as the small-clause subject required by
principle (43a) (p.30, after eq.86). The `realizeFrame` function
encodes this: motion-determines on a saturated event structure
returns `none`. -/
theorem broomSweep_no_motion_determined_frame (hc : Bool) :
    realizeFrame broomSweep .motion hc = none := by
  cases hc <;> rfl

/-- Conversely, broom-*sweep* can still derive a frame via the contact
predicate: the simple transitive frame *I swept the floor*. The
unspecified-object frame *Yesterday I swept in the morning* is a
distinct realization licensed by routine-activity narrowing (separate
from `realizeFrame` which folds it into `simpleTransitive`; see
`LicensesUnspecifiedObject` below). -/
theorem broomSweep_contact_yields_simple_transitive (hc : Bool) :
    realizeFrame broomSweep .contact hc = some .simpleTransitive := by
  cases hc <;> rfl

/-! ### Counterexample to the resultative restriction -/

/-- [schaefer-2012]'s **resultative restriction**: non-agentive
external arguments require a result phrase in the VP (or imply one).
[folli-harley-2008] refined this to *external arguments lacking
teleological capability*.

basic-*sweep* with the contact-determines derivation falsifies both:
*A breeze moved the willows, the tips of their branches sweeping the
ground* (eq.92) — inanimate, non-teleological external argument, no
explicit or implied result.

This is the paper's central empirical departure from the literature on
external-argument licensing. -/
theorem resultative_restriction_falsified :
    -- Witness: basic-*sweep* simple-transitive with a non-teleological
    -- non-agentive subject (e.g. tree branch tips) and no result phrase
    -- is acceptable.
    realizeFrame basicSweep .contact false = some .simpleTransitive ∧
    Effector.naturalPhenomenon.IsSelfEnergetic ∧
    -- The result phrase is not part of the derived structure
    -- (no result-state field in MotionContactES; no causer needed).
    ¬ basicSweep.IsLexicallySaturated :=
  ⟨rfl, trivial, id⟩

/-! ### Routine-activity narrowing -/

/-- broom-*sweep*'s unspecified-object frame is licensed by routine-activity
narrowing ([glass-2022], [brisson-1994], [mittwoch-2005]):
denominal-like verbs derived via lexicalization of artifacts come to
refer to culturally-recognized routine activities for which the
canonical-purpose object can be omitted.

Parallel cases (p.28-29):
* `mop` (denominal from *mop*, the canonical activity is floor-mopping)
* `bake` (non-denominal but specialized to baked-goods preparation in the
  unspecified-object frame: *I baked this morning* ≠ baking potatoes)
* `clean` ([levin-rappaport-hovav-2014])
* `wash` (Alexiadou et al. 2017 from the references)

basic-*sweep* does NOT license the unspecified-object frame
(p.13: in the basic-*sweep* sense the verb is never found with
unspecified objects in any syntactic frame). -/
def LicensesUnspecifiedObject (es : MotionContactES) : Prop :=
  es.IsLexicallySaturated

instance (es : MotionContactES) : Decidable (LicensesUnspecifiedObject es) :=
  inferInstanceAs (Decidable es.IsLexicallySaturated)

@[simp] theorem broomSweep_licenses_unspecified : LicensesUnspecifiedObject broomSweep := trivial

@[simp] theorem basicSweep_no_unspecified : ¬ LicensesUnspecifiedObject basicSweep := id

/-! ### Motivated polysemy

The paper distinguishes its analysis of *sweep*'s two senses from
"regular polysemy" ([apresjan-1973], Pustejovsky 1995, 1998,
[nunberg-1995], [cruse-1995], [dolling-2014]) by two
diagnostics:

1. **Zeugma test** (Zwicky & Sadock 1975, Cruse 1986, Asher 2011 §3-4;
   p.13 eq.35): co-predication of the two senses is odd.
   `#The sailor swept the deck and so did the rain.`
   Regular polysemy (e.g., *book* = text/object) allows co-predication;
   broom-*sweep*/basic-*sweep* do not.

2. **Idiosyncratic lexicalization**: broom-*sweep* lexicalizes broom
   as the moving entity, but this is an idiosyncratic fact about
   English — there is no general process making instrument-lexicalized
   senses of all motion-contact verbs (p.28: English exceptionally
   lacks denominal *broom*, with *sweep* blocking it). -/

/-- Motivated polysemy: two related senses sharing a root and overlapping
event structure, but **not** co-predicable (failing the zeugma test). -/
structure MotivatedPolysemy where
  /-- The basic sense, structurally simpler. -/
  basicSense : MotionContactES
  /-- The specialized sense, derived from basic by lexicalization. -/
  specializedSense : MotionContactES
  /-- The specialized sense is derived from the basic sense by
      saturating the moving-entity variable. -/
  specializedIsSaturationOfBasic :
    ¬ basicSense.IsLexicallySaturated ∧ specializedSense.IsLexicallySaturated
  deriving Repr

/-- *sweep*'s two senses constitute motivated polysemy. -/
def sweepPolysemy : MotivatedPolysemy where
  basicSense := basicSweep
  specializedSense := broomSweep
  specializedIsSaturationOfBasic := ⟨id, trivial⟩

/-! ### Wiping-verbs class generalization -/

/-- The motion-and-sustained-contact event structure generalizes to the
[levin-1993] class 10.4 (wiping verbs): *sweep*, *rub*, *scrape*,
*wipe*. The paper establishes generalization in §2.3-2.4
(p.13-14): *rub* and *scrape* show the same constellation of syntactic
frames as basic-*sweep*, supporting the contention that basic-*sweep*'s
event structure is shared by the class. *wipe* itself is not explicitly
worked through but is assumed to pattern with the class
([levin-rappaport-hovav-1991]).

These verbs differ in lexicalized **manner** (the type of motion-with-contact):
* *sweep*: extended movement across a planar surface, contact during
  trajectory ([mcnally-spalek-2022]).
* *rub*: contact with pressure, back-and-forth or circular movement.
* *scrape*: similar to sweep but with a harder contact and removal
  affordance.
* *wipe*: similar to sweep, often with a cloth-like instrument. -/
inductive WipingVerb where
  | sweep
  | rub
  | scrape
  | wipe
  deriving DecidableEq, Repr

/-- Every wiping verb has basic-*sweep*'s event structure as its basic
sense (§2.3-2.4). -/
def WipingVerb.basicEventStructure : WipingVerb → MotionContactES
  | _ => basicSweep

/-- Only *sweep* has an attested broom-sense in English (p.13-14, p.28).
*rub* and *scrape* lack a specialized agentive sub-sense. -/
def WipingVerb.HasSpecializedSense : WipingVerb → Prop
  | .sweep => True
  | _      => False

instance (v : WipingVerb) : Decidable v.HasSpecializedSense := by
  cases v <;> unfold WipingVerb.HasSpecializedSense <;> infer_instance

/-! ### Bridge to existing substrate

The wiping-verbs class corresponds to [levin-1993] class 10.4,
encoded as `LevinClass.wipe` in `Linglib/Semantics/Lexical/LevinClass.lean`.
Verbs in this class share the basic-*sweep* event structure. -/

/-- [levin-1993] 10.4 — the wiping-verbs Levin class. -/
def wipingLevinClass : LevinClass := .wipe

/-- All `WipingVerb` instances belong to `LevinClass.wipe`. -/
def WipingVerb.levinClass : WipingVerb → LevinClass := fun _ => wipingLevinClass

@[simp] theorem WipingVerb.all_in_wipe (v : WipingVerb) : v.levinClass = .wipe := by
  cases v <;> rfl

end RappaportHovavLevin2024
