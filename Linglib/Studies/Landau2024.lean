/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Tier
import Linglib.Syntax.Control.Taxonomy

/-!
# Landau (2024): Control

Formalizes [landau-2024] (Cambridge Elements in Generative Syntax),
the survey synthesizing the state of control theory: the revised
Visser's generalization ((19), [van-urk-2013]), the direct-discourse
correlation behind embedded-speech-act theories ((33),
[postal-1970]) and its Korean jussive realization ((35)), the
attitude-only distribution of partial control ((36)–(37)), the
OC/NOC/NC trichotomy ((41)), NOC's dual topic/logophoric licensing
((52)), and the strict-vs-alternating adjunct split with the
propositional-variant criterion ((84)/(89)). The dual theory of §5
is substrate
(`Syntax/Control/Tier.lean`, `Clause.lean`, `Dependency.lean`); this
file holds the Element's own empirical generalizations. Its (95)
challenges — backward control, PC's residue, agreement under
property theories, the OC-NC generalization's crosslinguistic
variation ([ganenkov-2019]), overt-PRO licensing, adjunct loci — are
the open frontier.

## References

* [I. Landau, *Control*][landau-2024]
-/

namespace Landau2024

open Control SetRel

/-! ### The OC/NOC/NC trichotomy

NOC is the non-OC behavior of clauses that *can* display OC; clauses
that never can (finite complements, in most languages) are no control
(NC). The Spanish paradigm (41): infinitival complements are OC,
infinitival subjects NOC, finite clauses NC in either position. -/

/-- Control statuses: obligatory, non-obligatory, and no control. -/
inductive Status where
  | oc
  | noc
  | nc
  deriving DecidableEq, Repr

/-- A row of the Spanish paradigm (41): clause finiteness, whether the
    clause sits in complement position, and its control status. -/
structure Ex41Row where
  finite : Bool
  complement : Bool
  status : Status
  deriving DecidableEq, Repr

/-- The four configurations of (41). -/
def ex41 : List Ex41Row :=
  [ ⟨false, true,  .oc⟩    -- (41a) infinitival complement
  , ⟨false, false, .noc⟩   -- (41b) infinitival subject
  , ⟨true,  true,  .nc⟩    -- (41c) finite complement
  , ⟨true,  false, .nc⟩ ]  -- (41d) finite subject

/-- NOC occurs only in clauses that can display OC: never in finite
    clauses, whose uncontrolled behavior is NC. -/
theorem noc_only_in_oc_capable :
    ∀ r ∈ ex41, r.status = .noc → r.finite = false := by
  decide

/-- Finite clauses are NC in every position. -/
theorem finite_is_nc : ∀ r ∈ ex41, r.finite = true → r.status = .nc := by
  decide

/-! ### The revised Visser's generalization

(19), [van-urk-2013]: implicit subjects cannot control if T agrees
with a referential DP. The Norwegian minimal pair (20): the personal
passive (T agrees with the promisee) blocks implicit control; the
impersonal passive (expletive, no referential agreement) allows it.
The interrogative complements of (22) are a genuine standing
exception. -/

/-- A passive control configuration: does T agree with a referential
    DP, and is implicit control licensed? -/
structure PassiveConfig where
  tAgreesReferential : Bool
  implicitControlOK : Bool
  deriving DecidableEq, Repr

/-- The Norwegian pair (20): personal vs impersonal passive of
    'promise'. -/
def ex20 : List PassiveConfig :=
  [⟨true, false⟩, ⟨false, true⟩]

/-- The revised Visser's generalization on (20): implicit control is
    licensed exactly where T does not agree with a referential DP. -/
theorem rvg : ∀ c ∈ ex20, c.implicitControlOK = !c.tAgreesReferential := by
  decide

/-! ### The direct-discourse correlation and Korean jussives

[postal-1970]'s generalization ((33)): if the direct-discourse
counterpart's subject is second person, the controller is the object;
if first person, the subject. The Korean jussive markers realize the
correlation grammatically ((35), with *mal* 'say' held fixed): the
volitional marker is speaker-oriented and induces subject control,
the imperative addressee-oriented inducing object control, the
exhortative speaker+addressee-oriented inducing split control;
the indicative induces no control. -/

/-- The subject of the direct-discourse counterpart. -/
inductive DDSubject where
  | speaker
  | addressee
  | speakerPlusAddressee
  deriving DecidableEq, Repr

/-- Which matrix argument controls. -/
inductive Choice where
  | subject
  | object
  | split
  deriving DecidableEq, Repr

/-- [postal-1970]'s correlation (33), stated over discourse roles:
    speaker-subject direct discourse → subject control,
    addressee-subject → object control, joint → split. -/
def postalChoice : DDSubject → Choice
  | .speaker              => .subject
  | .addressee            => .object
  | .speakerPlusAddressee => .split

/-- The Korean control-inducing jussive markers ((35b–d)). -/
inductive Jussive where
  /-- volitional *keyss* -/
  | volitional
  /-- imperative *la* -/
  | imperative
  /-- exhortative *ca* -/
  | exhortative
  deriving DecidableEq, Repr

/-- The discourse orientation of each jussive marker. -/
def Jussive.orientation : Jussive → DDSubject
  | .volitional  => .speaker
  | .imperative  => .addressee
  | .exhortative => .speakerPlusAddressee

/-- The controller each marker induces under *mal* 'say' ((35b–d)). -/
def Jussive.controller : Jussive → Choice
  | .volitional  => .subject
  | .imperative  => .object
  | .exhortative => .split

/-- The Korean jussive table realizes [postal-1970]'s correlation:
    controller choice is the direct-discourse role of the marker's
    orientation — determined by the embedded mood, not the (fixed)
    matrix verb. -/
theorem korean_realizes_postal (j : Jussive) :
    j.controller = postalChoice j.orientation := by
  cases j <;> rfl

/-! ### Partial control is attitude-only

(36)–(37): PC is attested in attitude complements and unavailable
under implicatives — *\*John managed to gather at 6* (37a). On the
dual theory this is `Control.IsSaturating.not_hasPartial`: implicative
complements are predicative, and predication saturates, sharing the
referent exhaustively. The (37a) configuration refutes saturating
status for its hypothetical PC reading, never the other way around. -/

/-- The (37a) configuration: matrix controller position `0`, embedded
    subject position `1`. -/
def ex37Dependency : SetRel (Fin 2) (Fin 2) := {(0, 1)}

/-- The PC reading's referent sizes: the controller (John) is properly
    contained in the gathering group. -/
def ex37Val : Fin 2 → ℕ :=
  fun p => if p = 0 then 1 else 2

/-- A partial-control reading is incompatible with a saturating
    dependency: (37a)'s star, from exhaustive sharing. -/
theorem manage_excludes_pc : ¬ IsSaturating ex37Val ex37Dependency :=
  fun h => h.not_hasPartial ⟨0, 1, rfl, by decide⟩

/-! ### NOC: dual licensing by topic and logophoric center

(52): topicality and logophoricity are each
sufficient for NOC antecedence and neither is necessary — (52a) is
NOC by a `[−top, +log]` antecedent (an implicit passive agent), (52b)
by `[+top, −log]` (an established topic with no mental perspective on
the event). The `[+human]` character of logophoric antecedents
follows from mental perspective; topical antecedents are only
*preferentially* human ((49)–(50), a defeasible empathy default). -/

/-- A candidate NOC antecedent's discourse status. -/
structure Antecedent where
  topic : Bool
  logophoricCenter : Bool
  deriving DecidableEq, Repr

/-- (55): a DP may serve as NOC controller iff it is a topic or a
    logophoric center. -/
def Antecedent.MayControl (a : Antecedent) : Prop :=
  a.topic = true ∨ a.logophoricCenter = true

instance (a : Antecedent) : Decidable a.MayControl :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- (52a): the implicit passive agent — a logophoric center that is
    no topic — controls. -/
theorem noc_by_log_alone : Antecedent.MayControl ⟨false, true⟩ := by decide

/-- (52b): the established topic with no perspective on the event
    controls. -/
theorem noc_by_topic_alone : Antecedent.MayControl ⟨true, false⟩ := by decide

/-- Neither licensor is necessary — each (52) case lacks the other's. -/
theorem neither_licensor_necessary :
    ¬(∀ a : Antecedent, a.MayControl → a.topic = true) ∧
      ¬(∀ a : Antecedent, a.MayControl → a.logophoricCenter = true) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h ⟨false, true⟩ (by decide)
  · simpa using h ⟨true, false⟩ (by decide)

/-- A DP with neither status cannot serve as NOC controller. -/
theorem no_status_no_control : ¬ Antecedent.MayControl ⟨false, false⟩ := by
  decide

/-! ### Adjunct control: strict OC vs alternating OC/NOC

(84): English controlled adjuncts split into strict
OC adjuncts and adjuncts alternating OC/NOC; strict *NOC* adjuncts
are unattested. The propositional-variant criterion ((89)): an
adjunct type alternates iff its head also builds a variant hosting a
lexical subject — the P head s-selects a property only (strict) or a
property/proposition ambiguously (alternating). -/

/-- The English controlled-adjunct types of (84). -/
inductive AdjunctType where
  | goal
  | result
  | stimulus
  | subjectPurpose
  | objectPurpose
  | rationale
  | temporal
  | absolutive
  | justification
  | telic
  deriving DecidableEq, Repr

/-- (84)'s observed split: does the adjunct type ever alternate into
    NOC? -/
def observedAlternates : AdjunctType → Bool
  | .goal | .result | .stimulus | .subjectPurpose => false
  | _ => true

/-- (89)'s structural column: does the adjunct head build a
    propositional variant (one hosting a lexical subject)? -/
def hasPropositionalVariant : AdjunctType → Bool
  | .goal | .result | .stimulus | .subjectPurpose => false
  | _ => true

/-- The propositional-variant criterion, validated on the English
    inventory: an adjunct type alternates into NOC exactly when its
    head has a propositional variant. -/
theorem alternates_iff_propositional_variant (a : AdjunctType) :
    observedAlternates a = hasPropositionalVariant a := by
  cases a <;> rfl

end Landau2024
