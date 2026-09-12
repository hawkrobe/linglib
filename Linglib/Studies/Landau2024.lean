/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Basic
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Studies.Landau2015

/-!
# Landau (2024): Control

This file formalizes the empirical generalizations of [landau-2024], the Element surveying
control theory. The trichotomy of obligatory control, non-obligatory control, and no control
is read off finiteness and position on the Spanish paradigm (41): finite clauses show no
control in either position, infinitival complements obligatory control, and infinitival
subjects non-obligatory control, so non-obligatory control arises only in clauses that can
display obligatory control (`Status.of`, `noc_only_in_oc_capable`). The revised Visser's
generalization of [van-urk-2013] (19) bars implicit control when T agrees with a
referential DP, the Norwegian personal and impersonal passives of *promise* (20) being the
minimal pair (`RVG`, `norwegian_rvg`). The direct-discourse correlation of [postal-1970]
(33) predicts the controller from the person of the direct-discourse counterpart's subject,
and the Korean jussive markers (35) realize it grammatically: the volitional, imperative,
and exhortative markers induce subject, object, and split control under one verb of saying
(`korean_realizes_postal`). Partial control is confined to attitude complements ((36),
(37)): a predicative complement is saturated by its controller, which the library's
saturating dependencies deny a partial reading (`manage_excludes_pc`), and only
propositional complements host lexical subjects ((56), (58), (72), after [grano-2015]).
Non-obligatory control is licensed by topicality or by logophoric centrality, each
sufficient and neither necessary ((52), (55), `Antecedent.MayControl`), and controlled
adjuncts split into strict and alternating types by whether their head also builds a
propositional variant ((84), (89), `alternates_iff_propositional_variant`).

## Implementation notes

The tier system is that of `Studies/Landau2015.lean`; the generalizations are stated over
the Element's own configurations, and the partial-control row is the one derived from the
substrate. The strict/alternating split records both columns of table (89), the criterion
being validated on the English inventory rather than derived.

## References

* [landau-2024]
* [van-urk-2013]
* [postal-1970]
* [grano-2015]
-/

namespace Landau2024

open Control SetRel
open Semantics.Composition.TypeShifting (ComplementDenotation)

/-! ### The trichotomy (41) -/

/-- Control statuses: obligatory, non-obligatory, and no control. -/
inductive Status where
  | oc
  | noc
  | nc
  deriving DecidableEq

/-- The control status of a clause by its finiteness and its position, the Spanish
paradigm (41): finite clauses show no control anywhere, infinitival complements obligatory
control, and infinitival subjects non-obligatory control. -/
def Status.of (finite complement : Bool) : Status :=
  if finite then .nc else if complement then .oc else .noc

/-- Non-obligatory control occurs only in clauses that can display obligatory control, the
infinitives; an uncontrolled finite clause is no control. -/
theorem noc_only_in_oc_capable (f c : Bool) : Status.of f c = .noc → f = false := by
  cases f <;> cases c <;> decide

/-- Finite clauses are no control in every position. -/
theorem finite_is_nc (c : Bool) : Status.of true c = .nc := rfl

/-! ### The revised Visser's generalization (19), (20) -/

/-- A passive control configuration: whether T agrees with a referential DP, and whether
implicit control obtains. -/
structure PassiveConfig where
  tAgreesReferential : Bool
  implicitControl : Bool
  deriving DecidableEq

/-- The revised Visser's generalization of [van-urk-2013] (19): an implicit subject cannot
control when T agrees with a referential DP. -/
def RVG (c : PassiveConfig) : Prop :=
  c.tAgreesReferential = true → c.implicitControl = false

instance (c : PassiveConfig) : Decidable (RVG c) := inferInstanceAs (Decidable (_ → _))

/-- The Norwegian personal passive of *promise* (20a): T agrees with the promisee, and the
implicit agent cannot control. -/
def personalPassive : PassiveConfig := ⟨true, false⟩

/-- The impersonal passive (20b): an expletive, no referential agreement, and implicit
control. -/
def impersonalPassive : PassiveConfig := ⟨false, true⟩

/-- The pair obeys the generalization, and the impersonal passive shows that the absence of
referential agreement is what frees implicit control. -/
theorem norwegian_rvg : RVG personalPassive ∧ RVG impersonalPassive := by decide

/-! ### The direct-discourse correlation (33) and the Korean jussives (35) -/

/-- The subject of the direct-discourse counterpart. -/
inductive DDSubject where
  | speaker
  | addressee
  | speakerPlusAddressee
  deriving DecidableEq

/-- Which matrix argument controls. -/
inductive Choice where
  | subject
  | object
  | split
  deriving DecidableEq

/-- The correlation of [postal-1970] (33): a first-person direct-discourse subject gives
subject control, a second-person one object control, and a joint one split control. -/
def postalChoice : DDSubject → Choice
  | .speaker => .subject
  | .addressee => .object
  | .speakerPlusAddressee => .split

/-- The Korean control-inducing jussive markers (35): volitional *keyss*, imperative *la*,
exhortative *ca*. -/
inductive Jussive where
  | volitional
  | imperative
  | exhortative
  deriving DecidableEq

/-- The discourse orientation of each marker. -/
def Jussive.orientation : Jussive → DDSubject
  | .volitional => .speaker
  | .imperative => .addressee
  | .exhortative => .speakerPlusAddressee

/-- The controller each marker induces under *mal* 'say' (35). -/
def Jussive.controller : Jussive → Choice
  | .volitional => .subject
  | .imperative => .object
  | .exhortative => .split

/-- The jussive table realizes the correlation: the controller is fixed by the embedded
mood's orientation, not by the matrix verb, which is held constant. -/
theorem korean_realizes_postal (j : Jussive) : j.controller = postalChoice j.orientation := by
  cases j <;> rfl

/-! ### Partial control is confined to attitude complements (36), (37) -/

/-- The semantic layer a tier's complement inhabits ((56), (58)): predicative complements are
properties, logophoric ones propositions. -/
def tierDenotation : Landau2015.Tier → ComplementDenotation
  | .predicative => .property
  | .logophoric => .proposition

/-- Generalization (72): a lexical subject saturates a property, so exactly the propositional,
logophoric complements license one, the generalization originating with [grano-2015]. -/
theorem lexicalSubject_iff_logophoric (t : Landau2015.Tier) :
    tierDenotation t = .proposition ↔ t = .logophoric := by
  cases t <;> decide

/-- The configuration of (37a), *John managed to gather at 6*: the matrix controller in
position `0`, the embedded subject in position `1`. -/
def ex37Dependency : SetRel (Fin 2) (Fin 2) := {(0, 1)}

/-- The partial-control reading's referent sizes: the controller is properly contained in the
gathering group. -/
def ex37Val : Fin 2 → ℕ := λ p => if p = 0 then 1 else 2

/-- A partial-control reading is incompatible with a saturating dependency: the star on (37a),
from exhaustive sharing. -/
theorem manage_excludes_pc : ¬ IsSaturating ex37Val ex37Dependency :=
  λ h => h.not_isPartial ⟨0, 1, rfl, by decide⟩

/-! ### Non-obligatory control: topic and logophoric center (52), (55) -/

/-- A candidate antecedent's discourse status. -/
structure Antecedent where
  topic : Bool
  logophoricCenter : Bool
  deriving DecidableEq

/-- (55a): a DP may serve as non-obligatory controller iff it is a topic or a logophoric
center. -/
def Antecedent.MayControl (a : Antecedent) : Prop :=
  a.topic = true ∨ a.logophoricCenter = true

instance (a : Antecedent) : Decidable a.MayControl := inferInstanceAs (Decidable (_ ∨ _))

/-- (52): the implicit passive agent, a logophoric center that is no topic, controls (52a),
and so does an established topic with no perspective on the event (52b), while a DP with
neither status cannot. -/
theorem licensing_cases :
    Antecedent.MayControl ⟨false, true⟩ ∧ Antecedent.MayControl ⟨true, false⟩ ∧
      ¬ Antecedent.MayControl ⟨false, false⟩ := by
  decide

/-- Neither licensor is necessary: each case of (52) lacks the other's. -/
theorem neither_licensor_necessary :
    ¬ (∀ a : Antecedent, a.MayControl → a.topic = true) ∧
      ¬ (∀ a : Antecedent, a.MayControl → a.logophoricCenter = true) := by
  refine ⟨λ h => ?_, λ h => ?_⟩
  · simpa using h ⟨false, true⟩ (by decide)
  · simpa using h ⟨true, false⟩ (by decide)

/-! ### Adjunct control: strict against alternating (84), (89) -/

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
  deriving DecidableEq

/-- The observed split of (84): the adjunct type alternates between obligatory and
non-obligatory control, or is strictly obligatory. -/
def AdjunctType.Alternates : AdjunctType → Prop
  | .goal | .result | .stimulus | .subjectPurpose => False
  | _ => True

/-- The structural column of (89): the adjunct's head also builds a propositional variant,
one hosting a lexical subject. -/
def AdjunctType.HasPropositionalVariant : AdjunctType → Prop
  | .goal | .result | .stimulus | .subjectPurpose => False
  | _ => True

instance : DecidablePred AdjunctType.Alternates := λ a => by
  cases a <;> unfold AdjunctType.Alternates <;> infer_instance

instance : DecidablePred AdjunctType.HasPropositionalVariant := λ a => by
  cases a <;> unfold AdjunctType.HasPropositionalVariant <;> infer_instance

/-- The propositional-variant criterion on the English inventory: an adjunct type alternates
into non-obligatory control exactly when its head has a propositional variant, so the strict
types are the purely predicative ones. -/
theorem alternates_iff_propositional_variant (a : AdjunctType) :
    a.Alternates ↔ a.HasPropositionalVariant := by
  cases a <;> decide

end Landau2024
