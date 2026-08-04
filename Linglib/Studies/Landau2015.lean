import Linglib.Syntax.Control.Tier
import Linglib.Semantics.Verb.Basic
import Linglib.Data.Complementation.Noonan2007
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Landau (2015): A Two-Tiered Theory of Control
[landau-2015] [landau-2004] [landau-2013]

MIT Press. ISBN 978-0-262-02885-1.

The TTC framework itself — `Control.Tier`, `Control.PredicateClass`,
`Control.ClauseClass`, the Feature Transmission asymmetry, and the OC-NC
generalization — lives in `Syntax/Control/Tier.lean`. This file holds
the book's empirical engagement: the table (80) contrasts, the
*de se*/*de te* split in object control (table (36)), the derivation of
predicate classes from English Fragment verb entries, and the
consilience bridge to [noonan-2007]'s CTP classification.

## Main results

- `Table80Row` with the two availability columns: the six empirical
  contrasts of table (80), a perfect split between the tiers
  (`table80_complementary`); the mechanism rows cite their
  `Control.IsSaturating` derivations
- `objectControlReading`: psychological → *de se*, communicative →
  *de te* (table (36))
- `derivedLandauClass` / `derivedControlTier`: predicate classes derived
  from Fragment verb fields rather than stored
- `ctpToControlTier` / `ctpToLandauClass`: Noonan CTP classes mapped to
  the TTC, with the tier-consistency theorem
-/

namespace Landau2015

open Control
open Features (Attitude)

/-! ### Table (80): empirical contrasts -/

/-- The six contrast rows of table (80) of [landau-2015]. -/
inductive Table80Row where
  /-- OC into an inflected complement (the OC-NC generalization (70);
      `inflectedComplement_realizes_ocnc`) -/
  | inflectedComplement
  /-- `[−human]` PRO ((81): the logophoric binder is the
      AUTHOR/ADDRESSEE function, defined only for humans) -/
  | nonhumanPRO
  /-- Implicit control ((90)/(93): predication needs an overt
      external argument) -/
  | implicitControl
  /-- Control shift (`Control.IsSaturating.eq_of_controllers` blocks
      it under predication: the shifted reading assigns the saturated
      slot a different controller) -/
  | controlShift
  /-- Partial control (`Control.IsSaturating.not_hasPartial` blocks it
      under predication) -/
  | partialControl
  /-- Split control (`Control.IsSaturating.not_hasSplit` blocks it
      under predication) -/
  | splitControl
  deriving DecidableEq, Repr

/-- Table (80)'s predicative column. -/
def availableUnderPredicative : Table80Row → Bool
  | .inflectedComplement => true
  | .nonhumanPRO         => true
  | _                    => false

/-- Table (80)'s logophoric column. -/
def availableUnderLogophoric : Table80Row → Bool
  | .inflectedComplement => false
  | .nonhumanPRO         => false
  | _                    => true

/-- Table (80) is a perfect split: every contrast is available under
    exactly one tier. -/
theorem table80_complementary (r : Table80Row) :
    availableUnderLogophoric r = !availableUnderPredicative r := by
  cases r <;> rfl

/-- The inflected-complement row is the OC-NC generalization ((70)),
    derived from the calculus: `[+Agr]` leaves OC in `[−T]` complements
    (the predicative tier) and destroys it in `[+T]` complements (the
    logophoric tier), by the Feature Transmission asymmetry ((60):
    predication is not contingent on feature matching — Icelandic quirky
    constructions — while variable binding is, [heim-2008],
    [kratzer-2009]). Its empirical scope is contested ([ganenkov-2019]). -/
theorem inflectedComplement_realizes_ocnc :
    availableUnderPredicative .inflectedComplement
        = decide (ClauseClass.cSubjunctive.HasOC true)
    ∧ availableUnderLogophoric .inflectedComplement
        = decide (ClauseClass.fSubjunctive.HasOC true) := by
  exact ⟨by decide, by decide⟩

/-- EC verbs resist impersonal passives ((98) in [landau-2015]): a
    direct consequence of condition (90), since impersonal passives
    suppress the external argument that predicative control needs —
    the implicit-control row of table (80). Cross-linguistic evidence:
    Hebrew, German, Dutch, Russian. -/
theorem ec_resists_impersonal_passives :
    availableUnderPredicative .implicitControl = false := rfl

/-! ### De se / de te in object control (table (36)) -/

/-- The two logophoric readings of OC PRO under attitude predicates
    (table (36) of [landau-2015]): which coordinate of the embedded
    context is projected depends on the object control verb subclass. -/
inductive DeSeReading where
  /-- PRO = AUTHOR(i'): attitude holder's identification of self -/
  | deSe
  /-- PRO = ADDRESSEE(i'): attitude holder's identification of addressee -/
  | deTe
  deriving DecidableEq, Repr

/-- Object control verb subclasses (table (36)). -/
inductive ObjectControlSubclass where
  /-- Psychological verbs: *convince*, *persuade*, *dissuade*, *tempt* -/
  | psychological
  /-- Communicative verbs: *tell*, *ask*, *urge*, *recommend* -/
  | communicative
  deriving DecidableEq, Repr

/-- Psychological verbs bind the AUTHOR coordinate (*de se*);
    communicative verbs bind the ADDRESSEE coordinate (*de te*). -/
def objectControlReading : ObjectControlSubclass → DeSeReading
  | .psychological => .deSe
  | .communicative => .deTe

theorem psychological_deSe :
    objectControlReading .psychological = .deSe := rfl

theorem communicative_deTe :
    objectControlReading .communicative = .deTe := rfl

/-! ### Derived Landau class from Verb -/

/-- Derive [landau-2015]'s predicate class from Verb fields — a bridge
    from Fragment verb entries to the TTC deriving the classification
    from existing semantic fields rather than storing it independently.
    Returns `none` when the classification cannot be determined from the
    available fields (e.g., `try` has no `implicative`, `attitude`, or
    `cosType`).

    Mapping: `cosType` → aspectual; `implicative`/`causative` →
    implicative; `factivePresup` → factive; question-embedding without
    attitude → interrogative; doxastic → propositional; preferential →
    desiderative. -/
def derivedLandauClass (v : Verb) : Option PredicateClass :=
  if v.cosType.isSome then some .aspectual
  else if v.implicative.isSome then some .implicative
  else if v.causative.isSome then some .implicative
  else if v.factivePresup then some .factive
  else if v.takesQuestionBase && v.attitude.isNone then some .interrogative
  else match v.attitude with
    | some (.doxastic _)     => some .propositional
    | some (.preferential _) => some .desiderative
    | none                   => none

/-- Derive control tier from Verb fields: a control verb induces
    logophoric control iff it selects an attitude complement (detected
    via `attitude`, `factivePresup`, or `takesQuestionBase`); otherwise
    predicative. Returns `none` for non-control verbs. -/
def derivedControlTier (v : Verb) : Option Tier :=
  if v.controlType == ControlType.none && v.altControlType == ControlType.none then Option.none
  else match derivedLandauClass v with
    | some cls => some cls.tier
    | none =>
      if v.attitude.isSome || v.factivePresup || v.takesQuestionBase
      then some .logophoric
      else some .predicative

/-! ### Per-verb verification -/

section VerbVerification
open English.Predicates.Verbal

-- Predicative (EC) verbs: derived class → predicative tier

/-- "stop" (CoS cessation) → aspectual → predicative -/
theorem stop_aspectual :
    derivedLandauClass stop.toVerb = some .aspectual := rfl

/-- "start" (CoS inception) → aspectual → predicative -/
theorem start_aspectual :
    derivedLandauClass start.toVerb = some .aspectual := rfl

/-- "begin" (CoS inception) → aspectual → predicative -/
theorem begin_aspectual :
    derivedLandauClass begin_.toVerb = some .aspectual := rfl

/-- "continue" (CoS continuation) → aspectual → predicative -/
theorem continue_aspectual :
    derivedLandauClass continue_.toVerb = some .aspectual := rfl

/-- "manage" (positive implicative) → implicative → predicative -/
theorem manage_implicative :
    derivedLandauClass manage.toVerb = some .implicative := rfl

/-- "fail" (negative implicative) → implicative → predicative -/
theorem fail_implicative :
    derivedLandauClass fail.toVerb = some .implicative := rfl

/-- "remember" (positive implicative) → implicative → predicative -/
theorem remember_implicative :
    derivedLandauClass remember.toVerb = some .implicative := rfl

/-- "forget" (negative implicative) → implicative → predicative -/
theorem forget_implicative :
    derivedLandauClass forget.toVerb = some .implicative := rfl

/-- "force" (coercive causative) → implicative → predicative -/
theorem force_implicative :
    derivedLandauClass force.toVerb = some .implicative := rfl

-- Logophoric (PC) verbs: derived class → logophoric tier

/-- "want" (preferential attitude) → desiderative → logophoric -/
theorem want_desiderative :
    derivedLandauClass want.toVerb = some .desiderative := rfl

/-- "hope" (preferential attitude) → desiderative → logophoric -/
theorem hope_desiderative :
    derivedLandauClass hope.toVerb = some .desiderative := rfl

/-- "promise" (preferential attitude) → desiderative → logophoric.
    Previously unclassified; fixed by adding `attitude` to the
    Fragment entry per [landau-2015] (5c). -/
theorem promise_desiderative :
    derivedLandauClass promise.toVerb = some .desiderative := rfl

/-- "persuade" (preferential attitude, object control) → desiderative →
    logophoric, per [landau-2015] table (36). -/
theorem persuade_desiderative :
    derivedLandauClass persuade.toVerb = some .desiderative := rfl

/-- "regret" (factive) → factive → logophoric -/
theorem regret_factive :
    derivedLandauClass regret.toVerb = some .factive := rfl

/-- "know" (factive + question) → factive → logophoric -/
theorem know_factive :
    derivedLandauClass know.toVerb = some .factive := rfl

/-- "believe" (doxastic attitude) → propositional → logophoric -/
theorem believe_propositional :
    derivedLandauClass believe.toVerb = some .propositional := rfl

/-- "think" (doxastic attitude) → propositional → logophoric -/
theorem think_propositional :
    derivedLandauClass think.toVerb = some .propositional := rfl

/-- "wonder" (question-embedding, non-attitude) → interrogative → logophoric -/
theorem wonder_interrogative :
    derivedLandauClass wonder.toVerb = some .interrogative := rfl

-- Negative test: verbs that should NOT be classifiable

/-- "try" has no cosType, implicative, causative, factivePresup,
    takesQuestionBase, or attitude, so `derivedLandauClass` cannot
    classify it. This is correct: "try" is not implicative (trying
    doesn't entail succeeding) and not clearly attitudinal. -/
theorem try_unclassifiable :
    derivedLandauClass try_.toVerb = none := rfl

-- Control tier verification: derived tier matches expected tier

theorem stop_predicative_tier :
    (derivedLandauClass stop.toVerb).map (·.tier) = some .predicative := rfl

theorem manage_predicative_tier :
    (derivedLandauClass manage.toVerb).map (·.tier) = some .predicative := rfl

theorem want_logophoric_tier :
    (derivedLandauClass want.toVerb).map (·.tier) = some .logophoric := rfl

theorem regret_logophoric_tier :
    (derivedLandauClass regret.toVerb).map (·.tier) = some .logophoric := rfl

theorem believe_logophoric_tier :
    (derivedLandauClass believe.toVerb).map (·.tier) = some .logophoric := rfl

theorem wonder_logophoric_tier :
    (derivedLandauClass wonder.toVerb).map (·.tier) = some .logophoric := rfl

theorem promise_logophoric_tier :
    (derivedLandauClass promise.toVerb).map (·.tier) = some .logophoric := rfl

theorem persuade_logophoric_tier :
    (derivedLandauClass persuade.toVerb).map (·.tier) = some .logophoric := rfl

end VerbVerification

/-! ### Noonan CTP → Landau tier bridge -/

/-- Map [noonan-2007]'s CTP classes to [landau-2015]'s control tiers:
    modal/phasal/achievement/negative are nonattitude (predicative);
    utterance/propAttitude/commentative/knowledge/desiderative/
    manipulative are attitude (logophoric); pretence is ambiguous and
    perception typically takes no controlled complement. -/
def ctpToControlTier : CTPClass → Option Tier
  | .modal        => some .predicative
  | .phasal       => some .predicative
  | .achievement  => some .predicative
  | .negative     => some .predicative
  | .utterance    => some .logophoric
  | .propAttitude => some .logophoric
  | .commentative => some .logophoric
  | .knowledge    => some .logophoric
  | .desiderative => some .logophoric
  | .manipulative => some .logophoric
  | .pretence     => none
  | .perception   => none

/-- Map [noonan-2007]'s CTP classes to [landau-2015]'s predicate classes
    (where the mapping is unambiguous). -/
def ctpToLandauClass : CTPClass → Option PredicateClass
  | .modal        => some .modal
  | .phasal       => some .aspectual
  | .achievement  => some .implicative
  | .negative     => some .implicative
  | .commentative => some .factive
  | .knowledge    => some .factive
  | .propAttitude => some .propositional
  | .utterance    => some .propositional
  | .desiderative => some .desiderative
  | .manipulative => some .desiderative
  | .pretence     => none
  | .perception   => none

/-- When both mappings are defined, they agree on the control tier. -/
theorem ctp_tier_consistent (c : CTPClass)
    (hTier : (ctpToControlTier c).isSome = true)
    (hClass : (ctpToLandauClass c).isSome = true) :
    ctpToControlTier c = (ctpToLandauClass c).map (·.tier) := by
  cases c <;> simp_all [ctpToControlTier, ctpToLandauClass, PredicateClass.tier]

/-! [noonan-2007]'s equi-deletion criterion (§2.1) and [landau-2015]'s
    control tiers classify the same English verbs by independent
    properties; the bridge theorem makes the consilience kernel-checked,
    witnessed by `manage`. -/

open Data.Complementation.Noonan2007 (english_manage)

/-- Cross-paper consilience: Noonan-equi on the achievement class
    coincides with Landau's predicative tier. -/
theorem manage_equi_implies_predicative :
    english_manage.hasEquiDeletion = true →
    ctpToControlTier english_manage.ctpClass = some .predicative := by
  intro _
  rfl

end Landau2015
