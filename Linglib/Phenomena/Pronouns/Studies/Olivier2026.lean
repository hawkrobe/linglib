import Linglib.Theories.Syntax.Minimalism.PersonGeometry
import Linglib.Phenomena.AuxiliaryVerbs.Studies.Olivier2026

/-!
# @cite{olivier-2026} — clitic-typology asymmetry

A novel empirical observation in @cite{olivier-2026}: not all
climbing clitics interact with Auxiliary Switch. **Prepositional
clitics** (locative *y/ci*, partitive *en/ne*, dative *lui*) climb
to the matrix domain WITHOUT triggering AS. Only **reflexive**
clitic climbing correlates with AS.

The asymmetry follows from the ID-feature analysis. Reflexive
clitics carry an unvalued ID-feature that gets valued by the
binder via Voice*. When climbing equates the embedded ID with the
matrix subject's ID, T's ID-feature matches vAux's, and BE
surfaces. Prepositional clitics carry no matching ID — locatives
and partitives bear no φ at all, datives bear φ but no
ID-identity to the matrix subject — so their climbing is invisible
to the aux-selection rule.

This file formalises the asymmetry as a per-clitic-type predicate
derived from a featural profile, and bridges to the AS predicate
defined in `Phenomena.AuxiliaryVerbs.Studies.Olivier2026`.
-/

namespace Phenomena.Pronouns.Studies.Olivier2026

/-! ## Clitic types -/

/-- Clitic categories relevant to the @cite{olivier-2026}
    AS-trigger asymmetry. -/
inductive CliticType where
  | reflexive   -- se, si — bound by the local subject
  | locative    -- y, ci
  | partitive   -- en, ne
  | dative      -- lui, gli
  | accusative  -- le/la/lo
  deriving DecidableEq, Repr

/-! ## Featural profile

A clitic's ability to trigger AS on climbing is determined by
three structural properties: whether it bears φ-features at all,
whether it carries an ID-subfeature, and — most importantly —
whether the binding configuration aligns its ID with the matrix
subject's ID. Reflexives are the only category with all three. -/

/-- Featural profile of a clitic relevant to the AS-trigger rule. -/
structure CliticFeatureProfile where
  /-- Bears φ-features (person/number/gender). -/
  hasPhi : Bool
  /-- Carries an ID-subfeature (referential index, in the sense
      of `Minimalism.IdFeature`). -/
  hasId : Bool
  /-- ID-feature matches the binder's ID (as it does for a
      reflexive bound by the matrix subject). -/
  hasMatchingIdToBinder : Bool
  deriving DecidableEq, Repr

/-- The featural profile of each clitic type
    (@cite{olivier-2026}).

    - Reflexives bear φ, an ID, and (after binding by the matrix
      subject via Voice*) a matching ID. They alone trigger AS.
    - Locative and partitive clitics are PP-internal and bear no φ.
    - Datives bear φ but no matching ID — they refer to a
      goal/recipient distinct from the matrix subject.
    - Accusatives bear φ and an ID, but the ID is distinct from
      the matrix subject's (accusative ≠ subject by the
      θ-criterion). -/
def cliticProfile : CliticType → CliticFeatureProfile
  | .reflexive  => { hasPhi := true,  hasId := true,  hasMatchingIdToBinder := true }
  | .locative   => { hasPhi := false, hasId := false, hasMatchingIdToBinder := false }
  | .partitive  => { hasPhi := false, hasId := false, hasMatchingIdToBinder := false }
  | .dative     => { hasPhi := true,  hasId := false, hasMatchingIdToBinder := false }
  | .accusative => { hasPhi := true,  hasId := true,  hasMatchingIdToBinder := false }

/-- A climbing clitic triggers Auxiliary Switch iff its ID-feature
    matches the binder's. Derived from `cliticProfile`, not
    stipulated per case. -/
def triggersAuxSwitchOnClimbing (c : CliticType) : Bool :=
  (cliticProfile c).hasMatchingIdToBinder

/-! ## Theorems -/

/-- Reflexive clitics trigger AS on climbing — the canonical case
    of @cite{olivier-2026}. -/
theorem reflexive_triggers_as_on_climbing :
    triggersAuxSwitchOnClimbing .reflexive = true := rfl

/-- Locative clitics climb without triggering AS. -/
theorem locative_no_as_on_climbing :
    triggersAuxSwitchOnClimbing .locative = false := rfl

/-- Partitive clitics climb without triggering AS. -/
theorem partitive_no_as_on_climbing :
    triggersAuxSwitchOnClimbing .partitive = false := rfl

/-- Dative clitics climb without triggering AS — they bear φ but
    no ID-identity to the matrix subject. -/
theorem dative_no_as_on_climbing :
    triggersAuxSwitchOnClimbing .dative = false := rfl

/-- Accusative clitics likewise: they carry an ID, but it is
    distinct from the matrix subject's. -/
theorem accusative_no_as_on_climbing :
    triggersAuxSwitchOnClimbing .accusative = false := rfl

/-! ## Bridge to the AS predicate -/

open Phenomena.AuxiliaryVerbs.Studies.Olivier2026

/-- The reflexive case from `triggersAuxSwitchOnClimbing` agrees
    with the AS predicate in `Phenomena.AuxiliaryVerbs`: a modal
    matrix in compound tense with a reflexive complement whose
    clitic has climbed shows AS exactly when the reflexive
    triggers it. -/
theorem reflexive_climbing_aligns_with_as_predicate :
    triggersAuxSwitchOnClimbing .reflexive =
      auxiliarySwitchOccurs beWantReflexiveClimbed := rfl

end Phenomena.Pronouns.Studies.Olivier2026
