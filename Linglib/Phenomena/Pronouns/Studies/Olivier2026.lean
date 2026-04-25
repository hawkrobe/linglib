import Linglib.Theories.Syntax.Minimalism.PersonGeometry
import Linglib.Theories.Syntax.Minimalism.Phase
import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Phenomena.AuxiliaryVerbs.Studies.Olivier2026

/-!
# @cite{olivier-2026} — clitic-typology asymmetry

Novel observation in @cite{olivier-2026} (also reported by
@cite{cardinaletti-shlonsky-2004}, but not previously formalised):
not all climbing clitics interact with Auxiliary Switch.
**Prepositional clitics** (locative *y/ci*, partitive *en/ne*,
non-reflexive dative *lui/gli*) climb to the matrix domain
WITHOUT triggering AS. Only **reflexive** clitic climbing
correlates with AS.

## Mechanism (Olivier 2026 §6.2, §7.1)

The asymmetry derives from one structural property: a reflexive
clitic is bound by the External Argument via Voice* (the strong,
agentive phase head — @cite{wurmbrand-shimamura-2017},
@cite{wood-2015}'s [+θ, +D] reflexive Voice). Under the SHARE
mode of φ-feature transfer (@cite{ouali-2008}, formalised in
`Minimalism.TransferStyle`), Voice* shares the now-EA-identical
clitic features with vMOD; vAux inherits these via head-splitting;
T probes EA and ends up with matching person/ID values, yielding
BE-insertion. Other clitic types do not enter the EA-binding chain,
so no ID-matching obtains and HAVE surfaces.

All argument clitics carry φ-features (Olivier fn 27 — locatives
and partitives included); the asymmetry is not that some clitics
lack φ. The asymmetry is which clitics enter binding by EA via
Voice*.

## What this file commits to

This file's load-bearing claim is the per-clitic-type structural
property `boundByEAviaVoiceStar` and the projection from a clitic
type to an `AuxiliaryVerbs.Studies.Olivier2026.RestructuringClause`
configuration. The AS prediction is then *derived* from the
sibling file's `AuxiliarySwitchOccurs` predicate — not stipulated
per case.

The `Minimalism.TransferStyle` (KEEP/SHARE/DONATE) and `VoiceHead`
infrastructure are imported but not parametrised at the
phenomenon level — language-level KEEP-vs-SHARE variation lives
in the AuxVerbs sibling's diachronic-French / Sardinian
generalisations, not here.

## Empirical caveat (Olivier fn 18, Cinque 2006:60 fn 49)

Prepositional-clitic climbing out of unaccusative complements
(e.g. Italian *Maria c'ha dovuto venire molte volte* — locative
climbing + HAVE despite unaccusative *venire*) is colloquial and
yields varying acceptability among speakers. Olivier's analysis
predicts AS in such cases (the embedded verb is unaccusative);
the absence of AS is treated as diatopic markedness rather than
counter-evidence. The formalisation below does not capture this
colloquial-Italian deviation.

The contrast formalised here is the canonical case: prepositional
clitics climbing out of *transitive* complements vs reflexive
clitics climbing out of *reflexive* complements.
-/

namespace Phenomena.Pronouns.Studies.Olivier2026

open Phenomena.AuxiliaryVerbs.Studies.Olivier2026
  (RestructuringClause AuxiliarySwitchOccurs predictedMatrixAux
   beWantReflexiveClimbed)
open Phenomena.AuxiliaryVerbs.Selection (TransitivityClass PerfectAux SelectsBe)

/-! ## Clitic types

Romance argument-clitic categories relevant to the AS-trigger
asymmetry. The taxonomy is empirically supported by the distinct
forms (*y/ci*, *en/ne*, *lui/gli*, *le/la/lo*, *se/si*) and by
their differential climbing behaviour in restructuring contexts. -/

/-- Romance clitic categories relevant to the AS-trigger asymmetry
    in @cite{olivier-2026}. -/
inductive CliticType where
  /-- *se*, *si* — bound by the local subject via Voice*. -/
  | reflexive
  /-- *y*, *ci* — PP-internal locative. -/
  | locative
  /-- *en*, *ne* — PP-internal partitive. -/
  | partitive
  /-- *lui*, *gli* — non-reflexive dative (PP- or Appl-internal). -/
  | dative
  /-- *le*, *la*, *lo* — direct internal argument with independent
      reference. -/
  | accusative
  deriving DecidableEq, Repr

/-! ## The load-bearing configurational property

Per @cite{olivier-2026} §6.2: only reflexive clitics enter binding
by the External Argument via Voice*. This is the single structural
property from which the AS-trigger asymmetry derives. -/

/-- Whether a clitic of this type enters EA-binding via Voice*.

    Only reflexive clitics do — locatives and partitives are
    PP-internal arguments not introduced by Voice*; non-reflexive
    datives have independent referents; accusatives bear their own
    referential index distinct from EA's. -/
def CliticType.boundByEAviaVoiceStar : CliticType → Bool
  | .reflexive => true
  | _          => false

/-- The embedded-verb transitivity class induced when a clitic of
    this type is the embedded internal argument. Only a reflexive
    clitic forces a `.reflexive` embedded class (and hence
    BE-selection of the embedded predicate); the others appear with
    transitive embedded verbs.

    This is the projection from clitic-type taxonomy to the
    `Phenomena.AuxiliaryVerbs.Selection.TransitivityClass` enum
    used by the AuxVerbs sibling's AS predicate. -/
def CliticType.embeddedClassOnClimbing : CliticType → TransitivityClass
  | .reflexive => .reflexive
  | _          => .transitive

/-! ## Canonical climbing scenarios

For each clitic type, the canonical modal-compound restructuring
clause induced by climbing of a clitic of that type. The embedded
verb class follows from the clitic type; the reflexive position
flag is `.climbed` only when the clitic is itself reflexive. -/

/-- The canonical modal-compound restructuring scenario in which a
    clitic of type `c` has climbed to the matrix domain. -/
def CliticType.canonicalScenario (c : CliticType) : RestructuringClause :=
  { matrixModal := true
  , compoundTense := true
  , embeddedClass := c.embeddedClassOnClimbing
  , refCliticPos :=
      if c.boundByEAviaVoiceStar then .climbed else .none }

/-! ## Theorems: AS prediction is derived, not stipulated

The central claim is `triggersAS_iff_boundByEAviaVoiceStar`: the
AS prediction for a canonical climbing scenario is the iff of the
configurational property, derived from the AuxVerbs sibling's
`AuxiliarySwitchOccurs` predicate. The five per-clitic-type
smoke checks below follow from it. -/

/-- A clitic of type `c`, climbing in its canonical scenario,
    triggers Auxiliary Switch iff it is bound by the External
    Argument via Voice*. This is @cite{olivier-2026}'s central
    asymmetry, derived (not stipulated) from the structural
    property `boundByEAviaVoiceStar` and the AuxVerbs sibling's
    AS predicate. -/
theorem triggersAS_iff_boundByEAviaVoiceStar (c : CliticType) :
    AuxiliarySwitchOccurs c.canonicalScenario ↔
      c.boundByEAviaVoiceStar = true := by
  cases c <;>
    simp [CliticType.canonicalScenario,
          CliticType.boundByEAviaVoiceStar,
          CliticType.embeddedClassOnClimbing,
          AuxiliarySwitchOccurs, SelectsBe,
          Phenomena.AuxiliaryVerbs.Selection.canonicalSelection,
          Phenomena.AuxiliaryVerbs.Selection.selection]

/-! ### Per-clitic-type smoke checks

Decide-closed instantiations of `triggersAS_iff_boundByEAviaVoiceStar`.
They document expected outputs and serve as guards against
regressions in the AuxVerbs sibling's predicate. -/

example : AuxiliarySwitchOccurs CliticType.reflexive.canonicalScenario := by
  decide
example : ¬ AuxiliarySwitchOccurs CliticType.locative.canonicalScenario := by
  decide
example : ¬ AuxiliarySwitchOccurs CliticType.partitive.canonicalScenario := by
  decide
example : ¬ AuxiliarySwitchOccurs CliticType.dative.canonicalScenario := by
  decide
example : ¬ AuxiliarySwitchOccurs CliticType.accusative.canonicalScenario := by
  decide

/-- Predicted matrix auxiliary across all five clitic types: BE iff
    the clitic enters EA-binding via Voice*. -/
theorem predictedAux_eq_be_iff_boundByEAviaVoiceStar (c : CliticType) :
    predictedMatrixAux c.canonicalScenario = .be ↔
      c.boundByEAviaVoiceStar = true := by
  constructor
  · intro h
    apply (triggersAS_iff_boundByEAviaVoiceStar c).mp
    by_contra hne
    unfold predictedMatrixAux at h
    rw [if_neg hne] at h
    exact PerfectAux.noConfusion h
  · intro hb
    have hAS := (triggersAS_iff_boundByEAviaVoiceStar c).mpr hb
    unfold predictedMatrixAux
    rw [if_pos hAS]

/-! ## Bridge to AuxVerbs sibling's canonical reflexive scenario

The AuxVerbs sibling defines `beWantReflexiveClimbed` as the
canonical reflexive-climbing scenario. We confirm this is exactly
the canonical scenario produced by `CliticType.reflexive`. -/

/-- The canonical reflexive-clitic scenario coincides with the
    AuxVerbs sibling's `beWantReflexiveClimbed` witness. -/
theorem reflexive_canonical_eq_beWantReflexiveClimbed :
    CliticType.reflexive.canonicalScenario = beWantReflexiveClimbed := rfl

end Phenomena.Pronouns.Studies.Olivier2026
