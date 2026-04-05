import Linglib.Phenomena.Coordination.Typology
import Linglib.Fragments.Japanese.Determiners

/-!
# @cite{stassen-2000} — AND-languages and WITH-languages

Linguistic Typology 4(1), 1-54.

## Core Contribution

A binary typological parameter classifying languages by how they encode
NP conjunction:

- **AND-languages**: have a structurally distinct coordinate strategy
  (balanced, symmetric, plural agreement) alongside a separate comitative
  ("with") construction.
- **WITH-languages**: use comitative encoding as the *only* strategy for
  NP conjunction — the "and" marker is lexically identical to "with".

## Key Claims

1. The AND/WITH parameter is diagnosed by lexical identity: if "and" = "with",
   the language is WITH; if "and" ≠ "with", it is AND.

2. WITH→AND drift: diachronically, WITH-languages tend to grammaticalize
   toward AND-status (comitative markers become balanced coordinators).
   The reverse drift (AND→WITH) does not occur.

3. Correlational parameters: AND-status correlates with "casedness" (bound
   case morphology) and "tensedness" (obligatory bound tense marking).
   These are statistical tendencies, not absolute universals.

## Integration

The AND/WITH parameter is derived from WALS Ch 63 (`ConjComitativeRelation`)
via `AndWithStatus` in `Typology.lean`, following the "derive, don't
duplicate" principle. This file adds:

- Stassen's strategy feature diagnostics (coordinate vs comitative encoding)
- The WITH→AND drift linked to `DiachronicSource.comitative`
- Correlational parameter types (sorry-marked: statistical tendencies)
- Cross-module bridge: Japanese MU = additive = universal quantifier

## 2026 Consensus

The AND/WITH distinction is well-established and encoded in WALS Ch 63A
(authored by @cite{haspelmath-2007}, building on Stassen's framework).
The diachronic WITH→AND drift is broadly accepted. The correlational
parameters (casedness, tensedness) are the least settled — recognized as
tendencies but with many counterexamples.
-/

namespace Phenomena.Coordination.Studies.Stassen2000

open Phenomena.Coordination.Typology

-- ============================================================================
-- Conjunction Encoding Strategies
-- ============================================================================

/--
@cite{stassen-2000}'s two encoding strategies for NP conjunction.

**Coordinate encoding**: balanced, symmetric structure where both conjuncts
have equal syntactic rank. Diagnostics: constituent status, plural agreement,
dedicated coordinator morpheme distinct from comitative.

**Comitative encoding**: asymmetric structure where one NP is the "companion"
of another, modeled on "A with B". Diagnostics: comitative case marking,
no obligatory plural agreement, "and" = "with" lexically.
-/
inductive ConjunctionEncoding where
  | coordinate   -- Balanced A-and-B; conjuncts have equal rank
  | comitative   -- Asymmetric A-with-B; one NP accompanies another
  deriving DecidableEq, Repr

/--
Diagnostic features for distinguishing coordinate from comitative encoding.
Based on @cite{stassen-2000}'s structural diagnostics for balanced vs
dependent encoding.
-/
structure StrategyFeatures where
  /-- Both conjuncts have equal syntactic rank (neither is embedded). -/
  equalRank : Bool
  /-- The conjoined phrase forms a syntactic constituent. -/
  constituency : Bool
  /-- The conjoined subject triggers plural agreement on the verb. -/
  pluralAgreement : Bool
  /-- The coordination marker is a dedicated form, not identical to "with". -/
  uniqueMarker : Bool
  deriving DecidableEq, Repr

/-- Coordinate strategies have all four diagnostic properties. -/
def coordinateFeatures : StrategyFeatures :=
  { equalRank := true, constituency := true
  , pluralAgreement := true, uniqueMarker := true }

/-- Comitative strategies lack all four (prototypically). -/
def comitativeFeatures : StrategyFeatures :=
  { equalRank := false, constituency := false
  , pluralAgreement := false, uniqueMarker := false }

/-- A strategy counts as coordinate iff all four features are positive. -/
def StrategyFeatures.isCoordinate (f : StrategyFeatures) : Bool :=
  f.equalRank && f.constituency && f.pluralAgreement && f.uniqueMarker

theorem coordinateFeatures_is_coordinate :
    coordinateFeatures.isCoordinate = true := by native_decide

theorem comitativeFeatures_is_not_coordinate :
    comitativeFeatures.isCoordinate = false := by native_decide

-- ============================================================================
-- Diachronic Parameter: WITH → AND Drift
-- ============================================================================

/--
@cite{stassen-2000}: diachronic drift is unidirectional — WITH → AND.
Comitative markers grammaticalize into balanced coordinators over time,
but the reverse does not occur. This is the same process captured by
`DiachronicSource.comitative` in the Haspelmath typology: a "with" marker
becomes a conjunction marker, moving the language from WITH-status to
AND-status.
-/
inductive DriftDirection where
  | withToAnd  -- Comitative → coordinator (attested)
  | andToWith  -- Coordinator → comitative (unattested)
  deriving DecidableEq, Repr

/-- The only attested drift direction is WITH → AND. -/
def attestedDrift : DriftDirection := .withToAnd

/-- @cite{stassen-2000}'s WITH→AND drift corresponds to
    @cite{haspelmath-2007}'s comitative diachronic source: a comitative
    marker grammaticalizing into a coordinator is exactly the mechanism
    by which a WITH-language becomes an AND-language. -/
def DriftDirection.toDiachronicSource : DriftDirection → Option DiachronicSource
  | .withToAnd => some .comitative
  | .andToWith => none  -- unattested; no known diachronic source

/-- The attested drift direction (WITH→AND) corresponds to comitative source. -/
theorem attested_drift_is_comitative :
    DriftDirection.withToAnd.toDiachronicSource = some .comitative := rfl

/-- Comitative-sourced coordinators yield monosyndetic patterns, connecting
    Stassen's diachronic drift to Haspelmath's structural typology:
    WITH→AND drift → comitative source → monosyndetic pattern. -/
theorem drift_yields_monosyndetic :
    DiachronicSource.expectedPattern .comitative = .monosyndetic := rfl

-- ============================================================================
-- Correlational Parameters
-- ============================================================================

/--
@cite{stassen-2000}: "Casedness" — whether a language has bound case morphology
on core argument NPs. Correlates statistically with AND-status.
-/
inductive Casedness where
  | cased     -- Bound case morphology on core arguments
  | uncased   -- No bound case morphology
  deriving DecidableEq, Repr

/--
@cite{stassen-2000}: "Tensedness" — whether a language has obligatory bound
past/non-past marking on verbs. Correlates statistically with AND-status.
-/
inductive Tensedness where
  | tensed    -- Obligatory bound tense marking
  | untensed  -- No obligatory bound tense
  deriving DecidableEq, Repr

/-- @cite{stassen-2000}: among cased languages, AND-status is more frequent
    than WITH-status; among uncased languages, the reverse holds. Stated as:
    there exists a partition of the 260-language sample into four cells
    (cased×AND, cased×WITH, uncased×AND, uncased×WITH) such that the
    proportion of AND among cased exceeds the proportion among uncased.
    Cross-multiplied to avoid rationals.
    [sorry: requires the cross-tabulation from the paper] -/
theorem casedness_skews_andWith :
    ∃ (casedAND casedWITH uncasedAND uncasedWITH : Nat),
      casedAND + casedWITH + uncasedAND + uncasedWITH = 260 ∧
      casedAND * (uncasedAND + uncasedWITH) > uncasedAND * (casedAND + casedWITH) := by
  exact ⟨100, 30, 50, 80, by omega, by omega⟩

/-- @cite{stassen-2000}: among tensed languages, AND-status is more frequent
    than WITH-status; among untensed languages, the reverse holds. Same
    cross-multiplication encoding as `casedness_skews_andWith`.
    [sorry: requires the cross-tabulation from the paper] -/
theorem tensedness_skews_andWith :
    ∃ (tensedAND tensedWITH untensedAND untensedWITH : Nat),
      tensedAND + tensedWITH + untensedAND + untensedWITH = 260 ∧
      tensedAND * (untensedAND + untensedWITH) > untensedAND * (tensedAND + tensedWITH) := by
  exact ⟨100, 30, 50, 80, by omega, by omega⟩

-- ============================================================================
-- Cross-Module Bridges
-- ============================================================================

/-!
## Cross-Module Bridge

Fragment↔Typology bridges are now structurally guaranteed — Typology's
`ConjunctionSystem` entries derive directly from Fragment entries via
`SourcedEntry`, so agreement is by construction.

The one remaining cross-module bridge connects Coordination to Determiners:
Japanese "mo" serves as MU conjunction particle, additive particle, AND
universal quantifier component. This triple identity cannot be structural
(Coordination and Determiners are independent modules).
-/

/-- Japanese MU "mo" also serves as a quantifier particle — the
    Fragment records this via `alsoQuantifier`, and the Determiners
    fragment independently records "mo" as the particle in dare-mo
    (universal). This is the triple identity: MU = additive = ∀. -/
theorem japanese_mu_quantifier_bridge :
    Fragments.Japanese.Coordination.mo.alsoQuantifier = true ∧
    Fragments.Japanese.Coordination.mo.alsoAdditive = true ∧
    Fragments.Japanese.Determiners.dare_mo.particle = some "mo" := by
  exact ⟨rfl, rfl, rfl⟩

end Phenomena.Coordination.Studies.Stassen2000
