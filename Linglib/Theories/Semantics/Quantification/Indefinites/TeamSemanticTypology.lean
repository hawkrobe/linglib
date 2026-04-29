import Linglib.Typology.Indefinite

/-!
# Degano & Aloni 2025: 7-type team-semantic typology of indefinites
@cite{degano-aloni-2025} @cite{hodges-1997} @cite{vaananen-2007}

A theory-side projection from the consensus
`Typology.Indefinite.IndefiniteEntry` substrate (Haspelmath-style
function-coverage data) into Degano & Aloni's 7-type classification.

This file follows the consensus-only Fragment-schema discipline: D&A's
classification is one paper's apparatus, so it lives here as a projection
rather than as a field of `IndefiniteEntry`. Per-language Fragment files
encode raw function-coverage data; consumers wanting D&A's typology
import this file and project.

## Schema

- `DAType`: the 7 types arising from Boolean combinations of `var(y,x)`
  and `dep(y,x)` with within-world (`v`) and across-all-worlds (`∅`)
  parameter choices.
- `DAType.profile`: each type's theoretical coverage on the
  Haspelmath SK/SU/NS triangle.
- `IndefiniteEntry.surfaceDAType`: classify an entry by exact match
  of its actual function-coverage to a D&A type's profile. Returns
  `none` when the entry covers a region D&A doesn't subdivide (e.g.,
  free choice, polarity-sensitive forms) or when actual ⊊ profile.
- `IndefiniteEntry.consistentWith`: weaker relation — actual coverage
  is a subset of the theoretical profile. Used for entries where
  paradigmatic competition narrows the actual distribution
  (e.g., Russian *kto-to* ⊊ type-iv epistemic profile).

## Type table

| Type | Requirement       | Profile (SK/SU/NS) | Example          |
|------|-------------------|--------------------|------------------|
| (i)   | (none)           | {SK, SU, NS}      | English *some-* |
| (ii)  | dep(v,x)         | {SK, SU}          | Yakut *kim ere* |
| (iii) | var(v,x)         | {NS}              | Russian *-nibud'*|
| (iv)  | var(∅,x)         | {SU, NS}          | German *irgend-*|
| (v)   | dep(∅,x)         | {SK}              | Russian *koe-*  |
| (vi)  | dep(∅,x)∧var(v,x)| {SK, NS}          | *unattested*    |
| (vii) | dep(v,x)∧var(∅,x)| {SU}              | Kannada *yāru-oo*|
-/

set_option autoImplicit false

namespace Semantics.Quantification.DeganoAloni2025

open Typology.Indefinite

/-- @cite{degano-aloni-2025}'s seven-type team-semantic typology.
    Types arise from Boolean combinations of `var(y,x)` (variation) and
    `dep(y,x)` (constancy/dependence) with two parameter choices for `y`:
    within-world (`v`) and across-all-worlds (`∅`). -/
inductive DAType where
  /-- (i) No restriction. Profile: SK ∪ SU ∪ NS. -/
  | unmarked
  /-- (ii) `dep(v,x)`: constancy within each epistemic world.
      Profile: SK + SU. -/
  | specific
  /-- (iii) `var(v,x)`: variation within some epistemic world.
      Profile: NS only. -/
  | nonSpecific
  /-- (iv) `var(∅,x)`: variation across all epistemic worlds.
      Profile: SU + NS. -/
  | epistemic
  /-- (v) `dep(∅,x)`: constancy across all epistemic worlds.
      Profile: SK only. -/
  | specificKnown
  /-- (vi) `dep(∅,x) ∧ var(v,x)`: contradictory; profile {SK, NS}
      is non-contiguous on Haspelmath's map and *unattested*. -/
  | skPlusNS
  /-- (vii) `dep(v,x) ∧ var(∅,x)`: rare conjunctive type; profile SU only. -/
  | specificUnknown
  deriving DecidableEq, Repr, BEq

/-- D&A theoretical profile: the SK/SU/NS subset of Haspelmath functions
    a type's semantics PERMITS. Actual paradigm distribution may be
    narrower due to competition with more-specific forms. -/
def DAType.profile : DAType → Finset HaspelmathFunction
  | .unmarked        =>
      {.specificKnown, .specificUnknown, .irrealis}
  | .specific        => {.specificKnown, .specificUnknown}
  | .nonSpecific     => {.irrealis}
  | .epistemic       => {.specificUnknown, .irrealis}
  | .specificKnown   => {.specificKnown}
  | .skPlusNS        => {.specificKnown, .irrealis}
  | .specificUnknown => {.specificUnknown}

/-- Type (vi) `skPlusNS` is contradictory in team semantics: `dep(∅,x)`
    forbids cross-world variation while `var(v,x)` requires intra-world
    variation. Empirically: no surveyed language has a form whose
    distribution exactly matches the `{SK, NS}` profile. -/
def DAType.IsAttested (t : DAType) : Prop := t ≠ .skPlusNS

instance : DecidablePred DAType.IsAttested :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

theorem skPlusNS_unattested : ¬ DAType.IsAttested .skPlusNS := by decide

end Semantics.Quantification.DeganoAloni2025

-- ============================================================================
-- IndefiniteEntry projections
-- ============================================================================

/- Methods on `IndefiniteEntry` live in its own namespace so that
   dot notation (`entry.surfaceDAType`) resolves them. -/
namespace Typology.Indefinite.IndefiniteEntry

open Semantics.Quantification.DeganoAloni2025

/-- Surface-classifier: project an entry to the D&A type whose theoretical
    profile exactly matches the entry's actual function-coverage.

    Returns `none` when the entry covers a region D&A doesn't subdivide
    (free choice, polarity-sensitive uses, or any function outside
    SK/SU/NS) or when actual coverage is a proper subset of any type's
    profile (a paradigmatic-competition case — see `consistentWith`). -/
def surfaceDAType (e : IndefiniteEntry) : Option DAType :=
  if e.functions = DAType.unmarked.profile then some .unmarked
  else if e.functions = DAType.specific.profile then some .specific
  else if e.functions = DAType.nonSpecific.profile then some .nonSpecific
  else if e.functions = DAType.epistemic.profile then some .epistemic
  else if e.functions = DAType.specificKnown.profile then some .specificKnown
  else if e.functions = DAType.skPlusNS.profile then some .skPlusNS
  else if e.functions = DAType.specificUnknown.profile then some .specificUnknown
  else none

/-- Consistency relation: an entry's actual coverage is contained in
    `t`'s theoretical profile. Allows actual ⊊ profile, capturing
    paradigmatic-competition cases such as Russian *kto-to* (type-iv
    epistemic profile permits SU + NS, but *-to* covers only SU because
    *-nibud'* blocks it from NS — see @cite{bubnov-2026} §7). -/
def consistentWith (e : IndefiniteEntry) (t : DAType) : Bool :=
  decide (e.functions ⊆ t.profile)

end Typology.Indefinite.IndefiniteEntry
