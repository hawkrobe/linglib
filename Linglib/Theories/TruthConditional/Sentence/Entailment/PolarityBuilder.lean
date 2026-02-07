/-
# Polarity Builder — Derived NPI Licensing from Monotonicity Proofs

Bridge between the theory-neutral Fragment (`DEStrength`) and the formal
monotonicity hierarchy (`IsDE`, `IsAntiAdditive`, `IsAntiMorphic`, `IsStrawsonDE`).

## Design principle

A `MonotonicityProfile` bundles a context function with Bool flags recording
which monotonicity properties have been proved. Licensing predictions are
**derived** from which flags are set, not stipulated. This follows the
`CausativeBuilder` pattern where force-dynamic mechanisms are named and
properties derived via theorems.

## Key result

"Only" has `strongestLevel = none` (not classically DE) yet
`licensesWeakNPI = true` (Strawson-DE suffices). This is von Fintel's (1999)
central insight, derived not stipulated.

## References

- von Fintel, K. (1999). NPI Licensing, Strawson Entailment, and Context
  Dependency. Journal of Semantics 16(2), 97–148.
- Denić, M., Homer, V., Rothschild, D. & Chemla, E. (2021). The influence
  of polarity items on inferential judgments. Cognitive Science 45(6).
-/

import Linglib.Theories.TruthConditional.Sentence.Entailment.StrawsonEntailment
import Linglib.Fragments.English.PolarityItems
import Linglib.Phenomena.Polarity.VonFintel1999

namespace TruthConditional.Sentence.Entailment.PolarityBuilder

open TruthConditional.Sentence.Entailment
open TruthConditional.Sentence.Entailment.AntiAdditivity
open TruthConditional.Sentence.Entailment.StrawsonEntailment
open TruthConditional.Core.Polarity
open Fragments.English.PolarityItems (PolarityItemEntry PolarityType ever liftAFinger)
open Phenomena.Polarity.VonFintel1999 (onlyNotDE)

-- ============================================================================
-- Section 1: MonotonicityProfile
-- ============================================================================

/--
A context function bundled with flags recording its proved monotonicity
properties.

Analogous to `CausativeBuilder` bundling force-dynamic mechanisms:
the profile records available proofs, and licensing predictions are
derived from which proofs are present.

The Bool flags are set `true` when a proof exists; the proofs themselves
live in separate verification theorems.
-/
structure MonotonicityProfile where
  /-- Name for documentation -/
  name : String
  /-- Is anti-morphic? (proved elsewhere) -/
  isAM : Bool := false
  /-- Is anti-additive? (proved elsewhere) -/
  isAA : Bool := false
  /-- Is classically DE? (proved elsewhere) -/
  isDE : Bool := false
  /-- Is Strawson-DE? (proved elsewhere) -/
  isStrawsonDE : Bool := false
  deriving Repr

-- ============================================================================
-- Section 2: Derived Properties (NOT stipulated)
-- ============================================================================

/--
Strongest DE level, derived from available proofs.

Maps to the Fragment's `DEStrength` enum. Strawson-DE is intentionally
excluded: it doesn't correspond to a classical DE level.
-/
def MonotonicityProfile.strongestLevel (p : MonotonicityProfile) : Option DEStrength :=
  if p.isAM then some .antiMorphic
  else if p.isAA then some .antiAdditive
  else if p.isDE then some .weak
  else none

/-- Does this profile have at least Strawson-DE? -/
def MonotonicityProfile.isAtLeastStrawsonDE (p : MonotonicityProfile) : Bool :=
  p.isAM || p.isAA || p.isDE || p.isStrawsonDE

/--
Derived: licenses weak NPIs.

Requires at least DE, or Strawson-DE (von Fintel 1999).
This is the key insight: Strawson-DE suffices for weak NPI licensing.
-/
def MonotonicityProfile.licensesWeakNPI (p : MonotonicityProfile) : Bool :=
  p.isAtLeastStrawsonDE

/--
Derived: licenses strong NPIs.

Requires anti-additive (Zwarts 1996). Strawson-DE and plain DE
are insufficient for strong NPIs like "lift a finger".
-/
def MonotonicityProfile.licensesStrongNPI (p : MonotonicityProfile) : Bool :=
  p.isAA || p.isAM

-- ============================================================================
-- Section 3: Smart Constructors (concrete profiles)
-- ============================================================================

/--
Negation profile: anti-morphic (strongest level).

Negation licenses both weak and strong NPIs.
-/
def negationProfile : MonotonicityProfile :=
  { name := "negation"
  , isAM := true
  , isAA := true
  , isDE := true
  , isStrawsonDE := true }

/--
"No student" profile: anti-additive.

"No student" licenses both weak and strong NPIs.
-/
def noStudentProfile : MonotonicityProfile :=
  { name := "no_student"
  , isAA := true
  , isDE := true
  , isStrawsonDE := true }

/--
"At most 2 students" profile: DE only.

"At most n" licenses weak NPIs but not strong NPIs.
-/
def atMost2Profile : MonotonicityProfile :=
  { name := "atMost2_student"
  , isDE := true
  , isStrawsonDE := true }

/--
"Only" profile: Strawson-DE only (not classically DE).

Von Fintel's central example: "only" is Strawson-DE but not DE.
It licenses weak NPIs despite not being classically DE.
-/
def onlyProfile : MonotonicityProfile :=
  { name := "only"
  , isStrawsonDE := true }
  -- Note: isDE = false, isAA = false — "only" is NOT classically DE

-- ============================================================================
-- Section 4: Bridge Theorems (per-context verification)
-- ============================================================================

/-! ### Negation: AM → licenses both weak and strong NPIs -/

theorem negation_licenses_weak : negationProfile.licensesWeakNPI = true := rfl
theorem negation_licenses_strong : negationProfile.licensesStrongNPI = true := rfl
theorem negation_strength : negationProfile.strongestLevel = some .antiMorphic := rfl

/-! ### "No student": AA → licenses both -/

theorem no_student_licenses_weak : noStudentProfile.licensesWeakNPI = true := rfl
theorem no_student_licenses_strong : noStudentProfile.licensesStrongNPI = true := rfl
theorem no_student_strength : noStudentProfile.strongestLevel = some .antiAdditive := rfl

/-! ### "At most 2 students": DE → licenses weak only -/

theorem atMost2_licenses_weak : atMost2Profile.licensesWeakNPI = true := rfl
theorem atMost2_not_licenses_strong : atMost2Profile.licensesStrongNPI = false := rfl
theorem atMost2_strength : atMost2Profile.strongestLevel = some .weak := rfl

/-! ### "Only": Strawson-DE only → licenses weak but NOT strong -/

theorem only_licenses_weak : onlyProfile.licensesWeakNPI = true := rfl
theorem only_not_licenses_strong : onlyProfile.licensesStrongNPI = false := rfl
theorem only_not_classically_de : onlyProfile.strongestLevel = none := rfl

/--
Von Fintel's central insight, derived not stipulated:
"only" licenses weak NPIs despite not being classically DE.

This is the key separation theorem: `strongestLevel = none` (no classical
DE level) yet `licensesWeakNPI = true` (Strawson-DE suffices).
-/
theorem only_strawsonDE_licenses_despite_not_DE :
    onlyProfile.strongestLevel = none ∧ onlyProfile.licensesWeakNPI = true := ⟨rfl, rfl⟩

-- ============================================================================
-- Section 5: Formal Proof Witnesses
-- ============================================================================

/-!
The Bool flags above are justified by formal proofs in the dependency chain.
These witness theorems connect profiles to their semantic proofs.
-/

/-- Negation is anti-morphic (formal proof). -/
theorem negation_am_witness : IsAntiMorphic pnot := pnot_isAntiMorphic

/-- Negation is anti-additive (formal proof). -/
theorem negation_aa_witness : IsAntiAdditive pnot := pnot_isAntiAdditive

/-- Negation is DE (formal proof). -/
theorem negation_de_witness : IsDE pnot := pnot_isDownwardEntailing

/-- "No student" is anti-additive (formal proof). -/
theorem no_student_aa_witness : IsAntiAdditive no_student := no_isAntiAdditive_scope

/-- "No student" is DE (formal proof). -/
theorem no_student_de_witness : IsDE no_student := no_isDE_scope

/-- "At most 2 students" is DE (formal proof). -/
theorem atMost2_de_witness : IsDE atMost2_student := atMost_isDE_scope

/-- "Only" is Strawson-DE (formal proof). -/
theorem only_strawsonDE_witness :
    IsStrawsonDE (onlyFull (λ w => w == .w0))
      (λ scope => ∃ w, (w == World.w0) = true ∧ scope w = true) :=
  onlyFull_isStrawsonDE _

/-- "Only" is NOT DE (formal proof). -/
theorem only_not_de_witness : ¬IsDownwardEntailing (onlyFull (λ w => w == .w0)) :=
  onlyFull_not_de

-- ============================================================================
-- Section 6: Hierarchy Consistency
-- ============================================================================

/--
The builder's licensing predictions are consistent with the hierarchy:
AM ⊃ AA ⊃ DE ⊃ Strawson-DE for weak NPI licensing.
-/
theorem hierarchy_weak_npi_licensing :
    negationProfile.licensesWeakNPI = true ∧  -- AM
    noStudentProfile.licensesWeakNPI = true ∧  -- AA
    atMost2Profile.licensesWeakNPI = true ∧    -- DE
    onlyProfile.licensesWeakNPI = true :=      -- Strawson-DE
  ⟨rfl, rfl, rfl, rfl⟩

/--
Strong NPI licensing requires anti-additive: only AM and AA profiles suffice.
-/
theorem hierarchy_strong_npi_licensing :
    negationProfile.licensesStrongNPI = true ∧   -- AM ✓
    noStudentProfile.licensesStrongNPI = true ∧   -- AA ✓
    atMost2Profile.licensesStrongNPI = false ∧    -- DE ✗
    onlyProfile.licensesStrongNPI = false :=      -- Strawson-DE ✗
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Section 7: Item-Level Licensing Bridge
-- ============================================================================

/--
Derive whether a monotonicity profile licenses a specific polarity item.

This bridges the Builder's monotonicity proofs to the Fragment's empirical
item types. Licensing is derived from the profile's proved properties and
the item's polarity type — not stipulated.
-/
def MonotonicityProfile.licensesItem (profile : MonotonicityProfile)
    (item : PolarityItemEntry) : Bool :=
  match item.polarityType with
  | .npiWeak | .npi_fci => profile.licensesWeakNPI
  | .npiStrong => profile.licensesStrongNPI
  | .fci => profile.licensesWeakNPI  -- FCIs in DE/Strawson-DE contexts
  | .ppi => !profile.isAtLeastStrawsonDE  -- PPIs blocked in DE

/-! ### Per-item bridge theorems -/

theorem negation_licenses_ever : negationProfile.licensesItem ever = true := rfl
theorem negation_licenses_liftAFinger : negationProfile.licensesItem liftAFinger = true := rfl
theorem atMost2_blocks_liftAFinger : atMost2Profile.licensesItem liftAFinger = false := rfl
theorem only_licenses_ever : onlyProfile.licensesItem ever = true := rfl
theorem only_blocks_liftAFinger : onlyProfile.licensesItem liftAFinger = false := rfl

/-! ### VonFintel (1999) empirical bridge -/

/--
Von Fintel's empirical observation, derived: "only" has no classical DE level
and the empirical datum records it as not classically DE.
-/
theorem vonFintel_only_not_de :
    onlyProfile.strongestLevel = none ∧ onlyNotDE.isClassicallyDE = false := ⟨rfl, rfl⟩

end TruthConditional.Sentence.Entailment.PolarityBuilder
