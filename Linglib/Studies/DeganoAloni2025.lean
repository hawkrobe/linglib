import Linglib.Syntax.Pronoun.IndefiniteParadigm

/-!
# Degano & Aloni 2025: 7-type team-semantic typology of indefinites
[degano-aloni-2025] [hodges-1997] [vaananen-2007]

Degano & Aloni 2025's 7-type classification of indefinite pronouns,
projected from the consensus `Indefinite.IndefinitePronoun`
substrate (Haspelmath 1997 function-coverage data).

The team-semantic logic primitives D&A use (Hodges 1997 / Väänänen 2007:
assignment teams, `variation`, `constancy`) are inlined here as a
private namespace prelude — they currently have only one downstream
linguistic consumer (this file + Bubnov 2026), so general placement in
`Core/Logic/` would be premature. When a second framework (branching
quantifiers, IF-logic for definites, partial-information ellipsis)
needs them, extract.

## D&A's classification ↔ Haspelmath's map

D&A's typology operates on the **SK/SU/NS triangle**:
- **SK** = specific known: speaker has a particular referent in mind, hearer can identify
- **SU** = specific unknown: speaker has a referent in mind, hearer cannot
- **NS** = non-specific: no particular referent

These map 1:1 to Haspelmath 1997's first three slots:
- D&A SK ↔ Haspelmath `specificKnown`
- D&A SU ↔ Haspelmath `specificUnknown`
- D&A NS ↔ Haspelmath `irrealis` (D&A focus on irrealis-modal non-specific uses;
  Haspelmath's `irrealis` slot is broader but D&A treat it as the canonical
  NS-bearing region — see D&A 2025 §2)

The `DAType.profile` function below uses the Haspelmath identifiers because
that's the substrate the projection consumes; the D&A column heading in the
type table is for reference.

## Schema

- `DAType`: the 7 types arising from Boolean combinations of `var(y,x)`
  and `dep(y,x)` with within-world (`v`) and across-all-worlds (`∅`)
  parameter choices.
- `DAType.profile`: each type's theoretical coverage on the
  Haspelmath SK/SU/irrealis triangle.
- `IndefinitePronoun.surfaceDAType`: classify an entry by exact match
  of its actual function-coverage to a D&A type's profile. Returns
  `none` when the entry covers a region D&A doesn't subdivide (e.g.,
  free choice, polarity-sensitive forms) or when actual ⊊ profile.
- `IndefinitePronoun.consistentWith`: weaker relation — actual coverage
  is a subset of the theoretical profile. Used for entries where
  paradigmatic competition narrows the actual distribution
  (e.g., Russian *kto-to* ⊊ type-iv epistemic profile).

## Type table (D&A's row labels; Haspelmath identifiers in `profile`)

| Type | Requirement       | D&A profile (SK/SU/NS) | Example          |
|------|-------------------|------------------------|------------------|
| (i)   | (none)           | {SK, SU, NS}          | English *some-* |
| (ii)  | dep(v,x)         | {SK, SU}              | Yakut *kim ere* |
| (iii) | var(v,x)         | {NS}                  | Russian *-nibud'*|
| (iv)  | var(∅,x)         | {SU, NS}              | German *irgend-*|
| (v)   | dep(∅,x)         | {SK}                  | Russian *koe-*  |
| (vi)  | dep(∅,x)∧var(v,x)| {SK, NS}              | *unattested*    |
| (vii) | dep(v,x)∧var(∅,x)| {SU}                  | Kannada *yāru-oo*|
-/

set_option autoImplicit false

-- ============================================================================
-- §0. Private prelude: Hodges/Väänänen team-semantic primitives
-- [hodges-1997] [vaananen-2007]
-- ============================================================================
-- Inlined here pending a second consumer (currently only D&A 2025 + Bubnov 2026
-- use these primitives). Promotion to `Core/Logic/DependenceLogic.lean` would
-- create substrate without independent consumers, the anti-pattern noted in
-- memory `project_pmf_check_mathlib_first.md`.

namespace DeganoAloni2025.DependenceLogic

/-- An assignment team: a list of variable-to-entity assignments.
    The setting for dependence logic ([vaananen-2007]) and D&A's
    indefinite semantics. -/
abbrev AssignmentTeam (V E : Type) := List (V → E)

/-- **Variation**: variable `x` varies w.r.t. parameter `y` in team `t`.
    `var(y, x)` holds iff there exist two assignments in `t` that agree on `y`
    but disagree on `x`. -/
def variation {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (y x : V) : Bool :=
  t.any λ a₁ => t.any λ a₂ => a₁ y == a₂ y && a₁ x != a₂ x

/-- **Constancy** (functional dependence): `x` depends on `y` in team `t`.
    `dep(y, x)` holds iff all assignments agreeing on `y` also agree on `x`. -/
def constancy {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (y x : V) : Bool :=
  t.all λ a₁ => t.all λ a₂ => a₁ y != a₂ y || a₁ x == a₂ x

/-- Concrete witness: a 2-assignment team where `var(y,x)` holds and `dep(y,x)` fails. -/
theorem constancy_excludes_variation_witness :
    let t : AssignmentTeam (Fin 2) (Fin 2) :=
      [λ v => if v = 0 then 0 else 0,
       λ v => if v = 0 then 0 else 1]
    variation t 0 1 = true ∧ constancy t 0 1 = false := by decide

/-- Constancy and variation are jointly unsatisfiable. -/
theorem constancy_excludes_variation {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (y x : V)
    (hdep : constancy t y x = true)
    (hvar : variation t y x = true) : False := by
  unfold constancy at hdep
  unfold variation at hvar
  simp only [List.all_eq_true, List.any_eq_true,
             Bool.and_eq_true, Bool.or_eq_true,
             bne_iff_ne, ne_eq, beq_iff_eq] at hdep hvar
  obtain ⟨a₁, ha₁, a₂, ha₂, hyeq, hxne⟩ := hvar
  have := hdep a₁ ha₁ a₂ ha₂
  rcases this with hyneq | hxeq
  · exact hyneq hyeq
  · exact hxne hxeq

/-- Variation lifts to a coarser parameter: if `v`-agreement implies `y`-agreement,
    then `var(v, x) → var(y, x)`. Grounds D&A's diachronic prediction
    `var(v, x) → var(∅, x)` (see [bubnov-2026] §6). -/
theorem variation_monotone {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (v y x : V)
    (hvar : variation t v x = true)
    (h_agree : ∀ (a₁ a₂ : V → E), a₁ v = a₂ v → a₁ y = a₂ y) :
    variation t y x = true := by
  unfold variation at hvar ⊢
  simp only [List.any_eq_true, Bool.and_eq_true,
             bne_iff_ne, ne_eq, beq_iff_eq] at hvar ⊢
  obtain ⟨a₁, ha₁, a₂, ha₂, hveq, hxne⟩ := hvar
  exact ⟨a₁, ha₁, a₂, ha₂, h_agree a₁ a₂ hveq, hxne⟩

end DeganoAloni2025.DependenceLogic

-- ============================================================================
-- §1. The 7-type classification
-- ============================================================================

namespace DeganoAloni2025

open Indefinite

/-- [degano-aloni-2025]'s seven-type team-semantic typology. -/
inductive DAType where
  /-- (i) No restriction. Profile: SK ∪ SU ∪ NS. -/
  | unmarked
  /-- (ii) `dep(v,x)`: constancy within each epistemic world. Profile: SK + SU. -/
  | specific
  /-- (iii) `var(v,x)`: variation within some epistemic world. Profile: NS only. -/
  | nonSpecific
  /-- (iv) `var(∅,x)`: variation across all epistemic worlds. Profile: SU + NS. -/
  | epistemic
  /-- (v) `dep(∅,x)`: constancy across all epistemic worlds. Profile: SK only. -/
  | specificKnown
  /-- (vi) `dep(∅,x) ∧ var(v,x)`: jointly forbidden by team-semantic
      logic AND empirically unattested in D&A's surveyed languages.
      The two failure modes are independent: even if some non-team-semantic
      account licensed it, the {SK, NS} profile would still need a witness. -/
  | skPlusNS
  /-- (vii) `dep(v,x) ∧ var(∅,x)`: rare conjunctive type; profile SU only. -/
  | specificUnknown
  deriving DecidableEq, Repr, BEq

/-- D&A theoretical profile: the SK/SU/NS subset of Haspelmath functions
    a type's semantics PERMITS. Actual paradigm distribution may be
    narrower due to competition with more-specific forms. -/
def DAType.profile : DAType → Finset HaspelmathFunction
  | .unmarked        => {.specificKnown, .specificUnknown, .irrealis}
  | .specific        => {.specificKnown, .specificUnknown}
  | .nonSpecific     => {.irrealis}
  | .epistemic       => {.specificUnknown, .irrealis}
  | .specificKnown   => {.specificKnown}
  | .skPlusNS        => {.specificKnown, .irrealis}
  | .specificUnknown => {.specificUnknown}

/-- Type (vi) `skPlusNS` is jointly forbidden by team-semantic logic AND
    empirically unattested. The team-semantic argument: `dep(∅,x)` forbids
    cross-world variation while `var(v,x)` requires intra-world variation.
    The empirical argument is independent: D&A find no surveyed language
    with a form whose distribution exactly matches the `{SK, NS}` profile.
    Both arguments must hold; the predicate marks attestation, not logical
    consistency. -/
def DAType.IsAttested (t : DAType) : Prop := t ≠ .skPlusNS

instance : DecidablePred DAType.IsAttested :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

theorem skPlusNS_unattested : ¬ DAType.IsAttested .skPlusNS := by decide

-- ----------------------------------------------------------------------------
-- Projection-range characterization
-- ----------------------------------------------------------------------------

/-- The Haspelmath functions that D&A's `profile` projection ranges over:
    the **specificity triangle** (specificKnown, specificUnknown, irrealis).
    D&A's typology is built around the SK/SU/NS dimension; D&A's `irrealis`
    slot identifies with Haspelmath's `irrealis` (see the module docstring's
    "D&A ↔ Haspelmath" section). -/
def specificityRegion : Finset HaspelmathFunction :=
  {.specificKnown, .specificUnknown, .irrealis}

/-- **Projection range, not framework scope.** Every D&A type's `profile` is
    a subset of `specificityRegion`. This is a structural fact about the
    *projection function* `DAType.profile`, not a claim about the empirical
    reach of D&A 2025's framework: D&A's account empirically covers
    polarity-sensitive uses of indefinites (e.g., German *irgendein* under
    modals) through composition mechanisms that are not captured by the
    direct `profile` projection. The theorem says only that the *range* of
    `profile` lies in the specificity region; what each type *predicts in
    composition* is a separate question.

    See the audit notes in `0.230.529`'s CHANGELOG entry on why the
    symmetric Chierchia-side scope theorem fails: Chierchia's
    `PSIProfile.predictedFunctions` for plain indefinites
    (`obligatoryDomainAlts := false`) ranges over `{SK, SU, irrealis}` too,
    so the would-be "disjoint scope" picture collapses. The structural
    pattern only survives on the D&A side. -/
theorem DAType.profile_subset_specificityRegion (t : DAType) :
    t.profile ⊆ specificityRegion := by
  cases t <;> decide

end DeganoAloni2025

-- ============================================================================
-- §2. IndefinitePronoun projections
-- ============================================================================

/- Methods on `IndefinitePronoun` live in its own namespace so that
   dot notation (`entry.surfaceDAType`) resolves them. -/
namespace Indefinite.IndefinitePronoun

open DeganoAloni2025

/-- Surface-classifier: project an entry to the D&A type whose theoretical
    profile exactly matches the entry's actual function-coverage.

    Returns `none` when the entry covers a region D&A doesn't subdivide
    (free choice, polarity-sensitive uses, or any function outside
    SK/SU/NS) or when actual coverage is a proper subset of any type's
    profile (a paradigmatic-competition case — see `consistentWith`). -/
def surfaceDAType (e : IndefinitePronoun) : Option DAType :=
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
    *-nibud'* blocks it from NS — see [bubnov-2026] §7). -/
def consistentWith (e : IndefinitePronoun) (t : DAType) : Bool :=
  decide (e.functions ⊆ t.profile)

end Indefinite.IndefinitePronoun
