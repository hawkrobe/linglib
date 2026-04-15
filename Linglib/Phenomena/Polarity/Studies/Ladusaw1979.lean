import Linglib.Core.Logic.Quantification
import Linglib.Theories.Semantics.Quantification.Quantifier
import Linglib.Phenomena.Polarity.NPIs

/-!
# Ladusaw (1979): Polarity Sensitivity as Inherent Scope Relations
@cite{ladusaw-1979}

Ladusaw's dissertation established the foundational generalization connecting
NPI licensing to downward entailingness (DE). The core claim:

> Weak NPIs are licensed in downward-entailing contexts.

This file bridges the GQ monotonicity proofs from `Core.Quantification` and
`Semantics.Quantification.Quantifier` to the NPI licensing data in
`Phenomena.Polarity.NPIs`, making the DE ↔ NPI connection formally explicit.

## Key connections

1. **Scope DE → weak NPI licensing**: `ScopeDownwardMono` licenses weak NPIs
   in the scope of a quantifier (e.g., "No student saw anyone").
2. **Restrictor DE → weak NPI licensing**: `RestrictorDownwardMono` licenses
   weak NPIs in the restrictor (e.g., "Everyone who saw anyone was questioned").
3. **Left anti-additivity → strong NPI licensing**: `LeftAntiAdditive`
   licenses strong NPIs (e.g., "Nobody lifted a finger").
   Mere DE ("few") is insufficient for strong NPIs.
-/

namespace Phenomena.Polarity.Studies.Ladusaw1979

open Core.Quantification
open Phenomena.Polarity.NPIs (LicensingContext)
open Core.IntensionalLogic
open Semantics.Montague (toyModel ToyEntity)
open Semantics.Quantification.Quantifier

-- ============================================================================
-- §1. Monotonicity classification of licensing contexts
-- ============================================================================

/-- The monotonicity-based licensing strength of a context.
    @cite{ladusaw-1979}: DE licenses weak NPIs.
    @cite{zwarts-1998}: anti-additive licenses strong NPIs. -/
inductive LicensingStrength where
  | antiAdditive  -- licenses both weak and strong NPIs
  | downwardEntailing  -- licenses only weak NPIs
  | nonDE  -- does not license NPIs by monotonicity
  deriving DecidableEq, Repr

/-- Classify NPI licensing contexts by their monotonicity-based strength.
    Anti-additive contexts (negation, "without", "no one", universal restrictor) license strong NPIs.
    Merely DE contexts ("few", conditionals) license only weak NPIs.
    Non-DE contexts (questions, superlatives) license NPIs via other mechanisms. -/
def licensingStrength : LicensingContext → LicensingStrength
  | .sententialNegation  => .antiAdditive
  | .constituentNegation => .antiAdditive
  | .withoutClause       => .antiAdditive
  | .denyVerb            => .antiAdditive
  | .universalRestrictor => .antiAdditive  -- P&W Prop 13: every/no are LAA
  | .fewNP               => .downwardEntailing
  | .beforeClause        => .downwardEntailing
  | .comparativeThan     => .downwardEntailing
  | .tooAdjective        => .downwardEntailing
  | .conditional         => .downwardEntailing
  | .onlyFocus           => .downwardEntailing
  | .doubtVerb           => .downwardEntailing
  | .adversative         => .downwardEntailing  -- Strawson-DE
  | .question            => .nonDE
  | .superlative         => .nonDE

-- ============================================================================
-- §2. GQ monotonicity → NPI licensing (the Ladusaw bridge)
-- ============================================================================

variable {m : Frame} [Fintype m.Entity] [DecidableEq m.Entity]

/-- The core Ladusaw generalization: scope-DE quantifiers license weak NPIs
    in their scope. Formally: `PScopeDownwardMono q` implies that the scope
    of `q` is a weak-NPI-licensing environment.

    Verified instances:
    - `no_scope_down`: "No student saw anyone" ✓
    - `few_scope_down`: "Few students saw anyone" ✓ -/
structure ScopeDELicensesWeakNPIs (q : m.Denot Ty.det) where
  scopeDE : PScopeDownwardMono q
  /-- The licensing context this corresponds to -/
  context : LicensingContext
  /-- The context is classified as at least DE -/
  isDE : licensingStrength context = .downwardEntailing ∨
         licensingStrength context = .antiAdditive

/-- "No" licenses weak NPIs in scope via scope-↓ monotonicity. -/
def no_scope_licenses_weak :
    ScopeDELicensesWeakNPIs (no_sem m) :=
  { scopeDE := no_scope_down
  , context := .constituentNegation
  , isDE := Or.inr rfl }

/-- "Few" licenses weak NPIs in scope via scope-↓ monotonicity. -/
def few_scope_licenses_weak :
    ScopeDELicensesWeakNPIs (few_sem m) :=
  { scopeDE := few_scope_down
  , context := .fewNP
  , isDE := Or.inl rfl }

/-- The restrictor Ladusaw generalization: restrictor-DE quantifiers license
    weak NPIs in their restrictor.

    Verified instances:
    - `every_restrictor_down`: "Everyone who saw anyone was questioned" ✓
    - `no_restrictor_down`: "No one who saw anyone was questioned" ✓ -/
structure RestrictorDELicensesWeakNPIs (q : m.Denot Ty.det) where
  restrictorDE : PRestrictorDownwardMono q
  context : LicensingContext
  isDE : licensingStrength context = .downwardEntailing ∨
         licensingStrength context = .antiAdditive

/-- "Every" licenses weak NPIs in restrictor via restrictor-↓ monotonicity. -/
def every_restrictor_licenses_weak :
    RestrictorDELicensesWeakNPIs (every_sem m) :=
  { restrictorDE := every_restrictor_down
  , context := .universalRestrictor
  , isDE := Or.inr rfl }

/-- "No" licenses weak NPIs in restrictor via restrictor-↓ monotonicity. -/
def no_restrictor_licenses_weak :
    RestrictorDELicensesWeakNPIs (no_sem m) :=
  { restrictorDE := no_restrictor_down
  , context := .constituentNegation
  , isDE := Or.inr rfl }

-- ============================================================================
-- §3. Anti-additivity → strong NPI licensing
-- ============================================================================

/-- @cite{zwarts-1998}: anti-additive contexts license strong NPIs.
    `LeftAntiAdditive q` means the restrictor of `q` is anti-additive,
    licensing strong NPIs like "lift a finger" and "in years".

    Verified instances:
    - `every_laa`: "Everyone who ever lifted a finger..." ✓
    - `no_laa`: "Nobody lifted a finger" ✓

    Counter-example: "few" is merely DE, not anti-additive:
    - *"Few people lifted a finger to help" ✗ -/
structure AntiAddLicensesStrongNPIs (q : m.Denot Ty.det) where
  laa : PLeftAntiAdditive q
  context : LicensingContext
  isAA : licensingStrength context = .antiAdditive

/-- "Every" is left-anti-additive → licenses strong NPIs in restrictor.
    P&W Prop 13: the restrictor of "every" is anti-additive (not just DE). -/
def every_laa_licenses_strong :
    AntiAddLicensesStrongNPIs (every_sem m) :=
  { laa := every_laa
  , context := .universalRestrictor
  , isAA := rfl }

/-- "No" is left-anti-additive → licenses strong NPIs in restrictor. -/
def no_laa_licenses_strong :
    AntiAddLicensesStrongNPIs (no_sem m) :=
  { laa := no_laa
  , context := .constituentNegation
  , isAA := rfl }

/-- Scope-level anti-additivity also licenses strong NPIs.
    `RightAntiAdditive q` means the scope of `q` is anti-additive.
    "Nobody lifted a finger" is licensed by scope-level AA of `no`. -/
structure ScopeAALicensesStrongNPIs (q : m.Denot Ty.det) where
  raa : PRightAntiAdditive q
  context : LicensingContext
  isAA : licensingStrength context = .antiAdditive

/-- "No" is right-anti-additive → licenses strong NPIs in scope.
    "Nobody lifted a finger" / "Nobody saw anyone". -/
def no_raa_licenses_strong :
    ScopeAALicensesStrongNPIs (no_sem m) :=
  { raa := no_raa
  , context := .constituentNegation
  , isAA := rfl }

-- ============================================================================
-- §4. Verification against NPI data
-- ============================================================================

/- The DE classification predicts NPI data: all DE contexts license weak NPIs,
   and only anti-additive contexts license strong NPIs.

   Cross-reference with `Phenomena.Polarity.NPIs`:
   - `anyUniversal`: "Everyone who saw anyone" — restrictor DE ✓
   - `anyFew`: "Few students saw anyone" — scope DE ✓
   - `liftFingerFew`: "*Few people lifted a finger" — scope DE but not AA ✗
   - `liftFingerWithout`: "without lifting a finger" — AA ✓
   - `liftFingerNegation`: "didn't lift a finger" — AA ✓ -/

set_option maxHeartbeats 400000 in
/-- "Few" is DE but NOT right-anti-additive in scope:
    `few(R, S∨S') ≠ few(R,S) ∧ few(R,S')` in general.
    This is why *"Few people lifted a finger" is bad — strong NPIs need AA.

    Counterexample: R = {john, mary, pizza}, S = {john}, S' = {mary}.
    - few(R, S∨S') = (2 < 1) = false
    - few(R, S) = (1 < 2) = true, few(R, S') = (1 < 2) = true
    - true ∧ true ≠ false -/
theorem few_DE_not_RAA :
    PScopeDownwardMono (few_sem (F := toyModel)) ∧
    ¬PRightAntiAdditive (few_sem (F := toyModel)) := by
  refine ⟨few_scope_down, fun h => ?_⟩
  -- Witness: R = not-book, S = john-only, S' = mary-only
  let R : ToyEntity → Prop := fun | .book => False | _ => True
  let S : ToyEntity → Prop := fun | .john => True | _ => False
  let S' : ToyEntity → Prop := fun | .mary => True | _ => False
  -- The ← direction of the ↔ gives us few(R, S∨S') from few(R,S) ∧ few(R,S')
  have hback := (h R S S').mpr
  -- few(R, S∨S') implies |R∩(S∨S')| < |R\(S∨S')|, i.e. 2 < 1, contradiction
  -- First establish few(R,S) ∧ few(R,S'), i.e. |R∩S|<|R\S| and |R∩S'|<|R\S'|
  -- TODO: noncomputable count prevents native_decide; manual proof needed
  sorry

/-- The Ladusaw hierarchy: AA ⊂ DE ⊂ NV (nonveridical).
    Strong NPIs need AA; weak NPIs need DE; "any" in questions needs NV.
    "Few" is DE but not AA, explaining the licensing contrast:
    ✓ "Few students saw anyone" (weak NPI in DE) vs
    ✗ "*Few people lifted a finger" (strong NPI needs AA). -/
theorem ladusaw_hierarchy :
    (licensingStrength .sententialNegation = .antiAdditive) ∧
    (licensingStrength .fewNP = .downwardEntailing) ∧
    (licensingStrength .question = .nonDE) := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §5. Connecting NPIDatum to monotonicity predictions
-- ============================================================================

/-- Prediction: all NPI licensing contexts classified as DE or AA
    should produce grammatical NPI sentences. This is verified
    by the `anyData` checks in `NPIs.lean` (#guard at line 695-696). -/
theorem de_contexts_license_weak_npis :
    licensingStrength .universalRestrictor ≠ .nonDE ∧
    licensingStrength .fewNP ≠ .nonDE ∧
    licensingStrength .sententialNegation ≠ .nonDE ∧
    licensingStrength .constituentNegation ≠ .nonDE ∧
    licensingStrength .withoutClause ≠ .nonDE ∧
    licensingStrength .beforeClause ≠ .nonDE ∧
    licensingStrength .conditional ≠ .nonDE := by decide

/-- Strong NPI prediction: only AA contexts license strong NPIs.
    "Few" (merely DE) does not license "lift a finger". -/
theorem strong_npi_requires_aa :
    licensingStrength .sententialNegation = .antiAdditive ∧
    licensingStrength .withoutClause = .antiAdditive ∧
    licensingStrength .fewNP ≠ .antiAdditive := by decide

end Phenomena.Polarity.Studies.Ladusaw1979
