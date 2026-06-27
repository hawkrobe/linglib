import Linglib.Semantics.Polarity.Item
import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Fragments.English.Toy

/-!
# Ladusaw (1979): Polarity Sensitivity as Inherent Scope Relations
[ladusaw-1979]

Ladusaw's dissertation established the foundational generalization connecting
NPI licensing to downward entailingness (DE). The core claim:

> Weak NPIs are licensed in downward-entailing contexts.

This file bridges the GQ monotonicity proofs from `Quantification` and
`Quantification.Quantifier` to the NPI licensing classification
indexed by `Semantics.Polarity.LicensingContext`, making the DE ↔ NPI
connection formally explicit.

## Key connections

1. **Scope DE → weak NPI licensing**: `ScopeDownwardMono` licenses weak NPIs
   in the scope of a quantifier (e.g., "No student saw anyone").
2. **Restrictor DE → weak NPI licensing**: `RestrictorDownwardMono` licenses
   weak NPIs in the restrictor (e.g., "Everyone who saw anyone was questioned").
3. **Left anti-additivity → strong NPI licensing**: `LeftAntiAdditive`
   licenses strong NPIs (e.g., "Nobody lifted a finger").
   Mere DE ("few") is insufficient for strong NPIs.
-/

namespace Ladusaw1979

open Quantification
open Semantics.Polarity (LicensingContext)
open Intensional
open Semantics.Montague (ToyEntity)

-- ============================================================================
-- §1. Monotonicity classification of licensing contexts
-- ============================================================================

/-- The monotonicity-based licensing strength of a context.
    [ladusaw-1979]: DE licenses weak NPIs.
    [zwarts-1998]: anti-additive licenses strong NPIs.

    A coarsening of `NaturalLogic.DEStrength` that collapses the
    `.antiMorphic` and `.antiAdditive` cases (Ladusaw treats them
    identically: both license strong NPIs). -/
inductive LicensingStrength where
  | antiAdditive  -- licenses both weak and strong NPIs (incl. anti-morphic)
  | downwardEntailing  -- licenses only weak NPIs
  | nonDE  -- does not license NPIs by monotonicity
  deriving DecidableEq, Repr

/-- Coarsen a `DEStrength` to Ladusaw's three-way classification. -/
def LicensingStrength.ofDEStrength : Option NaturalLogic.DEStrength → LicensingStrength
  | some .antiMorphic | some .antiAdditive => .antiAdditive
  | some .weak                              => .downwardEntailing
  | none                                    => .nonDE

/-- Classify NPI licensing contexts by their monotonicity-based strength,
    derived from `Semantics.Polarity.Licensing.contextProperties`. The Ladusaw
    classification is a coarsening of the Icard signature lattice. -/
def licensingStrength (c : LicensingContext) : LicensingStrength :=
  LicensingStrength.ofDEStrength
    (Semantics.Polarity.Licensing.contextProperties c).strawsonSignature.toDEStrength

-- ============================================================================
-- §2. GQ monotonicity → NPI licensing (the Ladusaw bridge)
-- ============================================================================

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The core Ladusaw generalization: scope-DE quantifiers license weak NPIs
    in their scope. Formally: `ScopeDownwardMono q` implies that the scope
    of `q` is a weak-NPI-licensing environment.

    Verified instances:
    - `no_scope_down`: "No student saw anyone" ✓
    - `few_scope_down`: "Few students saw anyone" ✓ -/
structure ScopeDELicensesWeakNPIs (q : Quantification.GQ α) where
  scopeDE : ScopeDownwardMono q
  /-- The licensing context this corresponds to -/
  context : LicensingContext
  /-- The context is classified as at least DE -/
  isDE : licensingStrength context = .downwardEntailing ∨
         licensingStrength context = .antiAdditive

/-- "No" licenses weak NPIs in scope via scope-↓ monotonicity. -/
def no_scope_licenses_weak :
    ScopeDELicensesWeakNPIs (no_sem (α := α)) :=
  { scopeDE := no_scope_down
  , context := .nobody
  , isDE := Or.inr rfl }

/-- "Few" licenses weak NPIs in scope via scope-↓ monotonicity. -/
def few_scope_licenses_weak :
    ScopeDELicensesWeakNPIs (few_sem (α := α)) :=
  { scopeDE := few_scope_down
  , context := .few
  , isDE := Or.inl rfl }

/-- The restrictor Ladusaw generalization: restrictor-DE quantifiers license
    weak NPIs in their restrictor.

    Verified instances:
    - `every_restrictor_down`: "Everyone who saw anyone was questioned" ✓
    - `no_restrictor_down`: "No one who saw anyone was questioned" ✓ -/
structure RestrictorDELicensesWeakNPIs (q : Quantification.GQ α) where
  restrictorDE : RestrictorDownwardMono q
  context : LicensingContext
  isDE : licensingStrength context = .downwardEntailing ∨
         licensingStrength context = .antiAdditive

/-- "Every" licenses weak NPIs in restrictor via restrictor-↓ monotonicity. -/
def every_restrictor_licenses_weak :
    RestrictorDELicensesWeakNPIs (every_sem (α := α)) :=
  { restrictorDE := every_restrictor_down
  , context := .universalRestrictor
  , isDE := Or.inr rfl }

/-- "No" licenses weak NPIs in restrictor via restrictor-↓ monotonicity. -/
def no_restrictor_licenses_weak :
    RestrictorDELicensesWeakNPIs (no_sem (α := α)) :=
  { restrictorDE := no_restrictor_down
  , context := .nobody
  , isDE := Or.inr rfl }

-- ============================================================================
-- §3. Anti-additivity → strong NPI licensing
-- ============================================================================

/-- [zwarts-1998]: anti-additive contexts license strong NPIs.
    `LeftAntiAdditive q` means the restrictor of `q` is anti-additive,
    licensing strong NPIs like "lift a finger" and "in years".

    Verified instances:
    - `every_laa`: "Everyone who ever lifted a finger..." ✓
    - `no_laa`: "Nobody lifted a finger" ✓

    Counter-example: "few" is merely DE, not anti-additive:
    - *"Few people lifted a finger to help" ✗ -/
structure AntiAddLicensesStrongNPIs (q : Quantification.GQ α) where
  laa : LeftAntiAdditive q
  context : LicensingContext
  isAA : licensingStrength context = .antiAdditive

/-- "Every" is left-anti-additive → licenses strong NPIs in restrictor.
    P&W Prop 13: the restrictor of "every" is anti-additive (not just DE). -/
def every_laa_licenses_strong :
    AntiAddLicensesStrongNPIs (every_sem (α := α)) :=
  { laa := every_laa
  , context := .universalRestrictor
  , isAA := rfl }

/-- "No" is left-anti-additive → licenses strong NPIs in restrictor. -/
def no_laa_licenses_strong :
    AntiAddLicensesStrongNPIs (no_sem (α := α)) :=
  { laa := no_laa
  , context := .nobody
  , isAA := rfl }

/-- Scope-level anti-additivity also licenses strong NPIs.
    `RightAntiAdditive q` means the scope of `q` is anti-additive.
    "Nobody lifted a finger" is licensed by scope-level AA of `no`. -/
structure ScopeAALicensesStrongNPIs (q : Quantification.GQ α) where
  raa : RightAntiAdditive q
  context : LicensingContext
  isAA : licensingStrength context = .antiAdditive

/-- "No" is right-anti-additive → licenses strong NPIs in scope.
    "Nobody lifted a finger" / "Nobody saw anyone". -/
def no_raa_licenses_strong :
    ScopeAALicensesStrongNPIs (no_sem (α := α)) :=
  { raa := no_raa
  , context := .nobody
  , isAA := rfl }

-- ============================================================================
-- §4. Verification against NPI data
-- ============================================================================

/- The DE classification predicts NPI data: all DE contexts license weak NPIs,
   and only anti-additive contexts license strong NPIs.

   Illustrative examples:
   - "Everyone who saw anyone" — restrictor DE ✓
   - "Few students saw anyone" — scope DE ✓
   - "*Few people lifted a finger" — scope DE but not AA ✗
   - "without lifting a finger" — AA ✓
   - "didn't lift a finger" — AA ✓ -/

set_option maxHeartbeats 400000 in
/-- "Few" is DE but NOT right-anti-additive in scope:
    `few(R, S∨S') ≠ few(R,S) ∧ few(R,S')` in general.
    This is why *"Few people lifted a finger" is bad — strong NPIs need AA.

    Counterexample: R = {john, mary, pizza}, S = {john}, S' = {mary}.
    - few(R, S∨S') = (2 < 1) = false
    - few(R, S) = (1 < 2) = true, few(R, S') = (1 < 2) = true
    - true ∧ true ≠ false -/
theorem few_DE_not_RAA :
    ScopeDownwardMono (few_sem (α := ToyEntity)) ∧
    ¬RightAntiAdditive (few_sem (α := ToyEntity)) := by
  refine ⟨few_scope_down, fun h => ?_⟩
  -- Witness: R = not-book, S = john-only, S' = mary-only
  let R : ToyEntity → Prop := fun | .book => False | _ => True
  let S : ToyEntity → Prop := fun | .john => True | _ => False
  let S' : ToyEntity → Prop := fun | .mary => True | _ => False
  -- The ← direction of the ↔ gives us few(R, S∨S') from few(R,S) ∧ few(R,S')
  have hback := (h R S S').mpr
  -- few(R, S∨S') implies |R∩(S∨S')| < |R\(S∨S')|, i.e. 2 < 1, contradiction
  -- First establish few(R,S) ∧ few(R,S'), i.e. |R∩S|<|R\S| and |R∩S'|<|R\S'|
  -- TODO: noncomputable count prevents decide; manual proof needed
  sorry

/-- The Ladusaw hierarchy: AA ⊂ DE ⊂ NV (nonveridical).
    Strong NPIs need AA; weak NPIs need DE; "any" in questions needs NV.
    "Few" is DE but not AA, explaining the licensing contrast:
    ✓ "Few students saw anyone" (weak NPI in DE) vs
    ✗ "*Few people lifted a finger" (strong NPI needs AA). -/
theorem ladusaw_hierarchy :
    (licensingStrength .negation = .antiAdditive) ∧
    (licensingStrength .few = .downwardEntailing) ∧
    (licensingStrength .question = .nonDE) := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §5. Connecting NPIDatum to monotonicity predictions
-- ============================================================================

/-- Prediction: all NPI licensing contexts classified as DE or AA
    should produce grammatical NPI sentences. -/
theorem de_contexts_license_weak_npis :
    licensingStrength .universalRestrictor ≠ .nonDE ∧
    licensingStrength .few ≠ .nonDE ∧
    licensingStrength .negation ≠ .nonDE ∧
    licensingStrength .nobody ≠ .nonDE ∧
    licensingStrength .withoutClause ≠ .nonDE ∧
    licensingStrength .beforeClause ≠ .nonDE ∧
    licensingStrength .conditionalAntecedent ≠ .nonDE := by decide

/-- Strong NPI prediction: only AA contexts license strong NPIs.
    "Few" (merely DE) does not license "lift a finger". -/
theorem strong_npi_requires_aa :
    licensingStrength .negation = .antiAdditive ∧
    licensingStrength .withoutClause = .antiAdditive ∧
    licensingStrength .few ≠ .antiAdditive := by decide

end Ladusaw1979
