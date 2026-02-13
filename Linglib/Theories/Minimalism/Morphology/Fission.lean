import Linglib.Theories.Minimalism.Core.Applicative
import Linglib.Fragments.Spanish.PersonFeatures
import Linglib.Fragments.Spanish.Clitics

/-!
# Fission (Distributed Morphology)

Fission is a postsyntactic operation that splits a single terminal node
into two morphological exponents. This module formalizes the Fission
operation from Muñoz Pérez (2026) that derives stylistic applicatives
in Chilean Spanish.

## The Rule (Muñoz Pérez 2026, ex. 55)

When Appl⁰ in an inchoative context (vGO ∧ vBE) bears [+PART, +SING]:
- Cl₁ gets [+PART, ±AUTHOR, +SING] → surfaces as *me* (1SG) or *te* (2SG)
- Cl₂ gets [+DATIVE] → surfaces as invariable *le*

## References

- Halle, M. & A. Marantz (1993). Distributed Morphology and the
  pieces of inflection. In *The View from Building 20*, 111–176.
- Noyer, R. (1997). *Features, Positions and Affixes in Autonomous
  Morphological Structure*. Garland.
- Muñoz Pérez, C. (2026). Stylistic applicatives. *Glossa* 11(1).
-/

namespace Minimalism.Morphology

open Minimalism
open Fragments.Spanish.PersonFeatures
open Fragments.Spanish.Clitics
open Phenomena.Agreement.PersonMarkingTypology

-- ============================================================================
-- § 1: Morphological Features
-- ============================================================================

/-- Morphological features relevant to clitic Fission. -/
inductive MorphFeature where
  | participant : Bool → MorphFeature  -- [±PART]
  | author : Bool → MorphFeature       -- [±AUTHOR]
  | singular : Bool → MorphFeature     -- [±SING]
  | case_ : CliticCase → MorphFeature  -- Case feature
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Fission Context
-- ============================================================================

/-- The structural context in which Fission applies.
    Fission requires an inchoative structure (vGO ∧ vBE). -/
def fissionContext (heads : List VerbHead) : Bool :=
  isInchoative heads

/-- Person/number condition: Fission applies to [+PART, +SING] only. -/
def fissionPersonCondition (p : PersonCategory) : Bool :=
  fissionApplicable p

-- ============================================================================
-- § 3: Fission Output
-- ============================================================================

/-- The result of Fission: two clitic positions. -/
structure FissionOutput where
  /-- Cl₁: bears person features → me/te -/
  cl1Form : String
  /-- Cl₂: bears case feature → invariable le -/
  cl2Form : String
  deriving Repr, BEq, DecidableEq

/-- Apply Fission to produce two clitics.
    Returns `none` if conditions are not met. -/
def applyFission (p : PersonCategory) (heads : List VerbHead) : Option FissionOutput :=
  if fissionContext heads && fissionPersonCondition p then
    let cl1 := if hasAuthor p then "me" else "te"
    some { cl1Form := cl1, cl2Form := "le" }
  else
    none

-- ============================================================================
-- § 4: PF Marking Condition
-- ============================================================================

/-- Muñoz Pérez (2026, ex. 58): Non-thematic Voice must be overtly
    marked by a reflexive-like element at PF. -/
def anticausativePFSatisfied (clitics : List String) : Bool :=
  -- PF is satisfied if any clitic is homophonous with reflexive
  clitics.any (fun c => c == "se" || c == "me" || c == "te" || c == "nos")

/-- When Fission produces a clitic syncretic with reflexive,
    the PF marking condition is satisfied without overt SE. -/
def fissionSatisfiesPF (p : PersonCategory) (heads : List VerbHead) : Bool :=
  match applyFission p heads with
  | some output => anticausativePFSatisfied [output.cl1Form]
  | none => false

-- ============================================================================
-- § 5: Verification Theorems
-- ============================================================================

/-- Fission applies to 1SG in inchoative context. -/
theorem fission_1sg_inchoative :
    applyFission .s1 [.vGO, .vBE] = some { cl1Form := "me", cl2Form := "le" } := by
  native_decide

/-- Fission applies to 2SG in inchoative context. -/
theorem fission_2sg_inchoative :
    applyFission .s2 [.vGO, .vBE] = some { cl1Form := "te", cl2Form := "le" } := by
  native_decide

/-- Fission does NOT apply to 3SG (not [+PART]). -/
theorem fission_blocked_3sg :
    applyFission .s3 [.vGO, .vBE] = none := by native_decide

/-- Fission does NOT apply in non-inchoative context (activity). -/
theorem fission_blocked_activity :
    applyFission .s1 [.vDO] = none := by native_decide

/-- Fission does NOT apply in causative context (has vDO). -/
theorem fission_blocked_causative :
    applyFission .s1 [.vDO, .vGO, .vBE] = none := by native_decide

/-- 1SG Fission output satisfies PF condition (me is syncretic with reflexive). -/
theorem fission_1sg_satisfies_pf :
    fissionSatisfiesPF .s1 [.vGO, .vBE] = true := by native_decide

/-- 2SG Fission output satisfies PF condition (te is syncretic with reflexive). -/
theorem fission_2sg_satisfies_pf :
    fissionSatisfiesPF .s2 [.vGO, .vBE] = true := by native_decide

/-- Cl₂ is always invariable "le". -/
theorem cl2_invariable_1sg :
    (applyFission .s1 [.vGO, .vBE]).map (·.cl2Form) = some "le" := by native_decide

theorem cl2_invariable_2sg :
    (applyFission .s2 [.vGO, .vBE]).map (·.cl2Form) = some "le" := by native_decide

/-- 1SG Cl₁ is "me" (reflects [+AUTHOR]). -/
theorem cl1_1sg_is_me :
    (applyFission .s1 [.vGO, .vBE]).map (·.cl1Form) = some "me" := by native_decide

/-- 2SG Cl₁ is "te" (reflects [-AUTHOR]). -/
theorem cl1_2sg_is_te :
    (applyFission .s2 [.vGO, .vBE]).map (·.cl1Form) = some "te" := by native_decide

end Minimalism.Morphology
