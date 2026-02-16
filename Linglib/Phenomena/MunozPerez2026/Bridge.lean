import Linglib.Phenomena.MunozPerez2026.Data
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Morphology.Fission
import Linglib.Fragments.Spanish.PersonFeatures
import Linglib.Fragments.Spanish.Predicates
import Linglib.Fragments.Spanish.Clitics

/-!
# Muñoz Pérez (2026) — Bridge Theorems

Derives the paper's empirical predictions by connecting the generic
Fission framework (Theory) to the Spanish clitic and verb data (Fragment).

The Spanish Fission rule is instantiated *here*, not in the Fragment,
because Fission is a Minimalist/DM operation — Fragments stay theory-neutral.

## Predictions Derived

1. **Person restriction**: Fission applies only to 1SG and 2SG
   (derived from [+PART, +SING] feature condition)

2. **Inchoative requirement**: Stylistic LE requires vGO ∧ vBE
   (derived from Fission's structural context)

3. **Marking restriction**: Unmarked anticausatives block stylistic LE
   (derived from the verb fragment data)

4. **SE-optionality**: SE is optional when Fission produces a clitic
   syncretic with reflexive (derived from PF marking condition)

5. **Three-way synonymy**: SE+CL, CL+LE, SE+CL+LE are semantically
   identical because Voice⁰ is semantically vacuous

## References

- Muñoz Pérez, C. (2026). Stylistic applicatives. *Glossa* 11(1).
-/

namespace Phenomena.MunozPerez2026.Bridge

open Minimalism
open Minimalism.Morphology
open Fragments.Spanish.PersonFeatures
open Fragments.Spanish.Predicates
open Fragments.Spanish.Clitics
open Core.PersonCategory

-- ============================================================================
-- § 0: Spanish Fission Instantiation
-- ============================================================================

/-- The stylistic applicative Fission rule for Chilean Spanish.
    Instantiates the generic Fission framework with Spanish-specific data:
    - Context: inchoative (vGO ∧ vBE)
    - Person: [+PART, +SING] (1SG or 2SG)
    - Realization: Cl₁ = me/te (from [±AUTHOR]), Cl₂ = le (invariable) -/
def spanishFissionRule : FissionRule PersonCategory where
  contextOk := isInchoative
  personOk := fissionApplicable
  realize := fun p => {
    cl1Form := if hasAuthor p then "me" else "te"
    cl2Form := "le"
  }

/-- Muñoz Pérez (2026, ex. 58): Non-thematic Voice must be overtly
    marked by a reflexive-like element at PF. -/
def spanishAnticausativePF : PFMarkingCondition where
  isSatisfied := fun cs => cs.any (fun c => c == "se" || c == "me" || c == "te" || c == "nos")

/-- Apply the Spanish stylistic applicative Fission rule. -/
def applySpanishFission (p : PersonCategory) (heads : List VerbHead) :
    Option FissionOutput :=
  applyFission spanishFissionRule p heads

/-- Check whether the Spanish Fission output satisfies the anticausative
    PF marking condition, making overt SE optional. -/
def spanishFissionSatisfiesPF (p : PersonCategory) (heads : List VerbHead) : Bool :=
  fissionSatisfiesPF spanishFissionRule spanishAnticausativePF p heads

-- ============================================================================
-- § 1: Person Restriction (Prediction 1)
-- ============================================================================

/-- Fission applies only to 1SG and 2SG.
    DERIVED from [+PARTICIPANT, +SINGULAR] feature condition. -/
theorem fission_person_restriction :
    fissionApplicable .s1 = true ∧
    fissionApplicable .s2 = true ∧
    fissionApplicable .s3 = false ∧
    fissionApplicable .minIncl = false ∧
    fissionApplicable .augIncl = false ∧
    fissionApplicable .excl = false ∧
    fissionApplicable .secondGrp = false ∧
    fissionApplicable .thirdGrp = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The person restriction matches the empirical data:
    Fission applies ↔ stylistic LE is grammatical. -/
theorem person_restriction_matches_data :
    -- 1SG: Fission applies, data says grammatical
    fissionApplicable .s1 = true ∧
    Data.person_1sg.acceptability = .grammatical ∧
    -- 2SG: Fission applies, data says grammatical
    fissionApplicable .s2 = true ∧
    Data.person_2sg.acceptability = .grammatical ∧
    -- 3SG: Fission blocked, data says ungrammatical
    fissionApplicable .s3 = false ∧
    Data.person_3sg.acceptability = .ungrammatical :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 2: Inchoative Requirement (Prediction 2)
-- ============================================================================

/-- Stylistic LE requires inchoative context (vGO ∧ vBE).
    DERIVED from Fission's structural context condition. -/
theorem stylLE_requires_inchoative :
    -- Fission applies in inchoative context
    (applySpanishFission .s1 [.vGO, .vBE]).isSome = true ∧
    -- Fission blocked in activity context
    (applySpanishFission .s1 [.vDO]).isSome = false ∧
    -- Fission blocked in causative context
    (applySpanishFission .s1 [.vDO, .vGO, .vBE]).isSome = false := by
  native_decide

/-- Every verb that licenses stylistic LE has inchoative structure.
    DERIVED from the verb fragment. -/
theorem stylLE_verbs_inchoative :
    (Fragments.Spanish.Predicates.allVerbs.filter (·.licensesStylLE)).all
      (fun v => isInchoative v.verbHead) = true := by native_decide

-- ============================================================================
-- § 3: Marking Restriction (Prediction 3)
-- ============================================================================

/-- Unmarked anticausatives block stylistic LE.
    DERIVED from the verb fragment: mejorar is unmarked and blocks LE. -/
theorem unmarked_blocks_stylLE :
    mejorar.anticausativeMarking = .unmarked ∧
    mejorar.licensesStylLE = false := ⟨rfl, rfl⟩

/-- Marked anticausatives license stylistic LE. -/
theorem marked_licenses_stylLE :
    quebrar.anticausativeMarking = .marked ∧
    quebrar.licensesStylLE = true := ⟨rfl, rfl⟩

/-- Optional SE-marking also licenses stylistic LE. -/
theorem optional_licenses_stylLE :
    hervir.anticausativeMarking = .optional ∧
    hervir.licensesStylLE = true := ⟨rfl, rfl⟩

/-- All verbs blocking stylistic LE are unmarked.
    DERIVED from the fragment data. -/
theorem blocking_verbs_all_unmarked :
    (Fragments.Spanish.Predicates.allVerbs.filter (!·.licensesStylLE)).all
      (fun v => v.anticausativeMarking == .unmarked) = true := by native_decide

-- ============================================================================
-- § 4: SE-Optionality (Prediction 4)
-- ============================================================================

/-- When Fission applies, the output clitic satisfies the PF
    marking condition (syncretic with reflexive), making SE optional. -/
theorem se_optional_1sg :
    spanishFissionSatisfiesPF .s1 [.vGO, .vBE] = true := by native_decide

theorem se_optional_2sg :
    spanishFissionSatisfiesPF .s2 [.vGO, .vBE] = true := by native_decide

/-- The DAT-REFL syncretism that enables SE-optionality is present
    for exactly the persons where Fission applies. -/
theorem syncretism_aligns_with_fission :
    datReflSyncretic .first .Sing = true ∧
    datReflSyncretic .second .Sing = true ∧
    datReflSyncretic .third .Sing = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Three-Way Synonymy (Prediction 5)
-- ============================================================================

/-- The three clitic patterns (SE+CL, CL+LE, SE+CL+LE) are semantically
    identical because non-thematic Voice contributes no semantics.
    SE is purely a PF marker — its presence or absence is phonological,
    not semantic. -/
theorem voice_semantically_vacuous :
    Minimalism.voiceAnticausative.hasSemantics = false := rfl

/-- The empirical three-way synonymy follows: since Voice has no
    semantics, adding or removing SE doesn't change meaning. -/
theorem three_way_synonymy_from_vacuity :
    -- All three patterns are grammatical (data)
    Data.romper_se_me.acceptability = .grammatical ∧
    Data.romper_me_le.acceptability = .grammatical ∧
    Data.romper_se_me_le.acceptability = .grammatical ∧
    -- Non-thematic Voice is semantically vacuous (theory)
    Minimalism.voiceAnticausative.hasSemantics = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: Fission Verification
-- ============================================================================

/-- Fission applies to 1SG in inchoative context. -/
theorem fission_1sg_inchoative :
    applySpanishFission .s1 [.vGO, .vBE] =
      some { cl1Form := "me", cl2Form := "le" } := by native_decide

/-- Fission applies to 2SG in inchoative context. -/
theorem fission_2sg_inchoative :
    applySpanishFission .s2 [.vGO, .vBE] =
      some { cl1Form := "te", cl2Form := "le" } := by native_decide

/-- Fission does NOT apply to 3SG (not [+PART]). -/
theorem fission_blocked_3sg :
    applySpanishFission .s3 [.vGO, .vBE] = none := by native_decide

/-- Fission does NOT apply in non-inchoative context (activity). -/
theorem fission_blocked_activity :
    applySpanishFission .s1 [.vDO] = none := by native_decide

/-- Fission does NOT apply in causative context (has vDO). -/
theorem fission_blocked_causative :
    applySpanishFission .s1 [.vDO, .vGO, .vBE] = none := by native_decide

/-- 1SG Cl₁ is "me" (reflects [+AUTHOR]). -/
theorem cl1_1sg_is_me :
    (applySpanishFission .s1 [.vGO, .vBE]).map (·.cl1Form) = some "me" := by native_decide

/-- 2SG Cl₁ is "te" (reflects [-AUTHOR]). -/
theorem cl1_2sg_is_te :
    (applySpanishFission .s2 [.vGO, .vBE]).map (·.cl1Form) = some "te" := by native_decide

/-- Cl₂ is always invariable "le". -/
theorem cl2_invariable :
    (applySpanishFission .s1 [.vGO, .vBE]).map (·.cl2Form) = some "le" ∧
    (applySpanishFission .s2 [.vGO, .vBE]).map (·.cl2Form) = some "le" := by native_decide

-- ============================================================================
-- § 7: Per-Verb Inchoative Verification
-- ============================================================================

/-- Each verb individually checked against the inchoative requirement. -/
theorem abrir_inchoative : isInchoative abrir.verbHead = true := by native_decide
theorem romper_inchoative : isInchoative romper.verbHead = true := by native_decide
theorem hundir_inchoative : isInchoative hundir.verbHead = true := by native_decide
theorem caer_inchoative : isInchoative caer.verbHead = true := by native_decide
theorem morir_inchoative : isInchoative morir.verbHead = true := by native_decide
theorem quebrar_inchoative : isInchoative quebrar.verbHead = true := by native_decide
theorem hervir_inchoative : isInchoative hervir.verbHead = true := by native_decide
theorem olvidar_inchoative : isInchoative olvidar.verbHead = true := by native_decide
theorem ocurrir_inchoative : isInchoative ocurrir.verbHead = true := by native_decide
theorem mejorar_inchoative : isInchoative mejorar.verbHead = true := by native_decide

end Phenomena.MunozPerez2026.Bridge
