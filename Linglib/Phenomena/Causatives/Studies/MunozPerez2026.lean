import Linglib.Core.Empirical
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Morphology.DM.Fission
import Linglib.Fragments.Spanish.PersonFeatures
import Linglib.Fragments.Spanish.Predicates
import Linglib.Fragments.Spanish.Clitics

open Core.Empirical

/-!
# Muñoz @cite{munoz-perez-2026} — Empirical Data
@cite{munoz-perez-2026}

Grammaticality judgments from Muñoz @cite{munoz-perez-2026} "Stylistic applicatives:
A lens into the nature of anticausative SE" (*Glossa* 11(1)).

## Key Data Points

1. **Three-way synonymy** (exx. 7–18): For marked anticausatives with
   1SG/2SG dative, three clitic patterns are interchangeable:
   - SE + CL_dat: *se me rompió* "it broke on me"
   - CL_dat + LE: *me le rompió*
   - SE + CL_dat + LE: *se me le rompió*

2. **Person restriction** (exx. 15–19): Stylistic LE is available only
   with 1SG (*me*) and 2SG (*te*), not 3SG (*le*), 1PL (*nos*), 2/3PL (*les*).

3. **Marking restriction** (exx. 39–40): Stylistic LE requires SE-marked
   (or optionally SE-marked) anticausatives. Unmarked anticausatives
   (*mejorar*) block it.

-/

namespace Phenomena.Causatives.Studies.MunozPerez2026

-- ============================================================================
-- § 1: Acceptability Data Types
-- ============================================================================

/-- Acceptability status for Chilean Spanish judgments. -/
inductive Acceptability where
  | grammatical      -- Fully acceptable (✓)
  | ungrammatical    -- Rejected (*)
  | marginal         -- Marginal (??)
  deriving DecidableEq, BEq, Repr

/-- A clitic pattern in an anticausative construction. -/
inductive CliticPattern where
  | se_cl        -- SE + dative clitic: se me rompió
  | cl_le        -- Dative clitic + LE: me le rompió (stylistic applicative)
  | se_cl_le     -- SE + dative clitic + LE: se me le rompió
  deriving DecidableEq, BEq, Repr

/-- Person of the dative clitic. -/
inductive DativeCliticPerson where
  | first_sg   -- me
  | second_sg  -- te
  | third_sg   -- le
  | first_pl   -- nos
  | third_pl   -- les
  deriving DecidableEq, BEq, Repr

/-- A single grammaticality judgment from the paper. -/
structure Judgment where
  /-- Example number in the paper -/
  exNumber : String
  /-- The verb -/
  verb : String
  /-- The clitic pattern -/
  pattern : CliticPattern
  /-- Person of the dative clitic -/
  dativePerson : DativeCliticPerson
  /-- Acceptability -/
  acceptability : Acceptability
  deriving Repr, BEq

-- ============================================================================
-- § 2: Three-Way Synonymy Data (exx. 7–18)
-- ============================================================================

/-- *romper* "break" with 1SG dative: all three patterns OK. -/
def romper_se_me : Judgment := { exNumber := "7", verb := "romper", pattern := .se_cl, dativePerson := .first_sg, acceptability := .grammatical }
def romper_me_le : Judgment := { exNumber := "8a", verb := "romper", pattern := .cl_le, dativePerson := .first_sg, acceptability := .grammatical }
def romper_se_me_le : Judgment := { exNumber := "8b", verb := "romper", pattern := .se_cl_le, dativePerson := .first_sg, acceptability := .grammatical }

/-- *hundir* "sink" with 1SG dative. -/
def hundir_se_me : Judgment := { exNumber := "9", verb := "hundir", pattern := .se_cl, dativePerson := .first_sg, acceptability := .grammatical }
def hundir_me_le : Judgment := { exNumber := "10a", verb := "hundir", pattern := .cl_le, dativePerson := .first_sg, acceptability := .grammatical }

/-- *caer* "fall" with 1SG dative. -/
def caer_se_me : Judgment := { exNumber := "11", verb := "caer", pattern := .se_cl, dativePerson := .first_sg, acceptability := .grammatical }
def caer_me_le : Judgment := { exNumber := "12a", verb := "caer", pattern := .cl_le, dativePerson := .first_sg, acceptability := .grammatical }

/-- *morir* "die" with 1SG dative. -/
def morir_se_me : Judgment := { exNumber := "13", verb := "morir", pattern := .se_cl, dativePerson := .first_sg, acceptability := .grammatical }
def morir_me_le : Judgment := { exNumber := "14a", verb := "morir", pattern := .cl_le, dativePerson := .first_sg, acceptability := .grammatical }

-- ============================================================================
-- § 3: Person Restriction Data (exx. 15–19)
-- ============================================================================

/-- 1SG: stylistic LE is OK. -/
def person_1sg : Judgment := { exNumber := "15", verb := "caer", pattern := .cl_le, dativePerson := .first_sg, acceptability := .grammatical }

/-- 2SG: stylistic LE is OK. -/
def person_2sg : Judgment := { exNumber := "16", verb := "caer", pattern := .cl_le, dativePerson := .second_sg, acceptability := .grammatical }

/-- 3SG: stylistic LE is BLOCKED. -/
def person_3sg : Judgment := { exNumber := "17", verb := "caer", pattern := .cl_le, dativePerson := .third_sg, acceptability := .ungrammatical }

/-- 1PL: stylistic LE is BLOCKED. -/
def person_1pl : Judgment := { exNumber := "18", verb := "caer", pattern := .cl_le, dativePerson := .first_pl, acceptability := .ungrammatical }

/-- 3PL: stylistic LE is BLOCKED. -/
def person_3pl : Judgment := { exNumber := "19", verb := "caer", pattern := .cl_le, dativePerson := .third_pl, acceptability := .ungrammatical }

/-- Person restriction data collected. -/
def personRestrictionData : List Judgment :=
  [person_1sg, person_2sg, person_3sg, person_1pl, person_3pl]

-- ============================================================================
-- § 4: Marking Restriction Data (exx. 39–40)
-- ============================================================================

/-- *quebrar* (marked SE) licenses stylistic LE. -/
def quebrar_le : Judgment := { exNumber := "39a", verb := "quebrar", pattern := .cl_le, dativePerson := .first_sg, acceptability := .grammatical }

/-- *mejorar* (unmarked) does NOT license stylistic LE. -/
def mejorar_le : Judgment := { exNumber := "39b", verb := "mejorar", pattern := .cl_le, dativePerson := .first_sg, acceptability := .ungrammatical }

/-- *hervir* (optional SE) DOES license stylistic LE. -/
def hervir_le : Judgment := { exNumber := "40", verb := "hervir", pattern := .cl_le, dativePerson := .first_sg, acceptability := .grammatical }

-- ============================================================================
-- § 5: Data Verification
-- ============================================================================

/-- All three-way synonymy patterns are grammatical for 1SG. -/
theorem three_way_all_grammatical :
    (romper_se_me.acceptability == .grammatical &&
    romper_me_le.acceptability == .grammatical &&
    romper_se_me_le.acceptability == .grammatical) = true := rfl

/-- Person restriction: exactly 1SG and 2SG are grammatical. -/
theorem person_restriction_data :
    (personRestrictionData.filter (·.acceptability == .grammatical)).length = 2 := by
  native_decide

/-- Person restriction: exactly 3SG, 1PL, 3PL are ungrammatical. -/
theorem person_restriction_blocked :
    (personRestrictionData.filter (·.acceptability == .ungrammatical)).length = 3 := by
  native_decide

/-- Marking restriction: marked/optional → OK, unmarked → blocked. -/
theorem marking_restriction :
    (quebrar_le.acceptability == .grammatical &&
    hervir_le.acceptability == .grammatical &&
    mejorar_le.acceptability == .ungrammatical) = true := rfl

-- ============================================================================
-- § 6: Bridge — Spanish Fission Instantiation
-- ============================================================================

open Minimalism
open Minimalism.Morphology
open Fragments.Spanish.PersonFeatures
open Fragments.Spanish.Predicates
open Fragments.Spanish.Clitics
open Core.PersonCategory

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

/-- Muñoz @cite{munoz-perez-2026}: Non-thematic Voice must be overtly
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
-- § 7: Bridge — Person Restriction (Prediction 1)
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
    person_1sg.acceptability = .grammatical ∧
    -- 2SG: Fission applies, data says grammatical
    fissionApplicable .s2 = true ∧
    person_2sg.acceptability = .grammatical ∧
    -- 3SG: Fission blocked, data says ungrammatical
    fissionApplicable .s3 = false ∧
    person_3sg.acceptability = .ungrammatical :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Bridge — Inchoative Requirement (Prediction 2)
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
-- § 9: Bridge — Marking Restriction (Prediction 3)
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
-- § 10: Bridge — SE-Optionality (Prediction 4)
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
-- § 11: Bridge — Three-Way Synonymy (Prediction 5)
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
    romper_se_me.acceptability = .grammatical ∧
    romper_me_le.acceptability = .grammatical ∧
    romper_se_me_le.acceptability = .grammatical ∧
    -- Non-thematic Voice is semantically vacuous (theory)
    Minimalism.voiceAnticausative.hasSemantics = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 12: Bridge — Fission Verification
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
-- § 13: Bridge — Per-Verb Inchoative Verification
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

end Phenomena.Causatives.Studies.MunozPerez2026
