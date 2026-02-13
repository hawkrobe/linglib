import Linglib.Core.Empirical

/-!
# Muñoz Pérez (2026) — Empirical Data

Grammaticality judgments from Muñoz Pérez (2026) "Stylistic applicatives:
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

## References

- Muñoz Pérez, C. (2026). Stylistic applicatives: A lens into the
  nature of anticausative SE. *Glossa* 11(1).
-/

namespace Phenomena.MunozPerez2026.Data

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

end Phenomena.MunozPerez2026.Data
