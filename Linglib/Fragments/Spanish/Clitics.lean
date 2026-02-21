import Linglib.Core.Word

/-!
# Spanish Clitic Paradigm

The full Spanish clitic paradigm, with syncretism data critical for
Muñoz Pérez (2026). The key observation: 1SG and 2SG are syncretic
across accusative, dative, and reflexive, while 3SG/PL are not.
This syncretism drives the availability of stylistic applicatives.

## Paradigm (Muñoz Pérez 2026, ex. 59)

|       | ACC    | DAT   | REFL |
|-------|--------|-------|------|
| 1SG   | me     | me    | me   | ← fully syncretic
| 2SG   | te     | te    | te   | ← fully syncretic
| 3SG   | lo/la  | le/se | se   | ← NOT syncretic (DAT ≠ REFL)
| 1PL   | nos    | nos   | nos  | ← syncretic, but not singular
| 2/3PL | los/las| les/se| se   | ← NOT syncretic

## References

- Muñoz Pérez, C. (2026). Stylistic applicatives. *Glossa* 11(1).
-/

namespace Fragments.Spanish.Clitics

-- ============================================================================
-- § 1: Clitic Cases
-- ============================================================================

/-- The three-way case distinction for Spanish clitics. -/
inductive CliticCase where
  | accusative
  | dative
  | reflexive
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Clitic Entries
-- ============================================================================

/-- A single clitic form in the paradigm. -/
structure CliticEntry where
  form : String
  person : Person
  number : Number
  case_ : CliticCase
  deriving Repr, BEq

-- ============================================================================
-- § 3: Paradigm Data
-- ============================================================================

-- 1SG clitics
def me_acc : CliticEntry := { form := "me", person := .first, number := .Sing, case_ := .accusative }
def me_dat : CliticEntry := { form := "me", person := .first, number := .Sing, case_ := .dative }
def me_refl : CliticEntry := { form := "me", person := .first, number := .Sing, case_ := .reflexive }

-- 2SG clitics
def te_acc : CliticEntry := { form := "te", person := .second, number := .Sing, case_ := .accusative }
def te_dat : CliticEntry := { form := "te", person := .second, number := .Sing, case_ := .dative }
def te_refl : CliticEntry := { form := "te", person := .second, number := .Sing, case_ := .reflexive }

-- 3SG clitics
def lo : CliticEntry := { form := "lo", person := .third, number := .Sing, case_ := .accusative }
def la : CliticEntry := { form := "la", person := .third, number := .Sing, case_ := .accusative }
def le_dat : CliticEntry := { form := "le", person := .third, number := .Sing, case_ := .dative }
def se_refl : CliticEntry := { form := "se", person := .third, number := .Sing, case_ := .reflexive }

-- 1PL clitics
def nos_acc : CliticEntry := { form := "nos", person := .first, number := .Plur, case_ := .accusative }
def nos_dat : CliticEntry := { form := "nos", person := .first, number := .Plur, case_ := .dative }
def nos_refl : CliticEntry := { form := "nos", person := .first, number := .Plur, case_ := .reflexive }

-- 3PL clitics
def los : CliticEntry := { form := "los", person := .third, number := .Plur, case_ := .accusative }
def las : CliticEntry := { form := "las", person := .third, number := .Plur, case_ := .accusative }
def les_dat : CliticEntry := { form := "les", person := .third, number := .Plur, case_ := .dative }
def se_refl_pl : CliticEntry := { form := "se", person := .third, number := .Plur, case_ := .reflexive }

-- ============================================================================
-- § 4: Paradigm and Syncretism
-- ============================================================================

/-- The full clitic paradigm as a flat list. -/
def paradigm : List CliticEntry :=
  [ me_acc, me_dat, me_refl,
    te_acc, te_dat, te_refl,
    lo, la, le_dat, se_refl,
    nos_acc, nos_dat, nos_refl,
    los, las, les_dat, se_refl_pl ]

/-- Look up the form for a given person, number, and case in the paradigm. -/
def lookupForm (p : Person) (n : Number) (c : CliticCase) : Option String :=
  (paradigm.find? (fun e => e.person == p && e.number == n && e.case_ == c)).map (·.form)

/-- Are two clitic cases syncretic for a given person/number combination?
    DERIVED from the paradigm data: syncretism holds iff the looked-up
    forms are identical (and both exist). -/
def isSyncretic (p : Person) (n : Number) (c1 c2 : CliticCase) : Bool :=
  match lookupForm p n c1, lookupForm p n c2 with
  | some f1, some f2 => f1 == f2
  | _, _ => false

/-- The set of person/number combinations where DAT and REFL are syncretic.
    This is the key condition for SE-optionality (Muñoz Pérez 2026). -/
def datReflSyncretic (p : Person) (n : Number) : Bool :=
  isSyncretic p n .dative .reflexive

-- ============================================================================
-- § 5: Verification Theorems
-- ============================================================================

/-- 1SG: dative and reflexive are syncretic (both "me"). -/
theorem syncretic_1sg : datReflSyncretic .first .Sing = true := rfl

/-- 2SG: dative and reflexive are syncretic (both "te"). -/
theorem syncretic_2sg : datReflSyncretic .second .Sing = true := rfl

/-- 3SG: dative and reflexive are NOT syncretic ("le" ≠ "se"). -/
theorem not_syncretic_3sg : datReflSyncretic .third .Sing = false := rfl

/-- 1PL: dative and reflexive are syncretic (both "nos"). -/
theorem syncretic_1pl : datReflSyncretic .first .Plur = true := rfl

/-- 3PL: dative and reflexive are NOT syncretic ("les" ≠ "se"). -/
theorem not_syncretic_3pl : datReflSyncretic .third .Plur = false := rfl

/-- 1SG forms are identical across all three cases. -/
theorem me_forms_identical :
    me_acc.form = me_dat.form ∧ me_dat.form = me_refl.form := ⟨rfl, rfl⟩

/-- 2SG forms are identical across all three cases. -/
theorem te_forms_identical :
    te_acc.form = te_dat.form ∧ te_dat.form = te_refl.form := ⟨rfl, rfl⟩

/-- 3SG dative ≠ 3SG reflexive (le ≠ se). -/
theorem le_ne_se : le_dat.form ≠ se_refl.form := by decide

end Fragments.Spanish.Clitics
