import Linglib.Features.Person.Decomposition
import Linglib.Fragments.Romance.Clitics

/-!
# Spanish Clitic Paradigm
[munoz-perez-2026]

The full Spanish clitic paradigm, with syncretism data critical for
Muñoz [munoz-perez-2026]. The key observation: 1SG and 2SG are syncretic
across accusative, dative, and reflexive, while 3SG/PL are not.
This syncretism drives the availability of stylistic applicatives.

## Paradigm (Muñoz [munoz-perez-2026], ex. 59)

|       | ACC    | DAT   | REFL |
|-------|--------|-------|------|
| 1SG   | me     | me    | me   | ← fully syncretic
| 2SG   | te     | te    | te   | ← fully syncretic
| 3SG   | lo/la  | le/se | se   | ← NOT syncretic (DAT ≠ REFL)
| 1PL   | nos    | nos   | nos  | ← syncretic, but not singular
| 2/3PL | los/las| les/se| se   | ← NOT syncretic

-/


namespace Spanish.Clitics

open Romance.Clitics (CliticEntry CliticCase)

/-! ### Paradigm data

Schema and capability instances are the shared Romance clitic schema
(`Fragments/Romance/Clitics.lean`). -/

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

/-! ### Paradigm and syncretism -/

/-- The full clitic paradigm as a flat list. -/
def paradigm : List CliticEntry :=
  [ me_acc, me_dat, me_refl,
    te_acc, te_dat, te_refl,
    lo, la, le_dat, se_refl,
    nos_acc, nos_dat, nos_refl,
    los, las, les_dat, se_refl_pl ]

/-- Look up the form for a given person, number, and case in the paradigm. -/
def lookupForm : UD.Person → UD.Number → CliticCase → Option String :=
  Romance.Clitics.lookupForm paradigm

/-- Are two clitic cases syncretic for a given person/number combination?
    Derived from the paradigm data. -/
def isSyncretic : UD.Person → UD.Number → CliticCase → CliticCase → Bool :=
  Romance.Clitics.isSyncretic paradigm

/-- The set of person/number combinations where DAT and REFL are syncretic.
    This is the key condition for SE-optionality. -/
def datReflSyncretic : UD.Person → UD.Number → Bool :=
  Romance.Clitics.datReflSyncretic paradigm

/-! ### Verification theorems -/

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

end Spanish.Clitics
