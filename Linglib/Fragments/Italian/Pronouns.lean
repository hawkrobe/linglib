import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Pronoun.Capabilities
import Linglib.Features.Person.Decomposition
import Linglib.Fragments.Romance.Clitics

/-! # Italian Pronoun and Clitic Fragment

Personal pronouns (strong forms) and clitic paradigm for Italian.

## Strong Pronouns
[munoz-perez-2026]

Italian has a T/V distinction in 2nd person:
- Singular: *tu* (familiar T) vs *Lei* (formal V, 3sg agreement)
- Plural: *voi* (familiar) vs *Loro* (formal, archaic; *voi* now used for both)

## Clitic Paradigm

Italian object clitics show the same syncretism pattern as Spanish: 1sg/2sg are syncretic across accusative, dative,
and reflexive cases, while 3sg/3pl are not.

| Person | ACC    | DAT    | REFL |
|--------|--------|--------|------|
| 1sg    | mi     | mi     | mi   | syncretic
| 2sg    | ti     | ti     | ti   | syncretic
| 3sg    | lo/la  | gli/le | si   | NOT syncretic
| 1pl    | ci     | ci     | ci   | syncretic
| 2pl    | vi     | vi     | vi   | syncretic
| 3pl    | li/le  | loro   | si   | NOT syncretic
-/


namespace Italian.Pronouns

open Pronoun
open Features.Register (Level)

-- ============================================================================
-- § 1: Strong Pronouns
-- ============================================================================

/-- *io* — 1sg. -/
def io : PersonalPronoun :=
  { form := "io", person := some .first, number := some .singular }

/-- *tu* — 2sg familiar (T form). -/
def tu : PersonalPronoun :=
  { form := "tu", person := some .second, number := some .singular, register := .informal }

/-- *Lei* — polite 2sg (V form). Formally 3rd person: triggers 3sg verbal
    agreement, patterns with 3sg.f clitics, binds 3rd person reflexive *si*.
    Interpretably 2nd person: triggers PCC effects, Fancy Constraint effects,
    2PL resolved agreement in coordination.
    [adamson-zompi-2025] -/
def lei_formal : PersonalPronoun :=
  { form := "Lei", person := some .third, number := some .singular, register := .formal,
    referentialPerson := some .second }

/-- *lui* — 3sg masculine. -/
def lui : PersonalPronoun :=
  { form := "lui", person := some .third, number := some .singular }

/-- *lei* — 3sg feminine. -/
def lei : PersonalPronoun :=
  { form := "lei", person := some .third, number := some .singular }

/-- *noi* — 1pl. -/
def noi : PersonalPronoun :=
  { form := "noi", person := some .first, number := some .plural }

/-- *voi* — 2pl (familiar; also used as general 2pl in modern Italian). -/
def voi : PersonalPronoun :=
  { form := "voi", person := some .second, number := some .plural, register := .informal }

/-- *Loro* — 2pl formal (archaic, largely replaced by *voi*). -/
def loro_formal : PersonalPronoun :=
  { form := "Loro", person := some .second, number := some .plural, register := .formal }

/-- *loro* — 3pl. -/
def loro : PersonalPronoun :=
  { form := "loro", person := some .third, number := some .plural }

def secondPersonPronouns : List PersonalPronoun := [tu, lei_formal]

def allPronouns : List PersonalPronoun :=
  [io] ++ secondPersonPronouns ++ [lui, lei, noi, voi, loro_formal, loro]

-- ============================================================================
-- § 2: Clitic Paradigm
-- ============================================================================

open Romance.Clitics (CliticEntry CliticCase)

/-! Schema and capability instances (`Proform`/`Bound`/`HasPerson`/
`HasNumber`/`HasCase`) are the shared Romance clitic schema
(`Fragments/Romance/Clitics.lean`). -/

-- 1sg clitics
def mi_acc : CliticEntry := { form := "mi", person := .first, number := .Sing, case_ := .accusative }
def mi_dat : CliticEntry := { form := "mi", person := .first, number := .Sing, case_ := .dative }
def mi_refl : CliticEntry := { form := "mi", person := .first, number := .Sing, case_ := .reflexive }

-- 2sg clitics
def ti_acc : CliticEntry := { form := "ti", person := .second, number := .Sing, case_ := .accusative }
def ti_dat : CliticEntry := { form := "ti", person := .second, number := .Sing, case_ := .dative }
def ti_refl : CliticEntry := { form := "ti", person := .second, number := .Sing, case_ := .reflexive }

-- 3sg clitics
def lo_cl : CliticEntry := { form := "lo", person := .third, number := .Sing, case_ := .accusative }
def la_cl : CliticEntry := { form := "la", person := .third, number := .Sing, case_ := .accusative }
def gli_dat : CliticEntry := { form := "gli", person := .third, number := .Sing, case_ := .dative }
def le_dat : CliticEntry := { form := "le", person := .third, number := .Sing, case_ := .dative }
def si_refl : CliticEntry := { form := "si", person := .third, number := .Sing, case_ := .reflexive }

-- 1pl clitics
def ci_acc : CliticEntry := { form := "ci", person := .first, number := .Plur, case_ := .accusative }
def ci_dat : CliticEntry := { form := "ci", person := .first, number := .Plur, case_ := .dative }
def ci_refl : CliticEntry := { form := "ci", person := .first, number := .Plur, case_ := .reflexive }

-- 2pl clitics
def vi_acc : CliticEntry := { form := "vi", person := .second, number := .Plur, case_ := .accusative }
def vi_dat : CliticEntry := { form := "vi", person := .second, number := .Plur, case_ := .dative }
def vi_refl : CliticEntry := { form := "vi", person := .second, number := .Plur, case_ := .reflexive }

-- 3pl clitics
def li_cl : CliticEntry := { form := "li", person := .third, number := .Plur, case_ := .accusative }
def le_cl : CliticEntry := { form := "le", person := .third, number := .Plur, case_ := .accusative }
def loro_dat : CliticEntry := { form := "loro", person := .third, number := .Plur, case_ := .dative }
def si_refl_pl : CliticEntry := { form := "si", person := .third, number := .Plur, case_ := .reflexive }

-- ============================================================================
-- § 3: Paradigm and Syncretism
-- ============================================================================

/-- The traditional atonic (object) paradigm as a flat list. NB: the series is
    not strength-homogeneous — [cardinaletti-starke-1999] classify dative
    *loro* as *weak*, not clitic (not verb-adjacent, never clusters); see
    `loroDatStrength` below. The rest are clitics proper. -/
def paradigm : List CliticEntry :=
  [ mi_acc, mi_dat, mi_refl,
    ti_acc, ti_dat, ti_refl,
    lo_cl, la_cl, gli_dat, le_dat, si_refl,
    ci_acc, ci_dat, ci_refl,
    vi_acc, vi_dat, vi_refl,
    li_cl, le_cl, loro_dat, si_refl_pl ]

/-! ### Capability checks -/

-- The reflexive clitic *si* is a Principle-A anaphor; the accusative *lo* a pronominal —
-- read through the generic `Bound` capability.
example : Bound.IsAnaphor si_refl := by decide
example : Bound.IsPronominal lo_cl := by decide

/-- Look up the form for a given person, number, and case in the paradigm. -/
def lookupForm : UD.Person → UD.Number → CliticCase → Option String :=
  Romance.Clitics.lookupForm paradigm

/-- Are two clitic cases syncretic for a given person/number combination?
    Derived from the paradigm data. -/
def isSyncretic : UD.Person → UD.Number → CliticCase → CliticCase → Bool :=
  Romance.Clitics.isSyncretic paradigm

/-- DAT/REFL syncretism for a given person/number. -/
def datReflSyncretic : UD.Person → UD.Number → Bool :=
  Romance.Clitics.datReflSyncretic paradigm

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

-- Syncretism
/-- 1sg: dative and reflexive are syncretic (both "mi"). -/
theorem syncretic_1sg : datReflSyncretic .first .Sing = true := rfl

/-- 2sg: dative and reflexive are syncretic (both "ti"). -/
theorem syncretic_2sg : datReflSyncretic .second .Sing = true := rfl

/-- 3sg: dative and reflexive are NOT syncretic ("gli" ≠ "si"). -/
theorem not_syncretic_3sg : datReflSyncretic .third .Sing = false := rfl

/-- 1pl: dative and reflexive are syncretic (both "ci"). -/
theorem syncretic_1pl : datReflSyncretic .first .Plur = true := rfl

/-- 2pl: dative and reflexive are syncretic (both "vi"). -/
theorem syncretic_2pl : datReflSyncretic .second .Plur = true := rfl

/-- 3pl: dative and reflexive are NOT syncretic ("loro" ≠ "si"). -/
theorem not_syncretic_3pl : datReflSyncretic .third .Plur = false := rfl

-- Form identity
/-- 1sg forms are identical across all three cases. -/
theorem mi_forms_identical :
    mi_acc.form = mi_dat.form ∧ mi_dat.form = mi_refl.form := ⟨rfl, rfl⟩

/-- 2sg forms are identical across all three cases. -/
theorem ti_forms_identical :
    ti_acc.form = ti_dat.form ∧ ti_dat.form = ti_refl.form := ⟨rfl, rfl⟩

/-- 3sg dative ≠ 3sg reflexive (gli ≠ si). -/
theorem gli_ne_si : gli_dat.form ≠ si_refl.form := by decide

-- T/V distinction
/-- *tu* is informal, *Lei* is formal. -/
theorem tv_distinction :
    tu.register = .informal ∧ lei_formal.register = .formal := ⟨rfl, rfl⟩

/-- *Lei* has 3rd person agreement features but 2nd person interpretable features.
    [adamson-zompi-2025] -/
theorem lei_formal_dual_person :
    lei_formal.person = some .third ∧
    lei_formal.referentialPerson = some .second := ⟨rfl, rfl⟩

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

/-- Both singular and plural are attested. -/
theorem has_both_numbers :
    allPronouns.any (·.number == some .singular) = true ∧
    allPronouns.any (·.number == some .plural) = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: Cardinaletti–Starke deficiency classes
-- ============================================================================

/-- Italian's tonic series (`allPronouns`) instantiates the Cardinaletti–Starke
    `.strong` class ([cardinaletti-starke-1999]). -/
def strongStrength : Strength := .strong

/-- The object clitics (`paradigm` minus dative *loro*) are the maximally
    deficient `.clitic` class: verb-adjacent heads that cluster
    ([cardinaletti-starke-1999]). -/
def cliticStrength : Strength := .clitic

/-- Dative *loro* is [cardinaletti-starke-1999]'s parade case for separating
    weak from clitic: deficient (reduced vs *a loro*, no coordination) but a
    maximal projection — not verb-adjacent, never clustering, bears word
    stress. -/
def loroDatStrength : Strength := .weak

/-- The clitic series is structurally more deficient than the strong series:
    the deficiency ordering behind their complementary distribution (clitics
    host-adjacent and unfocusable, strong forms free). -/
theorem clitics_more_deficient : cliticStrength < strongStrength := by decide

/-- The traditional atonic paradigm is not strength-homogeneous: dative *loro*
    (weak) sits strictly between the clitics and the strong series
    ([cardinaletti-starke-1999]). -/
theorem atonic_series_not_homogeneous :
    cliticStrength < loroDatStrength ∧ loroDatStrength < strongStrength :=
  ⟨by decide, by decide⟩

end Italian.Pronouns
