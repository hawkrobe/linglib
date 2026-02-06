import Linglib.Fragments.English.Predicates.Verbal

/-!
# Turkish Predicate Lexicon Fragment

Turkish predicates relevant to Qing et al. (2025). Properties like
C-distributivity and NVP class are DERIVED from the `attitudeBuilder` field.
-/

namespace Fragments.Turkish.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder AttitudeBuilder)
open IntensionalSemantics.Attitude.Preferential (AttitudeValence NVPClass)
open Theories.NadathurLauer2020.Builder (CausativeBuilder)

/-- "kork-" — fear (Class 2: C-distributive, negative, takes questions with symmetric interpretation). -/
def kork : VerbEntry where
  form := "kork-"
  form3sg := "korkuyor"
  formPast := "korktu"
  formPastPart := "korkmuş"
  formPresPart := "korkan"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- "um-" — hope (Class 3: C-distributive, positive, anti-rogative). -/
def um : VerbEntry where
  form := "um-"
  form3sg := "umuyor"
  formPast := "umdu"
  formPastPart := "ummuş"
  formPresPart := "uman"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- "merak et-" — wonder/be curious (rogative, non-preferential). -/
def merakEt : VerbEntry where
  form := "merak et-"
  form3sg := "merak ediyor"
  formPast := "merak etti"
  formPastPart := "merak etmiş"
  formPresPart := "merak eden"
  complementType := .question
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  takesQuestionBase := true

/-- "endişelen-" — worry (Class 1: non-C-distributive). -/
def endiselen : VerbEntry where
  form := "endişelen-"
  form3sg := "endişeleniyor"
  formPast := "endişelendi"
  formPastPart := "endişelenmiş"
  formPresPart := "endişelenen"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

/-! ## Causative predicates

Turkish morphological causative suffix -dür (Song 1996: COMPACT type).
Allomorphs: -dür, -tür, -dir, -tir (vowel harmony).
"Ali Hasan-ı öl-dür-dü" = "Ali killed Hasan" (öl 'die' + -dür CAUS) -/

/-- öl-dür-mek — die-CAUS = "to kill" (morphological COMPACT causative).

    Song (1996): Turkish *-dür* is a productive morphological causative
    suffix creating COMPACT causatives. -/
def ol_dur : VerbEntry where
  form := "öl-dür-mek"
  form3sg := "öl-dür-ür"
  formPast := "öl-dür-dü"
  formPastPart := "öl-dür-müş"
  formPresPart := "öl-dür-en"
  complementType := .np  -- Fused: no separate complement clause
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .causative
  causativeBuilder := some .make

/-- yap-tır-mak — do-CAUS = "to make (someone) do" (productive causative). -/
def yap_tir : VerbEntry where
  form := "yap-tır-mak"
  form3sg := "yap-tır-ır"
  formPast := "yap-tır-dı"
  formPastPart := "yap-tır-mış"
  formPresPart := "yap-tır-an"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .make

/-- Turkish causative *-dür* uses `.make` builder. -/
theorem ol_dur_is_make :
    ol_dur.causativeBuilder = some .make := rfl

def allVerbs : List VerbEntry := [kork, um, merakEt, endiselen, ol_dur, yap_tir]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Turkish.Predicates
