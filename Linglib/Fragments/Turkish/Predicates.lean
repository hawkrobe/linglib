import Linglib.Theories.Semantics.Verb.VerbEntry

/-!
# Turkish Predicate Lexicon Fragment
@cite{qing-uegaki-2025}

Turkish predicates relevant to @cite{qing-uegaki-2025}. Properties like
C-distributivity and NVP class are DERIVED from the `attitude` field.
-/

namespace Fragments.Turkish.Predicates

open Core.Verbs
open Semantics.Attitudes.Preferential (AttitudeValence NVPClass)
open Core.Verbs (Causative)

/-- Turkish verb entry: extends VerbCore with Turkish inflectional paradigm. -/
structure TurkishVerbEntry extends VerbCore where
  /-- Progressive form (-yor) -/
  formProg : String
  /-- Past form (-dı, -tı) -/
  formPast : String
  /-- Evidential form (-mış) -/
  formEvidential : String
  /-- Participle form (-an, -en) -/
  formParticiple : String
  deriving Repr, BEq

/-- "kork-" — fear (Class 2: C-distributive, negative). -/
def kork : TurkishVerbEntry where
  form := "kork-"
  formProg := "korkuyor"
  formPast := "korktu"
  formEvidential := "korkmuş"
  formParticiple := "korkan"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))

/-- "um-" — hope (Class 3: C-distributive, positive, anti-rogative). -/
def um : TurkishVerbEntry where
  form := "um-"
  formProg := "umuyor"
  formPast := "umdu"
  formEvidential := "ummuş"
  formParticiple := "uman"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- "merak et-" — wonder/be curious (rogative, non-preferential). -/
def merakEt : TurkishVerbEntry where
  form := "merak et-"
  formProg := "merak ediyor"
  formPast := "merak etti"
  formEvidential := "merak etmiş"
  formParticiple := "merak eden"
  complementType := .question
  passivizable := false
  opaqueContext := true
  takesQuestionBase := true

/-- "endişelen-" — worry (Class 1: non-C-distributive). -/
def endiselen : TurkishVerbEntry where
  form := "endişelen-"
  formProg := "endişeleniyor"
  formPast := "endişelendi"
  formEvidential := "endişelenmiş"
  formParticiple := "endişelenen"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased)

/-! ## Causative predicates

Turkish morphological causative suffix -dür (@cite{song-1996}: COMPACT type).
Allomorphs: -dür, -tür, -dir, -tir (vowel harmony).
"Ali Hasan-ı öl-dür-dü" = "Ali killed Hasan" (öl 'die' + -dür CAUS) -/

/-- öl-dür-mek — die-CAUS = "to kill" (morphological COMPACT causative). -/
def ol_dur : TurkishVerbEntry where
  form := "öldürmek"
  formProg := "öldürüyor"
  formPast := "öldürdü"
  formEvidential := "öldürmüş"
  formParticiple := "öldüren"
  complementType := .np
  causative := some .make

/-- yap-tır-mak — do-CAUS = "to make (someone) do" (productive causative). -/
def yap_tir : TurkishVerbEntry where
  form := "yaptırmak"
  formProg := "yaptırıyor"
  formPast := "yaptırdı"
  formEvidential := "yaptırmış"
  formParticiple := "yaptıran"
  complementType := .smallClause
  controlType := .objectControl
  causative := some .make

/-- Turkish causative *-dür* uses `.make` builder. -/
theorem ol_dur_is_make :
    ol_dur.causative = some .make := rfl

def allVerbs : List TurkishVerbEntry := [kork, um, merakEt, endiselen, ol_dur, yap_tir]

def lookup (form : String) : Option TurkishVerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Turkish.Predicates
