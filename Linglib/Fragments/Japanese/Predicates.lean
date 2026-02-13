import Linglib.Fragments.English.Predicates.Verbal

/-!
# Japanese Predicate Lexicon Fragment

Japanese predicates relevant to Qing et al. (2025). Properties like
C-distributivity and NVP class are DERIVED from the `attitudeBuilder` field.
-/

namespace Fragments.Japanese.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ControlType PreferentialBuilder AttitudeBuilder)
open IntensionalSemantics.Attitude.Preferential (AttitudeValence NVPClass)
open NadathurLauer2020.Builder (CausativeBuilder)

/-- 楽しみ "tanosimi" — looking forward to (Class 1: positive, non-C-distributive). -/
def tanosimi : VerbEntry where
  form := "tanosimi"
  form3sg := "tanosimi da"
  formPast := "tanosimi datta"
  formPastPart := "tanosimi"
  formPresPart := "tanosimi"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.relevanceBased .positive))

/-- 恐れ "osore" — fear (Class 2: negative, C-distributive). -/
def osore : VerbEntry where
  form := "osore"
  form3sg := "osoreru"
  formPast := "osoreta"
  formPastPart := "osorete"
  formPresPart := "osoreteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- 期待 "kitai" — expect/hope (Class 3: positive, C-distributive, anti-rogative). -/
def kitai : VerbEntry where
  form := "kitai"
  form3sg := "kitai suru"
  formPast := "kitai shita"
  formPastPart := "kitai shite"
  formPresPart := "kitai shiteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- 心配 "shinpai" — worry (Class 1: non-C-distributive). -/
def shinpai : VerbEntry where
  form := "shinpai"
  form3sg := "shinpai suru"
  formPast := "shinpai shita"
  formPastPart := "shinpai shite"
  formPresPart := "shinpai shiteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

/-! ## Causative predicates

Japanese morphological causative suffix *-(s)ase* (Song 1996: COMPACT type).
Case marking on the causee distinguishes coercion from permission:
- ACC *o* = less causee control → `.make` (coercive reading)
- DAT *ni* = more causee control → `.enable` (permissive reading)

"Hanako ga Ziroo o ik-ase-ta" = "Hanako made Ziro go" (ACC → make)
"Hanako ga Ziroo ni ik-ase-ta" = "Hanako let Ziro go" (DAT → enable) -/

/-- 行かせる "ik-ase-ru" — go-CAUS (ACC causee = make reading).

    Morphological COMPACT causative (Song 1996).
    ACC marking on causee signals less control → direct causation. -/
def ik_ase : VerbEntry where
  form := "ik-ase-ru"
  form3sg := "ik-ase-ru"
  formPast := "ik-ase-ta"
  formPastPart := "ik-ase-te"
  formPresPart := "ik-ase-teiru"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .make

/-- 食べさせる "tabe-sase-ru" — eat-CAUS (ACC causee = make reading). -/
def tabe_sase : VerbEntry where
  form := "tabe-sase-ru"
  form3sg := "tabe-sase-ru"
  formPast := "tabe-sase-ta"
  formPastPart := "tabe-sase-te"
  formPresPart := "tabe-sase-teiru"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .make

/-- Japanese causative -(s)ase uses `.make` builder (direct causation reading). -/
theorem ik_ase_is_make :
    ik_ase.causativeBuilder = some .make := rfl

def allVerbs : List VerbEntry := [tanosimi, osore, kitai, shinpai, ik_ase, tabe_sase]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Japanese.Predicates
