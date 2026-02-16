import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Japanese Predicate Lexicon Fragment

Japanese predicates relevant to Qing et al. (2025). Properties like
C-distributivity and NVP class are DERIVED from the `attitudeBuilder` field.
-/

namespace Fragments.Japanese.Predicates

open Core.Verbs
open Semantics.Attitudes.Preferential (AttitudeValence NVPClass)
open NadathurLauer2020.Builder (CausativeBuilder)

/-- Japanese verb entry: extends VerbCore with Japanese inflectional paradigm. -/
structure JapaneseVerbEntry extends VerbCore where
  /-- Nonpast finite form -/
  form3sg : String
  /-- Past form (-ta) -/
  formPast : String
  /-- Gerund / -te form -/
  formGerund : String
  /-- Progressive (-teiru) -/
  formProgressive : String
  deriving Repr, BEq

/-- 楽しみ "tanosimi" — looking forward to (Class 1: positive, non-C-distributive). -/
def tanosimi : JapaneseVerbEntry where
  form := "tanosimi"
  form3sg := "tanosimi da"
  formPast := "tanosimi datta"
  formGerund := "tanosimi"
  formProgressive := "tanosimi"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.relevanceBased .positive))

/-- 恐れ "osore" — fear (Class 2: negative, C-distributive). -/
def osore : JapaneseVerbEntry where
  form := "osore"
  form3sg := "osoreru"
  formPast := "osoreta"
  formGerund := "osorete"
  formProgressive := "osoreteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- 期待 "kitai" — expect/hope (Class 3: positive, C-distributive, anti-rogative). -/
def kitai : JapaneseVerbEntry where
  form := "kitai"
  form3sg := "kitai suru"
  formPast := "kitai shita"
  formGerund := "kitai shite"
  formProgressive := "kitai shiteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- 心配 "shinpai" — worry (Class 1: non-C-distributive). -/
def shinpai : JapaneseVerbEntry where
  form := "shinpai"
  form3sg := "shinpai suru"
  formPast := "shinpai shita"
  formGerund := "shinpai shite"
  formProgressive := "shinpai shiteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

/-! ## Causative predicates

Japanese morphological causative suffix *-(s)ase* (Song 1996: COMPACT type).
Case marking on the causee distinguishes coercion from permission:
- ACC *o* = less causee control → `.make` (coercive reading)
- DAT *ni* = more causee control → `.enable` (permissive reading)

"Hanako ga Ziroo o ik-ase-ta" = "Hanako made Ziro go" (ACC → make)
"Hanako ga Ziroo ni ik-ase-ta" = "Hanako let Ziro go" (DAT → enable) -/

/-- 行かせる "ik-ase-ru" — go-CAUS (ACC causee = make reading). -/
def ik_ase : JapaneseVerbEntry where
  form := "ik-ase-ru"
  form3sg := "ik-ase-ru"
  formPast := "ik-ase-ta"
  formGerund := "ik-ase-te"
  formProgressive := "ik-ase-teiru"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .make

/-- 食べさせる "tabe-sase-ru" — eat-CAUS (ACC causee = make reading). -/
def tabe_sase : JapaneseVerbEntry where
  form := "tabe-sase-ru"
  form3sg := "tabe-sase-ru"
  formPast := "tabe-sase-ta"
  formGerund := "tabe-sase-te"
  formProgressive := "tabe-sase-teiru"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .make

/-- Japanese causative -(s)ase uses `.make` builder (direct causation reading). -/
theorem ik_ase_is_make :
    ik_ase.causativeBuilder = some .make := rfl

def allVerbs : List JapaneseVerbEntry := [tanosimi, osore, kitai, shinpai, ik_ase, tabe_sase]

def lookup (form : String) : Option JapaneseVerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Japanese.Predicates
