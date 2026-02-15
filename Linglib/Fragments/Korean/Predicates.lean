import Linglib.Core.Verbs

/-!
# Korean Predicate Lexicon Fragment

Korean causative predicates, including the PURP-type *-ke ha-* causative
(Song 1996). The *-ke ha-* construction is non-implicative: the caused
event is not entailed to have actually occurred.

"Keeho-ka Jinee-ka wus-ke ha-əss-ta" = "Keeho caused Jinee to smile"
(Jinee may not have actually smiled — purposive, not sequential)

## References

- Song, J. J. (1996). Causatives and Causation. Longman. §5.1-5.3
-/

namespace Fragments.Korean.Predicates

open Core.Verbs
open NadathurLauer2020.Builder (CausativeBuilder)

/-- Korean verb entry: extends VerbCore with Korean inflectional paradigm. -/
structure KoreanVerbEntry extends VerbCore where
  /-- Declarative form (-ta) -/
  formDecl : String
  /-- Past form (-əss-ta) -/
  formPast : String
  /-- Adnominal form (-n) -/
  formAdnom : String
  /-- Progressive form (-go itta) -/
  formProgressive : String
  deriving Repr, BEq

/-- 웃게 하다 "wus-ke ha-da" — smile-PURP do = "cause to smile". -/
def wus_ke_ha : KoreanVerbEntry where
  form := "wus-ke ha-da"
  formDecl := "wus-ke ha-n-da"
  formPast := "wus-ke ha-əss-ta"
  formAdnom := "wus-ke ha-n"
  formProgressive := "wus-ke ha-go itta"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .cause

/-- 읽게 하다 "ilk-ke ha-da" — read-PURP do = "cause to read". -/
def ilk_ke_ha : KoreanVerbEntry where
  form := "ilk-ke ha-da"
  formDecl := "ilk-ke ha-n-da"
  formPast := "ilk-ke ha-əss-ta"
  formAdnom := "ilk-ke ha-n"
  formProgressive := "ilk-ke ha-go itta"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .cause

/-- 죽이다 "cwuk-i-da" — die-CAUS = "to kill" (lexical/morphological COMPACT). -/
def cwuk_i : KoreanVerbEntry where
  form := "cwuk-i-da"
  formDecl := "cwuk-i-n-da"
  formPast := "cwuk-yəss-ta"
  formAdnom := "cwuk-i-n"
  formProgressive := "cwuk-i-go itta"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .causative
  causativeBuilder := some .make

/-- Korean PURP-type *-ke ha-* uses `.cause` builder. -/
theorem wus_ke_ha_is_cause :
    wus_ke_ha.causativeBuilder = some .cause := rfl

/-- Korean COMPACT-type *-i-* uses `.make` builder. -/
theorem cwuk_i_is_make :
    cwuk_i.causativeBuilder = some .make := rfl

/-- The two Korean causative types use different builders. -/
theorem purp_compact_different_builders :
    wus_ke_ha.causativeBuilder ≠ cwuk_i.causativeBuilder := by decide

def allVerbs : List KoreanVerbEntry := [wus_ke_ha, ilk_ke_ha, cwuk_i]

def lookup (form : String) : Option KoreanVerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Korean.Predicates
