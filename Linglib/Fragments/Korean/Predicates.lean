import Linglib.Fragments.English.Predicates.Verbal

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

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType)
open Theories.NadathurLauer2020.Builder (CausativeBuilder)

/-- 웃게 하다 "wus-ke ha-da" — smile-PURP do = "cause to smile".

    Korean PURP-type causative (Song 1996). Non-implicative: the effect
    (smiling) is not entailed to have occurred. Uses `.cause` builder
    because the purposive structure asserts counterfactual dependence
    rather than direct sufficient guarantee. -/
def wus_ke_ha : VerbEntry where
  form := "wus-ke ha-da"
  form3sg := "wus-ke ha-n-da"
  formPast := "wus-ke ha-əss-ta"
  formPastPart := "wus-ke ha-n"
  formPresPart := "wus-ke ha-go itta"
  complementType := .infinitival  -- Purposive complement
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .cause  -- PURP = counterfactual/non-implicative

/-- 읽게 하다 "ilk-ke ha-da" — read-PURP do = "cause to read". -/
def ilk_ke_ha : VerbEntry where
  form := "ilk-ke ha-da"
  form3sg := "ilk-ke ha-n-da"
  formPast := "ilk-ke ha-əss-ta"
  formPastPart := "ilk-ke ha-n"
  formPresPart := "ilk-ke ha-go itta"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .cause

/-- 죽이다 "cwuk-i-da" — die-CAUS = "to kill" (lexical/morphological COMPACT).

    Unlike *-ke ha-*, the *-i-* causative is COMPACT and implicative:
    the effect is entailed. Uses `.make` builder. -/
def cwuk_i : VerbEntry where
  form := "cwuk-i-da"
  form3sg := "cwuk-i-n-da"
  formPast := "cwuk-yəss-ta"
  formPastPart := "cwuk-i-n"
  formPresPart := "cwuk-i-go itta"
  complementType := .np  -- Fused: no separate complement clause
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

/-- The two Korean causative types use different builders,
    reflecting the PURP vs COMPACT distinction (Song 1996). -/
theorem purp_compact_different_builders :
    wus_ke_ha.causativeBuilder ≠ cwuk_i.causativeBuilder := by decide

def allVerbs : List VerbEntry := [wus_ke_ha, ilk_ke_ha, cwuk_i]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Korean.Predicates
