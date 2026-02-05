import Linglib.Fragments.English.Predicates.Verbal

/-!
# Mandarin Predicate Lexicon Fragment

Mandarin predicates relevant to Qing et al. (2025). Properties like
C-distributivity and NVP class are DERIVED from the `attitudeBuilder` field.
-/

namespace Fragments.Mandarin.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder AttitudeBuilder)
open IntensionalSemantics.Attitude.Preferential (AttitudeValence NVPClass)

/-- 期待 "qidai" — look forward to (Class 1: positive, non-C-distributive, takes questions). -/
def qidai : VerbEntry where
  form := "qidai"
  form3sg := "qidai"
  formPast := "qidai"
  formPastPart := "qidai"
  formPresPart := "qidai"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.relevanceBased .positive))

/-- 担心 "danxin" — worry (Class 1: negative, non-C-distributive). -/
def danxin : VerbEntry where
  form := "danxin"
  form3sg := "danxin"
  formPast := "danxin"
  formPastPart := "danxin"
  formPresPart := "danxin"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

/-- 希望 "xiwang" — hope (Class 3: positive, C-distributive, anti-rogative). -/
def xiwang : VerbEntry where
  form := "xiwang"
  form3sg := "xiwang"
  formPast := "xiwang"
  formPastPart := "xiwang"
  formPresPart := "xiwang"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- 害怕 "haipa" — fear (Class 2: negative, C-distributive, takes questions). -/
def haipa : VerbEntry where
  form := "haipa"
  form3sg := "haipa"
  formPast := "haipa"
  formPastPart := "haipa"
  formPresPart := "haipa"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-!
## yǐwéi: Exceptional Postsupposition

yǐwéi "be under the impression" (Glass 2022, 2025) has a POSTSUPPOSITION
(output-context constraint) that ¬p is compatible with the Common Ground
after the utterance. This is NOT a presupposition and cannot be derived
from veridicality alone.

The postsupposition is interpreted in the Theory layer (ContrafactiveGap.lean).
Here we just flag the exceptional behavior.
-/

/-- 以为 "yǐwéi" — be under the impression that (weak contrafactive).

**Exceptional**: Has postsupposition ◇¬p (CG compatible with ¬p after utterance).
This cannot be derived from veridicality; see Glass (2022, 2025).
-/
def yiwei : VerbEntry where
  form := "yiwei"
  form3sg := "yiwei"
  formPast := "yiwei"
  formPastPart := "yiwei"
  formPresPart := "yiwei"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Doxastic non-veridical, but with exceptional postsupposition (see docs)
  attitudeBuilder := some (.doxastic .nonVeridical)

/-- Does this verb have an exceptional postsupposition (not derivable from veridicality)?

This is a theory-neutral flag. The actual CGRequirement interpretation
happens in the Bridge layer (ContrafactiveGap.lean).
-/
def hasExceptionalPostsupposition (form : String) : Bool :=
  form == "yiwei"

def allVerbs : List VerbEntry := [qidai, danxin, xiwang, haipa, yiwei]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Mandarin.Predicates
