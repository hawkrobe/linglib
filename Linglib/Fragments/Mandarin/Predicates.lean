import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Mandarin Predicate Lexicon Fragment
@cite{qing-uegaki-2025} @cite{glass-2025}

Mandarin predicates relevant to @cite{qing-uegaki-2025}. Properties like
C-distributivity and NVP class are DERIVED from the `attitude` field.
-/

namespace Fragments.Mandarin.Predicates

open Core.Verbs
open Semantics.Attitudes.Preferential (AttitudeValence NVPClass)

/-- Mandarin verb entry: extends VerbCore with no inflectional morphology
    (Mandarin is an isolating language). -/
structure MandarinVerbEntry extends VerbCore where
  deriving Repr, BEq

/-- Smart constructor: sets only the citation form (no inflection). -/
def MandarinVerbEntry.mk' (core : VerbCore) : MandarinVerbEntry :=
  { toVerbCore := core }

/-- 期待 "qidai" — look forward to (Class 1: positive, non-C-distributive, takes questions). -/
def qidai : MandarinVerbEntry := .mk' {
  form := "qidai"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.relevanceBased .positive)) }

/-- 担心 "danxin" — worry (Class 1: negative, non-C-distributive). -/
def danxin : MandarinVerbEntry := .mk' {
  form := "danxin"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased) }

/-- 希望 "xiwang" — hope (Class 3: positive, C-distributive, anti-rogative). -/
def xiwang : MandarinVerbEntry := .mk' {
  form := "xiwang"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 害怕 "haipa" — fear (Class 2: negative, C-distributive, takes questions). -/
def haipa : MandarinVerbEntry := .mk' {
  form := "haipa"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative)) }

/-!
## yǐwéi: Postsupposition via `postsupType`

yǐwéi "be under the impression" has a POSTSUPPOSITION
(output-context constraint) that ¬p is compatible with the Common Ground
after the utterance. This is NOT a presupposition and cannot be derived
from veridicality alone (@cite{glass-2025}, @cite{glass-2023}).

Encoded structurally as `postsupType := some .weakContrafactive` in VerbCore,
formalized as `Core.Postsupposition.weakContrafactive`, and exercised in
`Phenomena.Presupposition.Studies.Glass2025`.
-/

/-- 以为 "yǐwéi" — be under the impression that (weak contrafactive).

Has postsupposition ◇¬p (CG compatible with ¬p after utterance).
This cannot be derived from veridicality; see @cite{glass-2025} and @cite{glass-2023}.
The postsupposition is recorded structurally via `postsupType` and exercised
in `Phenomena.Presupposition.Studies.Glass2025`.
-/
def yiwei : MandarinVerbEntry := .mk' {
  form := "yiwei"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  postsupType := some .weakContrafactive }

def allVerbs : List MandarinVerbEntry := [qidai, danxin, xiwang, haipa, yiwei]

def lookup (form : String) : Option MandarinVerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Mandarin.Predicates
