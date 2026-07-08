import Linglib.Semantics.Verb.Basic

/-!
# Hungarian Predicate Lexicon Fragment
[kiss-2002]

Hungarian matrix predicates that embed finite *hogy*-clauses, extending `Verb`
with the Hungarian inflectional paradigm. The verbs here are the perception,
cognition, and communication predicates used in [egressy-2026]'s study of
sequence of tense (see `Studies.Egressy2026`).

## Definite vs indefinite conjugation

Hungarian verbs agree not just with the subject but with the definiteness of
the object: a definite object (including a clause whose accusative expletive
*az-t* 'it' is present) triggers **definite** conjugation (*tud-t-a*
know-PST-3SG.DF), an indefinite object the **indefinite** conjugation
(*tud-ott* know-PST.3SG.INDF) ([kiss-2002]). This is object agreement, not a
clause-size diagnostic.

## Clause type is not a verb property

A central point of [egressy-2026] is that whether a complement is
*speech-reporting* (encodes the content of a verbal/representational sign) or
*non-speech-reporting* (perception, dreaming, belief) is a property of the
*clause*, not of the matrix verb: perception verbs like *hall* 'hear' and
cognition verbs like *gondol* 'think' embed either type. So this fragment
records only general lexical class (perception / communication / attitude); the
clause-type analysis lives in `Studies.Egressy2026`.
-/

namespace Hungarian.Predicates

open ArgumentStructure

/-- Hungarian verb entry: extends `Verb` with the definite/indefinite
    conjugation paradigm. Conjugation fields default to `""` (unspecified)
    for entries whose paradigm is not needed here. -/
structure HungarianVerbEntry extends Verb where
  /-- English gloss -/
  gloss : String
  /-- 3sg present definite conjugation -/
  formPresDef : String := ""
  /-- 3sg present indefinite conjugation -/
  formPresIndef : String := ""
  /-- 3sg past definite conjugation -/
  formPastDef : String := ""
  /-- 3sg past indefinite conjugation -/
  formPastIndef : String := ""
  deriving Repr, BEq


-- ════════════════════════════════════════════════════════════════
-- § Perception verbs (embed non-speech-reporting clauses)
-- ════════════════════════════════════════════════════════════════

/-- *lát* 'see' — perception verb ([egressy-2026], exx. (4), (16)).
    With direct perception its complement is non-speech-reporting. -/
def lat : HungarianVerbEntry where
  form := "lát"
  gloss := "see"
  formPresDef := "látja"
  formPresIndef := "lát"
  formPastDef := "látta"
  formPastIndef := "látott"
  frames := [Frame.finiteClause]
  levinClass := some .see

/-- *hall* 'hear' — perception verb ([egressy-2026], exx. (5), (13), (17)).
    Takes a non-speech-reporting complement (perceiving an event) *or* a
    speech-reporting one (hearing a verbal report). -/
def hall : HungarianVerbEntry where
  form := "hall"
  gloss := "hear"
  formPresDef := "hallja"
  formPresIndef := "hall"
  formPastDef := "hallotta"
  formPastIndef := "hallott"
  frames := [Frame.finiteClause]
  levinClass := some .see

/-- *álmodik* 'dream' — perception-in-a-dream ([egressy-2026], exx. (6), (10)).
    Non-speech-reporting complement. -/
def almodik : HungarianVerbEntry where
  form := "álmodik"
  gloss := "dream"
  frames := [Frame.finiteClause]


-- ════════════════════════════════════════════════════════════════
-- § Cognition / attitude verbs (embed non-speech-reporting clauses)
-- ════════════════════════════════════════════════════════════════

/-- *gondol* 'think' — doxastic attitude verb ([egressy-2026], ex. (7)). -/
def gondol : HungarianVerbEntry where
  form := "gondol"
  gloss := "think"
  formPresDef := "gondolja"
  formPresIndef := "gondol"
  formPastDef := "gondolta"
  formPastIndef := "gondolt"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono

/-- *hisz* 'believe' — doxastic non-veridical attitude verb
    ([egressy-2026], ex. (7)). -/
def hisz : HungarianVerbEntry where
  form := "hisz"
  gloss := "believe"
  formPresDef := "hiszi"
  formPresIndef := "hisz"
  formPastDef := "hitte"
  formPastIndef := "hitt"
  frames := [Frame.finiteClause]
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono

/-- *tud* 'know' — factive doxastic veridical attitude verb. -/
def tud : HungarianVerbEntry where
  form := "tud"
  gloss := "know"
  formPresDef := "tudja"
  formPresIndef := "tud"
  formPastDef := "tudta"
  formPastIndef := "tudott"
  frames := [Frame.finiteClause]
  presupType := some .softTrigger
  attitude := some (.doxastic .veridical)
  takesQuestionBase := true
  complementSig := some .mono

/-- *aggaszt* 'worry' — subject-experiencer psych verb taking a subject clause
    ([egressy-2026], ex. (8)). Embeds a non-speech-reporting clause. -/
def aggaszt : HungarianVerbEntry where
  form := "aggaszt"
  gloss := "worry"
  frames := [Frame.finiteClause]


-- ════════════════════════════════════════════════════════════════
-- § Communication verbs (embed speech-reporting clauses)
-- ════════════════════════════════════════════════════════════════

/-- *mond* 'say' — speech verb ([egressy-2026], ex. (11a)). -/
def mond : HungarianVerbEntry where
  form := "mond"
  gloss := "say"
  formPresDef := "mondja"
  formPresIndef := "mond"
  formPastDef := "mondta"
  formPastIndef := "mondott"
  frames := [Frame.finiteClause]
  speechActVerb := true
  levinClass := some .say

/-- *rikolt* 'shout' — manner-of-speaking verb ([egressy-2026], ex. (11)). -/
def rikolt : HungarianVerbEntry where
  form := "rikolt"
  gloss := "shout"
  frames := [Frame.finiteClause]
  speechActVerb := true
  levinClass := some .mannerOfSpeaking

/-- *morog* 'growl' — manner-of-speaking verb ([egressy-2026], exx. (9), (11)).
    With a speech-reporting complement it reports the words growled; with a
    non-speech-reporting adjunct it gives the reason for growling (ex. (9)). -/
def morog : HungarianVerbEntry where
  form := "morog"
  gloss := "growl"
  frames := [Frame.finiteClause]
  speechActVerb := true
  levinClass := some .mannerOfSpeaking


-- ════════════════════════════════════════════════════════════════
-- § Collections
-- ════════════════════════════════════════════════════════════════

/-- All Hungarian verb entries from [egressy-2026]. -/
def allEntries : List HungarianVerbEntry :=
  [lat, hall, almodik, gondol, hisz, tud, aggaszt, mond, rikolt, morog]

/-- Entries whose full definite/indefinite past paradigm is recorded. -/
def conjugatedEntries : List HungarianVerbEntry :=
  [lat, hall, gondol, hisz, tud, mond]

/-- The definite and indefinite past forms are distinct for every verb whose
    paradigm is recorded — the object-agreement contrast [kiss-2002]. -/
theorem def_indef_distinct :
    ∀ v ∈ conjugatedEntries, v.formPastDef ≠ v.formPastIndef := by
  intro v hv
  simp only [conjugatedEntries, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [lat, hall, gondol, hisz, tud, mond]


end Hungarian.Predicates
