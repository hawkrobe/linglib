import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Hungarian Predicate Lexicon Fragment

Hungarian attitude verb entries, extending `VerbCore` with the
Hungarian inflectional paradigm. Hungarian has a distinctive
**definite/indefinite conjugation** split: verbs agree not just with
the subject but also with the definiteness of the object.

## Definite vs Indefinite Conjugation

The conjugation type correlates with complement size (Egressy 2026):
- *hogy*-CP complements trigger **definite** conjugation
  (*tud-t-a* know-PST-3SG.DEF)
- Bare (small clause) complements allow **indefinite** conjugation
  (*tud-ott* know-PST.3SG.INDEF)

This morphological distinction provides independent evidence for the
structural size difference between *hogy*-CP and bare complements.

## Attitude Verbs

The three verbs formalized here are used in Egressy (2026) to
demonstrate size-sensitive SOT:
- *tud* 'know' — factive, doxastic veridical
- *mond* 'say' — speech-act verb
- *hisz* 'believe' — doxastic non-veridical

## References

- Egressy, A. (2026). Size-sensitive sequence of tense in Hungarian.
  *The Linguistic Review*.
-/

namespace Fragments.Hungarian.Predicates

open Core.Verbs

/-- Hungarian verb entry: extends VerbCore with the definite/indefinite
    conjugation paradigm. -/
structure HungarianVerbEntry extends VerbCore where
  /-- English gloss -/
  gloss : String
  /-- 3sg present definite conjugation -/
  formPresDef : String
  /-- 3sg present indefinite conjugation -/
  formPresIndef : String
  /-- 3sg past definite conjugation -/
  formPastDef : String
  /-- 3sg past indefinite conjugation -/
  formPastIndef : String
  deriving Repr, BEq


-- ════════════════════════════════════════════════════════════════
-- § Attitude Verbs (Egressy 2026)
-- ════════════════════════════════════════════════════════════════

/-- *tud* 'know' — factive doxastic attitude verb.
    Egressy (2026), exx. (9)–(10): key verb for the size-sensitive SOT contrast.
    Selects both *hogy*-CP (definite conj.) and bare complement (indefinite conj.). -/
def tud : HungarianVerbEntry where
  form := "tud"
  gloss := "know"
  formPresDef := "tudja"
  formPresIndef := "tud"
  formPastDef := "tudta"
  formPastIndef := "tudott"
  complementType := .finiteClause
  altComplementType := some .smallClause
  subjectTheta := some .experiencer
  factivePresup := true
  presupType := some .softTrigger
  attitudeBuilder := some (.doxastic .veridical)
  takesQuestionBase := true
  complementSig := some .mono

/-- *mond* 'say' — speech-act verb.
    Egressy (2026), ex. (11a): extends SOT pattern to communication verbs.
    Selects *hogy*-CP (definite conj.); no bare complement frame. -/
def mond : HungarianVerbEntry where
  form := "mond"
  gloss := "say"
  formPresDef := "mondja"
  formPresIndef := "mond"
  formPastDef := "mondta"
  formPastIndef := "mondott"
  complementType := .finiteClause
  speechActVerb := true
  levinClass := some .say

/-- *hisz* 'believe' — doxastic non-veridical attitude verb.
    Egressy (2026), ex. (11b): extends SOT pattern to belief verbs.
    Selects *hogy*-CP (definite conj.); no bare complement frame. -/
def hisz : HungarianVerbEntry where
  form := "hisz"
  gloss := "believe"
  formPresDef := "hiszi"
  formPresIndef := "hisz"
  formPastDef := "hitte"
  formPastIndef := "hitt"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  opaqueContext := true
  attitudeBuilder := some (.doxastic .nonVeridical)
  complementSig := some .mono

/-- All Hungarian verb entries. -/
def allEntries : List HungarianVerbEntry := [tud, mond, hisz]


-- ════════════════════════════════════════════════════════════════
-- § Definite/Indefinite Conjugation Diagnostics
-- ════════════════════════════════════════════════════════════════

/-- Whether a verb form is in the definite conjugation.
    Used as a clause-size diagnostic (Egressy 2026, §5):
    definite conjugation → CP complement (*hogy*-clause). -/
def HungarianVerbEntry.pastDefForm (v : HungarianVerbEntry) : String :=
  v.formPastDef

/-- Whether a verb form is in the indefinite conjugation.
    Indefinite conjugation correlates with smaller complement size. -/
def HungarianVerbEntry.pastIndefForm (v : HungarianVerbEntry) : String :=
  v.formPastIndef

/-- The definite and indefinite past forms are distinct for all verbs. -/
theorem def_indef_distinct :
    ∀ v ∈ allEntries, v.formPastDef ≠ v.formPastIndef := by
  intro v hv
  simp only [allEntries, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> simp [tud, mond, hisz]


end Fragments.Hungarian.Predicates
