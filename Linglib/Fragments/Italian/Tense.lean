import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Theories.Semantics.Tense.ParticipantPerspective
import Linglib.Theories.Semantics.Tense.Kratzer

/-! # Italian Tense Fragment

Paradigm entries for Italian tense forms following the TAMEEntry and
TensePerspectiveEntry patterns from `Fragments/English/Tense.lean`.

## Italian Tense System

Italian distinguishes five core indicative tenses:

| Form               | Label            | EP          | UP      | Type         |
|--------------------|------------------|-------------|---------|--------------|
| passato prossimo   | present perfect  | downstream  | past    | periphrastic |
| passato remoto     | simple past      | downstream  | past    | synthetic    |
| imperfetto         | imperfect        | downstream  | past    | synthetic    |
| presente           | simple present   | downstream  | present | synthetic    |
| futuro semplice    | simple future    | unconstrained| future | synthetic    |

The passato prossimo / passato remoto distinction is significant:
both express past time reference, but they differ in morphological type
(periphrastic vs synthetic) and, following @cite{lakoff-1970}, in whether
they allow false-tense interpretations.

## Kratzer Decomposition

The passato prossimo (*ho mangiato*) parallels English present perfect:
PRESENT tense + PERFECT aspect. The auxiliary *avere*/*essere* makes the
PERF head morphologically transparent.
-/

namespace Fragments.Italian.Tense

open Semantics.Tense.Evidential
open Semantics.Tense.Kratzer
open Semantics.Tense
open Core.Tense
open Core.Morphology.Tense

-- ════════════════════════════════════════════════════════════════
-- § 1. TAMEEntry Instances
-- ════════════════════════════════════════════════════════════════

/-- Italian passato prossimo (present perfect): ho mangiato 'I have eaten'. @cite{lakoff-1970}
    EP downstream (T ≤ A), UP past (T < S). -/
def passatoProssimo : TAMEEntry where
  label := "passato prossimo"
  ep := .downstream
  up := .past

/-- Italian passato remoto (simple past/preterite): mangiai 'I ate'.
    EP downstream (T ≤ A), UP past (T < S). -/
def passatoRemoto : TAMEEntry where
  label := "passato remoto"
  ep := .downstream
  up := .past

/-- Italian imperfetto (imperfect): mangiavo 'I was eating / I used to eat'.
    EP downstream (T ≤ A), UP past (T < S). -/
def imperfetto : TAMEEntry where
  label := "imperfetto"
  ep := .downstream
  up := .past

/-- Italian presente (simple present): mangio 'I eat'.
    EP downstream (T ≤ A), UP present (T = S). -/
def presente : TAMEEntry where
  label := "presente"
  ep := .downstream
  up := .present

/-- Italian futuro semplice (simple future): mangerò 'I will eat'.
    EP unconstrained, UP future (S < T). -/
def futuroSemplice : TAMEEntry where
  label := "futuro semplice"
  ep := .unconstrained
  up := .future

/-- All Italian tense paradigm entries. -/
def allEntries : List TAMEEntry :=
  [passatoProssimo, passatoRemoto, imperfetto, presente, futuroSemplice]

-- ════════════════════════════════════════════════════════════════
-- § 2. TensePerspectiveEntry Instances (@cite{lakoff-1970})
-- ════════════════════════════════════════════════════════════════

/-- A tense paradigm entry enriched with Lakoff's perspective dimensions. -/
structure TensePerspectiveEntry extends TAMEEntry where
  /-- The grammatical tense this form realizes -/
  gramTense : GramTense
  /-- Synthetic (inflectional) or periphrastic (auxiliary-based) -/
  formType : TenseFormType

/-- Does this form allow false-tense interpretations?
    Derived from `formType`: only synthetic forms can. -/
def TensePerspectiveEntry.allowsFalseTense (e : TensePerspectiveEntry) : Bool :=
  e.formType == .synthetic

/-- Passato prossimo: past, periphrastic (avere/essere + past participle). -/
def passatoProssimoPerspective : TensePerspectiveEntry where
  label := "passato prossimo"
  ep := .downstream
  up := .past
  gramTense := .past
  formType := .periphrastic

/-- Passato remoto: past, synthetic. -/
def passatoRemotoPerspective : TensePerspectiveEntry where
  label := "passato remoto"
  ep := .downstream
  up := .past
  gramTense := .past
  formType := .synthetic

/-- Imperfetto: past, synthetic. -/
def imperfettoPerspective : TensePerspectiveEntry where
  label := "imperfetto"
  ep := .downstream
  up := .past
  gramTense := .past
  formType := .synthetic

/-- Presente: present, synthetic. -/
def presentePerspective : TensePerspectiveEntry where
  label := "presente"
  ep := .downstream
  up := .present
  gramTense := .present
  formType := .synthetic

/-- Futuro semplice: future, synthetic. -/
def futuroSemplicePerspective : TensePerspectiveEntry where
  label := "futuro semplice"
  ep := .unconstrained
  up := .future
  gramTense := .future
  formType := .synthetic

-- ════════════════════════════════════════════════════════════════
-- § 3. Perspective Entry Verification
-- ════════════════════════════════════════════════════════════════

/-- Synthetic forms allow false tense. -/
theorem passatoRemoto_allows_false : passatoRemotoPerspective.allowsFalseTense = true := by native_decide
theorem imperfetto_allows_false : imperfettoPerspective.allowsFalseTense = true := by native_decide
theorem presente_allows_false : presentePerspective.allowsFalseTense = true := by native_decide
theorem futuro_allows_false : futuroSemplicePerspective.allowsFalseTense = true := by native_decide

/-- Periphrastic forms block false tense. -/
theorem passatoProssimo_blocks_false : passatoProssimoPerspective.allowsFalseTense = false := by native_decide

/-- Passato prossimo and passato remoto: both past, different formType. -/
theorem prossimo_remoto_distinction :
    passatoProssimoPerspective.gramTense = passatoRemotoPerspective.gramTense ∧
    passatoProssimoPerspective.formType ≠ passatoRemotoPerspective.formType := by
  exact ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Kratzer Decomposition
-- ════════════════════════════════════════════════════════════════

/-- Italian passato prossimo: Kratzer decomposition.
    Surface "ho V-to" = PRESENT tense + PERFECT aspect.
    Parallel to English present perfect — the auxiliary *avere*/*essere*
    makes the PERF head morphologically transparent. -/
def kratzerPassatoProssimo : KratzerDecomposition where
  language := "Italian"
  surfaceForm := "avere/essere + V-to"
  tensePronoun := kratzerEnglishPast  -- Same underlying structure as English
  hasPerfect := true

/-- Italian passato prossimo can be deictic (from decomposition). -/
theorem kratzerPassatoProssimo_deictic :
    kratzerPassatoProssimo.canBeDeictic = true := rfl

/-- The underlying tense head is PRESENT, not PAST.
    Pastness comes from the PERF aspect head. -/
theorem kratzerPassatoProssimo_underlyingPresent :
    kratzerPassatoProssimo.tensePronoun.constraint = GramTense.present := rfl

/-- Italian passato prossimo shares the same underlying tense pronoun
    as English present perfect: both use `kratzerEnglishPast` (PRESENT
    tense head + indexical mode). The decomposition is PRESENT + PERFECT
    in both languages. -/
theorem italian_passatoProssimo_is_pres_perf :
    kratzerPassatoProssimo.tensePronoun = kratzerEnglishPast ∧
    kratzerPassatoProssimo.hasPerfect = true :=
  ⟨rfl, rfl⟩

end Fragments.Italian.Tense
