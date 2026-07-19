import Linglib.Semantics.Tense.Evidential
import Linglib.Semantics.Tense.SOT.Decomposition

/-! # Italian Tense Fragment

Paradigm entries for Italian tense forms following the TAMEEntry
pattern from `Fragments/English/Tense.lean`.

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
(periphrastic vs synthetic) and, following [lakoff-1970], in whether
they allow false-tense interpretations.

## Kratzer Decomposition

The passato prossimo (*ho mangiato*) parallels English present perfect:
PRESENT tense + PERFECT aspect. The auxiliary *avere*/*essere* makes the
PERF head morphologically transparent.
-/

open Time
open Tense

namespace Italian.Tense

open _root_.Tense.Evidential
open _root_.Tense.SOT.Decomposition
open _root_.Tense
open _root_.Tense

-- ════════════════════════════════════════════════════════════════
-- § 1. TAMEEntry Instances
-- ════════════════════════════════════════════════════════════════

/-- Italian passato prossimo (present perfect): ho mangiato 'I have eaten'. [lakoff-1970]
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

end Italian.Tense
