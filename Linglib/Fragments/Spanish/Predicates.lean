import Linglib.Semantics.Verb.Basic
import Linglib.Syntax.Minimalist.Verbal.Decomposition

/-!
# Spanish Verb Entries for the Causative Alternation
[cuervo-2003] [munoz-perez-2026] [koontz-garboden-2009]

Verbs from Muñoz [munoz-perez-2026] classified by anticausative marking (SE)
and event-structural decomposition, extended with causer specification
from [koontz-garboden-2009].

## Anticausative Marking Types

- **Marked**: Anticausative requires SE (*quebrar* → *quebrarse*)
- **Unmarked**: No SE in anticausative (*mejorar* → *mejorar*)
- **Optional**: SE is marginal (*hervir* → *?hervirse*)

## Causer Specification ([koontz-garboden-2009] §§3.1–3.2)

The thematic specification of the causing participant determines
whether a verb can anticausativize:
- **EFFECTOR** (underspecified): causative admits agents, instruments,
  natural forces, events → anticausative available (*romper*, *abrir*)
- **AGENT** (specified): causative requires agentive causer →
  no anticausative, only reflexive (*asesinar*, *cortar*)

-/

namespace Spanish.Predicates

open Minimalist
open Semantics.Lexical
open Semantics.ArgumentStructure.EntailmentProfile

-- ============================================================================
-- § 1: Anticausative Marking
-- ============================================================================

/-- How an anticausative verb is morphologically marked in Spanish. -/
inductive AnticausativeMarking where
  | marked     -- Requires SE (quebrar → quebrarse)
  | unmarked   -- No SE (mejorar → mejorar)
  | optional   -- Marginal SE (hervir → ?hervirse)
  deriving DecidableEq, Repr

/-- Thematic specification of the participant in the causing subevent
    ([koontz-garboden-2009] §§2.1, 3.1–3.2).

    The critical distinction: EFFECTOR ([van-valin-wilkins-1996])
    is thematically underspecified — the causer can be an agent, instrument,
    natural force, or event. AGENT is thematically specified — the causer
    must be agentive (volitional, sentient).

    This determines anticausativizability: reflexivization of an EFFECTOR
    verb yields an anticausative reading; reflexivization of an AGENT verb
    yields only a reflexive reading. -/
inductive CauserSpec where
  /-- Underspecified causer: admits agents, instruments, natural forces,
      events. Spanish *romper*, *abrir*, *hundir*, *ahogar*. -/
  | effector
  /-- Agentive causer required. Spanish *asesinar*, *cortar*. -/
  | agent
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Verb Entry Structure
-- ============================================================================

/-- A Spanish verb with its causative alternation properties.

    Extends `Verb` with Spanish-specific fields for anticausative
    marking and event-structural decomposition. -/
structure SpanishVerbEntry extends Verb where
  /-- How the anticausative is marked -/
  anticausativeMarking : AnticausativeMarking
  /-- Participates in causative/anticausative alternation -/
  causativeAlternation : Bool
  /-- Cuervo's decomposition of the inchoative form -/
  verbHead : List VerbHead
  /-- Empirical: does this verb license stylistic LE? -/
  licensesStylLE : Bool
  /-- Thematic specification of the causing participant
      ([koontz-garboden-2009]). `none` for non-causative verbs. -/
  causerSpec : Option CauserSpec := none
  deriving Repr, BEq

-- ============================================================================
-- § 3: Verb Data (Muñoz [munoz-perez-2026])
-- ============================================================================

/-- *abrir* "open" — marked anticausative, licenses stylistic LE.
    EFFECTOR causer: admits agents, instruments, natural forces
    ([koontz-garboden-2009] exx. 47–49). -/
def abrir : SpanishVerbEntry :=
  { form := "abrir", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true, causerSpec := some .effector,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *romper* "break" — marked anticausative, licenses stylistic LE.
    EFFECTOR causer: agents, instruments, natural forces, events
    ([koontz-garboden-2009] exx. 13–17). -/
def romper : SpanishVerbEntry :=
  { form := "romper", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true, causerSpec := some .effector,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *hundir* "sink" — marked anticausative, licenses stylistic LE.
    EFFECTOR causer ([koontz-garboden-2009] ex. 46). -/
def hundir : SpanishVerbEntry :=
  { form := "hundir", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true, causerSpec := some .effector,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *caer* "fall" — marked anticausative, licenses stylistic LE.
    (ex. 9, unaccusative) -/
def caer : SpanishVerbEntry :=
  { form := "caer", frames := [],
    unaccusative := true,
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true }

/-- *morir* "die" — marked anticausative, licenses stylistic LE.
    (ex. 10) -/
def morir : SpanishVerbEntry :=
  { form := "morir", frames := [],
    unaccusative := true,
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true }

/-- *cerrar* "close" — marked anticausative; vehicle for the person-paradigm
    in [munoz-perez-2026] exx. 15–19 (*me/te le cerró la ventana* OK,
    *le/nos/les le cerró la ventana* unacceptable). -/
def cerrar : SpanishVerbEntry :=
  { form := "cerrar", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true }

/-- *quebrar* "crack" — marked anticausative, licenses stylistic LE.
    (exx. 38–39) -/
def quebrar : SpanishVerbEntry :=
  { form := "quebrar", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true }

/-- *hervir* "boil" — optional SE marking, but still licenses stylistic LE.
    (exx. 41–44) -/
def hervir : SpanishVerbEntry :=
  { form := "hervir", frames := [Frame.np],
    anticausativeMarking := .optional,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true }

/-- *olvidar* "forget" — marked anticausative, licenses stylistic LE.
    (ex. 11, psych verb) -/
def olvidar : SpanishVerbEntry :=
  { form := "olvidar", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true }

/-- *ocurrir* "occur" — marked anticausative, licenses stylistic LE.
    (ex. 12) -/
def ocurrir : SpanishVerbEntry :=
  { form := "ocurrir", frames := [],
    unaccusative := true,
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true }

/-- *mejorar* "improve" — UNMARKED anticausative, does NOT license stylistic LE.
    (ex. 40b *Me le mejoró el sueldo) -/
def mejorar : SpanishVerbEntry :=
  { form := "mejorar", frames := [Frame.np],
    anticausativeMarking := .unmarked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := false }

/-- *rasgar* "tear (gash-like)" — Levin 45.1 equivalent; marked anticausative.
    Unlike English *tear*, *rasgar* requires flimsy/insubstantial patients and
    implies unidirectional (linear, gash-like) separation. Incompatible with
    careful controlled action. [spalek-mcnally-2026] (§3.2). -/
def rasgar : SpanishVerbEntry :=
  { form := "rasgar", frames := [Frame.np],
    causative := some .make,
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := true,
    levinClass := some .break_,
    root := { profile := {
      forceMag := some [.low, .moderate]
      forceDir := some [.unidirectional]
      patientRob := some [.insubstantial, .flimsy]
      resultType := some [.separation, .surfaceBreach]
      agentControl := some [.incompatible, .neutral]
    } } }

/-- *asesinar* "assassinate" — AGENT causer required. No anticausative.
    Reflexivization yields reflexive reading only (*El senador se asesinó*
    = 'The senator killed himself'). [koontz-garboden-2009] exx. 24–29. -/
def asesinar : SpanishVerbEntry :=
  { form := "asesinar", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := false, causerSpec := some .agent,
    subjectEntailments := some accomplishmentSubjectProfile }

/-- *cortar* "cut" — AGENT causer required. No anticausative.
    [koontz-garboden-2009] ex. 26. -/
def cortar : SpanishVerbEntry :=
  { form := "cortar", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := false, causerSpec := some .agent,
    subjectEntailments := some accomplishmentSubjectProfile }

/-- *ahogar* "drown" — EFFECTOR causer, but animate theme undergoers
    are typical. Alternates: *ahogarse* is a derived inchoative.
    [koontz-garboden-2009] exx. 50–52. -/
def ahogar : SpanishVerbEntry :=
  { form := "ahogar", frames := [Frame.np],
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vCAUSE, .vGO, .vBE],
    licensesStylLE := false, causerSpec := some .effector,
    subjectEntailments := some ⟨false, false, true, false, true,
                                 false, false, false, false, false⟩ }

/-- *empeorar* "worsen" — internally caused COS verb. No CAUSE in LSR.
    Rejects *por sí solo*. [koontz-garboden-2009] ex. 65a. -/
def empeorar : SpanishVerbEntry :=
  { form := "empeorar", frames := [Frame.np],
    anticausativeMarking := .unmarked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := false }

/-- *crecer* "grow" — internally caused COS verb. No CAUSE in LSR.
    Rejects *por sí solo*. [koontz-garboden-2009] ex. 65c. -/
def crecer : SpanishVerbEntry :=
  { form := "crecer", frames := [],
    unaccusative := true,
    anticausativeMarking := .unmarked,
    causativeAlternation := false, verbHead := [.vGO, .vBE],
    licensesStylLE := false }

/-- Verbs from [munoz-perez-2026] — tested for stylistic LE. -/
def munozVerbs : List SpanishVerbEntry :=
  [abrir, romper, hundir, caer, morir, cerrar, quebrar, hervir, olvidar, ocurrir, mejorar, rasgar]

/-- Verbs from [koontz-garboden-2009] — causer specification data,
    not tested for stylistic LE. -/
def kgVerbs : List SpanishVerbEntry :=
  [asesinar, cortar, ahogar, empeorar, crecer]

/-- All verb entries in the fragment. -/
def allVerbs : List SpanishVerbEntry := munozVerbs ++ kgVerbs

-- ============================================================================
-- § 4: Per-Verb Verification
-- ============================================================================

theorem abrir_licenses_stylLE : abrir.licensesStylLE = true := rfl
theorem romper_licenses_stylLE : romper.licensesStylLE = true := rfl
theorem hundir_licenses_stylLE : hundir.licensesStylLE = true := rfl
theorem caer_licenses_stylLE : caer.licensesStylLE = true := rfl
theorem morir_licenses_stylLE : morir.licensesStylLE = true := rfl
theorem cerrar_licenses_stylLE : cerrar.licensesStylLE = true := rfl
theorem quebrar_licenses_stylLE : quebrar.licensesStylLE = true := rfl
theorem hervir_licenses_stylLE : hervir.licensesStylLE = true := rfl
theorem olvidar_licenses_stylLE : olvidar.licensesStylLE = true := rfl
theorem ocurrir_licenses_stylLE : ocurrir.licensesStylLE = true := rfl
theorem mejorar_blocks_stylLE : mejorar.licensesStylLE = false := rfl

-- ============================================================================
-- § 4b: Koontz-Garboden (2009) Alternation Predictions
-- ============================================================================

/-- EFFECTOR verbs anticausativize; AGENT verbs do not.
    [koontz-garboden-2009] §§3.1–3.2. -/
theorem effector_verbs_alternate :
    (allVerbs.filter (fun v => v.causerSpec == some .effector)).all
      (·.causativeAlternation) = true := by decide

theorem agent_verbs_dont_alternate :
    (allVerbs.filter (fun v => v.causerSpec == some .agent)).all
      (!·.causativeAlternation) = true := by decide

-- ============================================================================
-- § 4c: Muñoz-Pérez (2026) Stylistic LE
-- ============================================================================

/-- All Muñoz-Pérez verbs that license stylistic LE are inchoative. -/
theorem stylLE_verbs_are_inchoative :
    (munozVerbs.filter (·.licensesStylLE)).all
      (fun v => isInchoative v.verbHead) = true := by decide

/-- The only Muñoz-Pérez verb that blocks stylistic LE is unmarked. -/
theorem blocking_verb_is_unmarked :
    (munozVerbs.filter (!·.licensesStylLE)).all
      (fun v => v.anticausativeMarking == .unmarked) = true := by decide

end Spanish.Predicates
