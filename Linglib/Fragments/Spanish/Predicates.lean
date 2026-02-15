import Linglib.Core.Verbs
import Linglib.Theories.Minimalism.Core.Applicative

/-!
# Spanish Verb Entries for the Causative Alternation

Verbs from Muñoz Pérez (2026) classified by anticausative marking (SE)
and event-structural decomposition (Cuervo 2003). The key empirical
generalization: stylistic LE is licensed only by verbs with inchoative
structure (vGO ∧ vBE) that require SE-marking.

## Anticausative Marking Types

- **Marked**: Anticausative requires SE (*quebrar* → *quebrarse*)
- **Unmarked**: No SE in anticausative (*mejorar* → *mejorar*)
- **Optional**: SE is marginal (*hervir* → *?hervirse*)

## References

- Muñoz Pérez, C. (2026). Stylistic applicatives. *Glossa* 11(1).
- Cuervo, M. C. (2003). Datives at Large. MIT.
-/

namespace Fragments.Spanish.Predicates

open Minimalism
open Core.Verbs

-- ============================================================================
-- § 1: Anticausative Marking
-- ============================================================================

/-- How an anticausative verb is morphologically marked in Spanish. -/
inductive AnticausativeMarking where
  | marked     -- Requires SE (quebrar → quebrarse)
  | unmarked   -- No SE (mejorar → mejorar)
  | optional   -- Marginal SE (hervir → ?hervirse)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Verb Entry Structure
-- ============================================================================

/-- A Spanish verb with its causative alternation properties.

    Extends `VerbCore` with Spanish-specific fields for anticausative
    marking and event-structural decomposition (Cuervo 2003). -/
structure SpanishVerbEntry extends VerbCore where
  /-- How the anticausative is marked -/
  anticausativeMarking : AnticausativeMarking
  /-- Participates in causative/anticausative alternation -/
  causativeAlternation : Bool
  /-- Cuervo's decomposition of the inchoative form -/
  verbHead : List VerbHead
  /-- Empirical: does this verb license stylistic LE? -/
  licensesStylLE : Bool
  deriving Repr, BEq

-- ============================================================================
-- § 3: Verb Data (Muñoz Pérez 2026)
-- ============================================================================

/-- *abrir* "open" — marked anticausative, licenses stylistic LE. -/
def abrir : SpanishVerbEntry :=
  { form := "abrir", verbClass := .causative, complementType := .np,
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *romper* "break" — marked anticausative, licenses stylistic LE.
    (exx. 7–8 in Muñoz Pérez 2026) -/
def romper : SpanishVerbEntry :=
  { form := "romper", verbClass := .causative, complementType := .np,
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *hundir* "sink" — marked anticausative, licenses stylistic LE.
    (exx. 9–10) -/
def hundir : SpanishVerbEntry :=
  { form := "hundir", verbClass := .causative, complementType := .np,
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *caer* "fall" — marked anticausative, licenses stylistic LE.
    (exx. 11–12, unaccusative) -/
def caer : SpanishVerbEntry :=
  { form := "caer", verbClass := .simple, complementType := .none,
    unaccusative := true,
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *morir* "die" — marked anticausative, licenses stylistic LE.
    (exx. 13–14) -/
def morir : SpanishVerbEntry :=
  { form := "morir", verbClass := .simple, complementType := .none,
    unaccusative := true,
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *quebrar* "crack" — marked anticausative, licenses stylistic LE.
    (ex. 39a) -/
def quebrar : SpanishVerbEntry :=
  { form := "quebrar", verbClass := .causative, complementType := .np,
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *hervir* "boil" — optional SE marking, but still licenses stylistic LE.
    (ex. 40) -/
def hervir : SpanishVerbEntry :=
  { form := "hervir", verbClass := .causative, complementType := .np,
    anticausativeMarking := .optional,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *olvidar* "forget" — marked anticausative, licenses stylistic LE.
    (exx. 15–16, psych verb) -/
def olvidar : SpanishVerbEntry :=
  { form := "olvidar", verbClass := .simple, complementType := .np,
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *ocurrir* "occur" — marked anticausative, licenses stylistic LE.
    (exx. 17–18) -/
def ocurrir : SpanishVerbEntry :=
  { form := "ocurrir", verbClass := .simple, complementType := .none,
    unaccusative := true,
    anticausativeMarking := .marked,
    causativeAlternation := false, verbHead := [.vGO, .vBE],
    licensesStylLE := true }

/-- *mejorar* "improve" — UNMARKED anticausative, does NOT license stylistic LE.
    (ex. 39b) -/
def mejorar : SpanishVerbEntry :=
  { form := "mejorar", verbClass := .causative, complementType := .np,
    anticausativeMarking := .unmarked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := false }

/-- *rasgar* "tear (gash-like)" — Levin 45.1 equivalent; marked anticausative.
    Unlike English *tear*, *rasgar* requires flimsy/insubstantial patients and
    implies unidirectional (linear, gash-like) separation. Incompatible with
    careful controlled action. Spalek & McNally (forthcoming, §3.2). -/
def rasgar : SpanishVerbEntry :=
  { form := "rasgar", verbClass := .causative, complementType := .np,
    causativeBuilder := some .make,
    anticausativeMarking := .marked,
    causativeAlternation := true, verbHead := [.vGO, .vBE],
    licensesStylLE := true,
    levinClass := some .break_,
    rootProfile := some {
      forceMag := some [.low, .moderate]
      forceDir := some [.unidirectional]
      patientRob := some [.insubstantial, .flimsy]
      resultType := some [.separation, .surfaceBreach]
      agentControl := some [.incompatible, .neutral]
    } }

/-- All verb entries in the fragment. -/
def allVerbs : List SpanishVerbEntry :=
  [abrir, romper, hundir, caer, morir, quebrar, hervir, olvidar, ocurrir, mejorar,
   rasgar]

-- ============================================================================
-- § 4: Per-Verb Verification
-- ============================================================================

theorem abrir_licenses_stylLE : abrir.licensesStylLE = true := rfl
theorem romper_licenses_stylLE : romper.licensesStylLE = true := rfl
theorem hundir_licenses_stylLE : hundir.licensesStylLE = true := rfl
theorem caer_licenses_stylLE : caer.licensesStylLE = true := rfl
theorem morir_licenses_stylLE : morir.licensesStylLE = true := rfl
theorem quebrar_licenses_stylLE : quebrar.licensesStylLE = true := rfl
theorem hervir_licenses_stylLE : hervir.licensesStylLE = true := rfl
theorem olvidar_licenses_stylLE : olvidar.licensesStylLE = true := rfl
theorem ocurrir_licenses_stylLE : ocurrir.licensesStylLE = true := rfl
theorem mejorar_blocks_stylLE : mejorar.licensesStylLE = false := rfl

/-- All verbs that license stylistic LE are inchoative. -/
theorem stylLE_verbs_are_inchoative :
    (allVerbs.filter (·.licensesStylLE)).all
      (fun v => isInchoative v.verbHead) = true := by native_decide

/-- The only verb that blocks stylistic LE is unmarked. -/
theorem blocking_verb_is_unmarked :
    (allVerbs.filter (!·.licensesStylLE)).all
      (fun v => v.anticausativeMarking == .unmarked) = true := by native_decide

end Fragments.Spanish.Predicates
