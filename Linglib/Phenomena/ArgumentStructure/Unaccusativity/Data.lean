/-
Note: This file intentionally has no imports beyond Lean's Prelude.
All types here (String, Bool) are built-in. This keeps the diagnostic
data fully theory-neutral.
-/

/-!
# Unaccusativity Diagnostic Data

Theory-neutral empirical data on unaccusativity diagnostics.

## Diagnostics

- **Quotative inversion** (QI): "whispered Mary" vs *"spoke Mary" (Storment 2026, NLLT)
- **There-insertion**: "there arrived a letter" vs *"there ran a man"
- **Locative inversion**: "into the room walked a man"
- **Resultative predication**: "the river froze solid" vs *"John ran tired"
- **Auxiliary selection**: Italian *è arrivato* (be) vs *ha dormito* (have)

## References

- Perlmutter, D. (1978). Impersonal passives and the Unaccusative Hypothesis.
- Burzio, L. (1986). Italian Syntax.
- Levin, B. & Rappaport Hovav, M. (1995). Unaccusativity.
- Storment, J. (2026). Quotative inversion as an unaccusativity diagnostic. NLLT.
-/

namespace Phenomena.ArgumentStructure.Unaccusativity.Data

/-- Syntactic diagnostics for unaccusativity. -/
inductive Diagnostic where
  | quotativeInversion       -- "whispered Mary" / *"spoke Mary"
  | thereInsertion           -- "there arrived a letter" / *"there ran a man"
  | locativeInversion        -- "into the room walked a man"
  | resultativePredication   -- "the river froze solid"
  | auxiliarySelection       -- Italian essere/avere split
  deriving DecidableEq, Repr, BEq

/-- Result of applying a diagnostic to a verb. -/
inductive DiagnosticResult where
  | passes    -- Verb behaves as unaccusative on this diagnostic
  | fails     -- Verb behaves as unergative/transitive
  | marginal  -- Intermediate or speaker-variable judgment
  deriving DecidableEq, Repr, BEq

/-- A single diagnostic judgment. -/
structure DiagnosticDatum where
  verbForm : String
  diagnostic : Diagnostic
  result : DiagnosticResult
  sentence : String
  note : String := ""
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § Quotative Inversion Data (Storment 2026)
-- ════════════════════════════════════════════════════

def qi_whisper : DiagnosticDatum :=
  { verbForm := "whisper"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"I'm tired,\" whispered Mary." }

def qi_murmur : DiagnosticDatum :=
  { verbForm := "murmur"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"It's cold,\" murmured the child." }

def qi_shout : DiagnosticDatum :=
  { verbForm := "shout"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Watch out!\" shouted the guard." }

def qi_cry : DiagnosticDatum :=
  { verbForm := "cry"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Help!\" cried the sailor." }

def qi_scream : DiagnosticDatum :=
  { verbForm := "scream"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"No!\" screamed the witness." }

def qi_speak : DiagnosticDatum :=
  { verbForm := "speak"
  , diagnostic := .quotativeInversion
  , result := .fails
  , sentence := "*\"Hello,\" spoke Mary." }

def qi_talk : DiagnosticDatum :=
  { verbForm := "talk"
  , diagnostic := .quotativeInversion
  , result := .fails
  , sentence := "*\"Hello,\" talked Mary." }

/-- `say` passes QI but its VerbEntry captures the transitive
    indirect-speech frame ("John said that..."), not the intransitive QI frame.
    This is the unmarked/lexicalized quotative — an edge case. -/
def qi_say : DiagnosticDatum :=
  { verbForm := "say"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"I'm tired,\" said Mary."
  , note := "say is the unmarked/lexicalized quotative; its VerbEntry captures the transitive indirect-speech frame (\"John said that...\"), not the intransitive QI frame" }

-- ════════════════════════════════════════════════════
-- § There-Insertion Data
-- ════════════════════════════════════════════════════

def there_arrive : DiagnosticDatum :=
  { verbForm := "arrive"
  , diagnostic := .thereInsertion
  , result := .passes
  , sentence := "There arrived a letter for you." }

def there_run : DiagnosticDatum :=
  { verbForm := "run"
  , diagnostic := .thereInsertion
  , result := .fails
  , sentence := "*There ran a man down the street." }

def there_sleep : DiagnosticDatum :=
  { verbForm := "sleep"
  , diagnostic := .thereInsertion
  , result := .fails
  , sentence := "*There slept a child in the bed." }

-- ════════════════════════════════════════════════════
-- § Locative Inversion Data
-- ════════════════════════════════════════════════════

def loc_arrive : DiagnosticDatum :=
  { verbForm := "arrive"
  , diagnostic := .locativeInversion
  , result := .passes
  , sentence := "Into the room arrived a messenger." }

def loc_whisper : DiagnosticDatum :=
  { verbForm := "whisper"
  , diagnostic := .locativeInversion
  , result := .marginal
  , sentence := "?From the back of the room whispered a voice."
  , note := "MoS verbs show variable acceptability in locative inversion" }

/-- All diagnostic data points. -/
def allData : List DiagnosticDatum :=
  [ qi_whisper, qi_murmur, qi_shout, qi_cry, qi_scream
  , qi_speak, qi_talk, qi_say
  , there_arrive, there_run, there_sleep
  , loc_arrive, loc_whisper ]

end Phenomena.ArgumentStructure.Unaccusativity.Data
