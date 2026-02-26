import Linglib.Core.Empirical

/-!
# Stojković (2026): L-Participle Variation — Empirical Data

Theory-neutral empirical observations about the South Slavic L-participle.
The same morphological form (-l-) serves different grammatical functions
(past tense vs. evidential) across Serbian/Croatian and Bulgarian, depending
on its syntactic context (with or without an auxiliary).

## Cross-Linguistic Table

| Language | Context    | Function    | Example             |
|----------|------------|-------------|---------------------|
| SC       | AUX + L    | past tense  | Radio sam (I worked)|
| SC       | bare L     | unavailable | *Radio.             |
| BG       | AUX + L    | past tense  | Rabotil sam         |
| BG       | bare L     | evidential  | Rabotil             |

## Key Observation

The L-participle is morphologically identical across the two languages,
yet its interpretation depends on its syntactic environment. In SC,
the auxiliary + L combination yields a simple past; bare L is ungrammatical
as a main clause. In BG, auxiliary + L is past tense, while bare L
encodes indirect (evidential) meaning.

## References

- Stojković, S. (2026). L-participle variation in South Slavic.
-/

namespace Phenomena.TenseAspect.Studies.Stojkovic2026.Data

-- ════════════════════════════════════════════════════
-- § 1. Languages and Contexts
-- ════════════════════════════════════════════════════

/-- South Slavic languages in the study. -/
inductive SouthSlavicLang where
  | SC  -- Serbian/Croatian
  | BG  -- Bulgarian
  deriving DecidableEq, Repr, BEq

/-- Syntactic context for the L-participle. -/
inductive LPartContext where
  | auxPlusL  -- auxiliary + L-participle
  | bareL     -- bare L-participle (no auxiliary)
  deriving DecidableEq, Repr, BEq

/-- Grammatical function of the L-participle in context. -/
inductive LPartFunction where
  | pastTense    -- simple past tense
  | evidential   -- indirect/reportative evidential
  | unavailable  -- ungrammatical in this context
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Same-Form Datum
-- ════════════════════════════════════════════════════

/-- A single empirical observation: the L-participle in a given language
    and syntactic context has a particular grammatical function. -/
structure SameFormDatum where
  /-- The language -/
  lang : SouthSlavicLang
  /-- Syntactic context -/
  context : LPartContext
  /-- Observed grammatical function -/
  function : LPartFunction
  /-- The morphological form (always L-participle) -/
  form : String := "-l-"
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 3. Core Data Points
-- ════════════════════════════════════════════════════

/-- SC AUX + L = past tense. "Radio sam" (I worked). -/
def scAuxL : SameFormDatum where
  lang := .SC
  context := .auxPlusL
  function := .pastTense

/-- SC bare L = unavailable. *"Radio." is ungrammatical as a main clause. -/
def scBareL : SameFormDatum where
  lang := .SC
  context := .bareL
  function := .unavailable

/-- BG AUX + L = past tense. "Rabotil sam" (I worked). -/
def bgAuxL : SameFormDatum where
  lang := .BG
  context := .auxPlusL
  function := .pastTense

/-- BG bare L = evidential. "Rabotil" (reportedly, he worked). -/
def bgBareL : SameFormDatum where
  lang := .BG
  context := .bareL
  function := .evidential

/-- All four core data points. -/
def coreData : List SameFormDatum :=
  [scAuxL, scBareL, bgAuxL, bgBareL]

-- ════════════════════════════════════════════════════
-- § 4. Cross-Linguistic Generalizations
-- ════════════════════════════════════════════════════

/-- The morphological form is identical across all data points. -/
theorem same_form : coreData.map (·.form) = ["-l-", "-l-", "-l-", "-l-"] := rfl

/-- AUX + L yields past tense in both languages. -/
theorem aux_yields_past :
    scAuxL.function = .pastTense ∧ bgAuxL.function = .pastTense := ⟨rfl, rfl⟩

/-- The languages differ on bare L: SC unavailable, BG evidential. -/
theorem bare_l_diverges :
    scBareL.function = .unavailable ∧ bgBareL.function = .evidential := ⟨rfl, rfl⟩

end Phenomena.TenseAspect.Studies.Stojkovic2026.Data
