/-!
# Form-Meaning Mapping Phenomena
@cite{kalin-bjorkman-etal-2026}

§4 of @cite{kalin-bjorkman-etal-2026} identifies seven descriptive types
of form-meaning mapping — the relationships between phonological exponents
and morphosyntactic features/functions.

These seven types are theory-neutral descriptive categories: any theory
of morphology must account for them (whether by generating them directly,
reanalyzing them, or invoking extra mechanisms).
-/

namespace Core.Morphology.FormMeaningMapping

/-- The seven descriptive types of form-meaning mapping.
    @cite{kalin-bjorkman-etal-2026} §4. -/
inductive MappingType where
  /-- One meaning/function ↔ one exponent, invariant.
      Example: root *cat* is always `\/kæt\/`. -/
  | oneToOne
  /-- One meaning/function → multiple *competing* exponents
      (context-sensitive selection).
      Example: English plural *-z, -s, -ɪz, -ən, ∅*. §4.1. -/
  | allomorphy
  /-- One meaning/function → multiple *co-occurring* exponents
      (non-competing, simultaneous expression).
      Example: Amharic *k'al-at-otʃtʃ* 'words' (two plural markers). §4.2. -/
  | multipleExponence
  /-- Multiple related meanings/functions → one exponent
      (non-co-occurring contexts share a form).
      Example: English *-ed* for past tense and past participle. §4.3. -/
  | syncretism
  /-- Multiple co-occurring meanings/functions → one exponent
      (bundled into a single form).
      Example: French *du* = *de* + *le*. §4.4. -/
  | portmanteau
  /-- A meaning/function has no corresponding form — the paradigm
      cell is empty.
      Example: English *stride* lacks a standard past participle. §4.5.1. -/
  | morphologicalGap
  /-- A form has no corresponding meaning/function.
      Example: Romance theme vowels, compound linkers. §4.5.2. -/
  | emptyMorph
  deriving DecidableEq, Repr

end Core.Morphology.FormMeaningMapping
