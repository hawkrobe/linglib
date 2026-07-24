import Linglib.Semantics.Aspect.Basic

/-!
# Shared Slavic Verbal-Lexicon Schema

Theory-light schema shared across the Slavic verbal-prefix fragments
(Russian, Polish, Bulgarian): the `VerbStem` lexical-entry type, with
aspect reused from `Semantics.Aspect.ViewpointAspectB`. The aspect field
records the dictionary-consensus value; analytical reinterpretations of
it (e.g. [istratkova-2004]'s claim that Bulgarian homogeneous simplexes
are aspectless, imperfective only by default) are study-level
classifications, not fragment data.

Prefixes need no schema of their own: a Slavic verbal prefix is a
`Morphology.Morph` (`Morph.pref`), and fragments deliberately record
only its form — a prefix's meaning per occurrence is what the competing
analyses dispute (e.g. [svenonius-2004]'s lexical / superlexical split,
which lives in `Studies/Svenonius2004.lean`, never in fragment data).
-/

namespace Slavic

open Semantics.Aspect (ViewpointAspectB)

/-- A Slavic verb-stem lexical entry: citation form, viewpoint aspect
    (the dictionary-consensus value), and gloss. -/
structure VerbStem where
  /-- Citation form. -/
  form   : String
  /-- Viewpoint aspect (dictionary-consensus value). -/
  aspect : ViewpointAspectB
  /-- English gloss. -/
  gloss  : String
  deriving DecidableEq, Repr

end Slavic
