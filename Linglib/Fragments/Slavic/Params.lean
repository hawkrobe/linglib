import Linglib.Semantics.Aspect.Basic

/-!
# Shared Slavic Verbal-Lexicon Schema

Theory-light schema shared across the Slavic verbal-prefix fragments
(Russian, Polish, Bulgarian): the `VerbStem` lexical-entry type, with
aspect reused from `Semantics.Aspect.ViewpointAspectB`. `aspect := none`
encodes aspectless stems — Bulgarian's homogeneous simplex verbs, which
have no perfective counterparts and behave as imperfective only by
default ([istratkova-2004]).

Prefixes need no schema of their own: a Slavic verbal prefix is a
`Morphology.Morph` (`Morph.pref`), and fragments deliberately record
only its form — a prefix's meaning per occurrence is what the competing
analyses dispute (e.g. [svenonius-2004]'s lexical / superlexical split,
which lives in `Studies/Svenonius2004.lean`, never in fragment data).
-/

namespace Slavic

open Semantics.Aspect (ViewpointAspectB)

/-- A Slavic verb-stem lexical entry: citation form, viewpoint aspect
    (`none` = aspectless homogeneous simplex), and gloss. -/
structure VerbStem where
  /-- Citation form. -/
  form   : String
  /-- Viewpoint aspect; `none` for aspectless stems. -/
  aspect : Option ViewpointAspectB
  /-- English gloss. -/
  gloss  : String
  deriving DecidableEq, Repr

end Slavic
