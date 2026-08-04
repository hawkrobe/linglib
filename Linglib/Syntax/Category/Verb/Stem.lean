import Linglib.Semantics.Aspect.Basic

/-!
# Verb stem entries

`Verb.Stem` is the light form-level verb lexical entry: citation form,
lexically encoded viewpoint aspect, and gloss. It is the stem entry for
languages that lexicalize the perfective / imperfective contrast on verb
stems (Slavic canonically; cf. [svenonius-2004]), the base that
derivational morphology such as prefixation attaches to. The aspect
field records the dictionary-consensus value; analytical
reclassifications (e.g. [istratkova-2004]'s aspectless homogeneous
class) are study-level, never entry data.

Contrast `Verb.Root` (the lexical-semantic root) and the full semantic
`Verb` entry of `Syntax/Category/Verb/Defs.lean`; `Verb.Stem` carries no
semantics beyond its gloss.
-/

namespace Verb

open Semantics.Aspect (Perfectivity)

/-- A verb-stem lexical entry: citation form, lexically encoded
    perfectivity (the dictionary-consensus value), and gloss. -/
structure Stem where
  /-- Citation form. -/
  form   : String
  /-- Perfectivity (dictionary-consensus value). -/
  perfectivity : Perfectivity
  /-- English gloss. -/
  gloss  : String
  deriving DecidableEq, Repr

end Verb
