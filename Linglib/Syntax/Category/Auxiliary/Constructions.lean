/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# The inflectional patterns of auxiliary verb constructions

An auxiliary verb construction pairs an auxiliary with a lexical verb, and
languages differ in which of the two carries the inflection. The lexical
verb is the semantic head whichever way that goes, and it is exactly that
mismatch between where the content sits and where the inflection sits that
makes the constructions typologically distinctive.

Five macro-patterns exhaust the possibilities: the auxiliary hosts the
inflection, the lexical verb does, both carry the same categories, the
categories divide between them, or they divide with some doubled. Which
categories land where is finer-grained than the pattern and is recorded by
the analysis that needs it, as in `Studies/Anderson2006.lean`.

## References

* [anderson-2006], §1.4, chs. 2-5
-/

namespace AuxiliaryVerbs

/-- The five inflectional patterns of auxiliary verb constructions. -/
inductive InflectionPattern where
  /-- The auxiliary hosts the inflection and the lexical verb is nonfinite:
      English *have eaten*, French *va manger*. -/
  | auxHeaded
  /-- The lexical verb hosts the inflection and the auxiliary is
      grammaticalized: Pipil *weli ni-nehnemi*. -/
  | lexHeaded
  /-- Both elements carry the same categories: Gorum *miŋ ne-gaʔ-ru
      ne-laʔ-ru*, subject and TAM on each. -/
  | doubled
  /-- The categories divide between the elements with no overlap: Jakaltek
      *šk-ach w-ila*, absolutive on the auxiliary and ergative on the
      lexical verb. -/
  | split
  /-- The categories divide, but some are carried by both elements.
      [anderson-2006] ch. 5 §5.2 gives thirty-odd exemplars, so this is a
      common pattern rather than a marginal one. -/
  | splitDoubled
  deriving DecidableEq, Repr, Inhabited

end AuxiliaryVerbs
