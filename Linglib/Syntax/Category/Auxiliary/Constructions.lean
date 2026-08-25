/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Auxiliary verb constructions: the inflectional patterns

An auxiliary verb construction pairs an auxiliary with a lexical verb, and
languages differ in which of the two carries the inflection. The lexical
verb is the semantic head whichever way that goes, and it is exactly that
mismatch between where the content sits and where the inflection sits that
makes the constructions typologically distinctive.

Five macro-patterns exhaust the possibilities: the auxiliary hosts the
inflection, the lexical verb does, both carry the same categories, the
categories divide between them, or they divide with some doubled.

## Main definitions

* `InflPattern` — the five patterns.
* `AVCElement` — which element of a construction bears a property.
* `InflPattern.inflHost` — the element hosting inflection.

## References

* [anderson-2006], §1.4, chs. 2-5
-/

namespace AuxiliaryVerbs

/-- Which element of an auxiliary verb construction bears a property. -/
inductive AVCElement where
  | aux
  | lex
  | both
  deriving DecidableEq, Repr

/-- The five inflectional patterns of auxiliary verb constructions. -/
inductive InflPattern where
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

/-- The element hosting inflection. The three patterns that put material on
both elements are distinguished by *which* categories go where, not by the
host, so they share a value here. -/
def InflPattern.inflHost : InflPattern → AVCElement
  | .auxHeaded => .aux
  | .lexHeaded => .lex
  | .doubled | .split | .splitDoubled => .both

/-- The inflectional host is the lexical verb — the element that is the
semantic head anyway — only in the lex-headed pattern. -/
theorem inflHost_eq_lex_iff (p : InflPattern) :
    p.inflHost = .lex ↔ p = .lexHeaded := by
  cases p <;> simp [InflPattern.inflHost]

end AuxiliaryVerbs
