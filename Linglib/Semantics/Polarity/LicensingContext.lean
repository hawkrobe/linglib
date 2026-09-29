module

public import Mathlib.Tactic.DeriveFintype

/-!
# Licensing contexts

The environments whose strength of negation decides where a polarity item may occur: clausal
negation, the downward-entailing quantifiers, the antecedent of a conditional, the connectives
*before*, *without* and *too … to*, the Strawson-downward-entailing operators, the comparatives,
and the questions and generic contexts that license free choice. The type is observational: its
23 cases name surface constructions, and the strength, mechanism and signature each is assigned
are the theory of `Semantics/Polarity/Licensing.lean`, so the typology of indefinite series in
`Semantics/Quantification/Indefinite.lean` can import the environments without the licensing
theory. The cases follow the English tradition from [ladusaw-1979] on; a language whose licensing
environments cut differently, as by [giannakidou-1998]'s veridicality, is not represented.

## References

* [ladusaw-1979]
* [kadmon-landman-1993]
* [giannakidou-1998]
-/

@[expose] public section

namespace PolarityItem

/-- The environments that can license a polarity-sensitive item. -/
inductive LicensingContext where
  /-- Clausal negation, as in *not*. -/
  | negation
  /-- A negative quantifier, as in *nobody*, *nothing*. -/
  | nobody
  /-- *Few* NP. -/
  | few
  /-- *At most n* NP. -/
  | atMost
  /-- The antecedent of a conditional. -/
  | conditionalAntecedent
  /-- A *before*-clause. -/
  | beforeClause
  /-- A *without*-phrase. -/
  | withoutClause
  /-- The scope of focus *only*. -/
  | onlyFocus
  /-- A question. -/
  | question
  /-- A phrasal comparative, *taller than NP*, on its genuine NP reading. -/
  | phrasalComparative
  /-- A clausal comparative, *taller than S*, including the surface *than NP* that reduces to
  one. -/
  | clausalComparative
  /-- A superlative. -/
  | superlative
  /-- *Too* ADJ *to* VP. -/
  | tooTo
  /-- A possibility modal. -/
  | modalPossibility
  /-- A necessity modal. -/
  | modalNecessity
  /-- An imperative. -/
  | imperative
  /-- A generic sentence. -/
  | generic
  /-- An adversative predicate, as in *sorry*, *surprised*, *regret*. -/
  | adversative
  /-- Temporal *since*, as in *it's been five years since*. -/
  | sinceTemporal
  /-- A free relative, as in *whatever*, *whoever*. -/
  | freeRelative
  /-- The restrictor of a universal, as in *everyone who*. -/
  | universalRestrictor
  /-- A verb of doubting, as in *I doubt that*. -/
  | doubtVerb
  /-- A verb of denying, as in *she denied that*. -/
  | denyVerb
  deriving DecidableEq, Fintype, Repr

end PolarityItem
