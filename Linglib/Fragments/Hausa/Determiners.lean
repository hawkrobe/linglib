/-!
# Hausa determiner inventory

Textbook-consensus types for the Hausa (Chadic) determiner system, with
no analytical denotations. Sources: [newman-2000] §17.5, §20, §21
and [jaggar-2001] §9.5, §12.3. Paper-specific denotations (Q_∀ +
ONE decomposition, choice-function vs. ∃-quantifier analysis of *wani*,
etc.) live in Studies files that consume these entries.

## Main declarations

* `Hausa.UniversalQuantifier` — the two
  morphologically distinct Hausa universal quantifiers.
* `Hausa.Indefinite` — bare vs. *wani*-series.

## Implementation notes

The *kō*-*wh* universal is morphologically productive — *kō* + any of
the *wh*-determiners from the *wa*- paradigm (Newman §21 Table 2,
Jaggar §9.5.1 Table 24). The `UniversalQuantifier.kowWh` constructor abstracts
over this productivity rather than enumerating each surface form.
-/

namespace Hausa

/-- The two morphologically distinct Hausa adnominal universal
quantifiers ([newman-2000] §17.5; [jaggar-2001] §9.5). -/
inductive UniversalQuantifier where
  /-- *kō-*+*wh* productive paradigm: *kōwā* 'everyone', *kōmē*
      'everything', *kōwānè* / *kōwàcè* / *kōwàdànnè* 'every X (m./f./pl.)',
      *kō'inā* 'everywhere', *kōyàushē* 'always'. Singulative-
      distributive: quantifies the individual members of the NP set
      unit-by-unit ([jaggar-2001] §9.5.1 p.370). -/
  | kowWh
  /-- *DUK* 'all', allomorphs *duk* and *dukà*. Collective "single set"
      scope; does not inflect for gender or number; can quantify SG
      count, PL count, or mass NPs ([jaggar-2001] §9.5.4 p.376). -/
  | duk
  deriving DecidableEq, Repr

/-- The two Hausa adnominal indefinite strategies
([jaggar-2001] §12.3). -/
inductive Indefinite where
  /-- Bare NP indefinite. -/
  | bare
  /-- *wani* (m.) / *wata* (f.) / *wa(dan)su* (pl.), the marked
      indefinite determiner from the *wa*-paradigm
      ([newman-2000] §21.1 row 8). -/
  | wani
  deriving DecidableEq, Repr

end Hausa
