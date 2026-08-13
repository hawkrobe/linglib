import Linglib.Syntax.Category.Determiner.Basic

/-!
# Hausa determiner inventory

Textbook-consensus types for the Hausa (Chadic, ISO `ha`) determiner system,
with no analytical denotations. Hausa has two definite articles: the weak
suffix *-n* (*-r̃* after feminine nouns), used for uniquely identifiable
referents including inferable first mentions, and the strong *ɗîn*, used for
referents already in the discourse. The two-article classification is
tentative, since bare nominals can also be definite and consonant-final
loanwords take *ɗîn* for both uses. Covarying (donkey) uses are unreported
for both articles. Indefinites are bare or take the *wani*-series; the two
universal quantifiers are the *kō*-*wh* paradigm and *DUK*. Paper-specific
denotations (Q_∀ + ONE decomposition, choice-function vs. ∃-quantifier
analysis of *wani*, etc.) live in Studies files that consume these entries.

## Main declarations

* `Hausa.Determiners.inventory` — the declared inventory, deriving the
  `.bipartite` Moroney cell.
* `Hausa.Determiners.UniversalQuantifier` — the two morphologically distinct
  Hausa universal quantifiers.
* `Hausa.Determiners.Indefinite` — bare vs. *wani*-series.

## Implementation notes

The *kō*-*wh* universal is morphologically productive — *kō* + any of
the *wh*-determiners from the *wa*- paradigm ([newman-2000] §21 Table 2,
[jaggar-2001] §9.5.1 Table 24). The `UniversalQuantifier.kowWh` constructor
abstracts over this productivity rather than enumerating each surface form.

## References

* [schwarz-2013], §4.2.2
* [buba-1997]
* [jaggar-2001], §9.5, §12.3
* [newman-2000], §17.5, §20, §21
-/

namespace Hausa.Determiners

/-- The Hausa determiners are the weak definite *-n*, the strong definite
    *ɗîn*, and the marked indefinite *wani* (feminine *wata*, plural *wasu*). -/
def inventory : Determiner.Inventory :=
  [ .article { form := "-n", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.largerSituation] },
    .article { form := "ɗîn", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric] },
    .article { form := "wani", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]

/-- Hausa derives the `.bipartite` Moroney cell. -/
theorem marking : inventory.markingStrategy = .bipartite := by decide

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

end Hausa.Determiners
