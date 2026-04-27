import Linglib.Features.InformationStructure

/-!
# Italian Polarity-Marking Strategies
@cite{garassino-jacob-2018} @cite{bernini-1995} @cite{poletto-zanuttini-2013} @cite{batllori-hernanz-2013}

Italian marks emphatic polarity affirmation with the construction *sì che*,
the surface-level cognate of Spanish *sí que*: an affirmative polarity
particle *sì* followed by the complementizer *che* introducing an embedded
clause carrying the asserted proposition. Whether the construction is
analyzed as a cleft, a left-peripheral PolP, or a reduplication structure
is contested (see "Analyses" below).

## Examples

- "È poi arrivato Gianni?" (Has Gianni arrived?)
  → "Sì che è arrivato." (Of course he has.) — example from
  @cite{poletto-zanuttini-2013} cited in @cite{garassino-jacob-2018} (ex. 17).

- "No ha cantado la soprano." (The soprano didn't sing.)
  → "Sí que ha cantado la soprano." (She DID sing.) — Spanish cognate,
  from @cite{batllori-hernanz-2013}.

## Corpus distribution (@cite{garassino-jacob-2018} Table 1)

In @cite{garassino-jacob-2018}'s search of the *Direct Europarl* corpus
(Italian 2.3M words, French 2.5M, Spanish 2.8M), the *sì che / sí que*
construction is attested **0 times in Italian, 61 times in Spanish**, and
not searched for in French. The picture is sharpened by the polar
left-dislocation counts in the same table (Italian 6, French 4, Spanish 0):
the two constructions are in **complementary distribution** across the
three languages — Italian uses LDs where Spanish uses *sí que*. *Sì che*
is well-attested in the Italian literature (@cite{bernini-1995};
@cite{poletto-zanuttini-2013}) and appears in Italian translations of
speeches originally given in other languages, but is dispreferred in
spontaneous Italian production at the European Parliament register.

## Cross-linguistic class — caveat

*Sì che* shares the surface schema *[affirmative-particle + complementizer]*
with Spanish *sí que*, but the wider lumping with French *si*, German *doch*,
and Swedish *jo* obscures real differences. Per @cite{garassino-jacob-2018}
(fn 11), French *si* is restricted to **dialogical contexts** — it answers a
preceding negative turn — making it a response particle, not a clause-initial
construction comparable to *sì che*. German *doch* and Swedish *jo* are
likewise sentence-medial discourse / response particles. So the substrate's
encoding of all five entries with `strategy = .polarityReversal` records a
shared functional role, not a shared syntactic category.

## Analyses

The literature does not converge on a single syntactic analysis:

- @cite{bernini-1995}: *sì che* is a **cleft-like** structure (a "profrasi"),
  with the embedded *che*-clause analogous to a cleft pivot.
- @cite{poletto-zanuttini-2013}: *sì che* is a **reduplication** structure
  in which the polarity particle *sì* and the complementizer *che* together
  realize the same syntactic head in the left periphery (a polarity head).

The Lean encoding here records the entry's surface form and pragmatic
distribution, and is neutral between these analyses. Analytical content
specific to Garassino & Jacob's chapter — the corpus interpretation,
the strategy taxonomy, and the explicit endorsement of Matić & Nikolaeva's
"salient polarity" framework — lives in
`Phenomena/Polarity/Studies/GarassinoJacob2018.lean`.
-/

namespace Fragments.Italian.PolarityMarking

open Features.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy PolarityMarkingEnv)

/-- *sì che* — Italian polarity-reversing affirmative construction.
    Cleft-like or left-peripheral PolP structure (analyses contested):
    affirmative particle *sì* + complementizer *che*. Clause-initial;
    not sentence-internal. Licensed in both *contrast* and *correction*
    environments — @cite{garassino-jacob-2018} ex. 17 (a positive
    answer to a yes/no question with no negative antecedent) is a
    contrast-context use, not a correction; @cite{batllori-hernanz-2013}
    note that the cognate Spanish *sí que* also occurs in
    non-contradictory contexts (G&J ex. 19). The earlier `correction`-only
    encoding was empirically too narrow.
    @cite{garassino-jacob-2018}: cognate of Spanish *sí que*;
    rare in spontaneous Italian corpora but grammatically available. -/
abbrev siChe : PolarityMarkingEntry where
  label := "sì che"
  form := some "sì che"
  environments := {.correction, .contrast}
  strategy := .polarityReversal

def allPolarityMarkings : List PolarityMarkingEntry := [siChe]

-- Per-entry verification theorems
theorem siChe_form : siChe.form = some "sì che" := rfl
theorem siChe_not_sentenceInternal : PolarityMarkingEnv.sentenceInternal ∉ siChe.environments := by decide
theorem siChe_contrastOk : PolarityMarkingEnv.contrast ∈ siChe.environments := by decide
theorem siChe_correctionOk : PolarityMarkingEnv.correction ∈ siChe.environments := by decide
theorem siChe_strategy : siChe.strategy = .polarityReversal := rfl

end Fragments.Italian.PolarityMarking
