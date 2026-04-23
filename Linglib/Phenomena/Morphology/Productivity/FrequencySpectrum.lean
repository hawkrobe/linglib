/-!
# Frequency spectra for English derivational suffixes

@cite{odonnell-2015}

Theory-neutral observations about the type/token frequency
distribution of words ending in three English derivational suffixes
that @cite{odonnell-2015} uses as central data in Chapters 6–7.

The three suffixes -*ness*, -*ity*, and -*th* are not equally
productive: -*ness* attaches freely to new bases (e.g.
*pine-scentedness*); -*ity* attaches more restrictively; -*th* is
essentially fossilized (*coolth* is marked).

This file states the **qualitative shape** of the spectra reported in
@cite{odonnell-2015} Figure 1.1 — derived from the CELEX +
SWITCHBOARD corpus used in Chapter 7. Specific token-frequency values
(e.g. the maxima 1097, 2981, 22026 visible in the figure) are not
formalized; per `CLAUDE.md`, regression-summary numbers belong in
prose with citations, not in theorems.

## What's here

- `Suffix` — the three suffixes
- `PeakLocation`, `TypeTokenRatio` — qualitative bins for the spectrum
- `SuffixSpectrum` — the three properties of the empirical spectrum
- `observed` — the spectrum shape attributed to each suffix
- `moreProductiveThan` — the pre-theoretic ordering visible in the
  spectra; theories must reproduce this to match the data

These data are picked up downstream by Studies files that bridge them
to predictions of the various probabilistic-grammar models discussed
in @cite{odonnell-2015} Chapters 4–5 (past tense) and 6–7
(derivational morphology).

## Theory neutrality

This file contains *no* theoretical interpretation. The terms
"productive" and "fossilized" used in the docstring above are
pre-theoretic descriptions; the file commits to nothing about *why*
-*th* is unproductive (whether by listing, by gap in the lexicon, by
phonological selectivity, or by inference from corpus distribution).
Theories that account for the observed pattern import this data and
produce explanations.

The "large number of rare events" classification in `SuffixSpectrum.isLNRE`
is a distributional property attributed in @cite{odonnell-2015} to a
broader literature on word-frequency distributions; it is not itself
a theoretical commitment about the mechanism that gives rise to such
distributions.
-/

namespace Phenomena.Morphology.Productivity

/--
The three English derivational suffixes that @cite{odonnell-2015}
uses as the central productivity contrast in Chapters 6–7. -*ness*
and -*ity* are nominal-from-adjective; -*th* is also nominal-from-
adjective but covers a small fossilized class (*warmth*, *width*,
*sloth*, *dearth*).
-/
inductive Suffix where
  | ness
  | ity
  | th
  deriving DecidableEq, Repr

/--
Where the mass of a word-frequency spectrum is concentrated. A
spectrum peaked at low frequencies indicates a large number of
low-token-count types — characteristic of a productive process that
generates many new coinages. A spectrum spread toward higher
frequencies indicates that the relevant types are mostly common
existing words rather than novel coinages.
-/
inductive PeakLocation where
  | low
  | mid
  | high
  deriving DecidableEq, Repr

/--
Type-token ratio class. `high` = many distinct types each with low
token count; `low` = few types each with high token count. The ratio
is itself a coarse proxy for productivity: productive processes
generate many novel types, raising the ratio.
-/
inductive TypeTokenRatio where
  | high
  | mid
  | low
  deriving DecidableEq, Repr

/--
Qualitative properties of the word-frequency spectrum for words
formed by some derivational process.

The `isLNRE` flag marks the "large number of rare events"
classification of word-frequency distributions used in
@cite{odonnell-2015} as a diagnostic for productive processes: a
distribution where most types are singletons or near-singletons and
the tail extends far is the distributional fingerprint of an active
word-formation process.
-/
@[ext]
structure SuffixSpectrum where
  peak : PeakLocation
  isLNRE : Bool
  typeTokenRatio : TypeTokenRatio
  deriving DecidableEq, Repr

/--
The three spectra shown qualitatively in Figure 1.1 of
@cite{odonnell-2015}.

- -*ness*: productive end — low-frequency peak, LNRE shape, high
  type-token ratio.
- -*ity*: intermediate — peak at low frequencies but less sharp,
  spectrum extends further toward higher frequencies, lower
  type-token ratio than -*ness*.
- -*th*: fossilized end — mass spread toward higher frequencies, no
  LNRE shape, low type-token ratio.
-/
def observed : Suffix → SuffixSpectrum
  | .ness => { peak := .low,  isLNRE := true,  typeTokenRatio := .high }
  | .ity  => { peak := .low,  isLNRE := false, typeTokenRatio := .mid  }
  | .th   => { peak := .high, isLNRE := false, typeTokenRatio := .low  }

/--
A pre-theoretic *productivity index* for the three suffixes — higher
is more productive. Used as the basis for `moreProductiveThan`.

Coding `ness > ity > th` reproduces the qualitative ordering visible
in the @cite{odonnell-2015} Figure 1.1 spectra.
-/
def Suffix.productivityIndex : Suffix → Nat
  | .ness => 2
  | .ity  => 1
  | .th   => 0

/--
The pre-theoretic strict ordering on the three suffixes by
productivity. Any theory of productivity that purports to account for
the @cite{odonnell-2015} data must reproduce this ordering; failure
to do so falsifies the theory against the data.

Defined as `>` on `Suffix.productivityIndex`, which gives
decidability and the standard order properties for free.
-/
def moreProductiveThan (a b : Suffix) : Prop :=
  a.productivityIndex > b.productivityIndex

instance : DecidableRel moreProductiveThan := fun a b =>
  inferInstanceAs (Decidable (a.productivityIndex > b.productivityIndex))

end Phenomena.Morphology.Productivity
