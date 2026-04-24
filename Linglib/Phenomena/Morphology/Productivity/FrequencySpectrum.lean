/-!
# Productivity rankings for English derivational suffixes

@cite{odonnell-2015}

Theory-neutral observations about three English nominalising
suffixes — *-ness*, *-ion*, *-ate* — that @cite{odonnell-2015}
Chapter 7 uses as the central empirical contrast for evaluating
the five FG-family models. The three suffixes are chosen because
intuitive judgments and earlier literature converge: *-ness*:Adj>N
is highly productive (e.g. *pine-scentedness*); *-ion*:V>N is
unproductive despite high token frequency (\**meetion* — see
@cite{odonnell-2015} p. 261); *-ate*:BND>V is restricted to bound
stems and so cannot productively attach to novel verbs.

The book's central Chapter 7 empirical claim (Fig 7.3, p. 262;
Table 7.1, p. 265) is that **only the FG model places *-ness* in
its top-5 most productive suffixes**, and **all four competing
models (DMPCFG, MAG, DOP1, ENDOP) wrongly predict *-ion* as
highly productive**, with three of them (DMPCFG, DOP1, ENDOP)
also wrongly predicting *-ate* as productive. The intuitive
ordering of productivity is `ness > ion ≈ ate` (the latter two
both unproductive, distinguished only by selectional restrictions).

The book's frequency-spectrum facts (Fig 7.4, p. 267; Fig 1.1,
p. 20 in the introduction) supply the distributional evidence:
*-ness* has the LNRE shape characteristic of a productive process
(many low-frequency types, hapax-rich); *-ion* and *-ate* do not.

This file states the **qualitative** rankings and spectrum shapes;
specific token-frequency values (e.g. the maxima visible in
Fig 7.4) are not formalized — per CLAUDE.md, regression-summary
numbers belong in prose.

## What's here

- `Suffix` — the three suffixes
- `PeakLocation`, `TypeTokenRatio` — qualitative bins for the
  spectrum
- `SuffixSpectrum` — the three properties of the empirical spectrum
- `observed` — the spectrum shape attributed to each suffix
- `Suffix.productivityIndex` — pre-theoretic numeric ranking
- `moreProductiveThan` — strict ordering on suffixes; theories must
  reproduce this to match @cite{odonnell-2015} Fig 7.3

These data are picked up downstream by Studies files that bridge
them to predictions of the various probabilistic-grammar models.

## Theory neutrality

This file contains *no* theoretical interpretation. The terms
"productive" and "unproductive" used in the docstring above are
pre-theoretic descriptions consistent with the literature
@cite{odonnell-2015} reviews; the file commits to nothing about
*why* one suffix is productive and another is not. Theories that
account for the observed pattern import this data and produce
explanations.

The "large number of rare events" classification in
`SuffixSpectrum.isLNRE` is a distributional property attributed
in @cite{odonnell-2015} to a broader literature on word-frequency
distributions; it is not itself a theoretical commitment about the
mechanism that gives rise to such distributions.
-/

namespace Phenomena.Morphology.Productivity

/--
The three English derivational suffixes that @cite{odonnell-2015}
Chapter 7 uses as the central productivity contrast.

- *-ness* (Adj>N): highly productive (`tall` → `tallness`,
  `pine-scented` → `pine-scentedness`).
- *-ion* (V>N): high token frequency but unproductive on novel
  verbs (\**meetion* — Ch 7 p. 261).
- *-ate* (BND>V): restricted to bound stems (e.g. `segregate`
  from `segregat-`); cannot productively attach to free verbs.
-/
inductive Suffix where
  | ness
  | ion
  | ate
  deriving DecidableEq, Repr

/--
Where the mass of a word-frequency spectrum is concentrated. A
spectrum peaked at low frequencies indicates a large number of
low-token-count types — characteristic of a productive process that
generates many novel coinages. A spectrum spread toward higher
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
The three spectra shown qualitatively in @cite{odonnell-2015}
Figure 7.4 (p. 267) and discussed in Chapter 7.

- *-ness*: low-frequency peak, LNRE shape, high type-token ratio
  (productive — the only one of the three placed in any model's
  top-5 by the FG model).
- *-ion*: peak shifted toward high frequencies, no LNRE shape,
  low type-token ratio (despite ~1117 word types, the distribution
  is dominated by high-frequency lemmas; not productive in the
  novel-coinage sense).
- *-ate*: similar high-frequency shape as *-ion*, restricted to
  bound stems (cannot attach to free verbs at all, so productivity
  on novel free-verb stems is structurally zero).
-/
def observed : Suffix → SuffixSpectrum
  | .ness => { peak := .low,  isLNRE := true,  typeTokenRatio := .high }
  | .ion  => { peak := .high, isLNRE := false, typeTokenRatio := .low  }
  | .ate  => { peak := .high, isLNRE := false, typeTokenRatio := .low  }

/--
A pre-theoretic *productivity index* for the three suffixes —
higher is more productive. Used as the basis for `moreProductiveThan`.

Coding `ness > ion > ate` reproduces the ordering implied by
@cite{odonnell-2015} Chapter 7 (Fig 7.3, Table 7.1, the §7.3.1.1
discussion). The `ion > ate` direction is a tie-break: both are
unproductive on novel forms, but `ate` is structurally more
restricted (bound stems only), so we rank it strictly lower.
-/
def Suffix.productivityIndex : Suffix → Nat
  | .ness => 2
  | .ion  => 1
  | .ate  => 0

/--
The pre-theoretic strict ordering on the three suffixes by
productivity. Any theory of productivity that purports to account
for the @cite{odonnell-2015} Chapter 7 data must reproduce this
ordering; failure to do so falsifies the theory against the data
(this is exactly the discriminator deployed against DMPCFG / MAG /
DOP1 / ENDOP in @cite{odonnell-2015} Fig 7.3, all of which place
*-ion* in their top 5).

Defined as `>` on `Suffix.productivityIndex`, which gives
decidability and the standard order properties for free.
-/
def moreProductiveThan (a b : Suffix) : Prop :=
  a.productivityIndex > b.productivityIndex

instance : DecidableRel moreProductiveThan := fun a b =>
  inferInstanceAs (Decidable (a.productivityIndex > b.productivityIndex))

end Phenomena.Morphology.Productivity
