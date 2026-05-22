import Linglib.Studies.KrizChemla2015

/-!
# @cite{augurzky-etal-2023}: QUD manipulation of homogeneity projection

Empirical data from Augurzky, Bonnet, Breheny, Cremers, Ebert, Mayr, Romoli,
Steinbach & Sudo (2023), "Putting plural definites into context," *Sinn und
Bedeutung 27*: 19-32.

## Empirical contribution

Augurzky et al. extend the Križ & Chemla 2015 paradigm
(`@cite{kriz-chemla-2015}`, formalized at
`Studies/KrizChemla2015.lean`) by manipulating the QUD
between participants:

- **Strict context**: QUD targets the strongest reading.
- **Lax context**: QUD targets the weakest reading.

Across two experiments, they find:

- `every` is highly QUD-sensitive (low acceptance in strict, high in lax).
- `no` is essentially QUD-insensitive (low acceptance in both).
- `not every` patterns with `every` (high in lax), NOT with `no` — despite
  both `no` and `not every` being downward-entailing.

The `no` / `not every` asymmetry is the central puzzle.

## Provenance

This data was previously bundled inside `Phenomena/Imprecision/Projection.lean`
(then `Studies/Haslinger2025.lean`). Moved here at 0.230.521 — the empirical
anchor is Augurzky et al. 2023, not Haslinger. The asymmetry's *theoretical
explanation* in the original file invoked exhaustification logic from
`@cite{bar-lev-2021}` rather than Augurzky's or Haslinger's account; that
explanation has been replaced with a statement of the empirical pattern alone,
with the rival explanations cited as future-work targets.

-/

namespace AugurzkyEtAl2023

open KrizChemla2015 (EmbeddingOperator)

/--
QUD-manipulation datum for plural-definite acceptance in gap scenarios.

Source: @cite{augurzky-etal-2023}, Experiments 1-2.

The acceptance fields are coded categorically ("low"/"medium"/"high") since
the original numerical rates depend on per-experiment baselines and stimulus
sets; consult @cite{augurzky-etal-2023} Tables 1-2 for raw rates.
-/
structure QUDManipulationDatum where
  /-- The embedding operator -/
  operator : EmbeddingOperator
  /-- Sentence -/
  sentence : String
  /-- Strict reading (QUD = strong) -/
  strictReading : String
  /-- Lax reading (QUD = weak) -/
  laxReading : String
  /-- Gap scenario -/
  gapScenario : String
  /-- Acceptance rate in STRICT context (gap scenario) -/
  strictContextAcceptance : String  -- "low", "medium", "high"
  /-- Acceptance rate in LAX context (gap scenario) -/
  laxContextAcceptance : String
  /-- Is there an interaction (context effect differs by operator)? -/
  contextEffect : Bool
  deriving Repr

def everyQUDEffect : QUDManipulationDatum :=
  { operator := .every
  , sentence := "Every boy opened his presents."
  , strictReading := "Every boy opened all his presents"
  , laxReading := "Every boy opened some of his presents"
  , gapScenario := "Every boy opened some, not all opened all"
  , strictContextAcceptance := "low"   -- strict QUD → reject in gap
  , laxContextAcceptance := "high"     -- lax QUD → accept in gap
  , contextEffect := true              -- big effect of QUD
  }

def noQUDEffect : QUDManipulationDatum :=
  { operator := .no
  , sentence := "No boy opened his presents."
  , strictReading := "No boy opened any presents"
  , laxReading := "No boy opened all his presents"
  , gapScenario := "Some boys opened some, none opened all"
  , strictContextAcceptance := "low"
  , laxContextAcceptance := "low"      -- still low — QUD-insensitive
  , contextEffect := false             -- small effect of QUD
  }

def notEveryQUDEffect : QUDManipulationDatum :=
  { operator := .notEvery
  , sentence := "Not every boy opened his presents."
  , strictReading := "At least one boy opened none"
  , laxReading := "At least one boy didn't open all"
  , gapScenario := "Some boys opened some but not all"
  , strictContextAcceptance := "low"
  , laxContextAcceptance := "high"     -- unlike `no`
  , contextEffect := true              -- big effect of QUD
  }


/--
The `no` / `not every` asymmetry: empirical pattern only.

Both operators are downward-entailing, yet `not every` permits the
weak/non-maximal reading in gap scenarios while `no` does not. This is
the central empirical puzzle of @cite{augurzky-etal-2023}.

Two rival theoretical accounts in the literature (cited as future-work
targets, NOT endorsed by this file):
- @cite{bar-lev-2021}: exhaustification — `not every` triggers a scalar
  implicature creating a non-monotonic context where embedded
  exhaustification can strengthen the embedded plural; `no` lacks the
  triggering implicature.
- @cite{haslinger-2025-diss} §3.6.2 (Magri effects): the asymmetry follows
  from how potential p-equivalence and complexity interact with embedding
  monotonicity; see also `Studies/Haslinger2025.lean`.

The two accounts make divergent predictions for embedded environments not
yet tested experimentally.
-/
structure NoNotEveryAsymmetryDatum where
  /-- `no` sentence -/
  noSentence : String
  /-- `not every` sentence -/
  notEverySentence : String
  /-- Gap scenario -/
  gapScenario : String
  /-- `no` permits weak reading in gap? -/
  noPermitsWeak : Bool
  /-- `not every` permits weak reading in gap? -/
  notEveryPermitsWeak : Bool
  deriving Repr

def noNotEveryAsymmetry : NoNotEveryAsymmetryDatum :=
  { noSentence := "No boy opened his presents."
  , notEverySentence := "Not every boy opened his presents."
  , gapScenario := "Half opened all, half opened some but not all"
  , noPermitsWeak := false      -- "no boy opened ALL" reading unavailable
  , notEveryPermitsWeak := true -- "not every boy opened ALL" available
  }


-- Collections

def qudManipulationData : List QUDManipulationDatum :=
  [everyQUDEffect, noQUDEffect, notEveryQUDEffect]

end AugurzkyEtAl2023
