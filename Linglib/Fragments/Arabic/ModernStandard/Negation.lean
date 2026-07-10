import Linglib.Syntax.Negation

/-!
# Modern Standard Arabic negation

The MSA standard-negation inventory — four preverbal particles (*laa*, *lam*,
*lan*, *maa*) plus the inflecting copular verb *lays-a* 'to not be' — typed
against `Syntax.Negation` and bundled into a `NegationSystem`.

## Main definitions

* `negMarkers` — the five sentential negators.
* `negationSystem` — markers plus WALS Ch 112A/143A/144A datapoints (`ofISO "arb"`).

## Implementation notes

*lam* / *lan* condition a mood shift (jussive / subjunctive) on an otherwise
finite verb, and *lays-a* supplies a finite copula where the affirmative is
verbless. MSA (`arb`) is absent from [miestamo-2005] and from WALS
Ch 113A/114A (which carry only Egyptian `arz`), so no symmetric/asymmetric
coding is recorded here; the position fields (Ch 143A/144A) are WALS-pulled
by `NegationSystem.ofISO`.

## References

* [ryding-2005] ch. 37: §37.1 *lays-a* (paradigm chart §37.1.1),
  §37.2 the particles (*laa* §37.2.1, *lam* §37.2.2.1, *maa* §37.2.2.2,
  *lan* §37.2.3); jussive §35.1, subjunctive §34.2.
* [benmamoun-2000] ch. 6.
-/

namespace Arabic.ModernStandard.Negation

open Syntax.Negation

/-- The five-marker inventory: *laa* (general / present), *lam* (past),
    *lan* (future), *maa* (past, colloquial-leaning), *lays-a* (copular). The
    four particles precede the verb; *lays-a* is itself a verb inflecting for
    person / number / gender. -/
def negMarkers : List NegMarkerEntry :=
  [ { form := "laa"
    , gloss := "NEG.IPFV"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "lam"
    , gloss := "NEG.PST"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "lan"
    , gloss := "NEG.FUT"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "maa"
    , gloss := "NEG.PST"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "lays-a"
    , gloss := "NEG.COP"
    , morphemeType := .auxVerb
    , position := .preverbal }
  ]

/-- Bundled `NegationSystem` (markers + WALS Ch 112A/143A/144A datapoints
    pulled from `Data.WALS` by ISO code `arb`). -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "arb" negMarkers

end Arabic.ModernStandard.Negation
