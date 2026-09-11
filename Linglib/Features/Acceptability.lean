import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Features.Acceptability — Linguistic Acceptability Diacritics

Standard acceptability diacritics used in linguistic papers, encoded as
a six-way taxonomy. These correspond to the conventional marks placed
before example sentences:

- (unmarked) = fully acceptable
- `?`        = degraded/marginal
- `??`       = quite degraded
- `*`        = clearly unacceptable
- `#`        = semantically/pragmatically anomalous (syntactically well-formed)
- `%`        = dialectally variable / speaker-dependent

The semantic-vs-syntactic split (`#` vs `*`) and dialect marker (`%`) are
linguistically substantive distinctions, not just gradient acceptability;
this is why the type is a labeled enum rather than a Likert-style ordinal.

`Judgment` is the ordinal cousin: the Schütze/Sprouse five-level
acceptability scale, a `LinearOrder` with `ungrammatical` at the bottom
and `acceptable` at the top, so that `≤` reads "rated at most as
acceptable as". It is the judgment type carried by
`Linglib/Data/Examples/Schema.lean`'s `LinguisticExample` and by the
minimal-pair vocabulary in `Linglib/Features/MinimalPairs.lean`. For
factorial-design machinery over experimental ratings (difference-in-
differences scores etc.), see `Linglib/Studies/SprouseEtAl2012.lean`.
-/

namespace Features

/-- Standard acceptability diacritics used in linguistic papers. -/
inductive Acceptability where
  /-- (unmarked) fully acceptable -/
  | ok
  /-- `?` degraded but not out -/
  | marginal
  /-- `??` quite degraded -/
  | degraded
  /-- `*` clearly unacceptable -/
  | unacceptable
  /-- `#` semantically/pragmatically odd -/
  | anomalous
  /-- `%` dialectally variable -/
  | variable
  deriving Repr, DecidableEq

/-- Acceptability / felicity judgment on the Schütze/Sprouse five-level
    scale, ordered by acceptability: `ungrammatical` is the least and
    `acceptable` the greatest judgment.

    Use `.acceptable` for clean grammatical/felicitous data; reserve
    `.ungrammatical` for hard star judgments and `.unacceptable` for
    pragmatic/felicity failure short of ungrammaticality. -/
inductive Judgment where
  | acceptable
  | marginal
  | questionable
  | unacceptable
  | ungrammatical
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- The position on the scale, `ungrammatical` lowest. -/
def Judgment.rank : Judgment → Fin 5
  | .ungrammatical => 0
  | .unacceptable => 1
  | .questionable => 2
  | .marginal => 3
  | .acceptable => 4

instance : LinearOrder Judgment := LinearOrder.lift' Judgment.rank (by decide)

end Features
